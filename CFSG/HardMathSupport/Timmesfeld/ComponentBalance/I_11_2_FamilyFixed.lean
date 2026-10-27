module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.HardMathSupport.Timmesfeld.Proving.FixedPointsGroup

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open

variable {G : Type*} [Group G]

theorem card_inf_centralizer_le_of_conj [Finite G] {p : ℕ} (hp : p.Prime) (Z Z₁ Z₂ Z₃ : Subgroup G)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hexp : ∀ a ∈ Z, a ^ p = 1)
    (x : G) (hx : ∀ v ∈ Z, x * v * x⁻¹ ∈ Z) (hZ₁ : Z₁ ≤ Z) (hcyc : IsCyclic Z₁)
    (hZ₂ : Z₂ ≤ Z₁.map (MulAut.conj x).toMonoidHom)
    (hZ₃ : Z₃ ≤ Z₂.map (MulAut.conj x).toMonoidHom) (hgen : Z ≤ Z₁ ⊔ Z₂ ⊔ Z₃) :
    Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set G)) ≤ p := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set z : G := (g : G) with hz
  have hzZ₁ : z ∈ Z₁ := g.2
  have hle1 : Z₁ ≤ Subgroup.zpowers z := by
    intro v hv
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨v, hv⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, congrArg Subtype.val hn⟩
  have hcx : ∀ w : G, (MulAut.conj x).toMonoidHom w = x * w * x⁻¹ := fun w => rfl
  set cx : G →* G := (MulAut.conj x).toMonoidHom with hcxdef
  have hle2 : Z₂ ≤ Subgroup.zpowers (cx z) := by
    refine hZ₂.trans ?_
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.map_mono hle1
  have hle3 : Z₃ ≤ Subgroup.zpowers (cx (cx z)) := by
    refine hZ₃.trans ?_
    have : Z₂.map cx ≤ (Subgroup.zpowers (cx z)).map cx := Subgroup.map_mono hle2
    rw [MonoidHom.map_zpowers] at this
    exact this
  have hclos : ∀ v ∈ Z, v ∈ Subgroup.closure
      ({z, x * z * x⁻¹, x * (x * z * x⁻¹) * x⁻¹} : Set G) := by
    intro v hv
    have hsub : Z ≤ Subgroup.closure ({z, x * z * x⁻¹, x * (x * z * x⁻¹) * x⁻¹} : Set G) := by
      refine hgen.trans (sup_le (sup_le ?_ ?_) ?_)
      · exact hle1.trans (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
      · refine hle2.trans (Subgroup.zpowers_le.2 (Subgroup.subset_closure ?_))
        simp [hcx]
      · refine hle3.trans (Subgroup.zpowers_le.2 (Subgroup.subset_closure ?_))
        simp [hcx]
    exact hsub hv
  have : Finite Z := inferInstance
  exact Proving.card_inf_centralizer_le hp Z hcomm hexp x hx (hZ₁ hzZ₁) hclos

theorem pRank_inf_le_one_of_conj [Finite G] {p : ℕ} (hp : p.Prime) (Z Z₁ Z₂ Z₃ : Subgroup G)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hexp : ∀ a ∈ Z, a ^ p = 1)
    (x : G) (hx : ∀ v ∈ Z, x * v * x⁻¹ ∈ Z) (hZ₁ : Z₁ ≤ Z) (hcyc : IsCyclic Z₁)
    (hZ₂ : Z₂ ≤ Z₁.map (MulAut.conj x).toMonoidHom)
    (hZ₃ : Z₃ ≤ Z₂.map (MulAut.conj x).toMonoidHom) (hgen : Z ≤ Z₁ ⊔ Z₂ ⊔ Z₃)
    (B : Subgroup G) (hB : ∀ b ∈ B, b * x = x * b) :
    pRank p (Z ⊓ B) ≤ 1 := by
  have hcard := card_inf_centralizer_le_of_conj hp Z Z₁ Z₂ Z₃ hcomm hexp x hx hZ₁ hcyc hZ₂ hZ₃ hgen
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEa => ?_
  have hEle : E ≤ Z ⊓ Subgroup.centralizer ({x} : Set G) := fun v hv =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hE hv)).1, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hB v (Subgroup.mem_inf.1 (hE hv)).2⟩
  calc Nat.card E ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set G)) :=
        Subgroup.card_le_of_le hEle
    _ ≤ p := hcard
    _ = p ^ 1 := (pow_one p).symm

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance

end
