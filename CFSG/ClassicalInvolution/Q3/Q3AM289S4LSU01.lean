module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Stmt
public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSU3

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.Q3PP (F9)

section Plain

theorem isUniqueInvolution_map {G X : Type} [Group G] [Group X] (ψ : G →* X)
    (hker : ψ.ker ≤ Subgroup.center G) {R : Subgroup G} {r : G} (hR : IsUniqueInvolution R r)
    (hcen : ∀ y ∈ R, y ∈ Subgroup.center G → y = 1) :
    IsUniqueInvolution (R.map ψ) (ψ r) where
  mem := Subgroup.mem_map_of_mem ψ hR.mem
  ne_one := fun h => hR.ne_one (hcen r hR.mem (hker (MonoidHom.mem_ker.mpr h)))
  sq := by rw [← map_mul, hR.sq, map_one]
  unique := by
    rintro _ ⟨y, hy, rfl⟩ hy2
    have h1 : y * y ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hy2
    have h2 : y * y = 1 := hcen _ (R.mul_mem hy hy) (hker h1)
    rcases hR.unique y hy h2 with h3 | h3
    · left
      rw [h3, map_one]
    · right
      rw [h3]

theorem map_conj_eq_conjSub {G X : Type} [Group G] [Group X] (ψ : G →* X) {R₀ R : Subgroup G}
    {g : G} (h : R = R₀.map (MulAut.conj g).toMonoidHom) :
    R.map ψ = conjSub (ψ g) (R₀.map ψ) := by
  subst h
  ext x
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨ψ s, ⟨s, hs, rfl⟩, by simp [map_mul, map_inv]⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨g * s * g⁻¹, ⟨s, hs, rfl⟩, by simp [map_mul, map_inv]⟩

end Plain

section Layer


variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {zb : X}

theorem S4LayerKind.exists_hom {c : CompData} (h : S4LayerKind c Φ zb) :
    ∃ φ : c.G →* X, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center c.G ∧
      (∀ L ∈ Φ, ∃ R ∈ c.fund, L = R.map φ) ∧ ∃ f ∈ Subgroup.center c.G, φ f = zb := by
  obtain ⟨ι, -, D, i₁, hi, hk, f, hf, rfl⟩ := h
  subst hk
  refine ⟨D.hom i₁, ?_, D.ker_le_center i₁, fun L hL => ?_, f, hf, rfl⟩
  · have hrange : (D.hom i₁).range = ⊤ := by
      have h1 : (⨆ i, (D.hom i).range) = (D.hom i₁).range := by
        apply le_antisymm
        · exact iSup_le fun i => by rw [hi i]
        · exact le_iSup (fun i => (D.hom i).range) i₁
      rw [← h1]
      exact D.generate
    exact MonoidHom.range_eq_top.mp hrange
  · obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl := hi i
    exact ⟨R, hR, hLR⟩

theorem S4LayerKind.exists_su4_hom (h : S4LayerKind (CompData.model .PSU 4) Φ zb) :
    ∃ ψ : Su F9 3 1 4 →* X, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (Su F9 3 1 4) ∧
      (∀ L ∈ Φ, ∃ R ∈ longRootSetU (K := F9) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num),
        L = R.map ψ) ∧ ∃ z ∈ Subgroup.center (Su F9 3 1 4), ψ z = zb := by
  obtain ⟨φ, hs, hk, hΦ, f, hf, rfl⟩ := h.exists_hom
  have hadm : StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨e, he⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  refine ⟨φ.comp e.symm.toMonoidHom, ?_, ?_, ?_, e f, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨e x, by simp⟩
  · intro x hx
    have h1 : e.symm x ∈ φ.ker := hx
    have h2 := Subgroup.mem_map_of_mem (e : (CompData.model .PSU 4).G →* Su F9 3 1 4) (hk h1)
    rw [Subgroup.map_center_eq e] at h2
    simpa using h2
  · intro L hL
    obtain ⟨R, hR, rfl⟩ := hΦ L hL
    refine ⟨R.map e.toMonoidHom, (he R).mp hR, ?_⟩
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp
  · rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem _ hf
  · simp

end Layer

section Conj

variable {X : Type} [Group X]

theorem exists_conj_map_longRoot (ψ : Su F9 3 1 4 →* X) {R₀ R : Subgroup (Su F9 3 1 4)}
    (h₀ : R₀ ∈ longRootSetU (K := F9) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num))
    (h : R ∈ longRootSetU (K := F9) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num)) :
    ∃ g : X, R.map ψ = conjSub g (R₀.map ψ) := by
  obtain ⟨g₀, hg₀⟩ := (mem_longRootSetU_iff (by norm_num)).mp h₀
  obtain ⟨g, hg⟩ := (mem_longRootSetU_iff (by norm_num)).mp h
  refine ⟨ψ (g * g₀⁻¹), map_conj_eq_conjSub ψ ?_⟩
  rw [hg₀, hg, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

end Conj

end CFSG.ClassicalInvolution.Q3.Q3AM
