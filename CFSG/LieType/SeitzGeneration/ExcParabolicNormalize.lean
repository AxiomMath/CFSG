module

public import CFSG.RankThree.PartOne.KF1514B.Sylow
public import CFSG.LieType.Chevalley.OppositeBorel

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Chevalley

theorem mem_map_conjInv_iff {G : Type*} [Group G] {Q : Subgroup G} {g w : G} :
    w ∈ Q.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * w * g⁻¹ ∈ Q := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    show g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ ∈ Q
    have : g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z := by group
    rw [this]
    exact hz
  · intro h
    refine ⟨g * w * g⁻¹, h, ?_⟩
    show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w
    group

theorem exists_normalized_of_inner {C H : Type*} [Group C] [Group H] [Finite H] (φ : C ≃* H)
    {p r : ℕ} [Fact p.Prime] {P Q : Subgroup H} (hP : ¬ p ∣ P.index)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set H)) (hQ0 : Q ≠ ⊥) (hQr : IsPGroup r Q)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    {E : Subgroup (MulAut C)} (hEp : IsPGroup p E)
    (hE : E ≤ (MulAut.conj : C →* MulAut C).range) :
    ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r R ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R := by
  set c : C →* MulAut C := MulAut.conj with hc
  set E₀ : Subgroup C := E.comap c with hE₀
  have hE₀p : IsPGroup p E₀ := hEp.of_injective (c.subgroupComap E) fun x y h =>
    Subtype.ext (hinj (congrArg Subtype.val h))
  set E₁ : Subgroup H := E₀.map φ.toMonoidHom with hE₁
  have hE₁p : IsPGroup p E₁ := hE₀p.map _
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KF1514B.exists_conj_le_of_not_dvd_index hP hE₁p
  set Q' : Subgroup H := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'0 : Q' ≠ ⊥ := fun h =>
    hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q
      (fun a b hab => (MulAut.conj g⁻¹).injective hab)).1 h)
  have hQ'r : IsPGroup r Q' := hQr.map _
  have hnorm : ∀ y ∈ E₁, y ∈ Subgroup.normalizer (Q' : Set H) := by
    intro y hy
    have hn : g * y * g⁻¹ ∈ Subgroup.normalizer (Q : Set H) := hPQ (hg ⟨y, hy, rfl⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 : w ∈ (Q' : Set H) ↔ g * w * g⁻¹ ∈ Q := mem_map_conjInv_iff
    have h2 : y * w * y⁻¹ ∈ (Q' : Set H) ↔ g * (y * w * y⁻¹) * g⁻¹ ∈ Q := mem_map_conjInv_iff
    have h3 := Subgroup.mem_normalizer_iff.1 hn (g * w * g⁻¹)
    have h4 : g * y * g⁻¹ * (g * w * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * w * y⁻¹) * g⁻¹ := by
      group
    rw [h4] at h3
    exact h1.trans (h3.trans h2.symm)
  refine ⟨Q'.map φ.symm.toMonoidHom, ?_, hQ'r.map _, ?_⟩
  · exact fun h => hQ'0 ((Subgroup.map_eq_bot_iff_of_injective Q' φ.symm.injective).1 h)
  · intro ε hε
    obtain ⟨x, rfl⟩ := hE hε
    have hx : x ∈ E₀ := hε
    have hxn : φ x ∈ Subgroup.normalizer (Q' : Set H) := hnorm _ ⟨x, hx, rfl⟩
    have hmem : ∀ z : C, z ∈ Q'.map φ.symm.toMonoidHom ↔ φ z ∈ Q' := fun z => by
      rw [Subgroup.mem_map_equiv]
      simp
    exact map_conj_eq_of_mem_normalizer (Subgroup.mem_normalizer_iff.2 fun z => by
      rw [hmem, hmem, map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.1 hxn (φ z))

end CFSG.LieType.SeitzGeneration
