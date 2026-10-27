module

public import CFSG.HardMathSupport.Lang.E6Descent.OutRankE6
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Lang.E6Descent

section Abstract

variable {P : Type*} [Group P]

theorem closure_fixUnion_eq_top_of_maximal_escape {E : Subgroup (MulAut P)} {α β : MulAut P}
    (hα : α ∈ E) (hα1 : α ≠ 1) (hβ : β ∈ E) (hβ1 : β ≠ 1)
    (hmax : ∀ M : Subgroup P, fixedSubgroup α ≤ M → M = fixedSubgroup α ∨ M = ⊤)
    (hesc : ¬ fixedSubgroup β ≤ fixedSubgroup α) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  have hRH : fixedSubgroup α ≤ Subgroup.closure (fixUnion E) :=
    fun x hx => Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hα hα1 hx)
  have hSH : fixedSubgroup β ≤ Subgroup.closure (fixUnion E) :=
    fun x hx => Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hβ hβ1 hx)
  rcases hmax _ hRH with h | h
  · exact absurd (fun x hx => h ▸ hSH hx) hesc
  · exact h

theorem closure_fixUnion_eq_top_of_kernel_escape [Finite P] {N : Subgroup (MulAut P)} [N.Normal]
    {R : Subgroup P} (hmax : ∀ M : Subgroup P, R ≤ M → M = R ∨ M = ⊤)
    (hker : ∀ ι ∈ N, (∀ x ∈ R, ι x = x) → ι = 1) {E : Subgroup (MulAut P)}
    {α ι ψa ψb : MulAut P} (hαE : α ∈ E) (hιE : ι ∈ E) (hα1 : α ≠ 1) (hβ1 : α * ι ≠ 1)
    (hι1 : ι ≠ 1) (hιN : ι ∈ N) (hFa : fixedSubgroup (ψa * α * ψa⁻¹) = R)
    (hFb : fixedSubgroup (ψb * (α * ι) * ψb⁻¹) = R) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  rw [fixedSubgroup_conj] at hFa hFb
  have hmaxα : ∀ M : Subgroup P, fixedSubgroup α ≤ M → M = fixedSubgroup α ∨ M = ⊤ := by
    intro M hM
    have hle : R ≤ M.map ψa.toMonoidHom := by
      rw [← hFa]
      exact Subgroup.map_mono hM
    have hMeq : M = (M.map ψa.toMonoidHom).comap ψa.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective ψa.injective M).symm
    rcases hmax _ hle with h | h
    · left
      rw [hMeq, h, ← hFa]
      exact Subgroup.comap_map_eq_self_of_injective ψa.injective _
    · right
      rw [hMeq, h]
      exact Subgroup.comap_top _
  refine closure_fixUnion_eq_top_of_maximal_escape hαE hα1 (E.mul_mem hαE hιE) hβ1 hmaxα ?_
  intro hle
  have hcard : Nat.card (fixedSubgroup (α * ι)) = Nat.card (fixedSubgroup α) := by
    have h1 := congrArg (fun H : Subgroup P => Nat.card H) hFb
    have h2 := congrArg (fun H : Subgroup P => Nat.card H) hFa
    rw [Subgroup.card_map_of_injective ψb.injective] at h1
    rw [Subgroup.card_map_of_injective ψa.injective] at h2
    rw [h1, h2]
  have heq : fixedSubgroup (α * ι) = fixedSubgroup α :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hιfix : ∀ x ∈ fixedSubgroup α, ι x = x := by
    intro x hx
    have hx' : x ∈ fixedSubgroup (α * ι) := heq ▸ hx
    have h1 : (α * ι) x = x := hx'
    have h2 : α x = x := hx
    simp only [MulAut.mul_apply] at h1
    exact α.injective (h1.trans h2.symm)
  have hι'fix : ∀ x ∈ R, (ψa * ι * ψa⁻¹) x = x := by
    intro x hx
    rw [← hFa] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show (ψa * ι * ψa⁻¹) (ψa y) = ψa y
    simp [MulAut.mul_apply, hιfix y hy]
  have h1 := hker _ (‹N.Normal›.conj_mem ι hιN ψa) hι'fix
  apply hι1
  have h2 : ψa⁻¹ * (ψa * ι * ψa⁻¹) * ψa = ι := by group
  rw [← h2, h1]
  simp

theorem exists_ne_one_mem_ker_of_card_le {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (Θ : MulAut P →* H) [Finite {h : H // h ^ p = 1}] (hH : Nat.card {h : H // h ^ p = 1} ≤ p)
    (E : Subgroup (MulAut P)) [hE : CFSG.IsElementaryAbelian p ↥E] (hEc : Nat.card ↥E = p ^ 2) :
    ∃ ι ∈ E, ι ≠ 1 ∧ ι ∈ Θ.ker := by
  have : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨a, b, hab, hΘ⟩ := exists_ne_map_eq_of_plane hp Θ hH E
    (fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx) hEc
  refine ⟨(a : MulAut P)⁻¹ * (b : MulAut P), E.mul_mem (E.inv_mem a.2) b.2, ?_, ?_⟩
  · intro h
    exact hab (Subtype.ext (inv_mul_eq_one.1 h))
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hΘ, inv_mul_cancel]

end Abstract

section Transport

variable {d : TauCeti.ValidLieTypeIndex} {P : Type} [Group P]

theorem planeGen_outer_of_closure (e : Cat d ≃* P) {p : ℕ} (hp : p.Prime)
    (h : ∀ E' : Subgroup (MulAut P), CFSG.IsElementaryAbelian p E' → Nat.card E' = p ^ 2 →
      (¬ ∀ φ ∈ E', ∃ g : P, φ = MulAut.conj g) → Subgroup.closure (fixUnion E') = ⊤)
    {E : Subgroup (MulAut (Cat d))} (hE : CFSG.Open.IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane d p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h'
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h' φ hφ).imp fun g hg => hg.symm
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr (h _ hEi hc' hout'))

end Transport

end CFSG.LieType.SeitzGeneration.ExcWideThree
