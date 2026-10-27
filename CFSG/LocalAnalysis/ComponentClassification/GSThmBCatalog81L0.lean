module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Small
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace L0Psp

open CatFactsSp4 Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open scoped commutatorElement

theorem commutator_self_of_perfect {G : Type*} [Group G] {L : Subgroup G}
    (hL : Group.IsPerfect L) : ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hL.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

variable {K : Type} [Field K]

theorem commutator_fixOf_le (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g)) :
    ⁅fixOf α, fixOf α⁆ ≤ (fixOf θ).map (proj 2 K) := by
  have hfix : ∀ x ∈ fixOf α, ∃ g, proj 2 K g = x ∧ θ g * g⁻¹ ∈ spScalars 2 K := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨g, rfl, ?_⟩
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← hθα, mem_fixOf.mp hx, mul_inv_cancel]
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl, hg⟩ := hfix x hx
  obtain ⟨h, rfl, hh⟩ := hfix y hy
  refine ⟨⁅g, h⁆, ?_, map_commutatorElement _ _ _⟩
  exact fix_commutator (fun z hz => mem_center_of_mem_spScalars hz) θ.toMonoidHom hg hh

theorem commutator_fixOf_eq (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g))
    (hperf : Group.IsPerfect (fixOf θ)) :
    ⁅fixOf α, fixOf α⁆ = (fixOf θ).map (proj 2 K) := by
  refine le_antisymm (commutator_fixOf_le θ hθα) ?_
  rw [← commutator_self_of_perfect hperf, Subgroup.map_commutator]
  exact commutator_mono (map_fixOf_le θ hθα) (map_fixOf_le θ hθα)

theorem card_L0_psp {K₀ : Type} [Group K₀] [Finite K₀] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK₀ : Blueprint.LieModel K₀ .PSp 2 p f) (α : MulAut K₀)
    (hα : Cat8.IsAdmQ K₀ (p ^ f) α) : Nat.card (Cat8.L0 K₀ α) = Cat8.ordL2 ((p ^ f) ^ 2) := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hK₀
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨hsimp, u, w, huw⟩ := cfSec8Simple K₀ p f hp hp2 hf (Or.inl hK₀)
  have hc : ∀ z : K₀, z ∈ center K₀ → z = 1 := by
    intro z hz
    have hn : (center K₀).Normal := inferInstance
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [h, mem_bot] at hz
      exact hz
    · exfalso
      have hu : u ∈ center K₀ := h ▸ mem_top u
      exact huw (mem_center_iff.mp hu w).symm
  have hfixeq : Eight.fixSubgroup α = fixOf α := by
    ext x
    rfl
  set α' : MulAut (StatedProj (StatedSp 2 K)) := e.symm.trans (α.trans e) with hα'def
  have hcomm : ∀ x, e (α x) = α' (e x) := fun x => by
    simp only [hα'def, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hα'2 : α' * α' = 1 := by
    ext x
    have := congrArg (fun φ : MulAut K₀ => φ (e.symm x)) hα.sq
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    simp only [hα'def, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply, this, MulEquiv.apply_symm_apply]
  have hout' : α' ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
    rintro ⟨v, hv⟩
    apply hα.out
    refine ⟨e.symm v, ?_⟩
    ext x
    apply e.injective
    rw [hcomm, ← hv]
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hfixmap := map_fixOf_of_comm hcomm
  have hfix : Nat.card (fixOf α') = Nat.card (fixOf α) := by
    rw [← hfixmap]
    exact (Nat.card_congr ((fixOf α).equivMapOfInjective _ e.injective).toEquiv).symm
  have hdvd : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ∣ Nat.card (fixOf α') := by
    rw [hfix, ← hfixeq]
    exact hα.dvd
  obtain ⟨A, hA, d, hd0, hdsq, hAA, hμ⟩ :=
    exists_typeII_of_admissible hp hp2 hf hK α' hα'2 hout' hdvd
  obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A hd0 hdsq hAA hμ
  have hθα : ∀ g, α' (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
    rw [hA, conjAut_proj]
  have hZ : ∀ z ∈ spScalars 2 K, conjSp 2 K A z = z := fun z hz => conjSp_scalar A hz
  have heq := commutator_fixOf_eq (conjSp 2 K A) hθα hQ.1
  have hcardπ := card_map_fixOf_mul_two h2 (conjSp 2 K A) hZ
  rw [hcard] at hcardπ
  have hconj_inj : Function.Injective (MulAut.conj : K₀ →* MulAut K₀) :=
    fun g h hgh => conj_injective_of_center hc hgh
  have hL0 : Cat8.L0 K₀ α = (⁅fixOf α, fixOf α⁆).map (MulAut.conj : K₀ →* MulAut K₀) := by
    show ⁅Cat8.Inn K₀ ⊓ centralizer ({α} : Set (MulAut K₀)),
      Cat8.Inn K₀ ⊓ centralizer ({α} : Set (MulAut K₀))⁆ = _
    rw [← map_conj_fixOf hc α, Subgroup.map_commutator]
  have hcomm' : (⁅fixOf α, fixOf α⁆).map e.toMonoidHom = ⁅fixOf α', fixOf α'⁆ := by
    rw [Subgroup.map_commutator, hfixmap]
  have he : Nat.card ((⁅fixOf α, fixOf α⁆).map e.toMonoidHom) =
      Nat.card ↥(⁅fixOf α, fixOf α⁆ : Subgroup K₀) :=
    card_map_of_injective e.injective
  rw [hL0, card_map_of_injective hconj_inj, ← he, hcomm', heq]
  show _ = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2
  rw [← hcardπ, Nat.mul_div_cancel _ two_pos]

end L0Psp

open L0Psp in
theorem cf81L0 :
    CF81L0 := by
  intro K₀ _ _ p f hp hp2 hf hK α hα
  rcases hK with hK | ⟨rfl, rfl, hA8⟩
  · exact card_L0_psp hp hp2 hf hK α hα
  · have h360 : Cat8.ordL2 ((3 ^ 1) ^ 2) = 360 := by decide
    rw [h360]
    have hadm : Cat8.IsAdm K₀ α := ⟨hα.sq, hα.out, by simpa [Cat8.ordL2] using hα.dvd⟩
    exact (CatFactsSmall.cfQ3L0 K₀ (Or.inr ⟨rfl, rfl, hA8⟩) α hadm).1

end CFSG.ComponentClassification.GSThmB
