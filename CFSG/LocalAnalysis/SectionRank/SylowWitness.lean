module

public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.SectionRank

open CFSG.Open

variable {E S : Type*} [Group E] [Finite E] [Group S] [Finite S]

omit [Finite S] in
theorem isElemAbelian_closure_pair {r : ℕ} {x y : S} (hxr : x ^ r = 1) (hyr : y ^ r = 1)
    (hxy : x * y = y * x) : IsElemAbelian r (Subgroup.closure ({x, y} : Set S)) := by
  have hcomm : ({x, y} : Set S).Pairwise Commute := by
    intro u hu v hv _
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [Commute.refl _, hxy, hxy.symm, Commute.refl _]
  have := Subgroup.isMulCommutative_closure hcomm
  refine ⟨this, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl
    exacts [hxr, hyr]
  | one => exact one_pow r
  | mul u v hu hv ihu ihv =>
    have huv : Commute u v :=
      congrArg Subtype.val (this.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    rw [huv.mul_pow, ihu, ihv, one_mul]
  | inv u hu ihu => rw [inv_pow, ihu, inv_one]

theorem card_eq_pow_factorization_of_card {r k : ℕ} [hr : Fact r.Prime] (Q : Subgroup S)
    (hQ : Nat.card Q = r ^ k) (hS : ¬ r ^ (k + 1) ∣ Nat.card S) :
    Nat.card Q = r ^ (Nat.card S).factorization r := by
  have hdvd : r ^ k ∣ Nat.card S := hQ ▸ Subgroup.card_subgroup_dvd_card Q
  have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have h1 : k ≤ (Nat.card S).factorization r :=
    (Nat.Prime.pow_dvd_iff_le_factorization hr.out hS0).1 hdvd
  have h2 : (Nat.card S).factorization r < k + 1 := by
    by_contra h
    push Not at h
    exact hS ((Nat.Prime.pow_dvd_iff_le_factorization hr.out hS0).2 h)
  rw [hQ, show (Nat.card S).factorization r = k by omega]

theorem sylow_kernel_eq_bot_of_square_witness [Group.IsPerfect E] {r : ℕ} [hr : Fact r.Prime]
    (π : E →* S) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) {x y h : S}
    (hxr : x ^ r = 1) (hyr : y ^ r = 1) (hxy : x * y = y * x)
    (hQ : Nat.card (Subgroup.closure ({x, y} : Set S)) = r ^ 2) (hS : ¬ r ^ 3 ∣ Nat.card S)
    {a b c d : ℕ} (hx : h * x * h⁻¹ = x ^ a * y ^ c) (hy : h * y * h⁻¹ = x ^ b * y ^ d)
    (hdet : ((a * d - b * c : ℤ) : ZMod r) ≠ 1) (Cp : Sylow r π.ker) :
    (Cp : Subgroup π.ker) = ⊥ := by
  let Q : Sylow r S := Sylow.ofCard (Subgroup.closure ({x, y} : Set S))
    (card_eq_pow_factorization_of_card _ hQ hS)
  have hQeq : (Q : Subgroup S) = Subgroup.closure ({x, y} : Set S) := Sylow.coe_ofCard _ _
  refine sylow_kernel_eq_bot_of_normalizer_det π hπ hC Q ?_ hQeq.symm h hx hy hdet Cp
  rw [hQeq]
  exact isElemAbelian_closure_pair hxr hyr hxy

theorem ker_eq_bot_of_sylow_kernel_eq_bot [Group.IsPerfect E] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker))
    (hwit : ∀ r : ℕ, r.Prime → r ≠ 2 → r ^ 2 ∣ Nat.card S → ∀ [Fact r.Prime] (Cp : Sylow r π.ker),
      (Cp : Subgroup π.ker) = ⊥) : π.ker = ⊥ := by
  refine OddCover.eq_bot_of_forall_sylow_eq_bot _ fun r hr _ Cp => ?_
  by_cases hr2 : r = 2
  · subst hr2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Cp.isPGroup'
    have h1 : Nat.card (Cp : Subgroup π.ker) ∣ Nat.card π.ker := Subgroup.card_subgroup_dvd_card _
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.2 hodd)
        (even_iff_two_dvd.2 ((dvd_pow_self 2 hk0).trans (hk ▸ h1)))
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · by_cases hsq : r ^ 2 ∣ Nat.card S
    · exact hwit r hr hr2 hsq Cp
    · obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r S))
      exact CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cp Q
        (sylow_isCyclic_of_not_sq_dvd hsq Q)

theorem catalogStepConclusion_of_perfect_odd_cover_trivial {L : Type} [Group L] [Finite L]
    (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {S : Type} [Group S]
    (e : L ⧸ Subgroup.center L ≃* S)
    (htriv : ∀ (π : L →* S), Function.Surjective π → π.ker ≤ Subgroup.center L →
      Odd (Nat.card π.ker) → π.ker = ⊥) :
    Subgroup.center L = ⊥ ∧ CatalogStepConclusion L := by
  let π : L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := center_eq_ker_of_mulEquiv e
  have hZ : Subgroup.center L = ⊥ := hker ▸ htriv π hπ hker.le (hker ▸ hodd)
  exact ⟨hZ, catalogStepConclusion_of_center_eq_bot hSQT hZ⟩

end CFSG.SectionRank
