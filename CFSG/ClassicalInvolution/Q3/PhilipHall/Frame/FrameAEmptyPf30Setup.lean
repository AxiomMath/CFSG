module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf29Kbar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3C4
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace Out

theorem le_oddCoreOf_of_normalizes {G : Type} [Group G] {H M : Subgroup G} (hMH : M ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (M : Set G)) (hodd : Odd (Nat.card M)) :
    M ≤ oddCoreOf H := by
  have hnormal : (M.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMH).mpr hnorm
  have hodd' : Odd (Nat.card (M.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv]
  have hle : M.subgroupOf H ≤ classicalInvolutionOddCore ↥H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hMH hk⟩, hle hk, rfl⟩

theorem nonempty_equiv_q8' {G : Type} [Group G] {M : Subgroup G} (h : IsQuatSub M)
    (h8 : Nat.card M = 8) : Nonempty (↥M ≃* QuaternionGroup 2) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  have hc : Nat.card M = 4 * 2 ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : 2 ^ k = 2 ^ 1 := by omega
  have hk1 : k = 1 := Nat.pow_right_injective (le_refl 2) h2
  subst hk1
  exact ⟨e⟩

end Out

open Out

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Setup

theorem kbar_equiv_q8 (d : Std20Frame K K' J S R R' W V z t) : Nonempty (Kbar K ≃* Q8) := by
  have hΩ := d.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hRset : R ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKΩ d.hR
  obtain ⟨e⟩ := nonempty_equiv_q8' (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRset) d.card8
  let O : Subgroup ↥K := classicalInvolutionOddCore ↥K
  let f : ↥R →* Kbar K := (QuotientGroup.mk' O).comp (Subgroup.inclusion d.hR.1)
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥K
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : (Subgroup.inclusion d.hR.1 r : ↥K) ∈ O := (QuotientGroup.eq_one_iff _).mp hr
    have h2 : ((r : G)) ∈ oddCoreOf K := (mem_oddCoreOf_iff K _).mpr h1
    have h3 : orderOf (r : G) ∣ Nat.card (oddCoreOf K) := Subgroup.orderOf_dvd_natCard _ h2
    have h4 : orderOf (r : G) ∣ 2 ^ 3 := by
      have := Subgroup.orderOf_dvd_natCard R r.2
      rw [d.card8] at this
      simpa using this
    have h5 : Odd (orderOf (r : G)) := Odd.of_dvd_nat (oddCoreOf_odd_natCard K) h3
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    have hi0 : i = 0 := by
      by_contra hne
      have : Even (orderOf (r : G)) := by
        rw [hio]
        exact (Nat.even_pow.mpr ⟨even_two, hne⟩)
      exact (Nat.not_even_iff_odd.mpr h5) this
    rw [hi0] at hio
    have : orderOf (r : G) = 1 := by simpa using hio
    have h6 : (r : G) = 1 := orderOf_eq_one_iff.mp this
    exact Subtype.ext h6
  have hcardK : Nat.card ↥K = Nat.card (Kbar K) * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp d.twoGroup
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hP : IsSylow2In (P.map K.subtype) K := isSylow2In_map_sylow K P
  have hcR : Nat.card (P.map K.subtype) = 8 := by
    rw [← d.hR.natCard_eq hP, d.card8]
  have hfac : (8 : ℕ) = 2 ^ (Nat.card ↥K).factorization 2 := by
    rw [← hcR, Subgroup.card_map_of_injective K.subtype_injective]
    exact P.card_eq_multiplicity
  have hoodd : ¬ 2 ∣ Nat.card O := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hOodd
  have hfac2 : (Nat.card ↥K).factorization 2 = a := by
    rw [hcardK, ha, Nat.factorization_mul (by positivity) Nat.card_pos.ne',
      Nat.factorization_pow]
    simp [Nat.factorization_eq_zero_of_not_dvd hoodd, Nat.Prime.factorization_self Nat.prime_two]
  have h2a : Nat.card (Kbar K) = 8 := by
    rw [ha, ← hfac2, ← hfac]
  have hcr : Nat.card f.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, d.card8]
  have hr : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcr, h2a])
  have hsurj : Function.Surjective f := by
    intro y
    have : y ∈ f.range := by rw [hr]; exact Subgroup.mem_top y
    exact this
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans e⟩

theorem sec20X_le_normalizers_frame (d : Std20Frame K K' J S R R' W V z t) :
    sec20X (CoreAssembly.conjClass K) z K K' ≤
      Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (K' : Set G) := by
  unfold sec20X
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨hUU, hUC⟩ := hU
    obtain ⟨L₀, hL₀, hUL₀⟩ := Sec6Gen.exists_member_of_mem_USet d.late_hΩ hUU
    have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hUU
    obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet d.late_hΩ hUU
    refine le_inf ?_ ?_
    · by_cases h : L₀ = K
      · subst h
        exact hUL₀.trans Subgroup.le_normalizer
      · exact Sec6Gen.le_normalizer_of_le_centralizer d.late_hΩ d.late_mem_K hL₀ (Ne.symm h)
          d.viol.hzK hUL₀ hU2 (by omega) hUC
    · by_cases h : L₀ = K'
      · subst h
        exact hUL₀.trans Subgroup.le_normalizer
      · exact Sec6Gen.le_normalizer_of_le_centralizer d.late_hΩ d.late_mem_K' hL₀ (Ne.symm h)
          d.late_hzK' hUL₀ hU2 (by omega) hUC
  · exact le_inf Subgroup.le_normalizer d.late_K_le
  · exact le_inf d.late_K'_le Subgroup.le_normalizer

theorem twin_comm_mem (d : Std20Frame K K' J S R R' W V z t) {k k' : G} (hk : k ∈ K)
    (hk' : k' ∈ K') : ⁅k, k'⁆ ∈ oddCoreOf K ⊓ oddCoreOf K' := by
  obtain ⟨h1, h2⟩ := d.hyp.omega4 K d.late_mem_K K' d.late_mem_K' d.K_ne_K'
  have hz : z ∈ K ⊓ K' := ⟨d.viol.hzK.mem, d.late_hzK'.mem⟩
  have hv : padicValNat 2 (Nat.card ↥(K ⊓ K')) = 1 := by
    refine le_antisymm h1 ?_
    have hdvd : orderOf z ∣ Nat.card ↥(K ⊓ K') := Subgroup.orderOf_dvd_natCard _ hz
    have h2z : orderOf z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact d.viol.hzK.sq) d.viol.hzK.ne_one
    rw [h2z] at hdvd
    exact one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
  exact h2 hv (Subgroup.commutator_mem_commutator hk hk')

theorem le_trivialOnQuot_K (d : Std20Frame K K' J S R R' W V z t) : K' ≤ trivialOnQuot K := by
  intro k' hk'
  refine ⟨d.late_K'_le hk', fun x hx => ?_⟩
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ (twin_comm_mem d hx hk').1

theorem le_trivialOnQuot_K' (d : Std20Frame K K' J S R R' W V z t) : K ≤ trivialOnQuot K' := by
  intro k hk
  refine ⟨d.late_K_le hk, fun x hx => ?_⟩
  exact (twin_comm_mem d hk hx).2

end Setup

section Swap

variable (d : Std20Frame K K' J S R R' W V z t) {g : G}
  (hg : g ∈ Subgroup.centralizer ({z} : Set G)) (hgK : conjSub g K = K')
include d hg hgK

theorem conjSub_swap_K' : conjSub g K' = K := by
  rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inr rfl) hg with h | h
  · exact h
  · exfalso
    exact d.K_ne_K' ((conjSub_inj g).mp (hgK.trans h.symm))

theorem conj_swap_mem_normalizer {x : G} (hx : x ∈ Subgroup.normalizer (K' : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hx ⊢
  have h1 : conjSub (g⁻¹ * x * g) K = conjSub g⁻¹ (conjSub x (conjSub g K)) := by
    rw [conjSub_mul, conjSub_mul]
  rw [h1, hgK, hx]
  have := conjSub_inv_conjSub g K
  rw [← hgK]
  exact this

theorem conj_swap_K {x : G} (hx : x ∈ K) : g⁻¹ * x * g ∈ K' := by
  have h := conjSub_swap_K' d hg hgK
  rw [← h] at hx
  exact mem_conjSub_iff.mp hx

theorem conj_swap_K' {x : G} (hx : x ∈ K') : g⁻¹ * x * g ∈ K := by
  rw [← hgK] at hx
  exact mem_conjSub_iff.mp hx

theorem conj_swap_oddCore {x : G}
    (hx : x ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K')) :
    g⁻¹ * x * g ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  have hg' : g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := (Subgroup.centralizer _).inv_mem hg
  have h1 : conjSub g X ≤ X := conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins hg
  have h2 : conjSub g⁻¹ X ≤ X := conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins hg'
  have h3 : conjSub g X = X := by
    refine le_antisymm h1 ?_
    have := conjSub_mono (n := g) h2
    rwa [conjSub_conjSub_inv] at this
  have h4 : oddCoreOf X = conjSub g (oddCoreOf X) := by
    rw [← Thompson.oddCoreOf_conjSub_eq, h3]
  rw [h4] at hx
  exact mem_conjSub_iff.mp hx

end Swap

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
