module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Misc
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem center_ne_bot_of_mem_center [Finite G] {I : Subgroup G} {u : G}
    (hu : orderOf u = 2) (huI : u ∈ I) (hc : ∀ a ∈ I, a * u = u * a) :
    Subgroup.center (I ⧸ oddCore I) ≠ ⊥ := by
  intro hbot
  let uI : ↥I := ⟨u, huI⟩
  have huIcenter : uI ∈ Subgroup.center ↥I := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    show (a : G) * u = u * (a : G)
    exact hc a.1 a.2
  have hqcenter : (QuotientGroup.mk' (oddCore ↥I)) uI ∈
      Subgroup.center (↥I ⧸ oddCore ↥I) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (oddCore ↥I))
      ⟨uI, huIcenter, rfl⟩
  have hqne : (QuotientGroup.mk' (oddCore ↥I)) uI ≠ 1 := by
    intro hq1
    have hmem : uI ∈ oddCore ↥I := by
      have hker : uI ∈ MonoidHom.ker (QuotientGroup.mk' (oddCore ↥I)) :=
        MonoidHom.mem_ker.mpr hq1
      rwa [QuotientGroup.ker_mk'] at hker
    have horder : orderOf uI = 2 := by
      change orderOf (⟨u, huI⟩ : ↥I) = 2
      rw [Subgroup.orderOf_mk u huI, hu]
    have hdvd : 2 ∣ Nat.card (oddCore ↥I) := by
      rw [← horder]
      exact (oddCore ↥I).orderOf_dvd_natCard hmem
    exact (odd_card_oddCore' ↥I).not_two_dvd_nat hdvd
  rw [hbot] at hqcenter
  exact hqne (Subgroup.mem_bot.mp hqcenter)

private theorem isSimpleGroup_of_statedClassicalModel {Q : Type} [Group Q]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel Q t n p f) : IsSimpleGroup Q :=
  (CFSG.LieType.Simplicity.fam_classical_converse Q ⟨t, n, p, f, h⟩).2.2

private theorem not_prime_of_two_dvd {n : ℕ} (h2 : 2 ∣ n) (hne : n ≠ 2) : ¬ n.Prime := by
  intro hp
  rcases hp.eq_two_or_odd' with h | ho
  · exact hne h
  · exact ho.not_two_dvd_nat h2

private theorem not_prime_card_of_smallF3OmegaQuotient {Q : Type} [Group Q]
    (h : SmallF3OmegaQuotient Q) : ¬ (Nat.card Q).Prime := by
  rcases h with h | h | h | h | h | h
  · have hcard : Nat.card Q = 25920 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 6065280 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 3265920 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 4585351680 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 4952179814400 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 10151968619520 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.2 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)

private theorem not_prime_card_of_smallF3StarQuotient {Q : Type} [Group Q]
    (h : SmallF3StarQuotient Q) : ¬ (Nat.card Q).Prime := by
  rcases h with h | h | h | h
  · have hcard : Nat.card Q = 360 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 265680 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 5616 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)
  · have hcard : Nat.card Q = 6048 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
        (show (3 : ℕ) ≠ 2 by norm_num)
        (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
      decide +kernel
    rw [hcard]; exact not_prime_of_two_dvd (by norm_num) (by norm_num)

private theorem isSimpleGroup_of_smallF3OmegaQuotient {Q : Type} [Group Q]
    (h : SmallF3OmegaQuotient Q) : IsSimpleGroup Q := by
  rcases h with h | h | h | h | h | h <;>
    exact isSimpleGroup_of_statedClassicalModel (h.statedClassicalModel_of_ne_zero (by norm_num))

private theorem isSimpleGroup_of_smallF3StarQuotient {Q : Type} [Group Q]
    (h : SmallF3StarQuotient Q) : IsSimpleGroup Q := by
  rcases h with h | h | h | h <;>
    exact isSimpleGroup_of_statedClassicalModel (h.statedClassicalModel_of_ne_zero (by norm_num))

private theorem false_of_center_ne_bot_of_simple [Finite G] {I : Subgroup G} {u : G}
    (hu : orderOf u = 2) (huI : u ∈ I) (hc : ∀ a ∈ I, a * u = u * a)
    (hsimple : IsSimpleGroup (I ⧸ oddCore I))
    (hnp : ¬ (Nat.card (I ⧸ oddCore I)).Prime) : False := by
  have hne : Subgroup.center (I ⧸ oddCore I) ≠ ⊥ :=
    center_ne_bot_of_mem_center hu huI hc
  have htop : Subgroup.center (I ⧸ oddCore I) = ⊤ :=
    (hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (I ⧸ oddCore I))).resolve_left hne
  haveI : IsMulCommutative (I ⧸ oddCore I) := Subgroup.center_eq_top_iff.mp htop
  exact hnp (Group.is_simple_iff_prime_card.mp hsimple)

private theorem false_of_smallF3OmegaQuotient [Finite G] {I : Subgroup G} {u : G}
    (hu : orderOf u = 2) (huI : u ∈ I) (hc : ∀ a ∈ I, a * u = u * a)
    (h : SmallF3OmegaQuotient (I ⧸ oddCore I)) : False :=
  false_of_center_ne_bot_of_simple hu huI hc
    (isSimpleGroup_of_smallF3OmegaQuotient h) (not_prime_card_of_smallF3OmegaQuotient h)

private theorem false_of_smallF3StarQuotient [Finite G] {I : Subgroup G} {u : G}
    (hu : orderOf u = 2) (huI : u ∈ I) (hc : ∀ a ∈ I, a * u = u * a)
    (h : SmallF3StarQuotient (I ⧸ oddCore I)) : False :=
  false_of_center_ne_bot_of_simple hu huI hc
    (isSimpleGroup_of_smallF3StarQuotient h) (not_prime_card_of_smallF3StarQuotient h)

private theorem commutator_le_of_sup_central_eq_top {H : Type*} [Group H] {N M : Subgroup H}
    (hM : M ≤ Subgroup.center H) (hsup : N ⊔ M = ⊤) : commutator H ≤ N := by
  have hNnorm : N ≤ Subgroup.normalizer (N : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro n hn k hk
    exact N.mul_mem (N.mul_mem hn hk) (N.inv_mem hn)
  haveI : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le hNnorm (hM.trans (Subgroup.center_le_normalizer (N : Set H)))
  have hMcomm : IsMulCommutative M := by
    refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    exact (Subgroup.mem_center_iff.mp (hM a.2) (b : H)).symm
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hMcomm

theorem isTwoU43_of_mem_center [Finite G] {I : Subgroup G} (hI : InFStar I) {u : G}
    (hu : orderOf u = 2) (huI : u ∈ I) (hc : ∀ a ∈ I, a * u = u * a) :
    IsTwoU43 (I ⧸ oddCore I) := by
  unfold InFStar IsFStarGroup at hI
  rcases hI with hF | ⟨-, hstar⟩
  · unfold IsFGroup at hF
    rcases hF with ⟨-, hOmega | hTwo⟩
    · exact (false_of_smallF3OmegaQuotient hu huI hc hOmega).elim
    · exact hTwo
  · exact (false_of_smallF3StarQuotient hu huI hc hstar).elim

theorem eq_of_le_of_isTwoU43 [Finite G] {K I : Subgroup G} (hKI : K ≤ I)
    (hK : IsQuasisimple K) (hI : IsQuasisimple I) (hKt : IsTwoU43 (K ⧸ oddCore K))
    (hIt : IsTwoU43 (I ⧸ oddCore I)) : K = I := by
  have hKcard : Nat.card (K ⧸ oddCore K) = 6531840 := card_of_isTwoU43 hKt
  have hIcard : Nat.card (I ⧸ oddCore I) = 6531840 := card_of_isTwoU43 hIt
  let ψ : ↥K →* ↥I := Subgroup.inclusion hKI
  let φ : ↥K →* (↥I ⧸ oddCore ↥I) := (QuotientGroup.mk' (oddCore ↥I)).comp ψ
  have hker : φ.ker = (oddCore ↥I).comap ψ := by
    change ((QuotientGroup.mk' (oddCore ↥I)).comp ψ).ker = (oddCore ↥I).comap ψ
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hψinj : Function.Injective ψ := Subgroup.inclusion_injective hKI
  have hKodd : Odd (Nat.card φ.ker) := by
    rw [hker]
    exact (odd_card_oddCore' ↥I).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective (oddCore ↥I) ψ hψinj)
  have hKle : φ.ker ≤ oddCore ↥K := by
    show φ.ker ≤ sSup {N : Subgroup ↥K | N.Normal ∧ Odd (Nat.card N)}
    exact le_sSup ⟨inferInstance, hKodd⟩
  have h1 : Nat.card (↥K ⧸ oddCore ↥K) ∣ Nat.card (↥K ⧸ φ.ker) := by
    have h := Subgroup.card_quotient_dvd_card ((oddCore ↥K).map (QuotientGroup.mk' φ.ker))
    rw [← Nat.card_congr
      (QuotientGroup.quotientQuotientEquivQuotient φ.ker (oddCore ↥K) hKle).toEquiv]
    exact h
  have h2 : Nat.card (↥K ⧸ φ.ker) ∣ Nat.card (↥I ⧸ oddCore ↥I) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hdvd1 : 6531840 ∣ Nat.card (↥K ⧸ φ.ker) := by
    rw [← hKcard]; exact h1
  have hdvd2 : Nat.card (↥K ⧸ φ.ker) ∣ 6531840 := by
    rw [← hIcard]; exact h2
  have hKq : Nat.card (↥K ⧸ φ.ker) = 6531840 := Nat.dvd_antisymm hdvd2 hdvd1
  have hrange_top : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hKq, hIcard]
  have hsup : K.subgroupOf I ⊔ oddCore ↥I = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxrange : QuotientGroup.mk' (oddCore ↥I) x ∈ φ.range := by
      rw [hrange_top]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hxrange
    have hk' : QuotientGroup.mk' (oddCore ↥I) (Subgroup.inclusion hKI k) =
        QuotientGroup.mk' (oddCore ↥I) x := hk
    rw [QuotientGroup.mk'_eq_mk'] at hk'
    obtain ⟨o, ho, hko⟩ := hk'
    rw [← hko]
    exact Subgroup.mul_mem_sup (by rw [Subgroup.mem_subgroupOf]; exact k.2) ho
  have hOI_ne_top : oddCore ↥I ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥I ⧸ oddCore ↥I) := by
      rw [htop]; exact QuotientGroup.subsingleton_quotient_top
    have h1 : Nat.card (Subgroup.center (↥I ⧸ oddCore ↥I)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have htwo := hIt.1
    rw [h1] at htwo
    omega
  have hOI_le_center : oddCore ↥I ≤ Subgroup.center ↥I := by
    have hIopen : CFSG.Open.IsQuasisimple ↥I := ⟨hI.1.commutator_eq_top, hI.2.1⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      hIopen (oddCore ↥I) with h | h
    · exact h
    · exact absurd h hOI_ne_top
  have hKI_top : K.subgroupOf I = ⊤ := by
    have hcomm : commutator ↥I ≤ K.subgroupOf I :=
      commutator_le_of_sup_central_eq_top hOI_le_center hsup
    rw [hI.1.commutator_eq_top] at hcomm
    exact top_le_iff.mp hcomm
  exact le_antisymm hKI (Subgroup.subgroupOf_eq_top.mp hKI_top)

end CFSG.OddStandard.SmallF3.Omega
