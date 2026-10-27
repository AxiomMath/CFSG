module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenTargets

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement Pointwise MatrixGroups

namespace TwinExact

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_of_mem_oddCoreOf {K : Subgroup G} {y : G} (hy : y ∈ oddCoreOf K) :
    Odd (orderOf y) := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  have hodd := CFSG.ComponentClassification.OddCore.odd_card ↥K
  have hdvd : orderOf y' ∣ Nat.card ↥(classicalInvolutionOddCore ↥K) :=
    Subgroup.orderOf_dvd_natCard _ hy'
  have hy2 : orderOf (K.subtype y') = orderOf y' := by
    rw [← Subgroup.orderOf_coe]
    rfl
  rw [hy2]
  exact hodd.of_dvd_nat hdvd

theorem inf_oddCoreOf_eq_bot {K P : Subgroup G} (hP : IsPGroup 2 ↥P) :
    oddCoreOf K ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyO, hyP⟩
  obtain ⟨n, hn⟩ := hP ⟨y, hyP⟩
  have hn' : y ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hd : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have hodd := odd_orderOf_of_mem_oddCoreOf hyO
  have hc : Nat.Coprime (orderOf y) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_left.mpr hodd).symm
  have h1 : orderOf y = 1 := Nat.Coprime.eq_one_of_dvd hc hd
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

theorem not_mem_inf_of_sq {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hKK' : K ≠ K') {z r' : G} (hzK : IsUniqueInvolution K z)
    (hsq : r' * r' = z) (hr : r' ∈ K ⊓ K') : False := by
  have hz1 : z ≠ 1 := hzK.ne_one
  have h4 : r' ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hsq, hzK.sq]
  have h2 : r' ^ 2 ≠ 1 := by
    rw [pow_two, hsq]; exact hz1
  have hd4 : orderOf r' ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  have hnd2 : ¬ orderOf r' ∣ 2 := fun h => h2 (orderOf_dvd_iff_pow_eq_one.mp h)
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd4
  have hdiv : orderOf r' = 4 := by
    interval_cases i
    · exact absurd (by rw [hie]; simp) hnd2
    · exact absurd (by rw [hie]; simp) hnd2
    · rw [hie]; norm_num
  have hcard : 4 ∣ Nat.card ↥(K ⊓ K') := by
    rw [← hdiv]; exact Subgroup.orderOf_dvd_natCard _ hr
  have hne : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
  have hv : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ K')) :=
    (padicValNat_dvd_iff_le (p := 2) hne).mp (by simpa using hcard)
  have := (hΩ.omega4 K hK K' hK' hKK').1
  omega

noncomputable def sylowOfIsSylow2In {K R : Subgroup G} (h : IsSylow2In R K) : Sylow 2 ↥K where
  toSubgroup := R.subgroupOf K
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : R ≤ Q.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
    rfl

theorem mem_mul_oddCore_of_sylow {K R : Subgroup G}
    (hQ : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) (hRsyl : IsSylow2In R K) :
    ∀ k ∈ K, ∃ r ∈ R, ∃ o ∈ oddCoreOf K, k = r * o := by
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hNdef
  set A : Subgroup ↥K := R.subgroupOf K with hAdef
  set M : Subgroup ↥K := A ⊔ N with hMdef
  have hAodd : ¬ 2 ∣ A.index := Sylow.not_dvd_index (sylowOfIsSylow2In hRsyl)
  have hMA : M.index ∣ A.index := Subgroup.index_dvd_of_le le_sup_left
  have hModd : ¬ 2 ∣ M.index := fun h => hAodd (dvd_trans h hMA)
  have hker : (QuotientGroup.mk' N : ↥K →* ↥K ⧸ N).ker ≤ M := by
    rw [QuotientGroup.ker_mk']
    exact le_sup_right
  have hidx : (M.map (QuotientGroup.mk' N)).index = M.index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N) hker
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : (M.map (QuotientGroup.mk' N)).index ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hM1 : M.index = 1 := by
    rcases j with _ | j
    · rw [← hidx, hj]
      norm_num
    · exfalso
      apply hModd
      rw [← hidx, hj, pow_succ]
      exact dvd_mul_left 2 _
  have hMtop : M = ⊤ := Subgroup.index_eq_one.mp hM1
  intro k hk
  have hkM : (⟨k, hk⟩ : ↥K) ∈ (↑M : Set ↥K) := by
    rw [hMtop]
    exact Set.mem_univ _
  have hset : (⟨k, hk⟩ : ↥K) ∈ (A : Set ↥K) * (N : Set ↥K) := by
    rw [← Subgroup.mul_normal]
    exact hkM
  obtain ⟨a, ha, o, ho, hao⟩ := hset
  refine ⟨(a : G), (Subgroup.mem_subgroupOf).mp ha, (o : G), ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
  · have := congrArg Subtype.val hao
    simp only [Subgroup.coe_mul] at this
    exact this.symm

theorem le_oddCoreInv {X : Type} [Group X] {N : Subgroup X} (h1 : N.Normal)
    (h2 : Odd (Nat.card ↥N)) : N ≤ classicalInvolutionOddCore X :=
  le_sSup ⟨h1, h2⟩

omit [Finite G] in
theorem conj_mem_of_subgroupOf_normal {H M : Subgroup G} (hle : H ≤ M)
    (hN : (H.subgroupOf M).Normal) {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ H) :
    m * x * m⁻¹ ∈ H := by
  have h := hN.conj_mem ⟨x, hle hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨m, hm⟩
  simpa using Subgroup.mem_subgroupOf.mp h

def conjSubHom {H M : Subgroup G} (hle : H ≤ M) (hN : (H.subgroupOf M).Normal) {m : G}
    (hm : m ∈ M) : ↥H →* ↥H where
  toFun x := ⟨m * x * m⁻¹, conj_mem_of_subgroupOf_normal hle hN hm x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

omit [Finite G] in
theorem conjSubHom_surjective {H M : Subgroup G} (hle : H ≤ M) (hN : (H.subgroupOf M).Normal)
    {m : G} (hm : m ∈ M) : Function.Surjective (conjSubHom hle hN hm) := by
  intro y
  refine ⟨⟨m⁻¹ * y * m⁻¹⁻¹, conj_mem_of_subgroupOf_normal hle hN (M.inv_mem hm) y.2⟩, ?_⟩
  exact Subtype.ext (by simp [conjSubHom, mul_assoc])

omit [Finite G] in
theorem conjSubHom_injective {H M : Subgroup G} (hle : H ≤ M) (hN : (H.subgroupOf M).Normal)
    {m : G} (hm : m ∈ M) : Function.Injective (conjSubHom hle hN hm) := by
  intro x y h
  have h' := congrArg Subtype.val h
  simpa [conjSubHom] using h'

theorem oddCoreOf_le_of_normal_sub {H M : Subgroup G} (hle : H ≤ M)
    (hN : (H.subgroupOf M).Normal) : oddCoreOf H ≤ oddCoreOf M := by
  have hsubH : oddCoreOf H ≤ H := Subgroup.map_subtype_le _
  have hcmO : ∀ {g : G} (hg : g ∈ M),
      (classicalInvolutionOddCore ↥H).map (conjSubHom hle hN hg) ≤ classicalInvolutionOddCore ↥H := by
    intro g hg
    have hnorm : ((classicalInvolutionOddCore ↥H).map (conjSubHom hle hN hg)).Normal :=
      (classicalInvolutionOddCore_normal ↥H).map _ (conjSubHom_surjective hle hN hg)
    have hodd : Odd (Nat.card ↥((classicalInvolutionOddCore ↥H).map (conjSubHom hle hN hg))) := by
      rw [Subgroup.card_map_of_injective (conjSubHom_injective hle hN hg)]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥H
    exact le_oddCoreInv hnorm hodd
  have hnormM : ∀ {g : G} (hg : g ∈ M), ∀ x ∈ oddCoreOf H, g * x * g⁻¹ ∈ oddCoreOf H := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr
      ⟨conjSubHom hle hN hg y, hcmO hg (Subgroup.mem_map_of_mem _ hy), rfl⟩
  have hPnorm : ((oddCoreOf H).subgroupOf M).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      (by simpa using hnormM g.2 _ (Subgroup.mem_subgroupOf.mp hn))⟩
  have hPodd : Odd (Nat.card ↥((oddCoreOf H).subgroupOf M)) := by
    have hmap : ((oddCoreOf H).subgroupOf M).map M.subtype = oddCoreOf H := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hsubH.trans hle)]
    have h1 := Subgroup.card_map_of_injective (K := (oddCoreOf H).subgroupOf M) M.subtype_injective
    rw [hmap] at h1
    rw [← h1]
    have h2 := Subgroup.card_map_of_injective (K := classicalInvolutionOddCore ↥H) H.subtype_injective
    show Odd (Nat.card ↥((classicalInvolutionOddCore ↥H).map H.subtype))
    rw [h2]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hPle : (oddCoreOf H).subgroupOf M ≤ classicalInvolutionOddCore ↥M :=
    le_oddCoreInv hPnorm hPodd
  intro x hx
  have hxM : x ∈ M := hle (hsubH hx)
  have hmem : (⟨x, hxM⟩ : ↥M) ∈ classicalInvolutionOddCore ↥M :=
    hPle (Subgroup.mem_subgroupOf.mpr hx)
  exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, hmem, rfl⟩

theorem oddCoreOf_le_of_isSubnormal {H C : Subgroup G} (h : IsSubnormal H C) :
    oddCoreOf H ≤ oddCoreOf C := by
  induction h with
  | refl => exact le_rfl
  | step hle hN _ ih => exact (oddCoreOf_le_of_normal_sub hle hN).trans ih

end TwinExact

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
