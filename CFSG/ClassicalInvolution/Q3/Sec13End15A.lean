module

public import CFSG.ClassicalInvolution.Q3.Sec13End12
import CFSG.ClassicalInvolution.Q3.Sec13EndDEBasic
import CFSG.ClassicalInvolution.Q3.TL3T29

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

structure TwinSit (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G) : Prop where
  mem : K ∈ Ω
  isInv : IsUniqueInvolution K z
  twin : twinSet Ω K = {K, K'}
  ne : K ≠ K'

theorem zGroup_normal_of_conjInvariant {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) :
    (zGroup Ω).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : n ∈ Subgroup.closure {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨L, hL, hu⟩ := hx
    exact Subgroup.subset_closure ⟨conjSub g L, hΩ g L hL, hu.conj g⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact (zGroup Ω).one_mem
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact (zGroup Ω).mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact (zGroup Ω).inv_mem hx

namespace TwinSit

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem mem_twin (s : TwinSit Ω K K' z) : K' ∈ Ω ∧ IsUniqueInvolution K' z := by
  have hK' : K' ∈ twinSet Ω K := by
    rw [s.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨hΩ', z', hz'K, hz'K'⟩ := hK'
  refine ⟨hΩ', ?_⟩
  rw [s.isInv.eq hz'K]
  exact hz'K'

private theorem e15a_card_inf (h : EndHyp Ω) (s : TwinSit Ω K K' z) :
    Nat.card ↥(K ⊓ K') = 2 := by
  have hK' := s.mem_twin
  have hΩ4 := (h.thmD.hyp.omega4 K s.mem K' hK'.1 s.ne).1
  have hKc : Nat.card K = 8 := h.card_eq_eight s.mem
  have hK'c : Nat.card K' = 8 := h.card_eq_eight hK'.1
  have hdvd : Nat.card ↥(K ⊓ K') ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_left
  rw [hKc] at hdvd
  have hzI : z ∈ K ⊓ K' := ⟨s.isInv.mem, hK'.2.mem⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact s.isInv.sq) s.isInv.ne_one
  have hz2 : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hzo]
  have hle2 : 2 ≤ Nat.card ↥(K ⊓ K') := by
    have := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hzI)
    omega
  have hne8 : Nat.card ↥(K ⊓ K') ≠ 8 := by
    intro h8
    have hKI : K ⊓ K' = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hKK' : K ≤ K' := by
      rw [← hKI]
      exact inf_le_right
    have hEq : K = K' := Subgroup.eq_of_le_of_card_ge hKK' (by omega)
    exact s.ne hEq
  have hdvd' : Nat.card ↥(K ⊓ K') ∣ 2 ^ 3 := by
    norm_num
    exact hdvd
  obtain ⟨i, hi, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd'
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [pow_zero] at hpow
    omega
  · rw [pow_one] at hpow
    exact hpow
  · exfalso
    rw [hpow, padicValNat.prime_pow] at hΩ4
    omega
  · exfalso
    exact hne8 (hpow.trans (by norm_num))

theorem commutes (s : TwinSit Ω K K' z) (h : EndHyp Ω) : Commutes K K' := by
  have hK' := s.mem_twin
  have h4 := (h.thmD.hyp.omega4 K s.mem K' hK'.1 s.ne).2
    (by rw [e15a_card_inf h s]; exact padicValNat_self)
  have hO : oddCoreOf K ⊓ oddCoreOf K' = ⊥ := by
    rw [TL4.oddCoreOf_eq_bot_of_isPGroup (h.thmD.two K s.mem),
      TL4.oddCoreOf_eq_bot_of_isPGroup (h.thmD.two K' hK'.1), inf_idem]
  rw [hO] at h4
  exact fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.mem_bot.mp (h4 (Subgroup.commutator_mem_commutator hx hy)))

theorem inf_eq_zpowers (s : TwinSit Ω K K' z) (h : EndHyp Ω) : K ⊓ K' = Subgroup.zpowers z := by
  have hzI : z ∈ K ⊓ K' := ⟨s.isInv.mem, s.mem_twin.2.mem⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact s.isInv.sq) s.isInv.ne_one
  have hz2 : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hzo]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzI)
    (le_of_eq (by rw [e15a_card_inf h s, hz2]))).symm

theorem card_sup (s : TwinSit Ω K K' z) (h : EndHyp Ω) : Nat.card ↥(K ⊔ K') = 32 := by
  have hN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Asc77.AscL62.le_normalizer_of_commutes (s.commutes h).symm
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hN
  rw [sup_comm, inf_comm, e15a_card_inf h s, h.card_eq_eight s.mem,
    h.card_eq_eight s.mem_twin.1] at hprod
  omega

end TwinSit

private theorem e15a_conj_fix {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {A B : Subgroup G}
    (hT : twinSet Ω A = {A, B}) (hAB : A ≠ B) {g : G} (hg : conjSub g A = A) :
    conjSub g B = B := by
  have hB : B ∈ twinSet Ω A := by
    rw [hT]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hc := twinSet_conj hΩ hB g
  rw [hg, hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with e | e
  · exact absurd (conjSub_injective g (e.trans hg.symm)).symm hAB
  · exact e

private theorem e15a_mem_of_four_le {Ω : Set (Subgroup G)} (h : EndHyp Ω) (h9 : Perp9 Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {X : Subgroup G} (hXJ : X ≤ J ⊓ Subgroup.centralizer ({z} : Set G)) (hX2 : IsPGroup 2 X)
    (hX4 : 4 ≤ Nat.card X) : J ∈ omegaStarNbr Ω K ∨ J ∈ twinSet Ω K := by
  have hΩ := h.thmD.hyp
  by_cases htw : J ∈ twinSet Ω K
  · exact Or.inr htw
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXJ
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hV4 : 4 ≤ Nat.card V := hX4.trans (Subgroup.card_le_of_le hXV)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ htw t ht V hV
      (ht.mem_of_le hVJ hV.2.1 (by omega)) with
    ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVK⟩
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · have hJK : J ≠ K := fun e => htw (by rw [e]; exact ⟨hK, z, hz, hz⟩)
    exact Or.inl ⟨hJ, hJK, V, hVU, hVJ, hVN⟩
  · have hVJ' : V = J := ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ hVR hVJ).eq_of_le
      (h.thmD.two J hJ) le_rfl hVJ).symm
    rw [hVJ', TL4.oddCoreOf_eq_bot_of_isPGroup (h.thmD.two K hK)] at hVK
    have hcomm : Commutes J K := fun x hx y hy =>
      commutatorElement_eq_one_iff_mul_comm.mp
        (Subgroup.mem_bot.mp (hVK (Subgroup.commutator_mem_commutator hx hy)))
    have htz : t = z := h9 J hJ K hK hcomm t z ht hz
    exact Or.inr ⟨hJ, z, hz, by rw [← htz]; exact ht⟩

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem kPerp_eq_twinSet_of_perp9 (h : EndHyp Ω) (h9 : Perp9 Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    KPerp Ω L = twinSet Ω L := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
  ext J
  constructor
  · intro hJ
    unfold KPerp at hJ
    rw [Set.mem_insert_iff] at hJ
    rcases hJ with hJL | hJN
    · rw [hJL]
      exact ⟨hL, z, hz, hz⟩
    · obtain ⟨hJΩ, hJne, R, hR, hRJ, hRN⟩ := hJN
      have hRs : IsSylow2In R J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.thmD.hyp hJΩ hR hRJ
      have hJR : J = R := hRs.eq_of_le (h.thmD.two J hJΩ) le_rfl hRJ
      have hJN' : J ≤ Subgroup.normalizer (L : Set G) := by
        rw [hJR]
        exact hRN
      have hP2 : IsPGroup 2 ↥(J ⊔ L) :=
        (h.thmD.two J hJΩ).to_sup_of_normal_right' (h.thmD.two L hL) hJN'
      obtain ⟨S, hS⟩ := hP2.exists_le_sylow
      have hJS : J ≤ (S : Subgroup G) := le_sup_left.trans hS
      have hLS : L ≤ (S : Subgroup G) := le_sup_right.trans hS
      have hcomm : Commutes L J :=
        Q3CP.l67Gen G Ω h.thmD.hyp S L (TC.mem_RSet_of_isPGroup hL (h.thmD.two L hL)) J
          (TC.mem_RSet_of_isPGroup hJΩ (h.thmD.two J hJΩ)) hLS hJS (fun e => hJne e.symm)
      obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJΩ
      have hzz : z = z' := h9 L hL J hJΩ hcomm z z' hz hz'
      exact ⟨hJΩ, z, hz, by rw [hzz]; exact hz'⟩
  · intro hJ
    obtain ⟨hJΩ, z', hz'L, hz'J⟩ := hJ
    unfold KPerp
    rw [Set.mem_insert_iff]
    by_cases hJL : J = L
    · exact Or.inl hJL
    · exact Or.inr (Q3CL.T3.twin_mem_omegaNbr h.thmD.hyp hL hJΩ hJL hz'L hz'J)

theorem twinSet_pair (h : EndHyp Ω) (s : TwinSit Ω K K' z) {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ L' : Subgroup G, L' ≠ L ∧ twinSet Ω L = {L, L'} := by
  have hΩc := h.thmD.hyp.conjInvariant
  obtain ⟨g, hg⟩ := h.thmD.trans K s.mem L hL
  have hK'mem : K' ∈ twinSet Ω K := by
    rw [s.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  refine ⟨conjSub g K', fun e => s.ne (conjSub_injective g (e.trans hg.symm)).symm, ?_⟩
  ext M
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hM
    have hL' : conjSub g⁻¹ L = K := by
      rw [← hg, conjSub_inv_conjSub]
    have hM1 : conjSub g⁻¹ M ∈ twinSet Ω K := by
      have hc := twinSet_conj hΩc hM g⁻¹
      rwa [hL'] at hc
    rw [s.twin, Set.mem_insert_iff, Set.mem_singleton_iff] at hM1
    rcases hM1 with e | e
    · left
      calc M = conjSub g (conjSub g⁻¹ M) := (conjSub_conjSub_inv g M).symm
        _ = conjSub g K := by rw [e]
        _ = L := hg
    · right
      calc M = conjSub g (conjSub g⁻¹ M) := (conjSub_conjSub_inv g M).symm
        _ = conjSub g K' := by rw [e]
  · rintro (hML | hMK)
    · rw [hML]
      obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
      exact ⟨hL, z', hz', hz'⟩
    · rw [hMK, ← hg]
      exact twinSet_conj hΩc hK'mem g

theorem normalizer_twin (h : EndHyp Ω) (s : TwinSit Ω K K' z) :
    Subgroup.normalizer (K : Set G) = Subgroup.normalizer (K' : Set G) ∧
      Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  have hΩc := h.thmD.hyp.conjInvariant
  have hK'mem : K' ∈ twinSet Ω K := by
    rw [s.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hT' : twinSet Ω K' = {K', K} := by
    rw [Asc77.twinSet_eq_of_mem_twinSet s.isInv hK'mem, s.twin, Set.pair_comm]
  refine ⟨?_, ?_⟩
  · ext g
    rw [mem_normalizer_iff_conjSub_eq, mem_normalizer_iff_conjSub_eq]
    exact ⟨fun hg => e15a_conj_fix hΩc s.twin s.ne hg,
      fun hg => e15a_conj_fix hΩc hT' s.ne.symm hg⟩
  · intro g hg
    have e := s.isInv.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp e)

theorem mem_omegaStarNbr_or_twinSet (h : EndHyp Ω) (h9 : Perp9 Ω) {L M : Subgroup G} (hL : L ∈ Ω)
    (hM : M ∈ Ω) {s : G} (hs : IsUniqueInvolution M s)
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) : M ∈ omegaStarNbr Ω L ∨ M ∈ twinSet Ω L := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
  have hT4 := twinT4Hyp_of h.thmD.hyp h.thmD.two h.thmD.card h.thmD.aEmpty h.thmD.odd
  obtain ⟨X, hXL, hX2, hX4⟩ := hT4.exists_le_centralizer hL hM hz hs CFSG.pCore_normal
    CFSG.pCore_isPGroup (h.mem_pCore hL hz) (h.mem_pCore hM hs) hsN
  rcases e15a_mem_of_four_le h h9 hM hL hs hXL hX2 hX4 with hLN | ⟨-, z', hz'M, hz'L⟩
  · exact Or.inl (Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hM hL hLN)
  · exact Or.inr ⟨hM, z', hz'L, hz'M⟩

theorem eGroup_le_normalizer (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    eGroup Ω K ≤ Subgroup.normalizer (K : Set G) :=
  h.eGroup_le_normalizer_self hK

theorem mem_eGroup_of_normalizes (h : EndHyp Ω) (h9 : Perp9 Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ Ω) {s : G} (hs : IsUniqueInvolution M s)
    (hsN : s ∈ Subgroup.normalizer (K : Set G)) : s ∈ eGroup Ω K := by
  rcases h.mem_omegaStarNbr_or_twinSet h9 hK hM hs hsN with hMN | ⟨-, z, hzK, hzM⟩
  · exact h.mem_eGroup_of_mem_omegaStarNbr hMN hs
  · rw [hs.eq hzM]
    exact h.mem_eGroup_of_isUniqueInvolution hzK

theorem mem_eGroup_iff_mem_normalizer (h : EndHyp Ω) (h9 : Perp9 Ω) {K : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) {s : G} (hs : ∃ g : G, s = g * z * g⁻¹) :
    s ∈ eGroup Ω K ↔ s ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨g, rfl⟩ := hs
  refine ⟨fun hE => h.eGroup_le_normalizer hK hE, fun hN => ?_⟩
  exact h.mem_eGroup_of_normalizes h9 hK (h.thmD.hyp.conjInvariant g K hK) (hz.conj g) hN

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
