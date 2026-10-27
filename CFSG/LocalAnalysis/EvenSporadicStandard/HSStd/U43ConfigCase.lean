module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigSig
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.M24Std.CU43

theorem candOK_of_sig {Tt y0 c0 : Table} {T y c : Equiv.Perm (Fin 820)} (hT : Rep 820 Tt T)
    (hT2 : T * T = 1) (hy : Rep 820 y0 y) (hc : Rep 820 c0 c) (hy3 : orderOf y = 3)
    (hc3 : orderOf c = 3) (hyc : y * c = c * y) (hycp : y * (T * c * T⁻¹) = (T * c * T⁻¹) * y)
    (hccp : c * (T * c * T⁻¹) = (T * c * T⁻¹) * c)
    (h27 : Nat.card ↥(closure ({y, c, T * c * T⁻¹} : Set (Equiv.Perm (Fin 820)))) = 27) :
    candOK Tt y0 c0 = true := by
  have hTi : Rep 820 Tt T⁻¹ := by rw [inv_eq_of_mul_eq_one_right hT2]; exact hT
  have hcp : Rep 820 (cpOf Tt c0) (T * c * T⁻¹) := rep_conjT hT hTi hc
  have hn : (820 : ℕ) < 2 ^ 32 := by norm_num
  have hy3' : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  have hc3' : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc3] at this
  have hcp3 : (T * c * T⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3', mul_one, mul_inv_cancel]
  have hfree := relFree_of_card_27 hy3' hc3' hcp3 hyc hycp hccp h27
  simp only [candOK, Bool.and_eq_true]
  refine ⟨⟨⟨(ordTest_iff_perm hc (by norm_num)).2 hc3, (commTT_iff hc hcp).2 hccp⟩,
    (commTT_iff hy hcp).2 hycp⟩, ?_⟩
  simp only [relFree, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true']
  intro a ha b hb d hd
  by_cases h0 : a = 0 ∧ b = 0 ∧ d = 0
  · exact Or.inl ⟨⟨h0.1, h0.2.1⟩, h0.2.2⟩
  · right
    have hrep : Rep 820 (compT 820 (compT 820 (powT 820 a y0) (powT 820 b c0))
        (powT 820 d (cpOf Tt c0))) (y ^ a * c ^ b * (T * c * T⁻¹) ^ d) :=
      Rep.compT (Rep.compT (Rep.powT hn hy a) (Rep.powT hn hc b)) (Rep.powT hn hcp d)
    cases e : tblEq 820 (compT 820 (compT 820 (powT 820 a y0) (powT 820 b c0))
        (powT 820 d (cpOf Tt c0))) (idT 820)
    · rfl
    · exact absurd (hfree a b d ha hb hd ((tblEq_idT_iff hn hrep).1 e)) h0

theorem kOK_of_sig {Tt c0 k0 : Table} {T c k : Equiv.Perm (Fin 820)} (hT : Rep 820 Tt T)
    (hT2 : T * T = 1) (hc : Rep 820 c0 c) (hk : Rep 820 k0 k) (hkk : k * k = 1) (hk1 : k ≠ 1)
    (hkcp : k * (T * c * T⁻¹) = (T * c * T⁻¹) * k)
    (hkkp : k * (T * k * T⁻¹) = (T * k * T⁻¹) * k) (hkc : k * c * k⁻¹ = c⁻¹) :
    kOK Tt c0 k0 = true := by
  have hTi : Rep 820 Tt T⁻¹ := by rw [inv_eq_of_mul_eq_one_right hT2]; exact hT
  have hki : Rep 820 k0 k⁻¹ := by rw [inv_eq_of_mul_eq_one_right hkk]; exact hk
  have hcp : Rep 820 (cpOf Tt c0) (T * c * T⁻¹) := rep_conjT hT hTi hc
  have hkp : Rep 820 (cpOf Tt k0) (T * k * T⁻¹) := rep_conjT hT hTi hk
  have hn : (820 : ℕ) < 2 ^ 32 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : involOK 820 k0 = true :=
    involOK_of_orderOf hn hk (orderOf_eq_prime (by rwa [sq]) hk1)
  have hconj : Rep 820 (compT 820 (conjT 820 k0 k0 c0) c0) (k * c * k⁻¹ * c) :=
    Rep.compT (rep_conjT hk hki hc) hc
  simp only [kOK, Bool.and_eq_true]
  refine ⟨⟨⟨hinv, (commTT_iff hk hcp).2 hkcp⟩, (commTT_iff hk hkp).2 hkkp⟩, ?_⟩
  exact (tblEq_idT_iff hn hconj).2 (by rw [hkc, inv_mul_cancel])

theorem card_eq_length_of_list {M : Type*} [Group M] {H : Subgroup M} {L : List M}
    (hL : ∀ x, x ∈ H ↔ x ∈ L) (hnd : L.Nodup) : Nat.card ↥H = L.length := by
  classical
  have hset : (H : Set M) = ↑L.toFinset := by
    ext x
    simp [hL x]
  have : Nat.card ↥H = (H : Set M).ncard := Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem cent5_spec {G : Subgroup (Equiv.Perm (Fin 820))} {E : Array Table}
    {y c c' k k' : Equiv.Perm (Fin 820)} {c0 cp0 k0 kp0 : Table}
    (hErep : ∀ i < E.size, Rep 820 E[i]! (tablePerm 820 E[i]!))
    (hEmem : ∀ i < E.size, tablePerm 820 E[i]! ∈ G ⊓ centralizer ({y} : Set _))
    (hEcov : ∀ x ∈ G ⊓ centralizer ({y} : Set _), ∃ i < E.size, Rep 820 E[i]! x)
    (hnd : (E.toList.map (tablePerm 820)).Nodup) (hc : Rep 820 c0 c) (hcp : Rep 820 cp0 c')
    (hk : Rep 820 k0 k) (hkp : Rep 820 kp0 k') :
    Nat.card ↥(G ⊓ centralizer ({y, c, c', k, k'} : Set (Equiv.Perm (Fin 820)))) =
      (E.toList.filter fun z => commTT 820 z c0 && commTT 820 z cp0 && commTT 820 z k0 &&
        commTT 820 z kp0).length := by
  set p : Table → Bool := fun z => commTT 820 z c0 && commTT 820 z cp0 && commTT 820 z k0 &&
    commTT 820 z kp0 with hp
  have hL : ∀ z, z ∈ G ⊓ centralizer ({y, c, c', k, k'} : Set (Equiv.Perm (Fin 820))) ↔
      z ∈ (E.toList.filter p).map (tablePerm 820) := by
    intro z
    rw [List.mem_map]
    constructor
    · intro hz
      obtain ⟨hzG, hzc⟩ := mem_inf.1 hz
      rw [mem_centralizer_iff] at hzc
      have hzy : z ∈ G ⊓ centralizer ({y} : Set _) :=
        mem_inf.2 ⟨hzG, mem_centralizer_singleton_iff.2 (hzc y (by simp)).symm⟩
      obtain ⟨i, hi, hzi⟩ := hEcov z hzy
      refine ⟨E[i]!, List.mem_filter.2 ⟨?_, ?_⟩, tablePerm_eq hzi⟩
      · exact Array.mem_toList_iff.2 (getElem!_mem_array hi)
      · simp only [hp, Bool.and_eq_true]
        refine ⟨⟨⟨(commTT_iff hzi hc).2 (hzc c (by simp)).symm,
          (commTT_iff hzi hcp).2 (hzc c' (by simp)).symm⟩,
          (commTT_iff hzi hk).2 (hzc k (by simp)).symm⟩,
          (commTT_iff hzi hkp).2 (hzc k' (by simp)).symm⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨hemem, hpe⟩ := List.mem_filter.1 he
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.1 hemem)
      have hrep := hErep i (by simpa using hi)
      have hmem := hEmem i (by simpa using hi)
      rw [getElem!_pos E i (by simpa using hi)] at hrep hmem
      obtain ⟨hzG, hzy⟩ := mem_inf.1 hmem
      simp only [hp, Bool.and_eq_true] at hpe
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hpe
      refine mem_inf.2 ⟨hzG, mem_centralizer_iff.2 fun h hh => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl
      · exact (mem_centralizer_singleton_iff.1 hzy).symm
      · exact ((commTT_iff hrep hc).1 h1).symm
      · exact ((commTT_iff hrep hcp).1 h2).symm
      · exact ((commTT_iff hrep hk).1 h3).symm
      · exact ((commTT_iff hrep hkp).1 h4).symm
  have hnd' : ((E.toList.filter p).map (tablePerm 820)).Nodup :=
    hnd.sublist ((List.filter_sublist).map _)
  rw [card_eq_length_of_list hL hnd', List.length_map]

end CFSG.EvenSporadicStandard.HSStd.U43
