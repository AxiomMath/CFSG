module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Numerics
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThree
public import CFSG.RankThree.Native.SuzFiveCentralizers
public import Certificates.Certificate36907
public import Certificates.Certificate214031
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Sporadic.SuzOddCore (suzM suzT suzEquivM suzM_le_suzT)

namespace SuzCopy

section Generic

open scoped Pointwise

theorem exists_conj_le_sylow_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P K : Subgroup G) (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hK : IsPGroup p K) : ∃ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ P := by
  obtain ⟨Q, hKQ⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard P hP)
  have hP' : (P : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    have := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    simpa [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] using this.symm
  refine ⟨g, fun k hk => ?_⟩
  rw [hP']
  exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) _).2
    ⟨k, hKQ hk, by simp [MulAut.smul_def]⟩


end Generic

section Checks


theorem okP_spec {g : Array ℕ} (h : okP (levels ()) g = true) :
    Rep 1782 g (permOfArr 1782 g) ∧ permOfArr 1782 g ∈ suzM := by
  simp only [okP, Bool.and_eq_true] at h
  exact ⟨rep_of_validA h.1, mem_suzM_of_inP (rep_of_validA h.1) h.2⟩

theorem validA_of_okP {L : Array Level} {g : Array ℕ} (h : okP L g = true) :
    validA 1782 g = true := by
  simp only [okP, Bool.and_eq_true] at h
  exact h.1

theorem fuseCheckG_sound {tab ts ns : Array (Array ℕ)} {xA y x1 : Array ℕ}
    {Y X1 : Equiv.Perm (Fin 1782)} (hY : Rep 1782 y Y) (hX1 : Rep 1782 x1 X1)
    {cs : ℕ → ArrCert} (h : fuseCheckG (levels ()) tab ts ns xA y x1 cs = true) :
    Rep 1782 xA (permOfArr 1782 xA) ∧ permOfArr 1782 xA ∈ suzM ∧ permOfArr 1782 xA ^ 3 = 1 ∧
    permOfArr 1782 xA ≠ 1 ∧
    (∀ i < 6, ∀ k < (cs i).pts.size, ∀ p : Equiv.Perm (Fin 1782),
      Rep 1782 (cs i).pts[k]! p → p ^ 3 = 1 → p ≠ 1 →
        ∃ n ∈ suzM, n * p * n⁻¹ = permOfArr 1782 xA ∨ n * p * n⁻¹ = Y) ∧
    (∀ k < (cs 0).pts.size, ∀ p : Equiv.Perm (Fin 1782), Rep 1782 (cs 0).pts[k]! p →
      p ^ 3 = 1 → p ≠ 1 → p * X1 ≠ X1 * p) := by
  simp only [fuseCheckG, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hxA, hx3⟩, hx1⟩, hrows⟩, hcov⟩ := h
  obtain ⟨hXr, hXm⟩ := okP_spec hxA
  have hX3 : permOfArr 1782 xA ^ 3 = 1 :=
    (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hXr 3) rep_idA).1 hx3
  have hXne : permOfArr 1782 xA ≠ 1 := fun h1 => by
    have := (eqA_iff hXr rep_idA).2 h1
    rw [this] at hx1
    exact absurd hx1 (by decide)
  have hrow : ∀ j < tab.size, ∃ T N : Equiv.Perm (Fin 1782), Rep 1782 ts[j]! T ∧ N ∈ suzM ∧
      (N * T * N⁻¹ = permOfArr 1782 xA ∨ N * T * N⁻¹ = Y) := by
    intro j hj
    have hr := allLt_spec hrows hj
    simp only [Bool.and_eq_true] at hr
    obtain ⟨⟨hts, hns⟩, heq⟩ := hr
    obtain ⟨hTr, -⟩ := okP_spec hts
    obtain ⟨hNr, hNm⟩ := okP_spec hns
    have hc := rep_conjA (g := ns[j]!) (y := ts[j]!) (validA_of_okP hns) hTr
    refine ⟨permOfArr 1782 ts[j]!, permOfArr 1782 ns[j]!, hTr, hNm, ?_⟩
    unfold repOf at heq
    split_ifs at heq with hr0
    · exact Or.inl ((eqA_iff hc hXr).1 heq)
    · exact Or.inr ((eqA_iff hc hY).1 heq)
  refine ⟨hXr, hXm, hX3, hXne, ?_, ?_⟩
  · intro i hi k hk p hp hp3 hp1
    have hik := allLt_spec (allLt_spec hcov hi) hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hik
    rcases hik with (h1 | h2) | ⟨h3, -⟩
    · rw [(eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hp 3) rep_idA).2 hp3] at h1
      exact absurd h1 (by decide)
    · exact absurd ((eqA_iff hp rep_idA).1 h2) hp1
    · obtain ⟨j, hj, hjj⟩ := Co2T.anyLt_true h3
      simp only [Bool.and_eq_true, beq_iff_eq] at hjj
      obtain ⟨T, N, hTr, hNm, hNT⟩ := hrow j hj
      have hpT : p = T := (eqA_iff hp hTr).1 hjj.2
      subst hpT
      exact ⟨N, hNm, hNT⟩
  · intro k hk p hp hp3 hp1 hcomm
    have hik := allLt_spec (allLt_spec hcov (by norm_num : 0 < 6)) hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hik
    rcases hik with (h1 | h2) | ⟨-, h4⟩
    · rw [(eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hp 3) rep_idA).2 hp3] at h1
      exact absurd h1 (by decide)
    · exact absurd ((eqA_iff hp rep_idA).1 h2) hp1
    · simp only [bne_iff_ne, ne_eq, not_true_eq_false, false_or] at h4
      have hc := (commA_iff hp hX1).2 hcomm
      rw [hc] at h4
      exact absurd h4 (by decide)

theorem permsA_two_suz {n : ℕ} {gs : Array (Array ℕ)} (h : gs.size = 2) :
    permsA n gs = {permOfArr n gs[0]!, permOfArr n gs[1]!} := by
  ext x
  simp only [permsA, h, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩


end Checks

section Facts


noncomputable def xA : Equiv.Perm (Fin 1782) := permOfArr 1782 (rebuild (levels ()) xAβ)

theorem fuse_facts :
    Rep 1782 (rebuild (levels ()) xAβ) xA ∧ xA ∈ suzM ∧ xA ^ 3 = 1 ∧ xA ≠ 1 ∧
    (∀ i < 6, ∀ k < (suzFiveCCert i).pts.size, ∀ p : Equiv.Perm (Fin 1782),
      Rep 1782 (suzFiveCCert i).pts[k]! p → p ^ 3 = 1 → p ≠ 1 →
        ∃ n ∈ suzM, n * p * n⁻¹ = xA ∨ n * p * n⁻¹ = yPerm) ∧
    (∀ k < (suzFiveCCert 0).pts.size, ∀ p : Equiv.Perm (Fin 1782),
      Rep 1782 (suzFiveCCert 0).pts[k]! p → p ^ 3 = 1 → p ≠ 1 →
        p * suzFiveLine 1 ≠ suzFiveLine 1 * p) := by
  have h := Certificates.certificate36907.1
  unfold fuseCheck at h
  have hrep : Rep 1782 (suzFiveLineArr 1) (suzFiveLine 1) := rep_suzFiveLine 1
  exact fuseCheckG_sound rep_y hrep h


end Facts

section Classes


theorem orderOf_conj_eq {G : Type*} [Group G] (h s : G) :
    orderOf (h * s * h⁻¹) = orderOf s := by
  have := (MulAut.conj h : G ≃* G).orderOf_eq s
  simpa [MulAut.conj_apply] using this

theorem card_suzFiveQ_sylow :
    Nat.card (suzFiveQ.subgroupOf suzM) = 5 ^ (Nat.card suzM).factorization 5 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzFiveQ_le_M).toEquiv, suzFiveQ_spec.2.1,
    factorization_card_suzM_five]
  norm_num

theorem exists_conj_into_C {s g : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM) (hg : g ∈ suzM)
    (hg5 : orderOf g = 5) (hcomm : g * s = s * g) :
    ∃ h ∈ suzM, ∃ i : Fin 6, h * s * h⁻¹ ∈ suzFiveC i := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set E : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.zpowers g with hE
  have hEP : E ≤ suzM := (Subgroup.zpowers_le).2 hg
  have hEcard : Nat.card E = 5 := by rw [hE, Nat.card_zpowers, hg5]
  have hEG : IsPGroup 5 (E.subgroupOf suzM) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hEcard]
    norm_num
  obtain ⟨k, hk⟩ := exists_conj_le_sylow_of_card (suzFiveQ.subgroupOf suzM) (E.subgroupOf suzM)
    card_suzFiveQ_sylow hEG
  set kP : Equiv.Perm (Fin 1782) := (k : Equiv.Perm (Fin 1782)) with hkP
  have hgq : kP * g * kP⁻¹ ∈ suzFiveQ :=
    Subgroup.mem_subgroupOf.1 (hk ⟨g, hg⟩ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers g)))
  set g' := kP * g * kP⁻¹ with hg'
  have hg'5 : orderOf g' = 5 := by rw [hg', orderOf_conj_eq, hg5]
  have hH : Subgroup.zpowers g' ∈
      {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} :=
    ⟨(Subgroup.zpowers_le).2 hgq, by rw [Nat.card_zpowers, hg'5]⟩
  rw [suzFiveQ_lines.1] at hH
  obtain ⟨i, hi⟩ := hH
  have hxg : suzFiveLine i ∈ Subgroup.zpowers g' := by
    rw [← hi]
    exact Subgroup.mem_zpowers _
  set s' := kP * s * kP⁻¹ with hs'
  have hcomm' : g' * s' = s' * g' := by
    rw [hg', hs']
    calc kP * g * kP⁻¹ * (kP * s * kP⁻¹) = kP * (g * s) * kP⁻¹ := by group
      _ = kP * (s * g) * kP⁻¹ := by rw [hcomm]
      _ = kP * s * kP⁻¹ * (kP * g * kP⁻¹) := by group
  have hxs : suzFiveLine i * s' = s' * suzFiveLine i := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxg
    rw [← hm]
    exact (Commute.zpow_left (show Commute g' s' from hcomm') m).eq
  have hs'M : s' ∈ suzM := suzM.mul_mem (suzM.mul_mem k.2 hs) (suzM.inv_mem k.2)
  have hC : suzFiveC i = Subgroup.centralizer {suzFiveLine i} ⊓ suzT := suzFiveC_eq i.2
  refine ⟨kP, k.2, i, ?_⟩
  rw [hC]
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hxs.symm, suzM_le_suzT hs'M⟩

theorem exists_rep_of_mem_C {i : Fin 6} {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzFiveC i) :
    ∃ k < (suzFiveCCert i).pts.size, Rep 1782 (suzFiveCCert i).pts[k]! s :=
  enumOK_exists_rep suzFiveKeys_lt (suzFiveC_check_spec i.2).1 hs

theorem no_order25_centralized {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (hs3 : orderOf s = 3) {E : Subgroup (Equiv.Perm (Fin 1782))} (hEP : E ≤ suzM)
    (hE : Nat.card E = 25) (hcomm : ∀ e ∈ E, e * s = s * e) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hEG : IsPGroup 5 (E.subgroupOf suzM) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE]
    norm_num
  obtain ⟨k, hk⟩ := exists_conj_le_sylow_of_card (suzFiveQ.subgroupOf suzM) (E.subgroupOf suzM)
    card_suzFiveQ_sylow hEG
  set kP : Equiv.Perm (Fin 1782) := (k : Equiv.Perm (Fin 1782)) with hkP
  set E' : Subgroup (Equiv.Perm (Fin 1782)) := E.map (MulAut.conj kP).toMonoidHom with hE'
  have hE'Q : E' ≤ suzFiveQ := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hk ⟨e, hEP he⟩ (Subgroup.mem_subgroupOf.2 he))
  have hE'card : Nat.card E' = 25 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj kP).injective, hE]
  have hE'eq : E' = suzFiveQ :=
    Subgroup.eq_of_le_of_card_ge hE'Q (by rw [hE'card, suzFiveQ_spec.2.1])
  set s' := kP * s * kP⁻¹ with hs'
  have hs'M : s' ∈ suzM := suzM.mul_mem (suzM.mul_mem k.2 hs) (suzM.inv_mem k.2)
  have hcomm' : ∀ e ∈ E', e * s' = s' * e := by
    rintro _ ⟨e, he, rfl⟩
    have := hcomm e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs']
    calc kP * e * kP⁻¹ * (kP * s * kP⁻¹) = kP * (e * s) * kP⁻¹ := by group
      _ = kP * (s * e) * kP⁻¹ := by rw [this]
      _ = kP * s * kP⁻¹ * (kP * e * kP⁻¹) := by group
  have hx0 : suzFiveLine 0 ∈ E' := by
    rw [hE'eq]
    exact suzFiveLine_mem_Q 0
  have hx1 : suzFiveLine 1 ∈ E' := by
    rw [hE'eq]
    exact suzFiveLine_mem_Q 1
  have hC0 : suzFiveC 0 = Subgroup.centralizer {suzFiveLine 0} ⊓ suzT := suzFiveC_eq (by norm_num)
  have hs'C : s' ∈ suzFiveC 0 := by
    rw [hC0]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm' _ hx0).symm,
      suzM_le_suzT hs'M⟩
  obtain ⟨j, hj, hjrep⟩ := exists_rep_of_mem_C hs'C
  have hs'3 : s' ^ 3 = 1 := by
    have := pow_orderOf_eq_one s'
    rwa [hs', orderOf_conj_eq, hs3] at this
  have hs'1 : s' ≠ 1 := fun h1 => by
    have : orderOf s' = 3 := by rw [hs', orderOf_conj_eq, hs3]
    rw [h1, orderOf_one] at this
    omega
  exact fuse_facts.2.2.2.2.2 j hj s' hjrep hs'3 hs'1 (hcomm' _ hx1).symm

theorem not_25_dvd_centralizer {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (hs3 : orderOf s = 3) :
    ¬ 25 ∣ Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
      Subgroup (Equiv.Perm (Fin 1782))) := by
  intro hd
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.centralizer ({s} : Set _) ⊓ suzM with hC
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 (n := 2) (by simpa using hd)
  refine no_order25_centralized hs hs3 (E := E.map C.subtype) ?_ ?_ ?_
  · rintro _ ⟨e, -, rfl⟩
    exact (Subgroup.mem_inf.1 e.2).2
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hE]
    norm_num
  · rintro _ ⟨e, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 e.2).1

theorem classes_of_order_three {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (hs3 : orderOf s = 3) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
      Subgroup (Equiv.Perm (Fin 1782))) ∨
    (∃ k ∈ suzM, k * xA * k⁻¹ = s) ∨ (∃ k ∈ suzM, k * yPerm * k⁻¹ = s) := by
  by_cases h5 : 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
      Subgroup (Equiv.Perm (Fin 1782)))
  · right
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({s} :
      Set (Equiv.Perm (Fin 1782))) ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782)))) 5 h5
    have hxc := Subgroup.mem_inf.1 x.2
    have hg5 : orderOf (x : Equiv.Perm (Fin 1782)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨h, hh, i, hi⟩ := exists_conj_into_C hs hxc.2 hg5
      (Subgroup.mem_centralizer_singleton_iff.1 hxc.1)
    obtain ⟨j, hj, hjrep⟩ := exists_rep_of_mem_C hi
    have hs'3 : (h * s * h⁻¹) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (h * s * h⁻¹)
      rwa [orderOf_conj_eq, hs3] at this
    have hs'1 : h * s * h⁻¹ ≠ 1 := fun h1 => by
      have : orderOf (h * s * h⁻¹) = 3 := by rw [orderOf_conj_eq, hs3]
      rw [h1, orderOf_one] at this
      omega
    obtain ⟨n, hn, hcase⟩ := fuse_facts.2.2.2.2.1 i i.2 j hj _ hjrep hs'3 hs'1
    have hnh : (n * h)⁻¹ * (n * (h * s * h⁻¹) * n⁻¹) * (n * h) = s := by group
    have hnhM : (n * h)⁻¹ ∈ suzM := suzM.inv_mem (suzM.mul_mem hn hh)
    rcases hcase with hc | hc
    · left
      refine ⟨(n * h)⁻¹, hnhM, ?_⟩
      rw [← hnh, hc]
      group
    · right
      refine ⟨(n * h)⁻¹, hnhM, ?_⟩
      rw [← hnh, hc]
      group
  · exact Or.inl h5


end Classes

section YClass


theorem yPerm_ne_one : yPerm ≠ 1 := fun h1 => by
  have := (eqA_iff rep_y rep_idA).2 h1
  rw [cCheck_parts.2.2.2.1] at this
  exact absurd this (by decide)

theorem yPerm_ord : orderOf yPerm = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime yPerm_pow yPerm_ne_one

theorem card_Cy : Nat.card (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓
    suzM : Subgroup (Equiv.Perm (Fin 1782))) = 3 ^ 1 * 1080 := by
  rw [← (Cy_eq).1, (Cy_eq).2]
  norm_num


end YClass

section Main


theorem pairEqCheckG_sound {xA : Array ℕ} {X : Equiv.Perm (Fin 1782)} (hX : Rep 1782 xA X)
    {gs : Array (Array ℕ)} {fuel N : ℕ} (h : pairEqCheckG (levels ()) xA gs fuel N = true) :
    ∃ g₁ g₂ : Equiv.Perm (Fin 1782), g₁ ∈ suzM ∧ g₂ ∈ suzM ∧ g₁ * X = X * g₁ ∧
      g₂ * X = X * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 1782)))) = N := by
  simp only [pairEqCheckG, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hsz, hall⟩, henum, hN⟩ := h
  have hspec := enumOK_spec suzFiveKeys_lt henum
  have hcard : Nat.card (Subgroup.closure (permsA 1782 gs)) =
      (enumBfs 1782 gs suzFiveKeys fuel).pts.size := hspec.2.1
  have hone : ∀ k, k < 2 → orderOf (permOfArr 1782 gs[k]!) = 5 ∧ permOfArr 1782 gs[k]! ∈ suzM ∧
      permOfArr 1782 gs[k]! * X = X * permOfArr 1782 gs[k]! := by
    intro k hk
    have := allLt_spec hall hk
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    obtain ⟨⟨⟨hok, hcm⟩, hpow⟩, hne⟩ := this
    obtain ⟨hrep, hmem⟩ := okP_spec hok
    refine ⟨?_, hmem, (commA_iff hrep hX).1 hcm⟩
    have h5 : permOfArr 1782 gs[k]! ^ 5 = 1 :=
      (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrep 5) rep_idA).1 hpow
    have h1 : permOfArr 1782 gs[k]! ≠ 1 := fun h1 => by
      rw [(eqA_iff hrep rep_idA).2 h1] at hne
      exact absurd hne (by decide)
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime h5 h1
  obtain ⟨o0, m0, c0⟩ := hone 0 (by norm_num)
  obtain ⟨o1, m1, c1⟩ := hone 1 (by norm_num)
  refine ⟨_, _, m0, m1, c0, c1, o0, o1, ?_⟩
  have hs : Subgroup.closure (permsA 1782 gs) = Subgroup.closure ({permOfArr 1782 gs[0]!,
      permOfArr 1782 gs[1]!} : Set (Equiv.Perm (Fin 1782))) := by rw [permsA_two_suz hsz]
  rw [← hs, hcard]
  exact hN


theorem pair_xA :
    ∃ g₁ g₂ : Equiv.Perm (Fin 1782), g₁ ∈ suzM ∧ g₂ ∈ suzM ∧ g₁ * xA = xA * g₁ ∧
      g₂ * xA = xA * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 1782)))) = 405 := by
  have h := Certificates.certificate214031
  unfold pairEqCheck at h
  exact pairEqCheckG_sound fuse_facts.1 h

theorem xA_ord : orderOf xA = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime fuse_facts.2.2.1 fuse_facts.2.2.2.1

theorem card_suzM_eq : Nat.card ↥suzM = 448345497600 := by
  rw [← Nat.card_congr suzEquivM.toEquiv]
  exact CFSG.Sporadic.Suz.card_Suz

theorem l3Excl_suz : L3Excl (Nat.card ↥suzM) 5 4 := by
  rw [card_suzM_eq]
  exact l3Excl_448345497600_5_4

theorem noL3Comp_xA :
    NoL3Comp (Subgroup.centralizer ({xA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨g₁, g₂, h₁, h₂, c₁, c₂, o₁, o₂, hcard⟩ := pair_xA
  refine noL3Comp_of_prime_pair (P := suzM) inf_le_right (q := 5) (k := 4) (by norm_num)
    (by norm_num) l3Excl_suz ?_ ⟨g₁, ?_, g₂, ?_, o₁, o₂, ?_⟩
  · rw [show (5 : ℕ) ^ 2 = 25 by norm_num]
    exact not_25_dvd_centralizer fuse_facts.2.1 xA_ord
  · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 c₁, h₁⟩
  · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 c₂, h₂⟩
  · rw [hcard]
    norm_num

theorem noL3Comp_y :
    NoL3Comp (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  refine noL3Comp_of_noDvd ?_
  rw [card_Cy]
  exact noL3Dvd_3240

end Main

end SuzCopy

theorem sporL3DownInner_Suz
    (hbr : SporadicBridges) : SporL3DownInner .Suz := by
  haveI : Finite ↥suzM := Nat.finite_of_card_ne_zero (by rw [SuzCopy.card_suzM_eq]; norm_num)
  have hM : Nonempty (↥suzM ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) :=
    ⟨suzEquivM.symm.trans (hbr .Suz).some⟩
  refine sporL3DownInner_of_perm_comp (G := Equiv.Perm (Fin 1782)) suzM hM
    (by rw [SuzCopy.card_suzM_eq]; exact noL3Eq_448345497600) ?_
  intro x hx hx3
  rcases SuzCopy.classes_of_order_three hx hx3 with h5 | ⟨k, hk, hkx⟩ | ⟨k, hk, hky⟩
  · exact noL3Comp_of_not_dvd_sub inf_le_right (by norm_num) (by norm_num) SuzCopy.l3Excl_suz h5
  · have := noL3Comp_conj_class (P := suzM) (SuzCopy.fuse_facts.2.2.1) hk (e := 1) (Or.inl rfl)
      SuzCopy.noL3Comp_xA
    rwa [pow_one, hkx] at this
  · have := noL3Comp_conj_class (P := suzM) yPerm_pow hk (e := 1) (Or.inl rfl) SuzCopy.noL3Comp_y
    rwa [pow_one, hky] at this

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
