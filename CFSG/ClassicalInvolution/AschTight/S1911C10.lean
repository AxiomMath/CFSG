module

public import CFSG.ClassicalInvolution.AschTight.Hall196Basic
public import CFSG.ClassicalInvolution.AschTight.S1911EtaY

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem le_sec19X_member (hd : Sec19Data p f K z S W) : K ≤ sec19X K z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := hd.tight.toTightBranch
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_tight htb
  set N : Subgroup K := (sec19X K z).subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have hk := Hall196.centralizer_le_normalizer_sec19X K z (hKz k.2)
    simpa using (Subgroup.mem_normalizer_iff.mp hk n).mp hn
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hQN : (Q : Subgroup K) ≤ N := by
    intro x hx
    rw [hN, Subgroup.mem_subgroupOf]
    refine le_iSup₂ (f := fun (B : Subgroup G) (_ : (B ∈ USet (CoreAssembly.conjClass K) ∨
      B ∈ RSet (CoreAssembly.conjClass K)) ∧ B ≤ Subgroup.centralizer ({z} : Set G)) => B)
      ((Q : Subgroup K).map K.subtype)
      ⟨Or.inr ⟨K, CoreAssembly.mem_conjClass_self K, Q, rfl⟩,
        (Subgroup.map_subtype_le _).trans hKz⟩ ⟨x, hx, rfl⟩
  have hodd : Odd (Nat.card (K ⧸ N)) := by
    rw [← Subgroup.index]
    have h1 : N.index ∣ (Q : Subgroup K).index := Subgroup.index_dvd_of_le hQN
    have h2 : ¬ 2 ∣ (Q : Subgroup K).index := Q.not_dvd_index
    exact Nat.not_even_iff_odd.mp fun h => h2 ((even_iff_two_dvd.mp h).trans h1)
  have hsol : Group.IsSolvable (K ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect K := hd.tight.branch.member.perfect
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) hsol
  intro k hk
  have h1 : (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
  exact h1

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup {P N : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P ⊔ N) :
    ∃ m : ℕ, x ^ (2 ^ m) ∈ N := by
  have hx' : x ∈ ((P ⊔ N : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right P N hPN] at hx'
  obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.mp hx'
  have key : ∀ j : ℕ, ∃ c ∈ N, (a * n) ^ j = a ^ j * c := by
    intro j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨c, hc, hj⟩ := ih
      have hac : a⁻¹ * c * a ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPN ha)) c).mp hc
        simpa using this
      refine ⟨a⁻¹ * c * a * n, N.mul_mem hac hn, ?_⟩
      rw [pow_succ, hj, pow_succ]
      group
  obtain ⟨m, hm⟩ := hP ⟨a, ha⟩
  have hm' : a ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  obtain ⟨c, hc, hj⟩ := key (2 ^ m)
  refine ⟨m, ?_⟩
  rw [hj, hm', one_mul]
  exact hc

omit [Finite G] in
theorem mem_oddCore_of_mem {M : Subgroup G} [Finite M]
    (hKM : K ≤ Subgroup.normalizer (M : Set G)) (hM : Odd (Nat.card M)) {k : K}
    (hk : (k : G) ∈ M) : k ∈ classicalInvolutionOddCore K := by
  have hle : (K ⊓ M).subgroupOf K ≤ classicalInvolutionOddCore K := by
    unfold classicalInvolutionOddCore
    refine le_sSup ⟨⟨fun n hn g => ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (hKM g.2) n).mp hn.2
      simpa using this
    · have e : Nat.card ((K ⊓ M).subgroupOf K) = Nat.card ↥(K ⊓ M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [e]
      exact hM.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  exact hle (Subgroup.mem_subgroupOf.mpr ⟨k.2, hk⟩)

variable (p f) in
theorem c19_10_of : C19_10Tmp p f := by
  intro G _ _ _ K z S W hd heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ K ⊔ W) :=
    S.isPGroup'.to_le (sup_le inf_le_left hd.hWS)
  have hPX : (S : Subgroup G) ⊓ K ⊔ W ≤ sec19X K z :=
    sup_le (inf_le_right.trans (le_sec19X_member hd)) (le_sec19X hd)
  have hPN : (S : Subgroup G) ⊓ K ⊔ W ≤
      Subgroup.normalizer (oddCoreOf (sec19X K z) : Set G) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hPX hx))
  have hKN : K ≤ Subgroup.normalizer (oddCoreOf (sec19X K z) : Set G) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (le_sec19X_member hd hx))
  have hK2 : IsPGroup 2 (K ⧸ classicalInvolutionOddCore K) := by
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have hkX : (k : G) ∈ sec19X K z := le_sec19X_member hd k.2
    rw [heq] at hkX
    obtain ⟨m, hm⟩ := exists_pow_mem_of_mem_sup hPN hP2 hkX
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_oddCore_of_mem hKN (oddCoreOf_odd_natCard _) (by simpa using hm)
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hnt : Nontrivial (K ⧸ classicalInvolutionOddCore K) := by
    refine ⟨⟨QuotientGroup.mk ⟨z, hI.mem⟩, 1, fun h => ?_⟩⟩
    rw [QuotientGroup.eq_one_iff] at h
    have hz := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
      (show z ∈ oddCoreOf K from ⟨⟨z, hI.mem⟩, h, rfl⟩)
      (isPGroup_zpowers_of_mul_self_eq_one hI.sq hI.ne_one)
    exact hI.ne_one hz
  have : Group.IsPerfect K := hd.tight.branch.member.perfect
  exact Group.IsPerfect.not_isNilpotent (K ⧸ classicalInvolutionOddCore K) hK2.isNilpotent

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
