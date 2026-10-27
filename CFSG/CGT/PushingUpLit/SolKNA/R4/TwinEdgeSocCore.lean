module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeLift

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

theorem soc_a_pow {n : ℕ} (i : ZMod (2 * n)) (m : ℕ) :
    (QuaternionGroup.a i : QuaternionGroup n) ^ m =
      QuaternionGroup.a ((m : ZMod (2 * n)) * i) := by
  induction m with
  | zero => simp [QuaternionGroup.a_zero]
  | succ m ih => rw [pow_succ, ih, QuaternionGroup.a_mul_a]; congr 1; push_cast; ring

theorem soc_a_two_mul_mem {n : ℕ} [NeZero n] (k : ZMod (2 * n)) :
    (QuaternionGroup.a (2 * k) : QuaternionGroup n) ∈
      Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup n) := by
  have : (QuaternionGroup.a (2 * k) : QuaternionGroup n) = (QuaternionGroup.a 2) ^ k.val := by
    rw [soc_a_pow, ZMod.natCast_zmod_val, mul_comm]
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem soc_quaternion_commutator_mem {n : ℕ} [NeZero n] (g h : QuaternionGroup n) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup n) := by
  have h2n : (2 : ZMod (2 * n)) * (n : ZMod (2 * n)) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * n)
  rcases g with i | i <;> rcases h with j | j
  · show QuaternionGroup.a i * QuaternionGroup.a j * QuaternionGroup.a (-i) *
      QuaternionGroup.a (-j) ∈ _
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a]
    have := soc_a_two_mul_mem (n := n) 0
    rw [mul_zero] at this
    convert this using 2
    ring
  · show QuaternionGroup.a i * QuaternionGroup.xa j * QuaternionGroup.a (-i) *
      QuaternionGroup.xa ((n : ZMod (2 * n)) + j) ∈ _
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
    convert soc_a_two_mul_mem (n := n) i using 2
    linear_combination h2n
  · show QuaternionGroup.xa i * QuaternionGroup.a j * QuaternionGroup.xa ((n : ZMod (2 * n)) + i) *
      QuaternionGroup.a (-j) ∈ _
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa, QuaternionGroup.a_mul_a]
    convert soc_a_two_mul_mem (n := n) (-j) using 2
    linear_combination h2n
  · show QuaternionGroup.xa i * QuaternionGroup.xa j * QuaternionGroup.xa ((n : ZMod (2 * n)) + i) *
      QuaternionGroup.xa ((n : ZMod (2 * n)) + j) ∈ _
    rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_xa]
    convert soc_a_two_mul_mem (n := n) (j - i) using 2
    linear_combination h2n

theorem soc_quaternion_sq_eq_one_of_central {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (q : QuaternionGroup n) (hq : ∀ y : QuaternionGroup n, q * y = y * q) : q * q = 1 := by
  rcases q with k | k
  · have h := hq (QuaternionGroup.xa 0)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h
    have h1 : (0 : ZMod (2 * n)) - k = 0 + k := QuaternionGroup.xa.inj h
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
    congr 1
    linear_combination -h1
  · exfalso
    have h := hq (QuaternionGroup.a 1)
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at h
    have h1 : k + 1 = k - 1 := QuaternionGroup.xa.inj h
    have h2 : (2 : ZMod (2 * n)) = 0 := by linear_combination h1
    have h3 : (2 * n : ℕ) ∣ 2 := by
      have := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp (by exact_mod_cast h2)
      exact this
    have := Nat.le_of_dvd (by norm_num) h3
    omega

section Quat

variable {G : Type} [Group G] {R : Subgroup G} {n : ℕ} [NeZero n]

theorem soc_commutator_le_self (P : Subgroup G) : ⁅P, P⁆ ≤ P :=
  Subgroup.commutator_le.mpr fun x hx y hy =>
    P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)

theorem soc_commutator_eq_zpowers (e : ↥R ≃* QuaternionGroup n) :
    ⁅R, R⁆ = Subgroup.zpowers ((e.symm (QuaternionGroup.a 2) : ↥R) : G) := by
  set f : QuaternionGroup n →* G := R.subtype.comp e.symm.toMonoidHom with hf
  have hfx : ∀ x (hx : x ∈ R), f (e ⟨x, hx⟩) = x := fun x hx => by simp [hf]
  have hz : Subgroup.zpowers ((e.symm (QuaternionGroup.a 2) : ↥R) : G) =
      (Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup n)).map f := by
    rw [MonoidHom.map_zpowers]; rfl
  rw [hz]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hmem := Subgroup.mem_map_of_mem f
      (soc_quaternion_commutator_mem (e ⟨x, hx⟩) (e ⟨y, hy⟩))
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv, hfx x hx, hfx y hy] at hmem
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
    have h1 : f (QuaternionGroup.a 2) = ⁅f (QuaternionGroup.a 1), f (QuaternionGroup.xa 0)⁆ := by
      rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
        quaternion_comm_a_xa]
    show f (QuaternionGroup.a 2) ∈ ⁅R, R⁆
    rw [h1]
    exact Subgroup.commutator_mem_commutator
      (show f (QuaternionGroup.a 1) ∈ R from (e.symm (QuaternionGroup.a 1)).2)
      (show f (QuaternionGroup.xa 0) ∈ R from (e.symm (QuaternionGroup.xa 0)).2)

theorem soc_isCyclic_commutator_of_quat (e : ↥R ≃* QuaternionGroup n) : IsCyclic ↥⁅R, R⁆ := by
  rw [soc_commutator_eq_zpowers e]
  infer_instance

theorem soc_natCard_commutator_of_quat (e : ↥R ≃* QuaternionGroup n) (hn : 2 ≤ n) :
    Nat.card ↥⁅R, R⁆ = n := by
  rw [soc_commutator_eq_zpowers e, Nat.card_zpowers, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact orderOf_quaternion_a_two hn

theorem soc_four_le_card_commutator_of_quat (e : ↥R ≃* QuaternionGroup n) (hn : 4 ≤ n) :
    4 ≤ Nat.card ↥⁅R, R⁆ := by
  rw [soc_natCard_commutator_of_quat e (by omega)]
  exact hn

theorem soc_sq_eq_one_of_central (e : ↥R ≃* QuaternionGroup n) (hn : 2 ≤ n) {j : G} (hj : j ∈ R)
    (hc : ∀ y ∈ R, j * y = y * j) : j * j = 1 := by
  have h := soc_quaternion_sq_eq_one_of_central hn (e ⟨j, hj⟩) fun y => by
    have := congrArg e (Subtype.ext (hc (e.symm y : ↥R) (e.symm y).2) :
      (⟨j, hj⟩ : ↥R) * e.symm y = e.symm y * ⟨j, hj⟩)
    simpa using this
  have h2 : (⟨j, hj⟩ : ↥R) * ⟨j, hj⟩ = 1 := e.injective (by rw [map_mul, h, map_one])
  exact congrArg Subtype.val h2

end Quat

section SylowCore

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def socSylowOf {V P : Subgroup G} (h : IsSylow2In V P) : Sylow 2 ↥P where
  toSubgroup := V.subgroupOf P
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map P.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
    rfl

theorem soc_isSylow2In_commutator {K P N : Subgroup G}
    (hK2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) (hP : IsSylow2In P K)
    (hPN : ⁅P, P⁆ ≤ N) (hNK : N ≤ ⁅K, K⁆) : IsSylow2In ⁅P, P⁆ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hPN, hP.2.1.to_le (soc_commutator_le_self P), fun V hVN hV2 hle => ?_⟩
  set O := classicalInvolutionOddCore ↥K with hO
  let π : ↥K →* ↥K ⧸ O := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  let S₀ : Sylow 2 ↥K := socSylowOf hP
  have hS₀ : (S₀ : Subgroup ↥K) = P.subgroupOf K := rfl
  have hπS : (S₀ : Subgroup ↥K).map π = ⊤ := by
    have h := (Sylow.mapSurjective hπ S₀).is_maximal' (Q := ⊤)
      (hK2.of_equiv Subgroup.topEquiv.symm) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hπC : Subgroup.map π ⁅(S₀ : Subgroup ↥K), (S₀ : Subgroup ↥K)⁆ =
      ⁅(⊤ : Subgroup (↥K ⧸ O)), (⊤ : Subgroup (↥K ⧸ O))⁆ := by
    rw [Subgroup.map_commutator, hπS]
  have hcomK : Subgroup.map K.subtype ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⁅K, K⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCP : Subgroup.map K.subtype ⁅(S₀ : Subgroup ↥K), (S₀ : Subgroup ↥K)⁆ = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, hS₀, Subgroup.map_subgroupOf_eq_of_le hP.1]
  have hmt : (⊤ : Subgroup ↥K).map π = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hπ
  refine le_antisymm (fun x hx => ?_) hle
  have hxKK : x ∈ ⁅K, K⁆ := hNK (hVN hx)
  have hxK : x ∈ K := soc_commutator_le_self K hxKK
  have hxc : (⟨x, hxK⟩ : ↥K) ∈ ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ := by
    rw [← hcomK] at hxKK
    obtain ⟨y, hy, hyx⟩ := hxKK
    have : y = ⟨x, hxK⟩ := Subtype.ext hyx
    rwa [← this]
  have hπx : π ⟨x, hxK⟩ ∈ Subgroup.map π ⁅(S₀ : Subgroup ↥K), (S₀ : Subgroup ↥K)⁆ := by
    rw [hπC]
    have := Subgroup.mem_map_of_mem π hxc
    rwa [Subgroup.map_commutator, hmt] at this
  obtain ⟨c, hc, hcx⟩ := hπx
  have hcP : (c : G) ∈ ⁅P, P⁆ := by
    rw [← hCP]
    exact Subgroup.mem_map_of_mem K.subtype hc
  have hcV : (c : G) ∈ V := hle hcP
  have hoV : (c : G)⁻¹ * x ∈ V := V.mul_mem (V.inv_mem hcV) hx
  have hoK : (c : G)⁻¹ * x ∈ K := K.mul_mem (K.inv_mem c.2) hxK
  have hoO : (⟨(c : G)⁻¹ * x, hoK⟩ : ↥K) ∈ O := by
    have h1 : (⟨(c : G)⁻¹ * x, hoK⟩ : ↥K) = c⁻¹ * ⟨x, hxK⟩ := rfl
    rw [h1, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hcx' : ((c : ↥K) : ↥K ⧸ O) = ((⟨x, hxK⟩ : ↥K) : ↥K ⧸ O) := hcx
    rw [hcx', inv_mul_cancel]
  have hz2 : IsPGroup 2 (Subgroup.zpowers ((c : G)⁻¹ * x)) :=
    hV2.to_le (Subgroup.zpowers_le.mpr hoV)
  have ho1 : (c : G)⁻¹ * x = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
      (mem_oddCoreOf_iff.mpr ⟨hoK, hoO⟩) hz2
  rw [← inv_mul_eq_one.mp ho1]
  exact hcP

end SylowCore

end CFSG.CGT.PushingUpLit.SolKNA.R4
