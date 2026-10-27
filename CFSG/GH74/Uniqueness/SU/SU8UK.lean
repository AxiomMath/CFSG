module

public import CFSG.GH74.Uniqueness.SU.SU8UConf
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Uniqueness.Bender.Sylow2Special

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.UConf
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

namespace UK

theorem commutator_le_of_card {K : Type*} [Group K] [Finite K] {P M : Subgroup K} (hM : M ≤ P)
    (hP : Nat.card P ≤ 2 * Nat.card M) : ⁅P, P⁆ ≤ M := by
  classical
  set M' : Subgroup ↥P := M.subgroupOf P with hM'
  have hcard : Nat.card M' = Nat.card M := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv
  have h1 := Subgroup.card_mul_index M'
  rw [hcard] at h1
  have hpos : 0 < Nat.card M := Nat.card_pos
  have hidx : M'.index ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : Nat.card M * 3 ≤ Nat.card M * M'.index := Nat.mul_le_mul_left _ hlt
    omega
  have hcomm : _root_.commutator ↥P ≤ M' := by
    have hi : M'.index = 1 ∨ M'.index = 2 := by
      have : M'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    rcases hi with hi | hi
    · rw [Subgroup.index_eq_one.mp hi]; exact le_top
    · have : M'.Normal := Subgroup.normal_of_index_eq_two hi
      have hq : Nat.card (↥P ⧸ M') = 2 := by rw [← Subgroup.index, hi]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic (↥P ⧸ M') := isCyclic_of_prime_card hq
      have : IsMulCommutative (↥P ⧸ M') := inferInstance
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp this
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact hcomm (Subgroup.commutator_mem_commutator (G := ↥P) (Subgroup.mem_top ⟨a, ha⟩)
    (Subgroup.mem_top ⟨b, hb⟩))

theorem comm_of_cyclic_quotient {G : Type*} [Group G] (Dd : Subgroup G) [Dd.Normal]
    (hD : Nat.card Dd = 1) [IsCyclic (G ⧸ Dd)] (a b : G) : a * b = b * a := by
  have hbot : Dd = ⊥ := Subgroup.eq_bot_of_card_eq Dd hD
  have hinj : Function.Injective (QuotientGroup.mk' Dd) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]
  apply hinj
  rw [map_mul, map_mul]
  have : IsMulCommutative (G ⧸ Dd) := inferInstance
  exact this.is_comm.comm _ _

theorem exists_order_five {G : Type*} [Group G] [Finite G] (H : Subgroup G) (h : Nat.card H = 15) :
    ∃ c ∈ H, c ^ 5 = 1 ∧ c ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card H := by rw [h]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 h5
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem e_eq_five {e : ℕ} (h : BenderType K 2 3 e) : e = 5 := by
  rcases h.cases' with ⟨hi, -, -⟩ | ⟨hi, -, -⟩ | ⟨-, he, -⟩
  · omega
  · omega
  · rw [he]; norm_num

theorem exists_kconf
    {e : ℕ} (h : BenderType K 2 3 e) (P : Sylow 2 K) :
    ∃ (Zp : Subgroup K) (c : K), KConf (P : Subgroup K) Zp c := by
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  have he : e = 5 := e_eq_five h
  subst he
  have hcard : Nat.card (cartan (P : Subgroup K) t) = 15 := by
    rw [hc.card_cartan]; norm_num
  obtain ⟨c, hcC, hc5, hc1⟩ := exists_order_five _ hcard
  refine ⟨rootCenter (P : Subgroup K), c, ?_⟩
  exact
    { card_P := by rw [hc.card_eq]; norm_num
      card_Z := by rw [hc.card_center]; norm_num
      Z_le := rootCenter_le _
      Z_central := fun w hw p hp => ((mem_rootCenter_iff.mp hw).2 p hp).symm
      Z_sq := hc.center_sq
      comm_eq := (h.lemma_3_5_a_unitary P).1
      invol := fun g hg hg2 => hc.mem_rootCenter_of_mul_self hg hg2
      c_norm := fun p hp =>
        (Subgroup.mem_normalizer_iff.mp (cartan_le_borel _ t hcC) p).mp hp
      c_five := hc5
      fpf := fun p hp hcp =>
        h.fixedPointFree_unitary P hc.sq_eq_one hc.not_mem hcC hc1 hp hcp }

theorem K6 {e : ℕ} (h : BenderType K 2 3 e) :
    ∀ M : Subgroup K, IsPGroup 2 M → 32 ≤ Nat.card M →
      ∃ Z₁ : Subgroup K, Z₁ ≤ M ∧ Nat.card Z₁ = 4 ∧ ∀ w ∈ Z₁, ∀ m ∈ M, w * m = m * w := by
  intro M hM h32
  obtain ⟨P, hMP⟩ := hM.exists_le_sylow
  obtain ⟨Zp, c, kc⟩ := exists_kconf h P
  have hPM : Nat.card (P : Subgroup K) ≤ 2 * Nat.card M := by
    have := kc.card_P
    omega
  have hZM : Zp ≤ M := by
    rw [← kc.comm_eq]
    exact commutator_le_of_card hMP hPM
  exact ⟨Zp, hZM, kc.card_Z, fun w hw m hm => kc.Z_central w hw m (hMP hm)⟩

omit [Finite K] in
theorem outer_comm {e : ℕ} (h : BenderType K 2 3 e) (a b : Outer K) : a * b = b * a := by
  obtain ⟨Dd, hn, -, hd, hq, -⟩ := h.outer_unitary
  have := hn
  have := hq
  have hD : Nat.card Dd = 1 := by rw [hd]; norm_num
  exact comm_of_cyclic_quotient Dd hD a b

end UK

namespace UH

theorem habel_of_outer_comm {Hb : Type*} [Group Hb] (K : Subgroup Hb) [K.Normal]
    (hout : ∀ a b : Outer ↥K, a * b = b * a) (h h' : Hb) :
    ∃ k ∈ K, k⁻¹ * ⁅h, h'⁆ ∈ centralizer (K : Set Hb) := by
  let φ : Hb →* MulAut ↥K := MulAut.conjNormal
  let ψ : Hb →* Outer ↥K := (QuotientGroup.mk' (inner ↥K)).comp φ
  have h1 : ψ ⁅h, h'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hout _ _
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff (φ ⁅h, h'⁆)).mp h1
  refine ⟨k, k.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : x ∈ K := hx
  have e1 : ∀ g : Hb, (((φ g) ⟨x, hx'⟩ : ↥K) : Hb) = g * x * g⁻¹ := fun g => by
    simp [φ, MulAut.conjNormal_apply]
  have e2 : (((MulAut.conj k) ⟨x, hx'⟩ : ↥K) : Hb) = (k : Hb) * x * (k : Hb)⁻¹ := by
    simp [MulAut.conj_apply]
  have this : (k : Hb) * x * (k : Hb)⁻¹ = ⁅h, h'⁆ * x * ⁅h, h'⁆⁻¹ := by
    rw [← e2, ← e1 ⁅h, h'⁆, hk]
  calc x * ((k : Hb)⁻¹ * ⁅h, h'⁆) = (k : Hb)⁻¹ * ((k : Hb) * x * (k : Hb)⁻¹) * ⁅h, h'⁆ := by group
    _ = (k : Hb)⁻¹ * (⁅h, h'⁆ * x * ⁅h, h'⁆⁻¹) * ⁅h, h'⁆ := by rw [this]
    _ = (k : Hb)⁻¹ * ⁅h, h'⁆ * x := by group

end UH

end CFSG.GH74.Uniqueness.SU.SU8
