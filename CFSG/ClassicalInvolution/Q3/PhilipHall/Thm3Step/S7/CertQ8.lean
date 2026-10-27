module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowsBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205QTransport
public import CFSG.ClassicalInvolution.Q3.TL4VtxFam
public import Certificates.Data.S7Q8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  Certificates.S5Rows

section Lift

variable {G : Type*} [Group G] {i j : G}

theorem orderOf_eq_four_of_q8Rel (h : Q8Rel i j) : orderOf i = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (n := 1) (by simpa using h.2.1) (by simpa using h.1)

theorem q8Rel_mul_j (h : Q8Rel i j) : i * j = j * i⁻¹ := by
  calc i * j = j * (j⁻¹ * i * j) := by group
    _ = j * i⁻¹ := by rw [h.2.2.2]

theorem q8Rel_pow_val_add (h : Q8Rel i j) (x y : ZMod (2 * 2)) :
    i ^ (x + y).val = i ^ x.val * i ^ y.val := by
  rw [← pow_add, ZMod.val_add]
  have := pow_mod_orderOf i (x.val + y.val)
  rwa [orderOf_eq_four_of_q8Rel h] at this

theorem q8Rel_pow_mul_j (h : Q8Rel i j) (n : ℕ) : i ^ n * j = j * (i ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc i ^ (n + 1) * j = i ^ n * (i * j) := by rw [pow_succ, mul_assoc]
      _ = i ^ n * j * i⁻¹ := by rw [q8Rel_mul_j h, mul_assoc]
      _ = j * (i ^ (n + 1))⁻¹ := by rw [ih, pow_succ', mul_inv_rev, mul_assoc]

theorem q8Rel_pow_val_mul_j (h : Q8Rel i j) (x : ZMod (2 * 2)) :
    i ^ x.val * j = j * i ^ (-x).val := by
  rw [q8Rel_pow_mul_j h]
  congr 1
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← q8Rel_pow_val_add h, neg_add_cancel, ZMod.val_zero,
    pow_zero]

@[expose] def q8Lift (h : Q8Rel i j) : QuaternionGroup 2 →* G where
  toFun
    | QuaternionGroup.a k => i ^ k.val
    | QuaternionGroup.xa k => j * i ^ k.val
  map_one' := by
    change i ^ (0 : ZMod (2 * 2)).val = 1
    simp
  map_mul' := by
    have hsq : j * j = i ^ (2 : ZMod (2 * 2)).val := by
      change j * j = i ^ 2
      rw [← sq, h.2.2.1]
    rintro (x | x) (y | y)
    · change i ^ (x + y).val = i ^ x.val * i ^ y.val
      exact q8Rel_pow_val_add h x y
    · change j * i ^ (y - x).val = i ^ x.val * (j * i ^ y.val)
      rw [← mul_assoc, q8Rel_pow_val_mul_j h, mul_assoc, ← q8Rel_pow_val_add h, neg_add_eq_sub]
    · change j * i ^ (x + y).val = j * i ^ x.val * i ^ y.val
      rw [mul_assoc, q8Rel_pow_val_add h]
    · change i ^ (((2 : ℕ) : ZMod (2 * 2)) + y - x).val = j * i ^ x.val * (j * i ^ y.val)
      calc i ^ (((2 : ℕ) : ZMod (2 * 2)) + y - x).val
        _ = i ^ (2 : ZMod (2 * 2)).val * i ^ (-x + y).val := by
          rw [← q8Rel_pow_val_add h]
          congr 2
          push_cast
          ring
        _ = j * (i ^ x.val * j) * i ^ y.val := by
          rw [q8Rel_pow_val_mul_j h, ← hsq, q8Rel_pow_val_add h]
          simp only [mul_assoc]
        _ = j * i ^ x.val * (j * i ^ y.val) := by simp only [mul_assoc]

theorem q8Lift_a (h : Q8Rel i j) (k : ZMod (2 * 2)) :
    q8Lift h (QuaternionGroup.a k) = i ^ k.val := rfl

theorem q8Lift_xa (h : Q8Rel i j) (k : ZMod (2 * 2)) :
    q8Lift h (QuaternionGroup.xa k) = j * i ^ k.val := rfl

theorem q8Lift_injective (h : Q8Rel i j) : Function.Injective (q8Lift h) := by
  rw [injective_iff_map_eq_one]
  have ho := orderOf_eq_four_of_q8Rel h
  rintro (k | k) hk
  · rw [q8Lift_a] at hk
    have h1 : 4 ∣ k.val := by rw [← ho]; exact orderOf_dvd_of_pow_eq_one hk
    have h2 : k.val < 4 := ZMod.val_lt k
    have h3 : k.val = 0 := by omega
    rw [QuaternionGroup.one_def, (ZMod.val_eq_zero k).mp h3]
  · exfalso
    rw [q8Lift_xa] at hk
    have hj : j = (i ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have hc : j⁻¹ * i * j = i := by
      rw [hj, inv_inv]
      group
    apply h.2.1
    have h2 := h.2.2.2
    rw [hc] at h2
    rw [sq]
    calc i * i = i * i⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel i

theorem range_q8Lift (h : Q8Rel i j) : (q8Lift h).range = Subgroup.closure ({i, j} : Set G) := by
  have hi : i ∈ Subgroup.closure ({i, j} : Set G) := Subgroup.subset_closure (Set.mem_insert i _)
  have hj : j ∈ Subgroup.closure ({i, j} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem i (Set.mem_singleton j))
  apply le_antisymm
  · rintro _ ⟨k | k, rfl⟩
    · exact Subgroup.pow_mem _ hi _
    · exact Subgroup.mul_mem _ hj (Subgroup.pow_mem _ hi _)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact MonoidHom.mem_range.mpr ⟨QuaternionGroup.a 1, by rw [q8Lift_a]; exact pow_one i⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact MonoidHom.mem_range.mpr ⟨QuaternionGroup.xa 0, by rw [q8Lift_xa]; simp⟩

theorem nonempty_closure_pair_mulEquiv (h : Q8Rel i j) :
    Nonempty (↥(Subgroup.closure ({i, j} : Set G)) ≃* QuaternionGroup 2) := by
  rw [← range_q8Lift h]
  exact ⟨(MonoidHom.ofInjective (q8Lift_injective h)).symm⟩

theorem mem_closure_pair_iff (h : Q8Rel i j) {x : G} :
    x ∈ Subgroup.closure ({i, j} : Set G) ↔ x ∈ q8Span i j := by
  constructor
  · rw [← range_q8Lift h]
    have h4 : i ^ 4 = 1 := h.1
    have hinv : i⁻¹ = i ^ 3 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact h4
    have hj4' : j ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← h.2.2.1, ← pow_mul]
      exact h4
    have hj3 : j * i ^ 2 = j⁻¹ := by
      rw [h.2.2.1, eq_inv_iff_mul_eq_one]
      calc j * j ^ 2 * j = j ^ 4 := by group
        _ = 1 := hj4'
    have hj4 : j * i ^ 3 = i * j := by rw [q8Rel_mul_j h, hinv]
    rintro ⟨k | k, rfl⟩ <;> fin_cases k <;>
      simp only [q8Span, List.mem_cons, List.not_mem_nil, or_false]
    · left; exact pow_zero i
    · right; right; left; exact pow_one i
    · right; left; rfl
    · right; right; right; left; exact hinv.symm
    · right; right; right; right; left; change j * i ^ 0 = j; simp
    · right; right; right; right; right; right; right; change j * i ^ 1 = j * i; rw [pow_one]
    · right; right; right; right; right; left; exact hj3
    · right; right; right; right; right; right; left; exact hj4
  · exact fun hx => mem_of_mem_q8Span (Subgroup.subset_closure (Set.mem_insert i _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem i (Set.mem_singleton j))) hx

theorem card_closure_pair (h : Q8Rel i j) : Nat.card (Subgroup.closure ({i, j} : Set G)) = 8 := by
  obtain ⟨e⟩ := nonempty_closure_pair_mulEquiv h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

end Lift

section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem card_eq_eight {T : Subgroup G} (hT : Nonempty (↥T ≃* QuaternionGroup 2)) :
    Nat.card T = 8 := by
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem isPGroup_of_q8 {T : Subgroup G} (hT : Nonempty (↥T ≃* QuaternionGroup 2)) :
    IsPGroup 2 T :=
  IsPGroup.of_card (n := 3) (by rw [card_eq_eight hT]; norm_num)

theorem nonempty_conjSub_mulEquiv {T : Subgroup G} (hT : Nonempty (↥T ≃* QuaternionGroup 2))
    (g : G) : Nonempty (↥(conjSub g T) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := hT
  exact ⟨(Subgroup.equivMapOfInjective T _ (MulAut.conj g).injective).symm.trans e⟩

theorem mem_RSet_self {T : Subgroup G} (hT : T ∈ Ω) (hT8 : Nonempty (↥T ≃* QuaternionGroup 2)) :
    T ∈ RSet Ω :=
  mem_RSet_iff.mpr ⟨T, hT, le_rfl, isPGroup_of_q8 hT8, fun _ h₁ _ h₂ => le_antisymm h₁ h₂⟩

theorem eq_of_mem_RSet_le (hΩ : ∀ T ∈ Ω, Nonempty (↥T ≃* QuaternionGroup 2)) {R J : Subgroup G}
    (hR : R ∈ RSet Ω) (hRJ : R ≤ J) (hJ : Nonempty (↥J ≃* QuaternionGroup 2)) : R = J := by
  obtain ⟨J', hJ', hRJ', -, hmax⟩ := mem_RSet_iff.mp hR
  have h1 : J' = R := hmax J' le_rfl (isPGroup_of_q8 (hΩ J' hJ')) hRJ'
  refine Subgroup.eq_of_le_of_card_ge hRJ ?_
  rw [← h1, card_eq_eight (hΩ J' hJ'), card_eq_eight hJ]

theorem card_of_mem_RSet (hΩ : ∀ T ∈ Ω, Nonempty (↥T ≃* QuaternionGroup 2)) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : Nat.card R = 8 := by
  obtain ⟨J', hJ', hRJ', -, hmax⟩ := mem_RSet_iff.mp hR
  rw [← hmax J' le_rfl (isPGroup_of_q8 (hΩ J' hJ')) hRJ']
  exact card_eq_eight (hΩ J' hJ')

theorem exists_eq_zpowers_of_mem_USet (hΩ : ∀ T ∈ Ω, Nonempty (↥T ≃* QuaternionGroup 2))
    {U : Subgroup G} (hU : U ∈ USet Ω) : ∃ u ∈ U, U = Subgroup.zpowers u ∧ orderOf u = 4 := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  have hR8 := card_of_mem_RSet hΩ hR
  have hU4 : Nat.card U = 4 := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv, hR8] at h1
    rw [Subgroup.relIndex] at hidx
    rw [hidx] at h1
    omega
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  refine ⟨g, g.2, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact (Subgroup.zpowers_le).mpr g.2
  · rw [Subgroup.orderOf_coe, ← hU4]
    exact orderOf_eq_card_of_forall_mem_zpowers hg

theorem zpowers_mem_USet {J : Subgroup G} (hJ : J ∈ Ω) (hJ8 : Nonempty (↥J ≃* QuaternionGroup 2))
    {u : G} (hu : u ∈ J) (hu4 : orderOf u = 4) : Subgroup.zpowers u ∈ USet Ω := by
  refine ⟨J, mem_RSet_self hJ hJ8, (Subgroup.zpowers_le).mpr hu, inferInstance, ?_⟩
  have h1 := Subgroup.card_mul_index ((Subgroup.zpowers u).subgroupOf J)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).mpr hu)).toEquiv,
    Nat.card_zpowers, hu4, card_eq_eight hJ8] at h1
  rw [Subgroup.relIndex]
  omega

theorem le_normalizer_of_mem_omegaNbr (hΩ : ∀ T ∈ Ω, Nonempty (↥T ≃* QuaternionGroup 2))
    {K J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) : J ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hJΩ, -, R, hR, hRJ, hRN⟩ := hJ
  rwa [← eq_of_mem_RSet_le hΩ hR hRJ (hΩ J hJΩ)]

theorem mem_omegaNbr_of_le {K J : Subgroup G} (hJ : J ∈ Ω)
    (hJ8 : Nonempty (↥J ≃* QuaternionGroup 2)) (hne : J ≠ K)
    (hN : J ≤ Subgroup.normalizer (K : Set G)) : J ∈ omegaNbr Ω K :=
  ⟨hJ, hne, J, mem_RSet_self hJ hJ8, le_rfl, hN⟩

theorem orderOf_conj_inv_mul (n u : G) : orderOf (n⁻¹ * u * n) = orderOf u := by
  have h := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) u
  rwa [MulAut.conj_apply, inv_inv] at h

theorem mul_self_eq_of_orderOf_four {T : Subgroup G} {z u : G} (hz : IsUniqueInvolution T z)
    (hu : u ∈ T) (hu4 : orderOf u = 4) : u * u = z := by
  have h4 : u ^ 4 = 1 := hu4 ▸ pow_orderOf_eq_one u
  have h1 : u * u ≠ 1 := by
    intro h
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hu4] at this
    norm_num at this
  have h2 : u * u * (u * u) = 1 := by
    calc u * u * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  exact (hz.unique _ (T.mul_mem hu hu) h2).resolve_left h1

end Members

section Class

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_le_normalizer {Q S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (Q : Set G)) (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) {u : G}
    (hu : u ∈ Subgroup.normalizer (Q : Set G)) {k : ℕ} (hk : orderOf u = 2 ^ k) :
    ∃ n ∈ Subgroup.normalizer (Q : Set G), n⁻¹ * u * n ∈ S := by
  set H := Subgroup.normalizer (Q : Set G)
  have hP2 : IsPGroup 2 (S.subgroupOf H) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hPi : ¬ 2 ∣ (S.subgroupOf H).index := by
    intro h2
    apply hSi
    have := Subgroup.relIndex_mul_index hSN
    rw [Subgroup.relIndex] at this
    rw [← this]
    exact Dvd.dvd.mul_right h2 _
  have hz : IsPGroup 2 (Subgroup.zpowers (⟨u, hu⟩ : H)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hP2 hPi hz
  have h1 := hg _ (Subgroup.mem_zpowers _)
  exact ⟨g, g.2, Subgroup.mem_subgroupOf.mp h1⟩

theorem aEmpty_conjClass_of_sylow {Q S : Subgroup G} {z : G}
    (hQ : Nonempty (↥Q ≃* QuaternionGroup 2)) (hz : IsUniqueInvolution Q z)
    (hS : ∀ u ∈ Subgroup.normalizer (Q : Set G), orderOf u = 4 →
      ∃ n ∈ Subgroup.normalizer (Q : Set G), n⁻¹ * u * n ∈ S)
    (hC : ∀ c : G, c * z = z * c → c ∈ Subgroup.normalizer (Q : Set G))
    (hW : ∀ u ∈ S, orderOf u = 4 → ∃ x : G, x * z * x⁻¹ = u * u ∧
      (u ∈ conjSub x Q → conjSub x Q ≠ Q → ¬ conjSub x Q ≤ Subgroup.normalizer (Q : Set G) →
        ∃ g ∈ pairNormalizers Q (conjSub x Q) z (u * u), conjSub g Q = conjSub x Q)) :
    AEmpty (CoreAssembly.conjClass Q) Q := by
  intro J hJ hJn zK zJ hzK hzJ
  rw [hzK.eq hz]
  have hfam : ∀ T ∈ CoreAssembly.conjClass Q, Nonempty (↥T ≃* QuaternionGroup 2) := by
    rintro _ ⟨g, rfl⟩
    exact nonempty_conjSub_mulEquiv hQ g
  obtain ⟨hJΩ, hJne, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨y, rfl⟩ : ∃ y, conjSub y Q = J := hJΩ
  obtain ⟨u, huU, rfl, hu4⟩ := exists_eq_zpowers_of_mem_USet hfam hU
  have huJ : u ∈ conjSub y Q := hUJ huU
  have huN : u ∈ Subgroup.normalizer (Q : Set G) := hUN huU
  obtain ⟨n, hn, hnS⟩ := hS u huN hu4
  have hnQ : conjSub n Q = Q := mem_normalizer_iff_conjSub_eq.mp hn
  have hn'Q : conjSub n⁻¹ Q = Q := by
    calc conjSub n⁻¹ Q = conjSub n⁻¹ (conjSub n Q) := by rw [hnQ]
      _ = Q := conjSub_inv_conjSub n Q
  have hu'4 : orderOf (n⁻¹ * u * n) = 4 := by rw [orderOf_conj_inv_mul, hu4]
  obtain ⟨x, hxz, hx⟩ := hW _ hnS hu'4
  set J' := conjSub (n⁻¹ * y) Q with hJ'
  have hJJ' : conjSub n J' = conjSub y Q := by
    rw [hJ', conjSub_mul, conjSub_conjSub_inv]
  have hu'J' : n⁻¹ * u * n ∈ J' := by
    have h1 := conj_mem_conjSub (n := n⁻¹) huJ
    rw [inv_inv, ← conjSub_mul] at h1
    exact h1
  have hzJ' : IsUniqueInvolution J' ((n⁻¹ * y) * z * (n⁻¹ * y)⁻¹) := hz.conj _
  have hsq' := mul_self_eq_of_orderOf_four hzJ' hu'J' hu'4
  have hxJ' : conjSub x Q = J' := by
    have hc : ((n⁻¹ * y)⁻¹ * x) * z = z * ((n⁻¹ * y)⁻¹ * x) := by
      have e1 : x * z * x⁻¹ = (n⁻¹ * y) * z * (n⁻¹ * y)⁻¹ := hxz.trans hsq'
      calc (n⁻¹ * y)⁻¹ * x * z = (n⁻¹ * y)⁻¹ * (x * z * x⁻¹) * x := by group
        _ = (n⁻¹ * y)⁻¹ * ((n⁻¹ * y) * z * (n⁻¹ * y)⁻¹) * x := by rw [e1]
        _ = z * ((n⁻¹ * y)⁻¹ * x) := by group
    have hcQ := mem_normalizer_iff_conjSub_eq.mp (hC _ hc)
    calc conjSub x Q = conjSub (n⁻¹ * y) (conjSub ((n⁻¹ * y)⁻¹ * x) Q) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
      _ = J' := by rw [hcQ]
  rw [hxJ'] at hx
  have hne : J' ≠ Q := by
    intro h
    apply hJne
    rw [← hJJ', h, hnQ]
  have hnN : ¬ J' ≤ Subgroup.normalizer (Q : Set G) := by
    intro h
    apply hJn
    refine mem_omegaNbr_of_le ⟨y, rfl⟩ (hfam _ ⟨y, rfl⟩) hJne fun w hw => ?_
    rw [← hJJ', mem_conjSub_iff] at hw
    have h1 := h hw
    rw [← hnQ, mem_normalizer_conjSub_iff]
    exact h1
  obtain ⟨g₀, hg₀, hg₀Q⟩ := hx hu'J' hne hnN
  refine ⟨n * g₀ * n⁻¹, ?_, ?_⟩
  · have h1 : n * g₀ * n⁻¹ ∈ conjSub n (pairNormalizers Q J' z (n⁻¹ * u * n * (n⁻¹ * u * n))) :=
      conj_mem_conjSub hg₀
    rw [conjSub_pairNormalizers, hnQ, hJJ'] at h1
    have e1 : n * z * n⁻¹ = z := by
      have := hz.conj n
      rw [hnQ] at this
      exact this.eq hz
    have e2 : n * (n⁻¹ * u * n * (n⁻¹ * u * n)) * n⁻¹ = zJ := by
      rw [← mul_self_eq_of_orderOf_four hzJ huJ hu4]
      group
    rwa [e1, e2] at h1
  · rw [conjSub_mul, conjSub_mul, hn'Q, hg₀Q, hJJ']

end Class

section Inspect

variable {G : Type} [Group G] [Finite G]

abbrev q8Fam (G : Type) [Group G] : Set (Subgroup G) :=
  {T | Nonempty (↥T ≃* QuaternionGroup 2)}

theorem conjInvariant_q8Fam : ConjInvariant (q8Fam G) :=
  fun g T hT => nonempty_conjSub_mulEquiv hT g

theorem mem_of_mul_closed {T X : Set G} (h1 : (1 : G) ∈ T) (hX : ∀ x ∈ T, ∀ s ∈ X, x * s ∈ T)
    (hgen : Subgroup.closure X = ⊤) (g : G) : g ∈ T := by
  have hpow : ∀ s : G, (∀ x ∈ T, x * s ∈ T) → ∀ k : ℕ, ∀ x ∈ T, x * s ^ k ∈ T := by
    intro s hs k
    induction k with
    | zero => simp
    | succ k ih => exact fun x hx => by rw [pow_succ, ← mul_assoc]; exact hs _ (ih x hx)
  have key : ∀ g ∈ Subgroup.closure X, ∀ x ∈ T, x * g ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact fun x hx => hX x hx s hs
    | one => simp
    | mul a b _ _ ha hb => exact fun x hx => by rw [← mul_assoc]; exact hb _ (ha x hx)
    | inv a _ ha =>
      intro x hx
      have h := hpow a ha (orderOf a - 1) x hx
      have he : a ^ (orderOf a - 1) = a⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos a),
          pow_orderOf_eq_one]
      rwa [he] at h
  have := key g (hgen ▸ Subgroup.mem_top g) 1 h1
  rwa [one_mul] at this

theorem aStar_vStar_of_edges {Q₁ Q₂ : Subgroup G} {z : G} (h₁ : Q₁ ∈ q8Fam G)
    (h₂ : Q₂ ∈ q8Fam G) (hz₁ : IsUniqueInvolution Q₁ z) (hz₂ : IsUniqueInvolution Q₂ z)
    (hnc : ∀ g : G, conjSub g Q₁ ≠ Q₂)
    (hcls : ∀ T ∈ q8Fam G, ∃ g : G, T = conjSub g Q₁ ∨ T = conjSub g Q₂)
    (hΩ : ∀ T ∈ q8Fam G, T ≤ Subgroup.normalizer (Q₁ : Set G) →
      T ≤ Subgroup.normalizer (Q₂ : Set G) → T = Q₁ ∨ T = Q₂)
    {E : Set G}
    (hE : ∀ e ∈ E, (∃ u ∈ conjSub e Q₂, orderOf u = 4 ∧ u ∈ Subgroup.normalizer (Q₁ : Set G)) ∧
      ¬ conjSub e Q₂ ≤ Subgroup.normalizer (Q₁ : Set G))
    (hgen : Subgroup.closure (E ∪ (Subgroup.normalizer (Q₁ : Set G) : Set G) ∪
      (Subgroup.normalizer (Q₂ : Set G) : Set G)) = ⊤) :
    ∀ K ∈ q8Fam G, aStar (q8Fam G) K = q8Fam G ∧ vStar (q8Fam G) K = q8Fam G := by
  have hinv : ConjInvariant (q8Fam G) := conjInvariant_q8Fam
  have hfam : ∀ T ∈ q8Fam G, Nonempty (↥T ≃* QuaternionGroup 2) := fun _ hT => hT
  have hne : ∀ g : G, conjSub g Q₁ ≠ conjSub g Q₂ := fun g h =>
    hnc 1 (by rw [conjSub_one]; exact (conjSub_inj g).mp h)
  have htw : ∀ g : G, aGraphAdj (q8Fam G) (conjSub g Q₁) (conjSub g Q₂) := fun g =>
    ⟨hinv g Q₂ h₂, Or.inr (Or.inr ⟨⟨hinv g Q₂ h₂, g * z * g⁻¹, hz₁.conj g, hz₂.conj g⟩,
      (hne g).symm⟩)⟩
  have hA : ∀ e ∈ E, conjSub e Q₂ ∈ aSet (q8Fam G) Q₁ := by
    intro e he
    obtain ⟨⟨u, huJ, hu4, huN⟩, hnN⟩ := hE e he
    have hJ : conjSub e Q₂ ∈ q8Fam G := hinv e Q₂ h₂
    refine ⟨z, e * z * e⁻¹, ⟨hJ, ?_, Subgroup.zpowers u, zpowers_mem_USet hJ hJ huJ hu4,
      (Subgroup.zpowers_le).mpr huJ, (Subgroup.zpowers_le).mpr huN⟩, ?_, hz₁, hz₂.conj e, ?_⟩
    · intro heq
      apply hnc e⁻¹
      rw [← heq, conjSub_inv_conjSub]
    · exact fun hn => hnN (le_normalizer_of_mem_omegaNbr hfam hn)
    · intro g _ hg
      apply hnc (e⁻¹ * g)
      rw [conjSub_mul, hg, conjSub_inv_conjSub]
  set T : Set G := {x | conjSub x Q₁ ∈ aStar (q8Fam G) Q₁} with hT
  have hT2 : ∀ x ∈ T, conjSub x Q₂ ∈ aStar (q8Fam G) Q₁ := fun x hx => hx.tail (htw x)
  have hT2' : ∀ x, conjSub x Q₂ ∈ aStar (q8Fam G) Q₁ → x ∈ T := fun x hx =>
    hx.tail (aGraphAdj_symm (hinv x Q₁ h₁) (htw x))
  have h1T : (1 : G) ∈ T := by
    show conjSub 1 Q₁ ∈ aStar (q8Fam G) Q₁
    rw [conjSub_one]
    exact Relation.ReflTransGen.refl
  have hTall : ∀ x : G, x ∈ T := by
    refine mem_of_mul_closed h1T ?_ hgen
    rintro x hx s ((hs | hs) | hs)
    · apply hT2'
      have h1 := aSet_conj hinv (hA s hs) x
      rw [← conjSub_mul] at h1
      exact hx.tail ⟨hinv _ Q₂ h₂, Or.inl h1⟩
    · show conjSub (x * s) Q₁ ∈ aStar (q8Fam G) Q₁
      rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hs]
      exact hx
    · apply hT2'
      rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hs]
      exact hT2 x hx
  have hall : ∀ J ∈ q8Fam G, J ∈ aStar (q8Fam G) Q₁ := by
    intro J hJ
    obtain ⟨g, rfl | rfl⟩ := hcls J hJ
    · exact hTall g
    · exact hT2 g (hTall g)
  have hOV : ∀ K ∈ q8Fam G, omegaOfSet (q8Fam G) (twinSet (q8Fam G) K) = ∅ := by
    intro K hK
    obtain ⟨g, hg⟩ := hcls K hK
    have htw1 : conjSub g Q₁ ∈ twinSet (q8Fam G) K := by
      rcases hg with rfl | rfl
      · exact ⟨hinv g Q₁ h₁, g * z * g⁻¹, hz₁.conj g, hz₁.conj g⟩
      · exact ⟨hinv g Q₁ h₁, g * z * g⁻¹, hz₂.conj g, hz₁.conj g⟩
    have htw2 : conjSub g Q₂ ∈ twinSet (q8Fam G) K := by
      rcases hg with rfl | rfl
      · exact ⟨hinv g Q₂ h₂, g * z * g⁻¹, hz₁.conj g, hz₂.conj g⟩
      · exact ⟨hinv g Q₂ h₂, g * z * g⁻¹, hz₂.conj g, hz₂.conj g⟩
    refine Set.eq_empty_of_forall_notMem fun L hL => ?_
    have hL1 := omegaNbr_conj hinv (hL.2 _ htw1) g⁻¹
    have hL2 := omegaNbr_conj hinv (hL.2 _ htw2) g⁻¹
    rw [conjSub_inv_conjSub] at hL1 hL2
    rcases hΩ _ hL1.1 (le_normalizer_of_mem_omegaNbr hfam hL1)
        (le_normalizer_of_mem_omegaNbr hfam hL2) with h | h
    · exact hL1.2.1 h
    · exact hL2.2.1 h
  intro K hK
  refine ⟨Set.Subset.antisymm (fun J hJ => (mem_aStar_symm hK hJ).1) fun J hJ => ?_, ?_⟩
  · exact (mem_aStar_symm h₁ (hall K hK)).2.trans (hall J hJ)
  · ext J
    refine ⟨fun hJ => hJ.1, fun hJ => ⟨hJ, ?_⟩⟩
    rw [hOV K hK, hOV J hJ]

theorem thm3RConclG_of_aStar_vStar {Φ : Set (Subgroup G)} {K : Subgroup G}
    (hA : aStar Φ K = Φ) (hV : vStar Φ K = Φ)
    (hrow : Frame.FrameAEmptyPf.Thm3A.Thm3RowsG Φ (omegaGen Φ)) :
    Frame.FrameAEmptyPf.Thm3A.Thm3RConclG Φ K :=
  ⟨⟨hA.trans hV.symm, fun _ hL hLV => (hLV (by rw [hV]; exact hL)).elim⟩, by rw [hA]; exact hrow⟩

end Inspect

section Transport

variable {Y M : Type} [Group Y] [Finite Y] [Group M] [Finite M]

theorem map_mem_q8Fam (ψ : M ≃* Y) {T : Subgroup M} (hT : T ∈ q8Fam M) :
    T.map ψ.toMonoidHom ∈ q8Fam Y := by
  obtain ⟨e⟩ := hT
  exact ⟨(Subgroup.equivMapOfInjective T _ ψ.injective).symm.trans e⟩

theorem map_symm_map_eq (θ : Y ≃* M) (T : Subgroup M) :
    (T.map θ.symm.toMonoidHom).map θ.toMonoidHom = T :=
  Frame.QTransport.map_symm_map θ T

theorem map_map_symm_eq (θ : Y ≃* M) (T : Subgroup Y) :
    (T.map θ.toMonoidHom).map θ.symm.toMonoidHom = T :=
  Frame.QTransport.map_map_symm θ T

theorem aStar_vStar_of_edges_equiv (θ : Y ≃* M) {Q₁ Q₂ : Subgroup M} {z : M} (h₁ : Q₁ ∈ q8Fam M)
    (h₂ : Q₂ ∈ q8Fam M) (hz₁ : IsUniqueInvolution Q₁ z) (hz₂ : IsUniqueInvolution Q₂ z)
    (hnc : ∀ g : M, conjSub g Q₁ ≠ Q₂)
    (hcls : ∀ T ∈ q8Fam M, ∃ g : M, T = conjSub g Q₁ ∨ T = conjSub g Q₂)
    (hΩ : ∀ T ∈ q8Fam M, T ≤ Subgroup.normalizer (Q₁ : Set M) →
      T ≤ Subgroup.normalizer (Q₂ : Set M) → T = Q₁ ∨ T = Q₂)
    {E : Set M}
    (hE : ∀ e ∈ E, (∃ u ∈ conjSub e Q₂, orderOf u = 4 ∧ u ∈ Subgroup.normalizer (Q₁ : Set M)) ∧
      ¬ conjSub e Q₂ ≤ Subgroup.normalizer (Q₁ : Set M))
    (hgen : Subgroup.closure (E ∪ (Subgroup.normalizer (Q₁ : Set M) : Set M) ∪
      (Subgroup.normalizer (Q₂ : Set M) : Set M)) = ⊤) :
    ∀ K ∈ q8Fam Y, aStar (q8Fam Y) K = q8Fam Y ∧ vStar (q8Fam Y) K = q8Fam Y := by
  set ψ : M ≃* Y := θ.symm with hψ
  have hinj : ∀ (F : Subgroup M), ∀ x ∈ F, ψ.toMonoidHom x = 1 → x = 1 :=
    fun _ x _ hx => ψ.injective (hx.trans (map_one ψ).symm)
  have hN : ∀ T : Subgroup M, Subgroup.normalizer ((T.map ψ.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (T : Set M)).map ψ.toMonoidHom := fun T =>
    (Subgroup.map_equiv_normalizer_eq T ψ).symm
  have hcj : ∀ (g : M) (T : Subgroup M),
      (conjSub g T).map ψ.toMonoidHom = conjSub (ψ g) (T.map ψ.toMonoidHom) := fun g T =>
    AscQuot.map_conjSub ψ.toMonoidHom g T
  have hback : ∀ T : Subgroup Y, (T.map θ.toMonoidHom).map ψ.toMonoidHom = T :=
    fun T => map_map_symm_eq θ T
  have hfwd : ∀ T : Subgroup M, (T.map ψ.toMonoidHom).map θ.toMonoidHom = T :=
    fun T => map_symm_map_eq θ T
  refine aStar_vStar_of_edges (Q₁ := Q₁.map ψ.toMonoidHom) (Q₂ := Q₂.map ψ.toMonoidHom)
    (z := ψ z) (E := ψ '' E) (map_mem_q8Fam ψ h₁) (map_mem_q8Fam ψ h₂)
    (isUniqueInvolution_map_of_injOn _ (hinj Q₁) hz₁)
    (isUniqueInvolution_map_of_injOn _ (hinj Q₂) hz₂) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    apply hnc (θ g)
    have h1 := congrArg (Subgroup.map θ.toMonoidHom) hg
    rwa [AscQuot.map_conjSub, hfwd, hfwd] at h1
  · intro T hT
    obtain ⟨g, hg | hg⟩ := hcls _ (map_mem_q8Fam θ hT)
    · refine ⟨ψ g, Or.inl ?_⟩
      rw [← hcj, ← hg, hback]
    · refine ⟨ψ g, Or.inr ?_⟩
      rw [← hcj, ← hg, hback]
  · intro T hT hT1 hT2
    have hle : ∀ (Q : Subgroup M), T ≤ Subgroup.normalizer
        ((Q.map ψ.toMonoidHom : Subgroup Y) : Set Y) →
        T.map θ.toMonoidHom ≤ Subgroup.normalizer (Q : Set M) := by
      intro Q hQ
      rw [hN] at hQ
      have := Subgroup.map_mono (f := θ.toMonoidHom) hQ
      rwa [hfwd] at this
    rcases hΩ _ (map_mem_q8Fam θ hT) (hle Q₁ hT1) (hle Q₂ hT2) with h | h
    · left
      rw [← hback T, h]
    · right
      rw [← hback T, h]
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨⟨u, hu, hu4, huN⟩, hnN⟩ := hE e he
    refine ⟨⟨ψ u, ?_, ?_, ?_⟩, ?_⟩
    · rw [← hcj]
      exact Subgroup.mem_map_of_mem _ hu
    · rw [MulEquiv.orderOf_eq]
      exact hu4
    · rw [hN]
      exact Subgroup.mem_map_of_mem _ huN
    · intro hle
      apply hnN
      rw [← hcj, hN] at hle
      have := Subgroup.map_mono (f := θ.toMonoidHom) hle
      rwa [hfwd, hfwd] at this
  · have himg : ψ '' E ∪ ((Subgroup.normalizer
        ((Q₁.map ψ.toMonoidHom : Subgroup Y) : Set Y)) : Set Y) ∪
        ((Subgroup.normalizer ((Q₂.map ψ.toMonoidHom : Subgroup Y) : Set Y)) : Set Y) =
        ψ.toMonoidHom '' (E ∪ (Subgroup.normalizer (Q₁ : Set M) : Set M) ∪
          (Subgroup.normalizer (Q₂ : Set M) : Set M)) := by
      rw [Set.image_union, Set.image_union, hN, hN, Subgroup.coe_map, Subgroup.coe_map]
      rfl
    rw [himg, ← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective _ ψ.surjective]

theorem nonempty_q8_of_typeRHyp {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : Frame.FrameAEmptyPf.TypeRHyp (CoreAssembly.conjClass K)) {z : X}
    (hz : IsUniqueInvolution K z)
    (hC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥) :
    Nonempty (↥K ≃* QuaternionGroup 2) := by
  have hKm : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hsub := QuaternionBridge.CentQ.isSubnormal_centralizer_gen hK.hyp hKm hz
  have hle := Balance.oddCoreIn_le_of_isSubnormal hsub
  have hCin : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥ := by
    show (classicalInvolutionOddCore _).map _ = ⊥
    rw [hC, Subgroup.map_bot]
  rw [hCin, le_bot_iff] at hle
  have hO : classicalInvolutionOddCore ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hle
  have h2 : IsPGroup 2 ↥K := (hK.twoGroup K hKm).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  have hsyl : IsSylow2In K K := ⟨le_rfl, h2, fun _ h₁ _ h₃ => le_antisymm h₁ h₃⟩
  exact hK.sylow K hKm K hsyl

theorem conjClass_conjSub (g : M) (Q : Subgroup M) :
    CoreAssembly.conjClass (conjSub g Q) = CoreAssembly.conjClass Q := by
  ext T
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, conjSub_mul h g Q⟩
  · rintro ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    show conjSub (h * g⁻¹) (conjSub g Q) = conjSub h Q
    rw [conjSub_mul, conjSub_inv_conjSub]

theorem aEmpty_q8Fam_of_classes {Q₁ Q₂ : Subgroup M}
    (hcls : ∀ T ∈ q8Fam M, ∃ g : M, T = conjSub g Q₁ ∨ T = conjSub g Q₂)
    (h₁ : AEmpty (CoreAssembly.conjClass Q₁) Q₁) (h₂ : AEmpty (CoreAssembly.conjClass Q₂) Q₂) :
    ∀ T ∈ q8Fam M, AEmpty (CoreAssembly.conjClass T) T := by
  intro T hT
  obtain ⟨g, rfl | rfl⟩ := hcls T hT
  · rw [conjClass_conjSub]
    exact aEmpty_conj (TL4.conjInvariant_conjClass Q₁) h₁ g
  · rw [conjClass_conjSub]
    exact aEmpty_conj (TL4.conjInvariant_conjClass Q₂) h₂ g

theorem aEmpty_of_model {X : Type} [Group X] [Finite X] (θ : X ≃* M) {K : Subgroup X}
    (hK : Frame.FrameAEmptyPf.TypeRHyp (CoreAssembly.conjClass K))
    (hK8 : Nonempty (↥K ≃* QuaternionGroup 2))
    (hM : ∀ T ∈ q8Fam M, AEmpty (CoreAssembly.conjClass T) T) :
    AEmpty (CoreAssembly.conjClass K) K := by
  have himg : Frame.QTransport.mapFam θ (CoreAssembly.conjClass K) =
      CoreAssembly.conjClass (K.map θ.toMonoidHom) := by
    ext T
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨θ g, (AscQuot.map_conjSub θ.toMonoidHom g K).symm⟩
    · rintro ⟨m, rfl⟩
      refine ⟨conjSub (θ.symm m) K, ⟨θ.symm m, rfl⟩, ?_⟩
      show (conjSub (θ.symm m) K).map θ.toMonoidHom = _
      rw [AscQuot.map_conjSub]
      simp
  have h2 : ∀ T ∈ CoreAssembly.conjClass K,
      Subgroup.closure {x : X | x ∈ T ∧ IsPGroup 2 (Subgroup.zpowers x)} = T := by
    rintro _ ⟨g, rfl⟩
    have hp : IsPGroup 2 (conjSub g K) := isPGroup_of_q8 (nonempty_conjSub_mulEquiv hK8 g)
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
    · intro x hx
      refine Subgroup.subset_closure ⟨hx, ?_⟩
      exact hp.to_le ((Subgroup.zpowers_le).mpr hx)
  have hinv : ConjInvariant ((fun T : Subgroup X => T.map θ.toMonoidHom) ''
      CoreAssembly.conjClass K) := by
    have : ((fun T : Subgroup X => T.map θ.toMonoidHom) '' CoreAssembly.conjClass K) =
        CoreAssembly.conjClass (K.map θ.toMonoidHom) := himg
    rw [this]
    exact TL4.conjInvariant_conjClass _
  have hΔ := TL4.Vtx.hypOmegaGen_map_of_inj θ.toMonoidHom θ.injective hK.hyp h2 hinv
  refine Frame.QTransport.aEmpty_of_mapFam_sub θ hΔ le_rfl ?_
  have : ((fun T : Subgroup X => T.map θ.toMonoidHom) '' CoreAssembly.conjClass K) =
      CoreAssembly.conjClass (K.map θ.toMonoidHom) := himg
  rw [this]
  exact hM _ (map_mem_q8Fam θ.symm.symm hK8)

end Transport

section Sound

open Certificates.S7Q8

variable {G : Type} [Group G] [Finite G] [DecidableEq G] {i j : G}

theorem isUniqueInvolution_closure_pair (h : Q8Rel i j) :
    IsUniqueInvolution (Subgroup.closure ({i, j} : Set G)) (i * i) where
  mem := Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert i _))
    (Subgroup.subset_closure (Set.mem_insert i _))
  ne_one := by rw [← sq]; exact h.2.1
  sq := by
    calc i * i * (i * i) = i ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h.1
  unique := by
    intro y hy hy2
    rw [← range_q8Lift h] at hy
    obtain ⟨q, rfl⟩ := hy
    have hq : q * q = 1 := q8Lift_injective h (by rw [map_mul, hy2, map_one])
    have hQ8 : ∀ q : QuaternionGroup 2, q * q = 1 → q = 1 ∨ q = QuaternionGroup.a 2 := by
      decide
    rcases hQ8 q hq with rfl | rfl
    · exact Or.inl (map_one _)
    · right
      rw [q8Lift_a]
      exact sq i

theorem inSpanB_iff (h : Q8Rel i j) {x : G} :
    inSpanB i j x = true ↔ x ∈ Subgroup.closure ({i, j} : Set G) := by
  rw [inSpanB, decide_eq_true_iff, mem_closure_pair_iff h]

theorem q8Rel_conj (h : Q8Rel i j) (x : G) : Q8Rel (x * i * x⁻¹) (x * j * x⁻¹) := by
  have h1 := Q8Rel.map (MulAut.conj x).toMonoidHom h (fun h1 => h.2.1 (by
    have := congrArg (fun t => x⁻¹ * t * x) h1
    simpa [MulAut.conj_apply, mul_assoc] using this))
  simpa [MulAut.conj_apply] using h1

theorem closure_pair_le {Q : Subgroup G} {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    Subgroup.closure ({a, b} : Set G) ≤ Q := by
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · rw [hx]; exact ha
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hb

theorem closure_pair_eq_of_mem {a b : G} (hab : Q8Rel a b) (h : Q8Rel i j)
    (ha : a ∈ Subgroup.closure ({i, j} : Set G)) (hb : b ∈ Subgroup.closure ({i, j} : Set G)) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.closure ({i, j} : Set G) :=
  Subgroup.eq_of_le_of_card_ge (closure_pair_le ha hb)
    (by rw [card_closure_pair h, card_closure_pair hab])

theorem normB_iff (h : Q8Rel i j) {g : G} :
    normB i j g = true ↔ g ∈ Subgroup.normalizer ((Subgroup.closure ({i, j} : Set G)) : Set G) := by
  have hi : i ∈ Subgroup.closure ({i, j} : Set G) := Subgroup.subset_closure (Set.mem_insert i _)
  have hj : j ∈ Subgroup.closure ({i, j} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem i (Set.mem_singleton j))
  rw [normB, Bool.and_eq_true, inSpanB_iff h, inSpanB_iff h, mem_normalizer_iff_conjSub_eq,
    conjSub_closure_pair]
  constructor
  · rintro ⟨h1, h2⟩
    exact closure_pair_eq_of_mem (q8Rel_conj h g) h h1 h2
  · intro he
    rw [← he]
    exact ⟨Subgroup.subset_closure (Set.mem_insert _ _),
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

theorem ord4B_iff {u : G} : ord4B u = true ↔ orderOf u = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ord4B, Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨h4, h2⟩
    refine orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, sq]; exact h2) ?_
    rw [show 2 ^ (1 + 1) = 4 by rfl]
    simpa [pow_succ, mul_assoc] using h4
  · intro h
    have h4 : u ^ 4 = 1 := h ▸ pow_orderOf_eq_one u
    refine ⟨by simpa [pow_succ, mul_assoc] using h4, fun h2 => ?_⟩
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    rw [h] at this
    norm_num at this

theorem mem_normalizer_closure_of_conj_mem {X : Set G} {a : G}
    (h : ∀ x ∈ X, a * x * a⁻¹ ∈ Subgroup.closure X) :
    a ∈ Subgroup.normalizer ((Subgroup.closure X : Subgroup G) : Set G) := by
  have hle : conjSub a (Subgroup.closure X) ≤ Subgroup.closure X := by
    unfold conjSub
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  refine mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle ?_)
  unfold conjSub
  rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]

theorem mem_normalizer_of_normVB {z w a : G} (h : normVB z w a = true) :
    a ∈ Subgroup.normalizer ((Subgroup.closure ({z, w} : Set G) : Subgroup G) : Set G) := by
  have hz : z ∈ Subgroup.closure ({z, w} : Set G) := Subgroup.subset_closure (Set.mem_insert z _)
  have hw : w ∈ Subgroup.closure ({z, w} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem z (Set.mem_singleton w))
  have hlist : ∀ y ∈ [1, z, w, z * w], y ∈ Subgroup.closure ({z, w} : Set G) := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hz
    · exact hw
    · exact Subgroup.mul_mem _ hz hw
  rw [normVB, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
  refine mem_normalizer_closure_of_conj_mem fun x hx => ?_
  rcases hx with rfl | hx
  · exact hlist _ h.1
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hlist _ h.2

theorem classCheck_sound (h : Q8Rel i j) {S X : List G} (hc : classCheck i j S X = true)
    {u : G} (hu : u ∈ S) (hu4 : orderOf u = 4) :
    ∃ x : G, x * (i * i) * x⁻¹ = u * u ∧
      (u ∈ conjSub x (Subgroup.closure ({i, j} : Set G)) →
        conjSub x (Subgroup.closure ({i, j} : Set G)) ≠ Subgroup.closure ({i, j} : Set G) →
        ¬ conjSub x (Subgroup.closure ({i, j} : Set G)) ≤
          Subgroup.normalizer ((Subgroup.closure ({i, j} : Set G)) : Set G) →
        ∃ g ∈ pairNormalizers (Subgroup.closure ({i, j} : Set G))
            (conjSub x (Subgroup.closure ({i, j} : Set G))) (i * i) (u * u),
          conjSub g (Subgroup.closure ({i, j} : Set G)) =
            conjSub x (Subgroup.closure ({i, j} : Set G))) := by
  simp only [classCheck, List.all_eq_true] at hc
  have h1 := hc u hu
  rw [Bool.or_eq_true, Bool.not_eq_true', ord4B_iff.mpr hu4, List.any_eq_true] at h1
  obtain ⟨x, -, hx⟩ := h1.resolve_left (by decide)
  simp only [classStepB, Bool.and_eq_true, decide_eq_true_iff] at hx
  obtain ⟨hxz, hx⟩ := hx
  refine ⟨x, hxz, fun huJ hne hnN => ?_⟩
  set i' := x * i * x⁻¹
  set j' := x * j * x⁻¹
  have h' : Q8Rel i' j' := q8Rel_conj h x
  rw [conjSub_closure_pair] at huJ hne hnN ⊢
  have hb1 : inSpanB i' j' u = true := (inSpanB_iff h').mpr huJ
  have hb2 : (inSpanB i j i' && inSpanB i j j') = false := by
    rw [Bool.eq_false_iff]
    intro hb
    rw [Bool.and_eq_true, inSpanB_iff h, inSpanB_iff h] at hb
    exact hne (closure_pair_eq_of_mem h' h hb.1 hb.2)
  have hb3 : (normB i j i' && normB i j j') = false := by
    rw [Bool.eq_false_iff]
    intro hb
    rw [Bool.and_eq_true, normB_iff h, normB_iff h] at hb
    exact hnN (closure_pair_le hb.1 hb.2)
  rw [hb1, hb2, hb3] at hx
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    Bool.and_eq_true] at hx
  obtain ⟨a, ha, b, hb, ⟨⟨hza, hzb⟩, hgi⟩, hgj⟩ := hx
  have haQ : a ∈ Subgroup.closure ({i, j} : Set G) := (mem_closure_pair_iff h).mpr ha
  have hbJ : b ∈ Subgroup.closure ({i', j'} : Set G) := (mem_closure_pair_iff h').mpr hb
  refine ⟨a * b, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨haQ, mem_normalizer_of_normVB hza⟩)
      (Subgroup.mem_sup_right ⟨hbJ, mem_normalizer_of_normVB hzb⟩)
  · rw [conjSub_closure_pair]
    exact closure_pair_eq_of_mem (q8Rel_conj h (a * b)) h' ((inSpanB_iff h').mp hgi)
      ((inSpanB_iff h').mp hgj)

theorem normAllB_sound (h : Q8Rel i j) {C : List G} (hc : normAllB i j C = true) {c : G}
    (hcC : c ∈ C) : c ∈ Subgroup.normalizer ((Subgroup.closure ({i, j} : Set G)) : Set G) := by
  simp only [normAllB, List.all_eq_true] at hc
  exact (normB_iff h).mp (hc c hcC)

theorem q8InCheck_sound {i₁ j₁ i₂ j₂ : G} (h₁ : Q8Rel i₁ j₁) (h₂ : Q8Rel i₂ j₂) {L : List G}
    (hc : q8InCheck L i₁ j₁ i₂ j₂ = true) {T : Subgroup G}
    (hT : Nonempty (↥T ≃* QuaternionGroup 2)) (hTL : ∀ t ∈ T, t ∈ L) :
    T = Subgroup.closure ({i₁, j₁} : Set G) ∨ T = Subgroup.closure ({i₂, j₂} : Set G) := by
  obtain ⟨e⟩ := hT
  obtain ⟨a, haT, b, hbT, hab, hspan⟩ := exists_q8Pair e
  have hTab : T = Subgroup.closure ({a, b} : Set G) := by
    apply le_antisymm
    · intro t ht
      exact (mem_closure_pair_iff hab).mpr (hspan t ht)
    · exact closure_pair_le haT hbT
  simp only [q8InCheck, List.all_eq_true] at hc
  have h1 := hc a (hTL a haT) b (hTL b hbT)
  rw [q8RelB_eq_true_iff.mpr hab] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at h1
  rw [hTab]
  rcases h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl (closure_pair_eq_of_mem hab h₁ ((inSpanB_iff h₁).mp ha) ((inSpanB_iff h₁).mp hb))
  · exact Or.inr (closure_pair_eq_of_mem hab h₂ ((inSpanB_iff h₂).mp ha) ((inSpanB_iff h₂).mp hb))

theorem edgeB_sound {i₁ j₁ i₂ j₂ : G} (h₁ : Q8Rel i₁ j₁) (h₂ : Q8Rel i₂ j₂) {e : G}
    (hc : edgeB i₁ j₁ i₂ j₂ e = true) :
    (∃ u ∈ conjSub e (Subgroup.closure ({i₂, j₂} : Set G)), orderOf u = 4 ∧
        u ∈ Subgroup.normalizer ((Subgroup.closure ({i₁, j₁} : Set G)) : Set G)) ∧
      ¬ conjSub e (Subgroup.closure ({i₂, j₂} : Set G)) ≤
        Subgroup.normalizer ((Subgroup.closure ({i₁, j₁} : Set G)) : Set G) := by
  have h' := q8Rel_conj h₂ e
  simp only [edgeB, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨u, hu, hu4, huN⟩, hnN⟩ := hc
  rw [conjSub_closure_pair]
  refine ⟨⟨u, (mem_closure_pair_iff h').mpr hu, ord4B_iff.mp hu4, (normB_iff h₁).mp huN⟩, ?_⟩
  intro hle
  have h1 := (normB_iff h₁).mpr (hle (Subgroup.subset_closure (Set.mem_insert _ _)))
  have h2 := (normB_iff h₁).mpr
    (hle (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  rw [h1, h2] at hnN
  exact absurd hnN (by decide)

theorem factB_sound {i₁ j₁ i₂ j₂ : G} (h₁ : Q8Rel i₁ j₁) (h₂ : Q8Rel i₂ j₂) {E fs : List G}
    {g : G} (hc : factB i₁ j₁ i₂ j₂ E g fs = true) :
    g ∈ Subgroup.closure ({x | x ∈ E} ∪
      (Subgroup.normalizer ((Subgroup.closure ({i₁, j₁} : Set G)) : Set G) : Set G) ∪
      (Subgroup.normalizer ((Subgroup.closure ({i₂, j₂} : Set G)) : Set G) : Set G)) := by
  simp only [factB, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, Bool.or_eq_true]
    at hc
  obtain ⟨rfl, hf⟩ := hc
  refine list_prod_mem fun f hf' => ?_
  rcases hf f hf' with ((hE | hE') | hN1) | hN2
  · exact Subgroup.subset_closure (Or.inl (Or.inl hE))
  · rw [← inv_inv f]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl (Or.inl hE')))
  · exact Subgroup.subset_closure (Or.inl (Or.inr ((normB_iff h₁).mp hN1)))
  · exact Subgroup.subset_closure (Or.inr ((normB_iff h₂).mp hN2))

end Sound

section Map

open Certificates.S7Q8

variable {M N : Type*} [Group M] [Group N] [DecidableEq M] [DecidableEq N] {f : M →* N}

theorem decide_mem_map (hf : Function.Injective f) (x : M) (L : List M) :
    decide (f x ∈ L.map f) = decide (x ∈ L) := by
  simp only [List.mem_map_of_injective hf]

theorem inSpanB_map (hf : Function.Injective f) (i j x : M) :
    inSpanB (f i) (f j) (f x) = inSpanB i j x := by
  rw [inSpanB, inSpanB, ← map_q8Span, decide_mem_map hf]

theorem normB_map (hf : Function.Injective f) (i j g : M) :
    normB (f i) (f j) (f g) = normB i j g := by
  rw [normB, normB, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, inSpanB_map hf,
    inSpanB_map hf]

theorem ord4B_map (hf : Function.Injective f) (u : M) : ord4B (f u) = ord4B u := by
  simp only [ord4B, ← map_mul, ← map_one f, hf.eq_iff]

theorem normVB_map (hf : Function.Injective f) (z w a : M) :
    normVB (f z) (f w) (f a) = normVB z w a := by
  have hL : [1, f z, f w, f z * f w] = [1, z, w, z * w].map f := by simp
  rw [normVB, normVB, hL, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    decide_mem_map hf, decide_mem_map hf]

theorem q8RelB_map (hf : Function.Injective f) (i j : M) : q8RelB (f i) (f j) = q8RelB i j := by
  simp only [q8RelB, ← map_pow, ← map_mul, ← map_inv, ← map_one f, hf.eq_iff]

theorem classStepB_map (hf : Function.Injective f) (i j u x : M) :
    classStepB (f i) (f j) (f u) (f x) = classStepB i j u x := by
  simp only [classStepB, ← map_inv, ← map_mul, hf.eq_iff, inSpanB_map hf, normB_map hf,
    normVB_map hf, ← map_q8Span, List.any_map, Function.comp_def, decide_eq_decide]

theorem classCheck_map (hf : Function.Injective f) (i j : M) (S X : List M) :
    classCheck (f i) (f j) (S.map f) (X.map f) = classCheck i j S X := by
  simp only [classCheck, List.all_map, List.any_map, Function.comp_def, ord4B_map hf,
    classStepB_map hf]

theorem normAllB_map (hf : Function.Injective f) (i j : M) (C : List M) :
    normAllB (f i) (f j) (C.map f) = normAllB i j C := by
  simp only [normAllB, List.all_map, Function.comp_def, normB_map hf]

theorem q8InCheck_map (hf : Function.Injective f) (L : List M) (i₁ j₁ i₂ j₂ : M) :
    q8InCheck (L.map f) (f i₁) (f j₁) (f i₂) (f j₂) = q8InCheck L i₁ j₁ i₂ j₂ := by
  simp only [q8InCheck, List.all_map, Function.comp_def, q8RelB_map hf, inSpanB_map hf]

theorem edgeB_map (hf : Function.Injective f) (i₁ j₁ i₂ j₂ e : M) :
    edgeB (f i₁) (f j₁) (f i₂) (f j₂) (f e) = edgeB i₁ j₁ i₂ j₂ e := by
  simp only [edgeB, ← map_inv, ← map_mul, ← map_q8Span, List.any_map, Function.comp_def,
    ord4B_map hf, normB_map hf]

theorem factB_map (hf : Function.Injective f) (i₁ j₁ i₂ j₂ : M) (E : List M) (g : M)
    (fs : List M) :
    factB (f i₁) (f j₁) (f i₂) (f j₂) (E.map f) (f g) (fs.map f) =
      factB i₁ j₁ i₂ j₂ E g fs := by
  simp only [factB, ← map_list_prod, hf.eq_iff, List.all_map, Function.comp_def, ← map_inv,
    decide_mem_map hf, normB_map hf]

end Map

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
