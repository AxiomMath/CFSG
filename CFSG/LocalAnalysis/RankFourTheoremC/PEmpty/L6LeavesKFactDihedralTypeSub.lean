module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralTypeCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralTypeWreath

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType

open Subgroup
open CFSG.Wreathed (Wreath element)

variable {A : Type} [Group A]

@[expose] def baseIn {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) : Subgroup A :=
  ((wreathBaseSub (2 ^ n)).comap (e : ↥S →* Wreath (2 ^ n))).map S.subtype

theorem mem_baseIn {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) {x : A} :
    x ∈ baseIn e ↔ ∃ h : x ∈ S, e ⟨x, h⟩ ∈ wreathBaseSub (2 ^ n) := by
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨z.2, hz⟩
  · rintro ⟨h, hb⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, h⟩, hb, rfl⟩

theorem baseIn_commute {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) {x y : A}
    (hx : x ∈ baseIn e) (hy : y ∈ baseIn e) : x * y = y * x := by
  obtain ⟨hxS, hxb⟩ := (mem_baseIn e).mp hx
  obtain ⟨hyS, hyb⟩ := (mem_baseIn e).mp hy
  have h := wreathBaseSub_comm hxb hyb
  have h2 : e (⟨x, hxS⟩ * ⟨y, hyS⟩) = e (⟨y, hyS⟩ * ⟨x, hxS⟩) := by
    rw [map_mul, map_mul]
    exact h
  exact congrArg Subtype.val (e.injective h2)

theorem baseIn_relIndex {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) :
    (baseIn e).relIndex S = 2 := by
  have hsub : (baseIn e).subgroupOf S =
      (wreathBaseSub (2 ^ n)).comap (e : ↥S →* Wreath (2 ^ n)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨h, hb⟩ := (mem_baseIn e).mp (Subgroup.mem_subgroupOf.mp hz)
      exact hb
    · intro hz
      exact Subgroup.mem_subgroupOf.mpr ((mem_baseIn e).mpr ⟨z.2, hz⟩)
  show ((baseIn e).subgroupOf S).index = 2
  have hsurj : Function.Surjective (e : ↥S →* Wreath (2 ^ n)) := e.surjective
  rw [hsub, Subgroup.index_comap_of_surjective (H := wreathBaseSub (2 ^ n))
    (f := (e : ↥S →* Wreath (2 ^ n))) hsurj, index_wreathBaseSub]

@[expose] def transT1 {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) : Set A :=
  Set.range (fun p : Fin 2 × Fin 2 =>
    ((e.symm (element (2 ^ n) (halfCoord n p.1) (halfCoord n p.2) 0) : ↥S) : A))

@[expose] def transT2 {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) : Set A :=
  Set.range (fun i : Fin 2 =>
    ((e.symm (element (2 ^ n) (halfCoord n i) (halfCoord n i) 0) : ↥S) : A))

theorem card_transT1_le {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) :
    Nat.card (transT1 e) ≤ 4 := by
  unfold transT1
  exact (Finite.card_range_le _).trans (le_of_eq (by simp [Nat.card_eq_fintype_card]))

theorem card_transT2_le {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) :
    Nat.card (transT2 e) ≤ 2 := by
  unfold transT2
  exact (Finite.card_range_le _).trans (le_of_eq (by simp [Nat.card_eq_fintype_card]))

theorem sq_eq_one_of_pow_two {S : Subgroup A} {n : ℕ} (e : ↥S ≃* Wreath (2 ^ n)) {x : A}
    (hxS : x ∈ S) (hx2 : x ^ 2 = 1) : e ⟨x, hxS⟩ ^ 2 = 1 := by
  have hz : (⟨x, hxS⟩ : ↥S) ^ 2 = 1 := Subtype.ext hx2
  rw [← map_pow, hz, map_one]

theorem mem_transT1 {S : Subgroup A} {n : ℕ} (hn : 1 ≤ n) (e : ↥S ≃* Wreath (2 ^ n)) {x : A}
    (hx : x ∈ baseIn e) (hx2 : x ^ 2 = 1) : x ∈ transT1 e := by
  obtain ⟨hxS, hxb⟩ := (mem_baseIn e).mp hx
  obtain ⟨p, hp⟩ := base_two_torsion_mem hn hxb (sq_eq_one_of_pow_two e hxS hx2)
  have hp' : element (2 ^ n) (halfCoord n p.1) (halfCoord n p.2) 0 = e ⟨x, hxS⟩ := hp
  refine ⟨p, ?_⟩
  show ((e.symm (element (2 ^ n) (halfCoord n p.1) (halfCoord n p.2) 0) : ↥S) : A) = x
  rw [hp', MulEquiv.symm_apply_apply]

theorem mem_transT2 {S : Subgroup A} {n : ℕ} (hn : 1 ≤ n) (e : ↥S ≃* Wreath (2 ^ n)) {x t : A}
    (hx : x ∈ baseIn e) (hx2 : x ^ 2 = 1) (htS : t ∈ S) (ht : t ∉ baseIn e)
    (hcomm : x * t = t * x) : x ∈ transT2 e := by
  obtain ⟨hxS, hxb⟩ := (mem_baseIn e).mp hx
  have hw : e ⟨t, htS⟩ ∉ wreathBaseSub (2 ^ n) := fun h => ht ((mem_baseIn e).mpr ⟨htS, h⟩)
  have hzw : (⟨x, hxS⟩ : ↥S) * ⟨t, htS⟩ = ⟨t, htS⟩ * ⟨x, hxS⟩ := Subtype.ext hcomm
  have hcommW : e ⟨x, hxS⟩ * e ⟨t, htS⟩ = e ⟨t, htS⟩ * e ⟨x, hxS⟩ := by
    rw [← map_mul, ← map_mul, hzw]
  obtain ⟨i, hi⟩ := base_commute_two_torsion_mem hn hxb (sq_eq_one_of_pow_two e hxS hx2) hw
    hcommW
  have hi' : element (2 ^ n) (halfCoord n i) (halfCoord n i) 0 = e ⟨x, hxS⟩ := hi
  refine ⟨i, ?_⟩
  show ((e.symm (element (2 ^ n) (halfCoord n i) (halfCoord n i) 0) : ↥S) : A) = x
  rw [hi', MulEquiv.symm_apply_apply]

theorem card_preimage_val_le [Finite A] {R : Subgroup A} (T : Set A) :
    Nat.card (Subtype.val ⁻¹' T : Set R) ≤ Nat.card T := by
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, x.2⟩) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h)

theorem card_le_eight {S : Subgroup A} [Finite A] {n : ℕ} (hS : IsPGroup 2 ↥S) (hn : 1 ≤ n)
    (e : ↥S ≃* Wreath (2 ^ n)) {R : Subgroup A} (hRS : R ≤ S) :
    Nat.card (↥R ⧸ frattini ↥R) ≤ 8 := by
  have hRp : IsPGroup 2 ↥R :=
    hS.of_injective (Subgroup.inclusion hRS) (Subgroup.inclusion_injective hRS)
  have hidx : ((R ⊓ baseIn e).subgroupOf R).index ≤ 2 := by
    show (R ⊓ baseIn e).relIndex R ≤ 2
    rw [Subgroup.inf_relIndex_left]
    have h := Subgroup.relIndex_le_of_le_right hRS
      (show (baseIn e).relIndex S ≠ 0 by rw [baseIn_relIndex]; norm_num)
    rw [baseIn_relIndex] at h
    exact h
  have hcomm : ∀ a ∈ (R ⊓ baseIn e).subgroupOf R, ∀ b ∈ (R ⊓ baseIn e).subgroupOf R,
      a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact baseIn_commute e ((Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).2)
      ((Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).2)
  have hT : ∀ x ∈ (R ⊓ baseIn e).subgroupOf R, x ^ 2 = 1 →
      x ∈ (Subtype.val ⁻¹' transT1 e : Set R) := by
    intro x hx hx2
    have hx2' : (x.1 : A) ^ 2 = 1 := by
      have := congrArg Subtype.val hx2
      simpa using this
    exact mem_transT1 hn e ((Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2) hx2'
  calc Nat.card (↥R ⧸ frattini ↥R)
      ≤ ((R ⊓ baseIn e).subgroupOf R).index * Nat.card (Subtype.val ⁻¹' transT1 e : Set R) :=
        card_frattini_quotient_le hRp _ hcomm _ hT
    _ ≤ 2 * 4 := Nat.mul_le_mul hidx ((card_preimage_val_le _).trans (card_transT1_le e))
    _ = 8 := rfl

theorem card_le_four_of_abelian {S : Subgroup A} [Finite A] {n : ℕ} (hS : IsPGroup 2 ↥S)
    (hn : 1 ≤ n) (e : ↥S ≃* Wreath (2 ^ n)) {R : Subgroup A} (hRS : R ≤ S)
    (hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) : Nat.card (↥R ⧸ frattini ↥R) ≤ 4 := by
  have hRp : IsPGroup 2 ↥R :=
    hS.of_injective (Subgroup.inclusion hRS) (Subgroup.inclusion_injective hRS)
  by_cases hRB : R ≤ baseIn e
  ·
    have hcomm : ∀ a ∈ (⊤ : Subgroup ↥R), ∀ b ∈ (⊤ : Subgroup ↥R), a * b = b * a :=
      fun a _ b _ => Subtype.ext (hab a.1 a.2 b.1 b.2)
    have hT : ∀ x ∈ (⊤ : Subgroup ↥R), x ^ 2 = 1 →
        x ∈ (Subtype.val ⁻¹' transT1 e : Set R) := by
      intro x _ hx2
      have hx2' : (x.1 : A) ^ 2 = 1 := by
        have := congrArg Subtype.val hx2
        simpa using this
      exact mem_transT1 hn e (hRB x.2) hx2'
    calc Nat.card (↥R ⧸ frattini ↥R)
        ≤ (⊤ : Subgroup ↥R).index * Nat.card (Subtype.val ⁻¹' transT1 e : Set R) :=
          card_frattini_quotient_le hRp _ hcomm _ hT
      _ ≤ 1 * 4 := by
          rw [Subgroup.index_top]
          exact Nat.mul_le_mul_left _ ((card_preimage_val_le _).trans (card_transT1_le e))
      _ = 4 := rfl
  ·
    obtain ⟨t, htR, htB⟩ := SetLike.not_le_iff_exists.mp hRB
    have hidx : ((R ⊓ baseIn e).subgroupOf R).index ≤ 2 := by
      show (R ⊓ baseIn e).relIndex R ≤ 2
      rw [Subgroup.inf_relIndex_left]
      have h := Subgroup.relIndex_le_of_le_right hRS
        (show (baseIn e).relIndex S ≠ 0 by rw [baseIn_relIndex]; norm_num)
      rw [baseIn_relIndex] at h
      exact h
    have hcomm : ∀ a ∈ (R ⊓ baseIn e).subgroupOf R, ∀ b ∈ (R ⊓ baseIn e).subgroupOf R,
        a * b = b * a := by
      intro a ha b hb
      apply Subtype.ext
      exact baseIn_commute e ((Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).2)
        ((Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).2)
    have hT : ∀ x ∈ (R ⊓ baseIn e).subgroupOf R, x ^ 2 = 1 →
        x ∈ (Subtype.val ⁻¹' transT2 e : Set R) := by
      intro x hx hx2
      have hx2' : (x.1 : A) ^ 2 = 1 := by
        have := congrArg Subtype.val hx2
        simpa using this
      exact mem_transT2 hn e ((Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2) hx2'
        (hRS htR)
        htB (hab x.1 x.2 t htR)
    calc Nat.card (↥R ⧸ frattini ↥R)
        ≤ ((R ⊓ baseIn e).subgroupOf R).index * Nat.card (Subtype.val ⁻¹' transT2 e : Set R) :=
          card_frattini_quotient_le hRp _ hcomm _ hT
      _ ≤ 2 * 2 := Nat.mul_le_mul hidx ((card_preimage_val_le _).trans (card_transT2_le e))
      _ = 4 := rfl

theorem exists_abelian_index_two {S : Subgroup A} [Finite A] {n : ℕ} (hS : IsPGroup 2 ↥S)
    (hn : 1 ≤ n) (e : ↥S ≃* Wreath (2 ^ n)) {R : Subgroup A} (hRS : R ≤ S)
    (hcard : Nat.card (↥R ⧸ frattini ↥R) = 8) :
    ∃ M : Subgroup A, M ≤ R ∧ (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧ M.relIndex R = 2 := by
  by_cases hRB : R ≤ baseIn e
  · exfalso
    have hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a :=
      fun a ha b hb => baseIn_commute e (hRB ha) (hRB hb)
    have := card_le_four_of_abelian hS hn e hRS hab
    omega
  · refine ⟨R ⊓ baseIn e, inf_le_left, fun a ha b hb => baseIn_commute e
      ((Subgroup.mem_inf.mp ha).2) ((Subgroup.mem_inf.mp hb).2), ?_⟩
    show (R ⊓ baseIn e).relIndex R = 2
    rw [Subgroup.inf_relIndex_left]
    have h1 : (baseIn e).relIndex R ≠ 1 := fun h => hRB (Subgroup.relIndex_eq_one.mp h)
    have h2 : (baseIn e).relIndex R ≤ 2 := by
      have h := Subgroup.relIndex_le_of_le_right hRS
        (show (baseIn e).relIndex S ≠ 0 by rw [baseIn_relIndex]; norm_num)
      rw [baseIn_relIndex] at h
      exact h
    have h0 : (baseIn e).relIndex R ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    omega

theorem centralizes_of_wreath {S : Subgroup A} [Finite A] {n : ℕ} (hS : IsPGroup 2 ↥S)
    (hn : 1 ≤ n) (e : ↥S ≃* Wreath (2 ^ n)) {R : Subgroup A} (hRS : R ≤ S) {g : A}
    (hgN : g ∈ Subgroup.normalizer (R : Set A)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hord : orderOf g = r) : ∀ y ∈ R, g * y = y * g :=
  centralizes_of_frattini_bounds R
    (hS.of_injective (Subgroup.inclusion hRS) (Subgroup.inclusion_injective hRS)) hgN hr hr5 hord
    (card_le_eight hS hn e hRS) (fun hab => card_le_four_of_abelian hS hn e hRS hab)
    (fun hcard => exists_abelian_index_two hS hn e hRS hcard)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType
