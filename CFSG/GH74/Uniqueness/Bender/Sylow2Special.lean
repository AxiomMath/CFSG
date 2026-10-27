module

public import CFSG.GH74.Uniqueness.Bender.UnitaryOuterRoot

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG
open scoped commutatorElement

section Pure

variable {K : Type*} [Group K]

theorem commutator_mem_of_sq_mem {P Z : Subgroup K}
    (hZc : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z) (hsq : ∀ x ∈ P, x * x ∈ Z)
    {x y : K} (hx : x ∈ P) (hy : y ∈ P) : ⁅x, y⁆ ∈ Z := by
  have ha := hsq x hx
  have hb := hsq y hy
  have hc := hsq (x * y) (P.mul_mem hx hy)
  have hxy : x * y ∈ P := P.mul_mem hx hy
  have hxyx : x * y * x ∈ P := P.mul_mem hxy hx
  have e1 : x⁻¹ = (x * x)⁻¹ * x := by group
  have e2 : y⁻¹ = (y * y)⁻¹ * y := by group
  have c1 : (x * x)⁻¹ * (x * y) = (x * y) * (x * x)⁻¹ := hZc _ (Z.inv_mem ha) (x * y) hxy
  have c2 : (y * y)⁻¹ * (x * y * x) = (x * y * x) * (y * y)⁻¹ :=
    hZc _ (Z.inv_mem hb) (x * y * x) hxyx
  have key : ⁅x, y⁆ = (x * x)⁻¹ * (y * y)⁻¹ * ((x * y) * (x * y)) := by
    calc ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
      _ = x * y * ((x * x)⁻¹ * x) * ((y * y)⁻¹ * y) := by rw [← e1, ← e2]
      _ = ((x * y) * (x * x)⁻¹) * (x * ((y * y)⁻¹ * y)) := by group
      _ = ((x * x)⁻¹ * (x * y)) * (x * ((y * y)⁻¹ * y)) := by rw [c1]
      _ = (x * x)⁻¹ * ((x * y * x) * (y * y)⁻¹ * y) := by group
      _ = (x * x)⁻¹ * ((y * y)⁻¹ * (x * y * x) * y) := by rw [c2]
      _ = (x * x)⁻¹ * (y * y)⁻¹ * ((x * y) * (x * y)) := by group
  rw [key]
  exact Z.mul_mem (Z.mul_mem (Z.inv_mem ha) (Z.inv_mem hb)) hc

theorem commutator_le_of_sq_mem {P Z : Subgroup K}
    (hZc : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z) (hsq : ∀ x ∈ P, x * x ∈ Z) : ⁅P, P⁆ ≤ Z := by
  rw [Subgroup.commutator_le]
  exact fun x hx y hy => commutator_mem_of_sq_mem hZc hsq hx hy

theorem commutator_conj_mem {P : Subgroup K} {d : K} (hd : ∀ x ∈ P, d * x * d⁻¹ ∈ P)
    {w : K} (hw : w ∈ ⁅P, P⁆) : d * w * d⁻¹ ∈ ⁅P, P⁆ := by
  rw [Subgroup.commutator_def] at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨d * a * d⁻¹, hd a ha, d * b * d⁻¹, hd b hb, ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    convert this using 1
    group

theorem commutator_eq_of_transitive {P Z : Subgroup K} (D : Subgroup K)
    (hZc : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z) (hsq : ∀ x ∈ P, x * x ∈ Z)
    (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x)
    (hD : ∀ d ∈ D, ∀ x ∈ P, d * x * d⁻¹ ∈ P)
    (htrans : ∀ z ∈ Z, z ≠ 1 → ∀ z' ∈ Z, z' ≠ 1 → ∃ d ∈ D, z' = d⁻¹ * z * d) :
    ⁅P, P⁆ = Z := by
  refine le_antisymm (commutator_le_of_sq_mem hZc hsq) ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  have hz : ⁅x, y⁆ ∈ ⁅P, P⁆ := Subgroup.commutator_mem_commutator hx hy
  have hzZ : ⁅x, y⁆ ∈ Z := commutator_mem_of_sq_mem hZc hsq hx hy
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    apply hxy
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  intro z' hz'
  by_cases h1 : z' = 1
  · rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨d, hd, rfl⟩ := htrans _ hzZ hz1 z' hz' h1
  have := commutator_conj_mem (P := P) (d := d⁻¹) (fun x hx => by
    simpa using hD d⁻¹ (D.inv_mem hd) x hx) hz
  simpa using this

theorem commutator_subtype_eq {P Z : Subgroup K} (hcomm : ⁅P, P⁆ = Z) :
    _root_.commutator ↥P = Z.subgroupOf P := by
  have h1 : (_root_.commutator ↥P).map P.subtype = ⁅P, P⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h2 : _root_.commutator ↥P = ((_root_.commutator ↥P).map P.subtype).comap P.subtype :=
    (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
  rw [h2, h1, hcomm]
  rfl

theorem frattini_eq_of_special {P Z : Subgroup K} (hsq : ∀ x ∈ P, x * x ∈ Z)
    (hcomm : ⁅P, P⁆ = Z)
    (hburn : frattini ↥P = Subgroup.closure (((_root_.commutator ↥P : Subgroup ↥P) : Set ↥P) ∪
      Set.range (fun x : ↥P => x ^ 2))) :
    frattini ↥P = Z.subgroupOf P := by
  have hc := commutator_subtype_eq hcomm
  rw [hburn, hc]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (hz | ⟨x, rfl⟩)
    · exact hz
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      simpa [sq] using hsq x x.2
  · intro z hz
    exact Subgroup.subset_closure (Or.inl hz)

theorem normal_subgroupOf_of_central {P Z : Subgroup K}
    (hZc : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z) : (Z.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 := hZc _ hn g g.2
  have h : ((g * n * g⁻¹ : ↥P) : K) = (n : K) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : K) * n * (g : K)⁻¹ = ((n : K) * g) * (g : K)⁻¹ := by rw [h1]
      _ = n := by group
  rw [h]
  exact hn

theorem card_quotient_subgroupOf_mul {P Z : Subgroup K} (hZP : Z ≤ P) :
    Nat.card (↥P ⧸ Z.subgroupOf P) * Nat.card Z = Nat.card P := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf P)
  have h2 : Nat.card (Z.subgroupOf P) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  rw [h2] at h1
  exact h1.symm

end Pure

section Special

variable {K : Type*} [Group K] [Finite K] {q i e : ℕ} {P : Subgroup K} {t : K}

instance rootCenter_subgroupOf_normal (P : Subgroup K) : ((rootCenter P).subgroupOf P).Normal :=
  normal_subgroupOf_of_central (fun _ hz p hp => ((mem_rootCenter_iff.mp hz).2 p hp).symm)

theorem BenderCore.commutator_eq_rootCenter_of_sq_mem (hc : BenderCore q i e P t)
    (hsq : ∀ x ∈ P, x * x ∈ rootCenter P) (hne : rootCenter P ≠ P) :
    ⁅P, P⁆ = rootCenter P := by
  refine commutator_eq_of_transitive (cartan P t)
    (fun _ hz p hp => ((mem_rootCenter_iff.mp hz).2 p hp).symm) hsq ?_ ?_ ?_
  · by_contra hall
    push Not at hall
    apply hne
    apply le_antisymm (rootCenter_le P)
    intro x hx
    exact mem_rootCenter_iff.mpr ⟨hx, fun p hp => hall p hp x hx⟩
  · intro d hd x hx
    exact (Subgroup.mem_normalizer_iff.mp (cartan_le_borel P t hd) x).mp hx
  · intro z hz hz1 z' hz' hz1'
    exact hc.exists_cartan_conj hz hz1 hz' hz1'

theorem BenderCore.special_of_sq_mem (hc : BenderCore q i e P t) (hP : IsPGroup 2 P)
    (hi : 2 ≤ i) (hq : 2 ≤ q) (hsq : ∀ x ∈ P, x * x ∈ rootCenter P) :
    ⁅P, P⁆ = rootCenter P ∧ frattini ↥P = (rootCenter P).subgroupOf P ∧
      Subgroup.closure {x | x ∈ P ∧ x * x = 1} = rootCenter P ∧
      IsElementaryAbelian 2 (↥P ⧸ (rootCenter P).subgroupOf P) ∧
      Nat.card (↥P ⧸ (rootCenter P).subgroupOf P) = q ^ (i - 1) := by
  have hne : rootCenter P ≠ P := by
    intro heq
    have h1 := hc.card_eq
    rw [← heq, hc.card_center] at h1
    have : q < q ^ i := by
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ i := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hZc : ∀ z ∈ rootCenter P, ∀ p ∈ P, z * p = p * z :=
    fun _ hz p hp => ((mem_rootCenter_iff.mp hz).2 p hp).symm
  have hcomm := hc.commutator_eq_rootCenter_of_sq_mem hsq hne
  have : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
  have hburn := CFSG.frattini_eq_closure_commutator_union_powers (R := ↥P) (p := 2)
  have hfr := frattini_eq_of_special hsq hcomm hburn
  have hΩ : Subgroup.closure {x | x ∈ P ∧ x * x = 1} = rootCenter P := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨hxP, hx2⟩
      exact hc.mem_rootCenter_of_mul_self hxP hx2
    · intro z hz
      exact Subgroup.subset_closure ⟨rootCenter_le P hz, hc.center_sq z hz⟩
  have hEA : IsElementaryAbelian 2 (↥P ⧸ (rootCenter P).subgroupOf P) := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr
        (by rw [commutator_subtype_eq hcomm])
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro y
      refine QuotientGroup.induction_on y ?_
      intro x
      have hx2 : x ^ 2 ∈ (rootCenter P).subgroupOf P := by
        rw [Subgroup.mem_subgroupOf]
        simpa [sq] using hsq x x.2
      have := (QuotientGroup.eq_one_iff (N := (rootCenter P).subgroupOf P) (x ^ 2)).2 hx2
      simpa [QuotientGroup.mk_pow] using this
  have hcard : Nat.card (↥P ⧸ (rootCenter P).subgroupOf P) = q ^ (i - 1) := by
    have h1 := card_quotient_subgroupOf_mul (rootCenter_le P)
    rw [hc.card_center, hc.card_eq] at h1
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hqpos : 0 < q := by omega
    rw [pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right hqpos h1
  exact ⟨hcomm, hfr, hΩ, hEA, hcard⟩

end Special

section Unitary

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.lemma_3_5_a_unitary
    {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K) :
    ⁅(Q : Subgroup K), (Q : Subgroup K)⁆ = rootCenter (Q : Subgroup K) ∧
      frattini ↥(Q : Subgroup K) = (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K) ∧
      Subgroup.closure {x | x ∈ (Q : Subgroup K) ∧ x * x = 1} = rootCenter (Q : Subgroup K) ∧
      IsElementaryAbelian 2
        (↥(Q : Subgroup K) ⧸ (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K)) ∧
      Nat.card (↥(Q : Subgroup K) ⧸
        (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K)) = (2 ^ n) ^ 2 := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hn2 : 2 ≤ n := h.two_le.2
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hc.special_of_sq_mem Q.isPGroup' (by norm_num) hq
    (fun x hx => h.sq_mem_rootCenter_unitary Q hx)

end Unitary

end CFSG.GH74.Uniqueness.Bender
