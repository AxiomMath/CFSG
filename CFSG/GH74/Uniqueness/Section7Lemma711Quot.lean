module

public import CFSG.GH74.Uniqueness.Section7Lemma711Aux

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_subgroup_comm_mod {O L : Subgroup X} (hLO : L ≤ normalizer (O : Set X)) (y : X) :
    ∃ C : Subgroup X, ∀ x, x ∈ C ↔ x ∈ L ∧ x * y * x⁻¹ * y⁻¹ ∈ O := by
  refine ⟨{ carrier := {x | x ∈ L ∧ x * y * x⁻¹ * y⁻¹ ∈ O}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro a b ha hb
    obtain ⟨haL, ha⟩ := ha
    obtain ⟨hbL, hb⟩ := hb
    refine ⟨L.mul_mem haL hbL, ?_⟩
    have h1 : a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hLO haL) _).mp hb
    have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
        (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e]
    exact O.mul_mem h1 ha
  · refine ⟨L.one_mem, ?_⟩
    simp
  · intro a ha
    obtain ⟨haL, ha⟩ := ha
    refine ⟨L.inv_mem haL, ?_⟩
    have h1 : a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hLO (L.inv_mem haL)) _).mp (O.inv_mem ha)
    have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h1

omit [Finite X] in
theorem comm_mem_of_mem_sup_closure {O L : Subgroup X} {T : Set X} (hOL : O ≤ L)
    (hTL : T ⊆ L) (hLO : L ≤ normalizer (O : Set X))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ O) {x y : X}
    (hx : x ∈ O ⊔ closure T) (hy : y ∈ O ⊔ closure T) : x * y * x⁻¹ * y⁻¹ ∈ O := by
  have hBL : O ⊔ closure T ≤ L := sup_le hOL ((closure_le L).mpr hTL)
  have hO : ∀ y ∈ L, ∀ o ∈ O, o * y * o⁻¹ * y⁻¹ ∈ O := by
    intro y hy o ho
    have h1 : y * o⁻¹ * y⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hLO hy) _).mp (O.inv_mem ho)
    have e : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
    rw [e]
    exact O.mul_mem ho h1
  have step : ∀ y ∈ L, (∀ a ∈ T, a * y * a⁻¹ * y⁻¹ ∈ O) →
      ∀ x ∈ O ⊔ closure T, x * y * x⁻¹ * y⁻¹ ∈ O := by
    intro y hyL hTy x hx
    obtain ⟨C, hC⟩ := exists_subgroup_comm_mod hLO y
    have hle : O ⊔ closure T ≤ C := by
      refine sup_le (fun o ho => (hC o).mpr ⟨hOL ho, hO y hyL o ho⟩) ?_
      rw [closure_le]
      intro a ha
      exact (hC a).mpr ⟨hTL ha, hTy a ha⟩
    exact ((hC x).mp (hle hx)).2
  have h1 : ∀ b ∈ T, ∀ x ∈ O ⊔ closure T, x * b * x⁻¹ * b⁻¹ ∈ O := fun b hb =>
    step b (hTL hb) (fun a ha => hT a ha b hb)
  refine step y (hBL hy) ?_ x hx
  intro a ha
  have h2 := O.inv_mem (h1 a ha y hy)
  have e : (y * a * y⁻¹ * a⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ := by group
  rwa [e] at h2

omit [Finite X] in
theorem mul_self_mem_of_mem_sup_closure {O L : Subgroup X} {T : Set X} (hOL : O ≤ L)
    (hTL : T ⊆ L) (hLO : L ≤ normalizer (O : Set X))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ O) (hT2 : ∀ a ∈ T, a * a ∈ O) {x : X}
    (hx : x ∈ O ⊔ closure T) : x * x ∈ O := by
  let B : Subgroup X := O ⊔ closure T
  let E : Subgroup X :=
    { carrier := {x | x ∈ B ∧ x * x ∈ O}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haB, ha⟩ := ha
        obtain ⟨hbB, hb⟩ := hb
        refine ⟨B.mul_mem haB hbB, ?_⟩
        have hc := comm_mem_of_mem_sup_closure hOL hTL hLO hT (B.inv_mem haB) hbB
        have e : a * b * (a * b) = (a * a) * (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹) * (b * b) := by group
        rw [e]
        exact O.mul_mem (O.mul_mem ha hc) hb
      one_mem' := ⟨B.one_mem, by simp⟩
      inv_mem' := by
        intro a ha
        obtain ⟨haB, ha⟩ := ha
        refine ⟨B.inv_mem haB, ?_⟩
        have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        rw [e]
        exact O.inv_mem ha }
  have hle : B ≤ E := by
    refine sup_le (fun o ho => ⟨le_sup_left (a := O) ho, O.mul_mem ho ho⟩) ?_
    rw [closure_le]
    intro a ha
    exact ⟨le_sup_right (a := O) (subset_closure ha), hT2 a ha⟩
  exact (hle hx).2

section Quotient

variable {O B : Subgroup X}

omit [Finite X] in
theorem isMulCommutative_quotient_of_comm_mem [(O.subgroupOf B).Normal]
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ O) :
    IsMulCommutative (↥B ⧸ O.subgroupOf B) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  induction a using QuotientGroup.induction_on with
  | H x =>
  induction b using QuotientGroup.induction_on with
  | H y =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h := hcomm _ (B.inv_mem y.2) _ (B.inv_mem x.2)
  have e : (((x * y)⁻¹ * (y * x) : ↥B) : X) =
      (y : X)⁻¹ * (x : X)⁻¹ * (y : X)⁻¹⁻¹ * (x : X)⁻¹⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact h

omit [Finite X] in
theorem isPGroup_two_quotient_of_mul_self_mem [(O.subgroupOf B).Normal]
    (hsq : ∀ x ∈ B, x * x ∈ O) : IsPGroup 2 (↥B ⧸ O.subgroupOf B) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H x =>
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hsq _ x.2

theorem hasAbelianSylow_two_of_comm_mem (hOB : O ≤ B) (hBO : B ≤ normalizer (O : Set X))
    (hodd : Odd (Nat.card O)) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ O) :
    CFSG.BenderSuzuki.HasAbelianSylow 2 ↥B := by
  have : (O.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOB).mpr hBO
  have hodd' : Odd (Nat.card (O.subgroupOf B)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOB).toEquiv]
    exact hodd
  exact CFSG.BenderSuzuki.hasAbelianSylowTwo_of_odd_normal_quotient_isMulCommutative
    (O.subgroupOf B) hodd' (isMulCommutative_quotient_of_comm_mem hcomm)

theorem isSolvable_of_mul_self_mem (hOB : O ≤ B) (hBO : B ≤ normalizer (O : Set X))
    (hodd : Odd (Nat.card O)) (hsq : ∀ x ∈ B, x * x ∈ O) : Group.IsSolvable ↥B := by
  have : (O.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOB).mpr hBO
  have : Group.IsSolvable ↥O := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥O hodd
  have : Group.IsSolvable ↥(O.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hOB).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hOB).injective
  have : Group.IsNilpotent (↥B ⧸ O.subgroupOf B) :=
    (isPGroup_two_quotient_of_mul_self_mem hsq).isNilpotent
  exact isSolvable_of_normal_subgroup_and_quotient (O.subgroupOf B)

omit [Finite X] in
theorem le_of_odd_of_mul_self_mem {T : Subgroup X} (hsq : ∀ x ∈ B, x * x ∈ O) (hTB : T ≤ B)
    (hT : Odd (Nat.card T)) : T ≤ O := by
  intro x hx
  have hao : Odd (orderOf x) := Odd.of_dvd_nat hT (Subgroup.orderOf_dvd_natCard T hx)
  exact mem_of_mul_self_mem_of_odd_orderOf hao (hsq x (hTB hx))

theorem not_dvd_relIndex_of_mul_self_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hOB : O ≤ B)
    (hBO : B ≤ normalizer (O : Set X)) (hsq : ∀ x ∈ B, x * x ∈ O) : ¬ p ∣ O.relIndex B := by
  have : (O.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOB).mpr hBO
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_two_quotient_of_mul_self_mem hsq)
  intro hdvd
  have h1 : p ∣ 2 ^ k := by
    have e : O.relIndex B = Nat.card (↥B ⧸ O.subgroupOf B) := rfl
    rw [e, hk] at hdvd
    exact hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))

end Quotient

section Product

omit [Finite X] in
theorem subgroupOf_sup_subgroupOf_sup_eq_top (B R : Subgroup X) :
    B.subgroupOf (B ⊔ R) ⊔ R.subgroupOf (B ⊔ R) = ⊤ := by
  apply top_unique
  intro h _hh
  have hmapSup : (B.subgroupOf (B ⊔ R) ⊔ R.subgroupOf (B ⊔ R)).map (B ⊔ R).subtype = B ⊔ R := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  have hxMap : (h : X) ∈ (B.subgroupOf (B ⊔ R) ⊔ R.subgroupOf (B ⊔ R)).map (B ⊔ R).subtype := by
    rw [hmapSup]
    exact h.property
  rcases Subgroup.mem_map.mp hxMap with ⟨k, hk, hkEq⟩
  have : k = h := Subtype.ext hkEq
  rwa [this] at hk

theorem hasAbelianSylow_two_sup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B R : Subgroup X}
    (hRB : R ≤ normalizer (B : Set X)) (hRp : IsPGroup p R)
    (hB : CFSG.BenderSuzuki.HasAbelianSylow 2 ↥B) :
    CFSG.BenderSuzuki.HasAbelianSylow 2 ↥(B ⊔ R) := by
  have : (B.subgroupOf (B ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hRB)
  have hB' : CFSG.BenderSuzuki.HasAbelianSylow 2 ↥(B.subgroupOf (B ⊔ R)) :=
    hB.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  have hquot := isPGroup_quotient_sup_of_le_normalizer B R hRp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hquot
  have hodd : Odd (Nat.card (↥(B ⊔ R) ⧸ B.subgroupOf (B ⊔ R))) := by
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact CFSG.BenderSuzuki.HasAbelianSylow.of_normal_odd_quotient _ hB' hodd

theorem isSolvable_sup {p : ℕ} [Fact p.Prime] {B R : Subgroup X}
    (hRB : R ≤ normalizer (B : Set X)) (hRp : IsPGroup p R) (hB : Group.IsSolvable ↥B) :
    Group.IsSolvable ↥(B ⊔ R) := by
  have : (B.subgroupOf (B ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hRB)
  have : Group.IsSolvable ↥(B.subgroupOf (B ⊔ R)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : B ≤ B ⊔ R)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : B ≤ B ⊔ R)).injective
  have : Group.IsNilpotent (↥(B ⊔ R) ⧸ B.subgroupOf (B ⊔ R)) :=
    (isPGroup_quotient_sup_of_le_normalizer B R hRp).isNilpotent
  exact isSolvable_of_normal_subgroup_and_quotient (B.subgroupOf (B ⊔ R))

theorem isSylowOf_sup_of_le_normalizer {p : ℕ} [Fact p.Prime] {O B R P₀ : Subgroup X}
    (hOB : O ≤ B) (hindex : ¬ p ∣ O.relIndex B) (hRB : R ≤ normalizer (B : Set X))
    (hRp : IsPGroup p R) (hP₀ : ABGLocalTools.IsSylowOf p P₀ O) (hP₀R : P₀ ≤ R) :
    ABGLocalTools.IsSylowOf p R (B ⊔ R) := by
  have hp : p.Prime := Fact.out
  have hP₀O : P₀ ≤ O := hP₀.le
  have hP₀B : ABGLocalTools.IsSylowOf p P₀ B := by
    rw [ABGLocalTools.isSylowOf_iff] at hP₀ ⊢
    obtain ⟨-, hP₀p, hP₀idx⟩ := hP₀
    refine ⟨hP₀O.trans hOB, hP₀p, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P₀ O B hP₀O hOB]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hP₀idx h
    · exact hindex h
  have hRBeq : R ⊓ B = P₀ :=
    hP₀B.eq_of_le (le_inf hP₀R (hP₀O.trans hOB)) inf_le_right (hRp.to_le inf_le_left)
  have hRBsyl : ¬ p ∣ R.relIndex B := by
    rw [← Subgroup.inf_relIndex_right, hRBeq]
    exact (ABGLocalTools.isSylowOf_iff.mp hP₀B).2.2
  have : (B.subgroupOf (B ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hRB)
  have h1 := ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (B.subgroupOf (B ⊔ R))
    (R.subgroupOf (B ⊔ R))
  rw [subgroupOf_sup_subgroupOf_sup_eq_top, Subgroup.relIndex_top_right,
    Subgroup.relIndex_subgroupOf le_sup_left] at h1
  rw [ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_right, hRp, ?_⟩
  have e : R.relIndex (B ⊔ R) = (R.subgroupOf (B ⊔ R)).index := rfl
  rw [e, h1]
  exact hRBsyl

end Product

end CFSG.GH74.Uniqueness
