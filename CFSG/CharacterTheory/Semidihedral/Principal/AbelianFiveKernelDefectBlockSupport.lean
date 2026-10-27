module

public import CFSG.CharacterTheory.Semidihedral.Principal.DoublyTransitiveAugmentation
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasisDegreeSum

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

namespace FiveKernel

universe u

open Equiv

@[expose] def cyc (a b c d e : Fin 5) : Perm (Fin 5) :=
  swap a b * swap b c * swap c d * swap d e

@[expose] def fiveCycleList : Fin 6 → Perm (Fin 5) :=
  ![cyc 0 1 2 3 4, cyc 0 1 2 4 3, cyc 0 1 3 2 4, cyc 0 1 3 4 2, cyc 0 1 4 2 3, cyc 0 1 4 3 2]

theorem fiveCycleList_sign : ∀ i : Fin 6, Perm.sign (fiveCycleList i) = 1 := by
  decide

@[expose] def fiveCycle (i : Fin 6) : alternatingGroup (Fin 5) :=
  ⟨fiveCycleList i, Perm.mem_alternatingGroup.mpr (fiveCycleList_sign i)⟩

@[expose] def involution : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def sylowFixCount (σ : alternatingGroup (Fin 5)) : ℕ :=
  (Finset.univ.filter fun i : Fin 6 =>
    ∃ n : Fin 5, σ * fiveCycle i * σ⁻¹ = fiveCycle i ^ (n : ℕ)).card

@[expose] def pointFixCount (σ : alternatingGroup (Fin 5)) : ℕ :=
  (Finset.univ.filter fun a : Fin 5 => (σ : Perm (Fin 5)) a = a).card

theorem fiveCycle_pow_five : ∀ i : Fin 6, fiveCycle i ^ 5 = 1 ∧ fiveCycle i ≠ 1 := by
  decide +kernel

theorem eq_of_fiveCycle_eq_pow : ∀ i k : Fin 6, ∀ n : Fin 5,
    fiveCycle k = fiveCycle i ^ (n : ℕ) → k = i := by
  decide +kernel

theorem exists_fiveCycle_pow_eq : ∀ x : alternatingGroup (Fin 5), x ^ 5 = 1 → x ≠ 1 →
    ∃ i : Fin 6, ∃ n : Fin 5, x = fiveCycle i ^ (n : ℕ) := by
  decide +kernel

theorem sylowFixCount_eq : ∀ σ : alternatingGroup (Fin 5), sylowFixCount σ =
    if σ = 1 then 6 else if σ ^ 2 = 1 then 2 else if σ ^ 3 = 1 then 0 else 1 := by
  decide +kernel

theorem pointFixCount_eq : ∀ σ : alternatingGroup (Fin 5), pointFixCount σ =
    if σ = 1 then 5 else if σ ^ 2 = 1 then 1 else if σ ^ 3 = 1 then 2 else 0 := by
  decide +kernel

theorem pow_eq_one_cases : ∀ σ : alternatingGroup (Fin 5),
    σ = 1 ∨ σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

theorem sum_sylowFixCount : ∑ σ : alternatingGroup (Fin 5),
    ((sylowFixCount σ : ℤ) - 1) * ((sylowFixCount σ⁻¹ : ℤ) - 1) = 60 := by
  decide +kernel

theorem sum_pointFixCount : ∑ σ : alternatingGroup (Fin 5),
    ((pointFixCount σ : ℤ) - 1) * ((pointFixCount σ⁻¹ : ℤ) - 1) = 60 := by
  decide +kernel

theorem involution_sq : involution ^ 2 = 1 ∧ involution ≠ 1 := by
  decide +kernel

theorem card_commute_involution :
    (Finset.univ.filter fun σ : alternatingGroup (Fin 5) =>
      σ * involution = involution * σ).card = 4 := by
  decide +kernel

theorem card_alternating : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  decide +kernel

section Transport

variable {G : Type u} [Group G] [Fintype G] (e : G ≃* alternatingGroup (Fin 5))

omit [Fintype G] in
include e in
theorem card_eq_sixty : Nat.card G = 60 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternating]

@[expose] def sylowGenerator (i : Fin 6) : G := e.symm (fiveCycle i)

omit [Fintype G] in
theorem orderOf_sylowGenerator (i : Fin 6) : orderOf (sylowGenerator e i) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [sylowGenerator, MulEquiv.orderOf_eq]
  exact orderOf_eq_prime (fiveCycle_pow_five i).1 (fiveCycle_pow_five i).2

theorem mem_zpowers_sylowGenerator_iff (i : Fin 6) (x : G) :
    x ∈ Subgroup.zpowers (sylowGenerator e i) ↔ ∃ n : Fin 5, e x = fiveCycle i ^ (n : ℕ) := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_sylowGenerator, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨n, Finset.mem_range.mp hn⟩, ?_⟩
    rw [map_pow, sylowGenerator, MulEquiv.apply_symm_apply]
  · rintro ⟨n, hn⟩
    refine ⟨n, Finset.mem_range.mpr n.isLt, ?_⟩
    apply e.injective
    rw [map_pow, sylowGenerator, MulEquiv.apply_symm_apply, hn]

theorem zpowers_eq_of_mem_of_orderOf_five {x y : G} (hx : orderOf x = 5) (hy : orderOf y = 5)
    (h : x ∈ Subgroup.zpowers y) : Subgroup.zpowers x = Subgroup.zpowers y :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy])

omit [Fintype G] in
theorem isPGroup_zpowers_sylowGenerator (i : Fin 6) :
    IsPGroup 5 (Subgroup.zpowers (sylowGenerator e i)) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_sylowGenerator, pow_one])

omit [Fintype G] in
theorem index_zpowers_sylowGenerator (i : Fin 6) :
    (Subgroup.zpowers (sylowGenerator e i)).index = 12 := by
  have h := Subgroup.index_mul_card (Subgroup.zpowers (sylowGenerator e i))
  rw [Nat.card_zpowers, orderOf_sylowGenerator, card_eq_sixty e] at h
  omega

@[expose] noncomputable def sylowOf (i : Fin 6) : Sylow 5 G :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  (isPGroup_zpowers_sylowGenerator e i).toSylow
    (by rw [index_zpowers_sylowGenerator]; norm_num)

omit [Fintype G] in
theorem coe_sylowOf (i : Fin 6) :
    (sylowOf e i : Subgroup G) = Subgroup.zpowers (sylowGenerator e i) := rfl

theorem sylowOf_injective : Function.Injective (sylowOf e) := by
  intro i k h
  have hmem : sylowGenerator e k ∈ Subgroup.zpowers (sylowGenerator e i) := by
    rw [← coe_sylowOf, h, coe_sylowOf]
    exact Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := (mem_zpowers_sylowGenerator_iff e i _).mp hmem
  rw [sylowGenerator, MulEquiv.apply_symm_apply] at hn
  exact (eq_of_fiveCycle_eq_pow i k n hn).symm

theorem sylowOf_surjective : Function.Surjective (sylowOf e) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro P
  have hne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card (by rw [card_eq_sixty e]; norm_num)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' a
  rw [← Subgroup.orderOf_coe] at hk
  have hdvd : 5 ^ k ∣ 60 := by
    rw [← hk, ← card_eq_sixty e]
    exact orderOf_dvd_natCard _
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h25 : 5 ^ 2 ∣ 60 := (Nat.pow_dvd_pow 5 (by omega)).trans hdvd
    norm_num at h25
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact ha (Subtype.ext hk)
  have hord : orderOf (a : G) = 5 := by
    rw [hk, show k = 1 by omega, pow_one]
  have hpow : e a ^ 5 = 1 := by
    have h5 : (a : G) ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hord)
    rw [← map_pow, h5, map_one]
  have hne1 : e a ≠ 1 := by
    intro h1
    apply ha
    apply Subtype.ext
    rw [Subgroup.coe_one]
    exact e.injective (h1.trans (map_one e).symm)
  obtain ⟨i, n, hn⟩ := exists_fiveCycle_pow_eq (e a) hpow hne1
  have hmem : (a : G) ∈ Subgroup.zpowers (sylowGenerator e i) :=
    (mem_zpowers_sylowGenerator_iff e i a).mpr ⟨n, hn⟩
  have heq := zpowers_eq_of_mem_of_orderOf_five hord (orderOf_sylowGenerator e i) hmem
  have hle : (sylowOf e i : Subgroup G) ≤ P := by
    rw [coe_sylowOf, ← heq, Subgroup.zpowers_le]
    exact a.property
  exact ⟨i, Sylow.ext ((sylowOf e i).is_maximal' P.isPGroup' hle).symm⟩

theorem smul_sylowOf_eq_iff (g : G) (i : Fin 6) : g • sylowOf e i = sylowOf e i ↔
    ∃ n : Fin 5, e g * fiveCycle i * (e g)⁻¹ = fiveCycle i ^ (n : ℕ) := by
  have hcoe : ((g • sylowOf e i : Sylow 5 G) : Subgroup G) =
      Subgroup.zpowers (g * sylowGenerator e i * g⁻¹) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, coe_sylowOf]
    exact MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom (sylowGenerator e i)
  have hord : orderOf (g * sylowGenerator e i * g⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact orderOf_sylowGenerator e i
  rw [Sylow.ext_iff, hcoe, coe_sylowOf]
  constructor
  · intro h
    have hmem : g * sylowGenerator e i * g⁻¹ ∈ Subgroup.zpowers (sylowGenerator e i) :=
      h ▸ Subgroup.mem_zpowers _
    obtain ⟨n, hn⟩ := (mem_zpowers_sylowGenerator_iff e i _).mp hmem
    refine ⟨n, ?_⟩
    rw [← hn, map_mul, map_mul, map_inv, sylowGenerator, MulEquiv.apply_symm_apply]
  · rintro ⟨n, hn⟩
    apply zpowers_eq_of_mem_of_orderOf_five hord (orderOf_sylowGenerator e i)
    rw [mem_zpowers_sylowGenerator_iff]
    refine ⟨n, ?_⟩
    rw [map_mul, map_mul, map_inv, sylowGenerator, MulEquiv.apply_symm_apply, hn]

include e in
theorem card_sylow_five : Nat.card (Sylow 5 G) = 6 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨sylowOf_injective e, sylowOf_surjective e⟩),
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_fixedBy_sylow (g : G) :
    Nat.card (MulAction.fixedBy (Sylow 5 G) g) = sylowFixCount (e g) := by
  have h1 : Nat.card (MulAction.fixedBy (Sylow 5 G) g) =
      Nat.card {i : Fin 6 // g • sylowOf e i = sylowOf e i} :=
    Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ ⟨sylowOf_injective e, sylowOf_surjective e⟩)
      (fun _ => MulAction.mem_fixedBy.symm)).symm
  have h2 : Nat.card {i : Fin 6 // g • sylowOf e i = sylowOf e i} =
      Nat.card {i : Fin 6 // ∃ n : Fin 5, e g * fiveCycle i * (e g)⁻¹ = fiveCycle i ^ (n : ℕ)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun i => smul_sylowOf_eq_iff e g i)
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

@[expose, instance_reducible] def pointAction : MulAction G (ULift.{u} (Fin 5)) where
  smul g a := ⟨(e g : Perm (Fin 5)) a.down⟩
  one_smul a := by
    change (⟨(e 1 : Perm (Fin 5)) a.down⟩ : ULift (Fin 5)) = a
    rw [map_one]
    rfl
  mul_smul g h a := by
    change (⟨(e (g * h) : Perm (Fin 5)) a.down⟩ : ULift (Fin 5)) =
      ⟨(e g : Perm (Fin 5)) ((e h : Perm (Fin 5)) a.down)⟩
    rw [map_mul]
    rfl

omit [Fintype G] in
theorem card_fixedBy_point (g : G) :
    letI := pointAction e
    Nat.card (MulAction.fixedBy (ULift.{u} (Fin 5)) g) = pointFixCount (e g) := by
  let := pointAction e
  have h1 : Nat.card (MulAction.fixedBy (ULift.{u} (Fin 5)) g) =
      Nat.card {a : Fin 5 // (e g : Perm (Fin 5)) a = a} :=
    Nat.card_congr (Equiv.subtypeEquiv Equiv.ulift (fun a => by
      rw [MulAction.mem_fixedBy]
      constructor
      · intro h
        exact congrArg ULift.down h
      · intro h
        exact congrArg ULift.up h))
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end Transport

section Characters

@[expose] noncomputable def sylowAugmentation (G : Type u) [Group G] : G → ℂ :=
  fun g => (Nat.card (MulAction.fixedBy (Sylow 5 G) g) : ℂ) - 1

variable {G : Type u} [Group G] [Fintype G] (e : G ≃* alternatingGroup (Fin 5))

@[expose] noncomputable def pointAugmentation : G → ℂ :=
  letI := pointAction e
  fun g => (Nat.card (MulAction.fixedBy (ULift.{u} (Fin 5)) g) : ℂ) - 1

theorem sylowAugmentation_apply (g : G) :
    sylowAugmentation G g = (((sylowFixCount (e g) : ℤ) - 1 : ℤ) : ℂ) := by
  rw [sylowAugmentation, card_fixedBy_sylow e g]
  push_cast
  ring

omit [Fintype G] in
theorem pointAugmentation_apply (g : G) :
    pointAugmentation e g = (((pointFixCount (e g) : ℤ) - 1 : ℤ) : ℂ) := by
  have h := card_fixedBy_point e g
  simp only [pointAugmentation] at h ⊢
  rw [h]
  push_cast
  ring

include e in
theorem sylowAugmentation_one : sylowAugmentation G 1 = 5 := by
  rw [sylowAugmentation_apply e, map_one, sylowFixCount_eq]
  norm_num

omit [Fintype G] in
theorem pointAugmentation_one : pointAugmentation e 1 = 4 := by
  rw [pointAugmentation_apply e, map_one, pointFixCount_eq]
  norm_num

omit [Fintype G] in
theorem apply_ne_one_of_orderOf {g : G} {n : ℕ} (hn : orderOf g = n) (hn1 : n ≠ 1) :
    e g ≠ 1 := by
  intro h
  rw [← MulEquiv.orderOf_eq e, h, orderOf_one] at hn
  exact hn1 hn.symm

omit [Fintype G] in
theorem apply_pow_ne_one_of_orderOf {g : G} {n k : ℕ} (hn : orderOf g = n) (hnk : ¬ n ∣ k) :
    e g ^ k ≠ 1 := by
  intro h
  rw [← MulEquiv.orderOf_eq e] at hn
  exact hnk (hn ▸ orderOf_dvd_of_pow_eq_one h)

omit [Fintype G] in
theorem apply_pow_orderOf {g : G} {n : ℕ} (hn : orderOf g = n) : e g ^ n = 1 := by
  rw [← hn, ← MulEquiv.orderOf_eq e]
  exact pow_orderOf_eq_one _

include e in
theorem sylowAugmentation_of_orderOf_two {g : G} (hg : orderOf g = 2) :
    sylowAugmentation G g = 1 := by
  rw [sylowAugmentation_apply e, sylowFixCount_eq,
    ite_eq_right (apply_ne_one_of_orderOf e hg (by norm_num)),
    ite_eq_left (apply_pow_orderOf e hg)]
  norm_num

include e in
theorem sylowAugmentation_of_orderOf_three {g : G} (hg : orderOf g = 3) :
    sylowAugmentation G g = -1 := by
  rw [sylowAugmentation_apply e, sylowFixCount_eq,
    ite_eq_right (apply_ne_one_of_orderOf e hg (by norm_num)),
    ite_eq_right (apply_pow_ne_one_of_orderOf e hg (by norm_num)),
    ite_eq_left (apply_pow_orderOf e hg)]
  norm_num

include e in
theorem sylowAugmentation_of_orderOf_five {g : G} (hg : orderOf g = 5) :
    sylowAugmentation G g = 0 := by
  rw [sylowAugmentation_apply e, sylowFixCount_eq,
    ite_eq_right (apply_ne_one_of_orderOf e hg (by norm_num)),
    ite_eq_right (apply_pow_ne_one_of_orderOf e hg (by norm_num)),
    ite_eq_right (apply_pow_ne_one_of_orderOf e hg (by norm_num))]
  norm_num

@[expose] noncomputable def sylowPermutation (G : Type u) [Group G] [Finite G] :
    FiniteComplexRepresentation.{u, u} G :=
  { vector := MonoidAlgebra ℂ (Sylow 5 G)
    representation := Representation.ofMulAction ℂ G (Sylow 5 G) }

theorem sylowPermutation_character (g : G) :
    (sylowPermutation G).character g = Nat.card (MulAction.fixedBy (Sylow 5 G) g) := by
  let := Fintype.ofFinite (Sylow 5 G)
  exact DoublyTransitive.ofMulAction_character_eq_card_fixedBy g

@[expose] noncomputable def pointPermutation : FiniteComplexRepresentation.{u, u} G :=
  letI := pointAction e
  { vector := MonoidAlgebra ℂ (ULift.{u} (Fin 5))
    representation := Representation.ofMulAction ℂ G (ULift.{u} (Fin 5)) }

omit [Fintype G] in
theorem pointPermutation_character (g : G) :
    (pointPermutation e).character g =
      letI := pointAction e
      Nat.card (MulAction.fixedBy (ULift.{u} (Fin 5)) g) := by
  let := pointAction e
  exact DoublyTransitive.ofMulAction_character_eq_card_fixedBy g

variable (basis : FiniteIrreducibleCharacterBasis G)

theorem exists_principal_label : ∃ l : basis.index, (basis.representation l).character = 1 :=
  (finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G)
    (principalFiniteComplexRepresentation_isIrreducible G)).imp
    fun _ hl => hl.trans (principalFiniteComplexRepresentation_character G)

theorem exists_label_of_virtual_norm_one (f : G → ℂ) (hf : f ∈ virtualCharacters G)
    (hnorm : characterPairing f f = 1) (n : ℕ) (hpos : 0 < n) (hn : f 1 = n) :
    ∃ l : basis.index, (basis.representation l).character = f := by
  obtain ⟨l, h | h⟩ := virtual_norm_one_signed_basis_character basis f hf hnorm
  · exact ⟨l, h.symm⟩
  · exfalso
    have h1 := congrFun h 1
    rw [hn, Pi.neg_apply, FiniteComplexRepresentation.character, Representation.char_one] at h1
    have hzero : ((n + Module.finrank ℂ (basis.representation l).vector : ℕ) : ℂ) = 0 := by
      push_cast
      rw [h1]
      ring
    have := Nat.cast_eq_zero.mp hzero
    omega

include e in
theorem characterPairing_sylowAugmentation :
    characterPairing (sylowAugmentation G) (sylowAugmentation G) = 1 := by
  unfold characterPairing
  rw [card_eq_sixty e]
  have hsum : ∑ g : G, sylowAugmentation G g * sylowAugmentation G g⁻¹ = 60 := by
    calc ∑ g : G, sylowAugmentation G g * sylowAugmentation G g⁻¹
        = ∑ σ : alternatingGroup (Fin 5),
            ((((sylowFixCount σ : ℤ) - 1) * ((sylowFixCount σ⁻¹ : ℤ) - 1) : ℤ) : ℂ) := by
          refine Fintype.sum_equiv e.toEquiv _ _ fun g => ?_
          rw [sylowAugmentation_apply e, sylowAugmentation_apply e, map_inv, Int.cast_mul]
          rfl
      _ = 60 := by
          rw [← Int.cast_sum, sum_sylowFixCount]
          norm_num
  rw [hsum]
  norm_num

theorem characterPairing_pointAugmentation :
    characterPairing (pointAugmentation e) (pointAugmentation e) = 1 := by
  unfold characterPairing
  rw [card_eq_sixty e]
  have hsum : ∑ g : G, pointAugmentation e g * pointAugmentation e g⁻¹ = 60 := by
    calc ∑ g : G, pointAugmentation e g * pointAugmentation e g⁻¹
        = ∑ σ : alternatingGroup (Fin 5),
            ((((pointFixCount σ : ℤ) - 1) * ((pointFixCount σ⁻¹ : ℤ) - 1) : ℤ) : ℂ) := by
          refine Fintype.sum_equiv e.toEquiv _ _ fun g => ?_
          rw [pointAugmentation_apply e, pointAugmentation_apply e, map_inv, Int.cast_mul]
          rfl
      _ = 60 := by
          rw [← Int.cast_sum, sum_pointFixCount]
          norm_num
  rw [hsum]
  norm_num

include e in
theorem exists_label_sylowAugmentation :
    ∃ l : basis.index, (basis.representation l).character = sylowAugmentation G := by
  obtain ⟨one, hone⟩ := exists_principal_label basis
  have hvirt : sylowAugmentation G ∈ virtualCharacters G := by
    have hdiff : sylowAugmentation G =
        (sylowPermutation G).character - (basis.representation one).character := by
      funext g
      rw [Pi.sub_apply, sylowPermutation_character, hone, Pi.one_apply]
      rfl
    rw [hdiff]
    exact Submodule.sub_mem _ (character_mem_virtualCharacters _)
      (character_mem_virtualCharacters _)
  exact exists_label_of_virtual_norm_one basis _ hvirt (characterPairing_sylowAugmentation e) 5
    (by norm_num) (by rw [sylowAugmentation_one e]; norm_num)

theorem exists_label_pointAugmentation :
    ∃ l : basis.index, (basis.representation l).character = pointAugmentation e := by
  obtain ⟨one, hone⟩ := exists_principal_label basis
  have hvirt : pointAugmentation e ∈ virtualCharacters G := by
    have hdiff : pointAugmentation e =
        (pointPermutation e).character - (basis.representation one).character := by
      funext g
      rw [Pi.sub_apply, pointPermutation_character, hone, Pi.one_apply]
      rfl
    rw [hdiff]
    exact Submodule.sub_mem _ (character_mem_virtualCharacters _)
      (character_mem_virtualCharacters _)
  exact exists_label_of_virtual_norm_one basis _ hvirt (characterPairing_pointAugmentation e) 4
    (by norm_num) (by rw [pointAugmentation_one e]; norm_num)

theorem finrank_eq_of_character_one {l : basis.index} {n : ℕ}
    (h : (basis.representation l).character 1 = n) :
    Module.finrank ℂ (basis.representation l).vector = n := by
  rw [FiniteComplexRepresentation.character, Representation.char_one] at h
  exact_mod_cast h

include e in
theorem eq_sylowAugmentation_of_five_dvd (l : basis.index)
    (hl : 5 ∣ Module.finrank ℂ (basis.representation l).vector) :
    (basis.representation l).character = sylowAugmentation G := by
  classical
  obtain ⟨one, hone⟩ := exists_principal_label basis
  obtain ⟨xi, hxi⟩ := exists_label_pointAugmentation e basis
  obtain ⟨th, hth⟩ := exists_label_sylowAugmentation e basis
  have hone1 : Module.finrank ℂ (basis.representation one).vector = 1 :=
    finrank_eq_of_character_one basis (by rw [hone, Pi.one_apply, Nat.cast_one])
  have hxi4 : Module.finrank ℂ (basis.representation xi).vector = 4 :=
    finrank_eq_of_character_one basis (by rw [hxi, pointAugmentation_one e]; norm_num)
  have hth5 : Module.finrank ℂ (basis.representation th).vector = 5 :=
    finrank_eq_of_character_one basis (by rw [hth, sylowAugmentation_one e]; norm_num)
  by_contra hne
  have hlth : l ≠ th := fun h => hne (h ▸ hth)
  have hpos : 0 < Module.finrank ℂ (basis.representation l).vector := by
    apply Nat.pos_of_ne_zero
    intro h0
    apply irreducible_character_degree_ne_zero _ (basis.irreducible l)
    rw [FiniteComplexRepresentation.character, Representation.char_one, h0, Nat.cast_zero]
  have hge : 5 ≤ Module.finrank ℂ (basis.representation l).vector := Nat.le_of_dvd hpos hl
  have hlone : l ≠ one := by
    rintro rfl
    rw [hone1] at hl
    norm_num at hl
  have hlxi : l ≠ xi := by
    rintro rfl
    rw [hxi4] at hl
    norm_num at hl
  have honexi : one ≠ xi := by
    intro h
    rw [h, hxi4] at hone1
    norm_num at hone1
  have honeth : one ≠ th := by
    intro h
    rw [h, hth5] at hone1
    norm_num at hone1
  have hxith : xi ≠ th := by
    intro h
    rw [h, hth5] at hxi4
    norm_num at hxi4
  have hsum := finiteIrreducibleCharacterBasis_sum_finrank_sq basis
  rw [card_eq_sixty e] at hsum
  have hle := Finset.sum_le_sum_of_subset
    (f := fun k => Module.finrank ℂ (basis.representation k).vector ^ 2)
    (Finset.subset_univ ({one, xi, th, l} : Finset basis.index))
  rw [hsum, Finset.sum_insert (by simp [honexi, honeth, hlone.symm]),
    Finset.sum_insert (by simp [hxith, hlxi.symm]), Finset.sum_insert (by simp [hlth.symm]),
    Finset.sum_singleton, hone1, hxi4, hth5] at hle
  nlinarith

omit [Fintype G] in
theorem orderOf_symm_involution : orderOf (e.symm involution) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [MulEquiv.orderOf_eq]
  exact orderOf_eq_prime involution_sq.1 involution_sq.2

omit [Fintype G] in
theorem card_centralizer_symm_involution :
    Nat.card (Subgroup.centralizer ({e.symm involution} : Set G)) = 4 := by
  have h : Nat.card (Subgroup.centralizer ({e.symm involution} : Set G)) =
      Nat.card {σ : alternatingGroup (Fin 5) // σ * involution = involution * σ} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun g => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h' := congrArg e h
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
      · intro h
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact h))
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_commute_involution

end Characters

end FiveKernel

end CFSG.Semidihedral.Principal
