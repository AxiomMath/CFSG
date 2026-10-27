module

public import CFSG.HardMathSupport.Dickson.Bal207.Rank
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.KP.UnitaryTorus
import CFSG.HardMathSupport.Dickson.Bal207.U62Core
import CFSG.Open.StatedSUFieldChange
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KPUnitaryTorus CFSG.Fischer
  CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement Pointwise

abbrev U62S : Type := StatedProj (StatedSU 6 (2 ^ 1) F4)

@[expose] noncomputable def u62Perm : Equiv.Perm (Fin 6) →* U62S where
  toFun σ := QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem σ⁻¹⟩
  map_one' := by
    have h : (⟨permGL (1 : Equiv.Perm (Fin 6))⁻¹, permGL_mem _⟩ : StatedSU 6 (2 ^ 1) F4) = 1 :=
      Subtype.ext (Units.ext (by
        show ((1 : Equiv.Perm (Fin 6))⁻¹).permMatrix F4 = 1
        rw [inv_one, permMatrix_one]))
    rw [h, QuotientGroup.mk_one]
  map_mul' σ τ := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    show ((σ * τ)⁻¹).permMatrix F4 = σ⁻¹.permMatrix F4 * τ⁻¹.permMatrix F4
    rw [_root_.mul_inv_rev, permMatrix_mul]

theorem u62Perm_conj (σ : Equiv.Perm (Fin 6)) (a : sumZero6) :
    u62Perm σ * unitaryTorusHom (Multiplicative.ofAdd a) * (u62Perm σ)⁻¹ =
      unitaryTorusHom (Multiplicative.ofAdd (permSumZero σ a)) := by
  show (QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem σ⁻¹⟩ : U62S) * QuotientGroup.mk (torusElt a) *
      (QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem σ⁻¹⟩)⁻¹ =
    QuotientGroup.mk (torusElt (permSumZero σ a))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  show permGL σ⁻¹ * torusGL a * (permGL σ⁻¹)⁻¹ = torusGL (permSumZero σ a)
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul, permGL, torusGL, coe_diagGL]
  rw [permMatrix_mul_diagonal]
  rfl

theorem u62Perm_commute_iff (σ : Equiv.Perm (Fin 6)) (b : sumZero6) :
    u62Perm σ * unitaryTorusHom (Multiplicative.ofAdd b) =
        unitaryTorusHom (Multiplicative.ofAdd b) * u62Perm σ ↔
      ∃ k : ZMod 3, ∀ i, (b : Fin 6 → ZMod 3) (σ.symm i) - (b : Fin 6 → ZMod 3) i = k := by
  rw [← mul_inv_eq_iff_eq_mul, u62Perm_conj, ← mul_inv_eq_one, ← map_inv, ← map_mul,
    ← ofAdd_neg, ← ofAdd_add, unitaryTorusHom_eq_one_iff]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_sub, Pi.add_apply,
    Pi.neg_apply, Pi.sub_apply, CentralCoverThree.permSumZero_apply, ← sub_eq_add_neg]

theorem u62Perm_commutator (σ : Equiv.Perm (Fin 6)) (a b : sumZero6)
    (h : ∀ i, (b : Fin 6 → ZMod 3) i =
      (a : Fin 6 → ZMod 3) (σ.symm i) - (a : Fin 6 → ZMod 3) i) :
    ⁅u62Perm σ, unitaryTorusHom (Multiplicative.ofAdd a)⁆ =
      unitaryTorusHom (Multiplicative.ofAdd b) := by
  rw [commutatorElement_def, u62Perm_conj, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
  congr 2
  apply Subtype.ext
  funext i
  rw [h i]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_sub, Pi.add_apply,
    Pi.neg_apply, Pi.sub_apply, CentralCoverThree.permSumZero_apply, sub_eq_add_neg]

@[expose] def u62C1 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def u62C2 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def u62W0Elt (ij : Fin 3 × Fin 3) : Equiv.Perm (Fin 6) :=
  u62C1 ^ (ij.1 : ℕ) * u62C2 ^ (ij.2 : ℕ)

theorem u62W0Elt_mul : ∀ ij ij' : Fin 3 × Fin 3, ∃ ij'' : Fin 3 × Fin 3,
    u62W0Elt ij'' = u62W0Elt ij * u62W0Elt ij' := by
  decide

theorem u62W0Elt_inv : ∀ ij : Fin 3 × Fin 3, ∃ ij' : Fin 3 × Fin 3,
    u62W0Elt ij' = (u62W0Elt ij)⁻¹ := by
  decide

theorem u62W0Elt_comm : ∀ ij ij' : Fin 3 × Fin 3,
    u62W0Elt ij * u62W0Elt ij' = u62W0Elt ij' * u62W0Elt ij := by
  decide

theorem u62W0Elt_inj : ∀ ij ij' : Fin 3 × Fin 3, u62W0Elt ij = u62W0Elt ij' → ij = ij' := by
  decide

@[expose] def u62W0 : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := Set.range u62W0Elt
  mul_mem' := by
    rintro _ _ ⟨ij, rfl⟩ ⟨ij', rfl⟩
    exact u62W0Elt_mul ij ij'
  one_mem' := ⟨(0, 0), by decide⟩
  inv_mem' := by
    rintro _ ⟨ij, rfl⟩
    exact u62W0Elt_inv ij

@[expose] def u62B1 : Fin 6 → ZMod 3 := ![2, 1, 0, 0, 0, 0]

@[expose] def u62B2 : Fin 6 → ZMod 3 := ![0, 0, 0, 2, 1, 0]

@[expose] def u62A1 : Fin 6 → ZMod 3 := ![1, 0, 0, 0, 0, 2]

@[expose] def u62A2 : Fin 6 → ZMod 3 := ![2, 0, 0, 1, 0, 0]

theorem u62B1_mem : u62B1 ∈ sumZero6 := by
  rw [mem_sumZero6]
  decide

theorem u62B2_mem : u62B2 ∈ sumZero6 := by
  rw [mem_sumZero6]
  decide

theorem u62A1_mem : u62A1 ∈ sumZero6 := by
  rw [mem_sumZero6]
  decide

theorem u62A2_mem : u62A2 ∈ sumZero6 := by
  rw [mem_sumZero6]
  decide

theorem u62_check : ∀ ij : Fin 3 × Fin 3,
    (∃ k : ZMod 3, ∀ i, u62B1 ((u62W0Elt ij).symm i) - u62B1 i = k) →
    (∃ k : ZMod 3, ∀ i, u62B2 ((u62W0Elt ij).symm i) - u62B2 i = k) → u62W0Elt ij = 1 := by
  decide

@[expose] noncomputable def u62W : Subgroup U62S := u62W0.map u62Perm

@[expose] noncomputable def u62P : Subgroup U62S := unitaryTorusHom.range ⊔ u62W

theorem u62T_comm {x y : U62S} (hx : x ∈ unitaryTorusHom.range)
    (hy : y ∈ unitaryTorusHom.range) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem u62W_le_normalizer :
    u62W ≤ Subgroup.normalizer (unitaryTorusHom.range : Set U62S) := by
  rintro _ ⟨σ, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd (permSumZero σ (Multiplicative.toAdd a)), (u62Perm_conj σ _).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨Multiplicative.ofAdd (permSumZero σ⁻¹ (Multiplicative.toAdd a)), ?_⟩
    rw [← u62Perm_conj, ofAdd_toAdd, ha, map_inv]
    group

theorem u62W_comm {x y : U62S} (hx : x ∈ u62W) (hy : y ∈ u62W) : x * y = y * x := by
  obtain ⟨σ, ⟨ij, rfl⟩, rfl⟩ := hx
  obtain ⟨τ, ⟨ij', rfl⟩, rfl⟩ := hy
  rw [← map_mul, ← map_mul, u62W0Elt_comm]

theorem u62_eq_one {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ u62W0)
    (h1 : u62Perm σ * unitaryTorusHom (Multiplicative.ofAdd ⟨u62B1, u62B1_mem⟩) =
      unitaryTorusHom (Multiplicative.ofAdd ⟨u62B1, u62B1_mem⟩) * u62Perm σ)
    (h2 : u62Perm σ * unitaryTorusHom (Multiplicative.ofAdd ⟨u62B2, u62B2_mem⟩) =
      unitaryTorusHom (Multiplicative.ofAdd ⟨u62B2, u62B2_mem⟩) * u62Perm σ) : σ = 1 := by
  obtain ⟨ij, rfl⟩ := hσ
  exact u62_check ij ((u62Perm_commute_iff _ _).1 h1) ((u62Perm_commute_iff _ _).1 h2)

theorem u62_inf {x : U62S} (hxT : x ∈ unitaryTorusHom.range) (hxW : x ∈ u62W) : x = 1 := by
  obtain ⟨σ, hσ, rfl⟩ := hxW
  rw [u62_eq_one hσ (u62T_comm hxT (⟨_, rfl⟩))
    (u62T_comm hxT (⟨_, rfl⟩)), map_one]

theorem u62W_card : Nat.card u62W = 9 := by
  let f : Fin 3 × Fin 3 → u62W := fun ij => ⟨u62Perm (u62W0Elt ij), ⟨_, ⟨ij, rfl⟩, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro ij ij' h
    have h' : u62Perm (u62W0Elt ij) = u62Perm (u62W0Elt ij') := congrArg Subtype.val h
    have hmem : u62W0Elt ij * (u62W0Elt ij')⁻¹ ∈ u62W0 :=
      u62W0.mul_mem ⟨ij, rfl⟩ (u62W0.inv_mem ⟨ij', rfl⟩)
    have h1 : u62Perm (u62W0Elt ij * (u62W0Elt ij')⁻¹) = 1 := by
      rw [map_mul, map_inv, h', mul_inv_cancel]
    have hσ := u62_eq_one hmem (by rw [h1, one_mul, mul_one]) (by rw [h1, one_mul, mul_one])
    exact u62W0Elt_inj ij ij' (mul_inv_eq_one.1 hσ)
  have hsurj : Function.Surjective f := by
    rintro ⟨_, σ, ⟨ij, rfl⟩, rfl⟩
    exact ⟨ij, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  simp

theorem u62P_card : Nat.card u62P = 729 := by
  have hT : Nat.card unitaryTorusHom.range = 3 ^ 4 :=
    CentralCoverThree.card_range_eq unitaryTorusHom unitaryTorusHom_eq_one_iff
  let f : unitaryTorusHom.range × u62W → u62P := fun p =>
    ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨t, w⟩ ⟨t', w'⟩ h
    have h' : (t : U62S) * w = t' * w' := congrArg Subtype.val h
    have h1 : (t' : U62S)⁻¹ * t = w' * (w : U62S)⁻¹ := by
      calc (t' : U62S)⁻¹ * t = (t' : U62S)⁻¹ * (t * w) * (w : U62S)⁻¹ := by group
        _ = (t' : U62S)⁻¹ * (t' * w') * (w : U62S)⁻¹ := by rw [h']
        _ = w' * (w : U62S)⁻¹ := by group
    have hW : (t' : U62S)⁻¹ * t ∈ u62W := by
      rw [h1]
      exact u62W.mul_mem w'.2 (u62W.inv_mem w.2)
    have hg := u62_inf (unitaryTorusHom.range.mul_mem (unitaryTorusHom.range.inv_mem t'.2) t.2) hW
    have ht : (t' : U62S) = t := inv_mul_eq_one.1 hg
    have hw : (w : U62S) = w' := by
      rw [← ht] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext ht.symm) (Subtype.ext hw)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (unitaryTorusHom.range : Set U62S) * (u62W : Set U62S) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ u62W_le_normalizer]
      exact hx
    obtain ⟨t, ht, w, hw, rfl⟩ := hx'
    exact ⟨(⟨t, ht⟩, ⟨w, hw⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, hT, u62W_card]
  norm_num

theorem u62S_card : Nat.card U62S = 9196830720 := by
  have hF : Nat.card F4 = (2 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, F4.card]
    norm_num
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl hF
    (by norm_num : 2 ≤ 6)]
  decide

@[expose] noncomputable def u62Sylow : Sylow 3 U62S :=
  Sylow.ofCard u62P (by
    rw [u62P_card, u62S_card]
    have h : (9196830720 : ℕ) = 3 ^ 6 * 12615680 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num)

theorem u62_commutator_le : ⁅u62P, u62P⁆ ≤ unitaryTorusHom.range := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, u62P,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ u62W_le_normalizer] at hx hy
  obtain ⟨t, ht, w, hw, rfl⟩ := hx
  obtain ⟨t', ht', w', hw', rfl⟩ := hy
  have hww : w * w' = w' * w := u62W_comm hw hw'
  have h1 : w * t' * w⁻¹ ∈ unitaryTorusHom.range :=
    (Subgroup.mem_normalizer_iff.1 (u62W_le_normalizer hw) t').1 ht'
  have h2 : w' * t⁻¹ * w'⁻¹ ∈ unitaryTorusHom.range :=
    (Subgroup.mem_normalizer_iff.1 (u62W_le_normalizer hw') t⁻¹).1
      (unitaryTorusHom.range.inv_mem ht)
  have hc : w' * w⁻¹ = w⁻¹ * w' := by
    calc w' * w⁻¹ = w⁻¹ * (w * w') * w⁻¹ := by group
      _ = w⁻¹ * (w' * w) * w⁻¹ := by rw [hww]
      _ = w⁻¹ * w' := by group
  have key : ⁅t * w, t' * w'⁆ = t * (w * t' * w⁻¹) * (w' * t⁻¹ * w'⁻¹) * t'⁻¹ := by
    calc ⁅t * w, t' * w'⁆ = t * w * t' * (w' * w⁻¹) * t⁻¹ * w'⁻¹ * t'⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = t * w * t' * (w⁻¹ * w') * t⁻¹ * w'⁻¹ * t'⁻¹ := by rw [hc]
      _ = t * (w * t' * w⁻¹) * (w' * t⁻¹ * w'⁻¹) * t'⁻¹ := by group
  rw [key]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht h1) h2)
    (Subgroup.inv_mem _ ht')

theorem u62_cent {x : U62S} (hx : x ∈ u62P) (hc : ∀ u ∈ ⁅u62P, u62P⁆, x * u = u * x) :
    x ∈ unitaryTorusHom.range := by
  have hxTW : x ∈ (unitaryTorusHom.range : Set U62S) * (u62W : Set U62S) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ u62W_le_normalizer]
    exact hx
  obtain ⟨t, ht, _, ⟨σ, hσ, rfl⟩, rfl⟩ := hxTW
  have hP1 : u62Perm u62C1 ∈ u62P :=
    Subgroup.mem_sup_right ⟨u62C1, ⟨(1, 0), by decide⟩, rfl⟩
  have hP2 : u62Perm u62C2 ∈ u62P :=
    Subgroup.mem_sup_right ⟨u62C2, ⟨(0, 1), by decide⟩, rfl⟩
  have hu1 : unitaryTorusHom (Multiplicative.ofAdd ⟨u62B1, u62B1_mem⟩) ∈ ⁅u62P, u62P⁆ := by
    rw [← u62Perm_commutator u62C1 ⟨u62A1, u62A1_mem⟩ ⟨u62B1, u62B1_mem⟩ (by decide)]
    exact Subgroup.commutator_mem_commutator hP1
      (Subgroup.mem_sup_left (⟨_, rfl⟩))
  have hu2 : unitaryTorusHom (Multiplicative.ofAdd ⟨u62B2, u62B2_mem⟩) ∈ ⁅u62P, u62P⁆ := by
    rw [← u62Perm_commutator u62C2 ⟨u62A2, u62A2_mem⟩ ⟨u62B2, u62B2_mem⟩ (by decide)]
    exact Subgroup.commutator_mem_commutator hP2
      (Subgroup.mem_sup_left (⟨_, rfl⟩))
  have key : ∀ u ∈ unitaryTorusHom.range, t * u62Perm σ * u = u * (t * u62Perm σ) →
      u62Perm σ * u = u * u62Perm σ := by
    intro u hu h
    have htu : t * u = u * t := u62T_comm ht hu
    calc u62Perm σ * u = t⁻¹ * (t * u62Perm σ * u) := by group
      _ = t⁻¹ * (u * (t * u62Perm σ)) := by rw [h]
      _ = t⁻¹ * (u * t) * u62Perm σ := by group
      _ = t⁻¹ * (t * u) * u62Perm σ := by rw [htu]
      _ = u * u62Perm σ := by group
  have h1 := key _ (⟨_, rfl⟩) (hc _ hu1)
  have h2 := key _ (⟨_, rfl⟩) (hc _ hu2)
  show t * u62Perm σ ∈ unitaryTorusHom.range
  rw [u62_eq_one hσ h1 h2, map_one, mul_one]
  exact ht

theorem u62_preimage_comm {K : Type*} [Group K] {π : K →* U62S}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K) (x y : K)
    (hx : π x ∈ unitaryTorusHom.range) (hy : π y ∈ unitaryTorusHom.range) : x * y = y * x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have h := CentralCoverThree.torusPairing_eq hπ unitaryTorusHom hker
    (a := Multiplicative.toAdd a) (b := Multiplicative.toAdd b) (y := x) (z := y)
    (by rw [ofAdd_toAdd]; exact ha.symm) (by rw [ofAdd_toAdd]; exact hb.symm)
  rw [CentralCoverThree.torusPairing_eq_one hπ unitaryTorusHom hker unitaryTorus_conj] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem u62_exists_U {K : Type*} [Group K] [Finite K] {π : K →* U62S}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K) :
    ∃ U : Subgroup K, (∀ u ∈ U, π u ∈ unitaryTorusHom.range) ∧ (∀ u ∈ U, u ^ 3 = 1) ∧
      81 ≤ Nat.card U := by
  have : IsMulCommutative (unitaryTorusHom.range.comap π) :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (u62_preimage_comm hπ hker x y x.2 y.2)
  have hexp : ∀ x : unitaryTorusHom.range.comap π,
      (π.subgroupComap unitaryTorusHom.range x) ^ 3 = 1 := fun x => by
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 (π.subgroupComap unitaryTorusHom.range x).2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ha, ← map_pow, CentralCoverThree.pow_three_eq_one_sumZero6,
      map_one]
    rfl
  obtain ⟨V, hV, hVcard⟩ := CentralCoverThree.exists_isElementaryAbelian_of_surjective_cube
    (π.subgroupComap unitaryTorusHom.range)
    (π.subgroupComap_surjective unitaryTorusHom.range hπ) hexp
    (CentralCoverThree.card_range_eq unitaryTorusHom unitaryTorusHom_eq_one_iff)
  refine ⟨V.map (unitaryTorusHom.range.comap π).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact v.2
  · rintro _ ⟨v, hv, rfl⟩
    have := hV
    have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := V) v hv
    simpa using congrArg Subtype.val h
  · rw [Subgroup.card_subtype, hVcard]
    norm_num

theorem bal207RankU62_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : Bal207RankU62 := by
  intro K _ _ hq hK _ α hα
  obtain ⟨⟨dd, hv⟩, hd, ⟨e⟩⟩ := hK
  obtain ⟨q, rfl, hp2, hf1⟩ : ∃ q, dd = .twistedA 5 q ∧ q.p = 2 ∧ q.exponent = 1 := by
    cases dd <;> first
      | exact absurd hd id
      | exact ⟨_, by rw [hd.1], hd.2.1, hd.2.2⟩
  have hL : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group .PSU 6 2 1 := by
    have h := CFSG.Models.lieModel_twistedA 5 q hv (MulEquiv.refl _)
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ = 2 :=
      (TauCeti.LieTypeIndex.characteristic_twistedA 5 q).trans hp2
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ = 1 :=
      (TauCeti.LieTypeIndex.fieldExponent_twistedA 5 q).trans hf1
    rwa [hc, hf] at h
  have hZ : Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤ 3 :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_torsion_le hGA hq e hL
      Nat.prime_three).trans (by decide)
  obtain ⟨-, ⟨-, F, _, _, hF, ⟨e'⟩⟩ | ⟨h0, -⟩⟩ := hL
  · have : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card F4 := by
      rw [← Nat.card_eq_fintype_card, hF, F4.card]
      norm_num
    let e₂ := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1)
    let π : K →* U62S :=
      ((e.trans e').trans e₂).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
    have hπ : Function.Surjective π :=
      ((e.trans e').trans e₂).surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center K :=
      (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' _) ((e.trans e').trans e₂)).trans
        (QuotientGroup.ker_mk' _)
    obtain ⟨U, hUT, hU3, hUc⟩ := u62_exists_U hπ hker.le
    exact u62Aux_main hπ hker hZ u62Sylow le_sup_left u62_commutator_le
      (fun x hx hc => u62_cent hx hc) (u62_preimage_comm hπ hker.le) hUT hU3 hUc α hα
  · exact absurd h0 (by norm_num)

end CFSG.HardMathSupport.Dickson.Bal207
