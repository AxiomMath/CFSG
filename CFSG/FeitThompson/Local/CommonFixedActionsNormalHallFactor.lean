module

public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Local.ConjugateFixedPointOrders
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Perm.Cycle.Type

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {J H : Type*} [Group J] [Group H] [MulDistribMulAction J H]

theorem mem_fixedPoints_subgroup_iff_le_stabilizer (Y : Subgroup J) (h : H) :
    h ∈ FixedPoints.subgroup Y H ↔ Y ≤ MulAction.stabilizer J h := by
  simp only [FixedPoints.mem_subgroup, Subtype.forall, SetLike.le_def,
    MulAction.mem_stabilizer_iff]
  rfl

theorem fixedPoints_subgroup_anti {Y Z : Subgroup J} (hYZ : Y ≤ Z) :
    FixedPoints.subgroup Z H ≤ FixedPoints.subgroup Y H := fun h hh =>
  (mem_fixedPoints_subgroup_iff_le_stabilizer Y h).2
    (hYZ.trans ((mem_fixedPoints_subgroup_iff_le_stabilizer Z h).1 hh))

theorem fixedPoints_subgroup_sup_eq_inf (Y Z : Subgroup J) :
    FixedPoints.subgroup ↥(Y ⊔ Z) H
      = FixedPoints.subgroup Y H ⊓ FixedPoints.subgroup Z H := by
  ext h
  simp only [Subgroup.mem_inf, mem_fixedPoints_subgroup_iff_le_stabilizer, sup_le_iff]

theorem fixedPoints_subgroup_top_eq :
    FixedPoints.subgroup ↥(⊤ : Subgroup J) H = FixedPoints.subgroup J H := by
  ext h
  rw [mem_fixedPoints_subgroup_iff_le_stabilizer, FixedPoints.mem_subgroup, top_le_iff,
    Subgroup.eq_top_iff']
  simp [MulAction.mem_stabilizer_iff]

theorem fixedPoints_subgroup_le (Y : Subgroup J) :
    FixedPoints.subgroup J H ≤ FixedPoints.subgroup Y H := by
  rw [← fixedPoints_subgroup_top_eq]
  exact fixedPoints_subgroup_anti le_top

theorem conj_smul_eq_map (g : J) (Y : Subgroup J) :
    MulAut.conj g • Y = Y.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]; rfl

theorem smul_fixedPoints_subgroup_of_normal (D : Subgroup J) [D.Normal] (a : J) :
    a • FixedPoints.subgroup D H = FixedPoints.subgroup D H := by
  rw [smul_fixedPoints_subgroup, ← conj_smul_eq_map, Subgroup.Normal.conj_smul_eq_self]

theorem fixedPoints_subgroup_eq_of_semidirect [Finite J] [Group.IsSolvable J] {D B : Subgroup J}
    [D.Normal] (hsup : D ⊔ B = ⊤) (hinf : D ⊓ B = ⊥)
    (hcop : (Nat.card D).Coprime (Nat.card B))
    (hD : ∀ Y : Subgroup J, Y ≠ ⊥ → Y ≤ D →
      FixedPoints.subgroup Y H = FixedPoints.subgroup D H)
    (hB : ∀ Y : Subgroup J, Y ≠ ⊥ → Y ≤ B →
      FixedPoints.subgroup Y H = FixedPoints.subgroup B H)
    (hDB : FixedPoints.subgroup D H = FixedPoints.subgroup B H)
    {X : Subgroup J} (hX : X ≠ ⊥) :
    FixedPoints.subgroup X H = FixedPoints.subgroup J H := by
  set C : Subgroup H := FixedPoints.subgroup D H with hC
  have hCJ : FixedPoints.subgroup J H = C := by
    rw [← fixedPoints_subgroup_top_eq, ← hsup, fixedPoints_subgroup_sup_eq_inf, ← hDB, inf_idem]
  have hcompl : B.IsComplement' D := isComplement'_of_sup_eq_top_of_inf_eq_bot hsup hinf
  have hDindex : D.index = Nat.card B := hcompl.index_eq_card
  have hBindex : B.index = Nat.card D := hcompl.symm.index_eq_card
  have hdisj : Disjoint (Nat.card D).primeFactors (Nat.card B).primeFactors :=
    hcop.disjoint_primeFactors
  obtain ⟨q, hqp, hqdvd⟩ : ∃ q, q.Prime ∧ q ∣ Nat.card X :=
    Nat.exists_prime_and_dvd (by simpa [Subgroup.card_eq_one] using hX)
  have _i : Fact q.Prime := ⟨hqp⟩
  obtain ⟨x, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) q hqdvd
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup J, Y = Subgroup.zpowers (x : J) := ⟨_, rfl⟩
  have hYX : Y ≤ X := by rw [hYdef, Subgroup.zpowers_le]; exact x.2
  have hYcard : Nat.card Y = q := by
    rw [hYdef, Nat.card_zpowers, Subgroup.orderOf_coe, hxo]
  have hYbot : Y ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩] at hYcard
    exact hqp.one_lt.ne hYcard
  have hYfac : (Nat.card Y).primeFactors = {q} := by rw [hYcard, hqp.primeFactors]
  have key : FixedPoints.subgroup Y H = C := by
    have hqJ : q ∣ Nat.card B * Nat.card D := by
      rw [hcompl.card_mul_card]
      exact hqdvd.trans X.card_subgroup_dvd_card
    rcases (Nat.Prime.dvd_mul hqp).1 hqJ with hqB | hqD
    ·
      have hqmemB : q ∈ (Nat.card B).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hqp, hqB, Nat.card_pos.ne'⟩
      have hBHall : IsHallSubgroup ((Nat.card B).primeFactors : Set ℕ) B :=
        ⟨isPiNumber_iff.2 fun p hp => Finset.mem_coe.2 hp,
          isPiNumber_iff.2 fun p hp => by
            rw [hBindex] at hp
            exact fun hp' => Finset.disjoint_left.1 hdisj hp (Finset.mem_coe.1 hp')⟩
      have hYpi : IsPiNumber ((Nat.card B).primeFactors : Set ℕ) (Nat.card Y) :=
        isPiNumber_iff.2 fun p hp => by
          rw [hYfac, Finset.mem_singleton] at hp
          exact hp ▸ Finset.mem_coe.2 hqmemB
      obtain ⟨K, hK, hYK⟩ := exists_isHallSubgroup_ge hYpi
      obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup hK hBHall
      have hYgB : MulAut.conj g • Y ≤ B :=
        hg ▸ (Subgroup.pointwise_smul_le_pointwise_smul_iff).2 hYK
      have hYgbot : MulAut.conj g • Y ≠ ⊥ := by
        intro h
        rw [conj_smul_eq_map,
          Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at h
        exact hYbot h
      have h1 : FixedPoints.subgroup ↥(MulAut.conj g • Y) H = C :=
        (hB _ hYgbot hYgB).trans hDB.symm
      have h2 : g • FixedPoints.subgroup Y H = C := by
        rw [smul_fixedPoints_subgroup, ← conj_smul_eq_map]; exact h1
      have h3 : FixedPoints.subgroup Y H = g⁻¹ • C := by rw [← h2, inv_smul_smul]
      rw [h3, hC, smul_fixedPoints_subgroup_of_normal]
    ·
      have hqmemD : q ∈ (Nat.card D).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hqp, hqD, Nat.card_pos.ne'⟩
      have hDHall : IsHallPiSubgroup ((Nat.card D).primeFactors : Set ℕ) D :=
        ⟨isPiSubgroup_iff.2 fun p hp => Finset.mem_coe.2 hp, fun p hp => by
          rw [hDindex] at hp
          exact fun hp' => Finset.disjoint_left.1 hdisj (Finset.mem_coe.1 hp') hp⟩
      have hYpi : IsPiSubgroup ((Nat.card D).primeFactors : Set ℕ) Y :=
        isPiSubgroup_iff.2 fun p hp => by
          rw [hYfac, Finset.mem_singleton] at hp
          exact hp ▸ Finset.mem_coe.2 hqmemD
      exact hD _ hYbot (hDHall.le_of_isPiSubgroup hYpi)
  refine le_antisymm ?_ (fixedPoints_subgroup_le X)
  rw [hCJ, ← key]
  exact fixedPoints_subgroup_anti hYX

theorem coe_fixedPoints_subgroup (Y : Subgroup J) :
    (FixedPoints.subgroup Y H : Set H)
      = {h : H | ∀ y ∈ Y, MulDistribMulAction.toMulAut J H y h = h} := by
  ext h
  simp only [SetLike.mem_coe, FixedPoints.mem_subgroup, Subtype.forall, Set.mem_ofPred_eq]
  rfl

theorem coe_fixedPoints_subgroup_self :
    (FixedPoints.subgroup J H : Set H)
      = {h : H | ∀ j : J, MulDistribMulAction.toMulAut J H j h = h} := by
  ext h
  simp only [SetLike.mem_coe, FixedPoints.mem_subgroup, Set.mem_ofPred_eq]
  rfl

end

public section

variable {J H : Type*} [Group J] [Group H] {ρ : J →* MulAut H}

theorem toMulAut_compHom (ρ : J →* MulAut H) :
    letI := MulDistribMulAction.compHom H ρ
    MulDistribMulAction.toMulAut J H = ρ := by
  let _ := MulDistribMulAction.compHom H ρ
  ext j h
  rfl

theorem coe_fixedPoints_subgroup_compHom (Y : Subgroup J) :
    letI := MulDistribMulAction.compHom H ρ
    (FixedPoints.subgroup Y H : Set H) = {h : H | ∀ y ∈ Y, ρ y h = h} := by
  let _ := MulDistribMulAction.compHom H ρ
  rw [coe_fixedPoints_subgroup, toMulAut_compHom]

theorem coe_fixedPoints_subgroup_self_compHom :
    letI := MulDistribMulAction.compHom H ρ
    (FixedPoints.subgroup J H : Set H) = {h : H | ∀ j : J, ρ j h = h} := by
  let _ := MulDistribMulAction.compHom H ρ
  rw [coe_fixedPoints_subgroup_self, toMulAut_compHom]

theorem fixedPoints_eq_of_semidirect_mulAut_hom [Finite J] [Group.IsSolvable J]
    {D B : Subgroup J} [D.Normal] (hsup : D ⊔ B = ⊤) (hinf : D ⊓ B = ⊥)
    (hcop : (Nat.card D).Coprime (Nat.card B))
    (hD : ∀ Y : Subgroup J, Y ≠ ⊥ → Y ≤ D →
      {h : H | ∀ y ∈ Y, ρ y h = h} = {h : H | ∀ y ∈ D, ρ y h = h})
    (hB : ∀ Y : Subgroup J, Y ≠ ⊥ → Y ≤ B →
      {h : H | ∀ y ∈ Y, ρ y h = h} = {h : H | ∀ y ∈ B, ρ y h = h})
    (hDB : {h : H | ∀ y ∈ D, ρ y h = h} = {h : H | ∀ y ∈ B, ρ y h = h})
    {X : Subgroup J} (hX : X ≠ ⊥) :
    {h : H | ∀ y ∈ X, ρ y h = h} = {h : H | ∀ j : J, ρ j h = h} := by
  let _ := MulDistribMulAction.compHom H ρ
  have htr : ∀ Y : Subgroup J, ((FixedPoints.subgroup Y H : Subgroup H) : Set H)
      = {h : H | ∀ y ∈ Y, ρ y h = h} := fun Y => coe_fixedPoints_subgroup_compHom Y
  have hset : ∀ Y Z : Subgroup J,
      ({h : H | ∀ y ∈ Y, ρ y h = h} = {h : H | ∀ y ∈ Z, ρ y h = h}) ↔
        FixedPoints.subgroup Y H = FixedPoints.subgroup Z H := fun Y Z => by
    rw [← htr Y, ← htr Z, SetLike.coe_set_eq]
  have hmain := fixedPoints_subgroup_eq_of_semidirect (H := H) hsup hinf hcop
    (fun Y hY hYD => (hset Y D).1 (hD Y hY hYD))
    (fun Y hY hYB => (hset Y B).1 (hB Y hY hYB)) ((hset D B).1 hDB) hX
  rw [← htr X, hmain, coe_fixedPoints_subgroup_self_compHom]

end

end CFSG.FeitThompson
