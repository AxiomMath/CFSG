module

public import CFSG.FeitThompson.OddOrder.AbelianIrreducibleEnvelopingField
public import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
public import CFSG.FeitThompson.Foundations.FiniteFieldUnitsCyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Pointwise

private lemma sq_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hq
  simp only [Nat.add_sub_cancel_left]
  ring_nf
  omega

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def scalarsHom (k V : Type*) [Field k] [AddCommGroup V] [Module k V] : kˣ →* (V ≃ₗ[k] V) where
  toFun a := DistribMulAction.toLinearEquiv k V a
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp [mul_smul]

@[simp] lemma scalarsHom_apply (a : kˣ) (v : V) : scalarsHom k V a v = (a : k) • v := (rfl)

def scalarSubgroup (k V : Type*) [Field k] [AddCommGroup V] [Module k V] :
    Subgroup (V ≃ₗ[k] V) := (scalarsHom k V).range

lemma mem_scalarSubgroup_iff {f : V ≃ₗ[k] V} :
    f ∈ scalarSubgroup k V ↔ ∃ a : kˣ, ∀ v : V, f v = (a : k) • v := by
  simp only [scalarSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, fun v => by simp⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by ext v; simp [ha]⟩

lemma scalarsHom_mem_scalarSubgroup (a : kˣ) : scalarsHom k V a ∈ scalarSubgroup k V := ⟨a, rfl⟩

lemma inf_scalarSubgroup_eq_bot_iff {A : Subgroup (V ≃ₗ[k] V)} :
    A ⊓ scalarSubgroup k V = ⊥ ↔
      ∀ a ∈ A, (∃ c : kˣ, ∀ v : V, a v = (c : k) • v) → a = 1 := by
  rw [eq_bot_iff]
  refine ⟨fun h a ha hc => h ⟨ha, mem_scalarSubgroup_iff.2 hc⟩,
    fun h a ha => h a ha.1 (mem_scalarSubgroup_iff.1 ha.2)⟩

variable {A : Subgroup (V ≃ₗ[k] V)}

noncomputable def envelopingScalars (A : Subgroup (V ≃ₗ[k] V)) [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional k V] :
    Subgroup (↥(envelopingSubalgebra A))ˣ :=
  (Units.map (algebraMap k ↥(envelopingSubalgebra A)).toMonoidHom).range

lemma mem_envelopingScalars_iff [IsMulCommutative A] [(linearGroupRep A).IsIrreducible]
    [FiniteDimensional k V] {u : (↥(envelopingSubalgebra A))ˣ} :
    u ∈ envelopingScalars A ↔
      ∃ c : kˣ, ((u : ↥(envelopingSubalgebra A)) : Module.End k V) = (c : k) • 1 := by
  simp only [envelopingScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by simp [Algebra.algebraMap_eq_smul_one]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, Units.ext (Subtype.ext ?_)⟩
    simpa [Algebra.algebraMap_eq_smul_one] using hc.symm

lemma natCard_envelopingScalars [Finite k] [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional k V] :
    Nat.card (envelopingScalars A) = Nat.card k - 1 := by
  have : Nontrivial V := nontrivial_of_isIrreducible_linearGroupRep A
  have hinj : Function.Injective
      (Units.map (algebraMap k ↥(envelopingSubalgebra A)).toMonoidHom) :=
    Units.map_injective (f := (algebraMap k ↥(envelopingSubalgebra A)).toMonoidHom)
      injective_algebraMap_envelopingSubalgebra
  rw [envelopingScalars, ← Nat.card_units (α := k)]
  exact (Nat.card_congr (Equiv.ofInjective _ hinj)).symm

lemma inf_range_unitsHom_envelopingScalars_eq_bot [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional k V]
    (hA : A ⊓ scalarSubgroup k V = ⊥) :
    (unitsHom A).range ⊓ envelopingScalars A = ⊥ := by
  have : Nontrivial V := nontrivial_of_isIrreducible_linearGroupRep A
  rw [eq_bot_iff]
  rintro x ⟨⟨a, rfl⟩, hx⟩
  obtain ⟨c, hc⟩ := mem_envelopingScalars_iff.1 hx
  rw [coe_unitsHom] at hc
  have hmem : (a : V ≃ₗ[k] V) ∈ A ⊓ scalarSubgroup k V := by
    refine ⟨a.2, mem_scalarSubgroup_iff.2 ⟨c, fun v => ?_⟩⟩
    simpa using congrArg (fun f : Module.End k V => f v) hc
  rw [hA] at hmem
  have : a = 1 := Subtype.ext (hmem : (a : V ≃ₗ[k] V) = 1)
  simp [this]

theorem isCyclic_of_abelian_irreducible [Finite k] [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional k V] : IsCyclic A := by
  have : Finite ↥(envelopingSubalgebra A) := Module.finite_of_finite (R := k)
  have : IsCyclic (↥(envelopingSubalgebra A))ˣ :=
    isCyclic_units_of_finite_field ↥(envelopingSubalgebra A)
  exact isCyclic_of_injective (unitsHom A) injective_unitsHom

theorem natCard_mul_natCard_sub_one_dvd [Finite k] [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] [FiniteDimensional k V]
    (hA : A ⊓ scalarSubgroup k V = ⊥) :
    Nat.card A * (Nat.card k - 1) ∣ Nat.card ↥(envelopingSubalgebra A) - 1 := by
  have hntV : Nontrivial V := nontrivial_of_isIrreducible_linearGroupRep A
  have hfinF : Finite ↥(envelopingSubalgebra A) := Module.finite_of_finite (R := k)
  set F := ↥(envelopingSubalgebra A)
  set H := (unitsHom A).range with hH
  set K := envelopingScalars A with hK
  have hbot : H ⊓ K = ⊥ := inf_range_unitsHom_envelopingScalars_eq_bot hA
  have hHK : ((H ⊔ K : Subgroup Fˣ) : Set Fˣ) = (H : Set Fˣ) * (K : Set Fˣ) :=
    Subgroup.mul_normal H K
  have h1 : Nat.card ((H : Set Fˣ) * (K : Set Fˣ)) * Nat.card (H ⊓ K : Subgroup Fˣ)
      = Nat.card H * Nat.card K := natCard_mul_mul_natCard_inf H K
  rw [hbot, Subgroup.card_bot, mul_one] at h1
  have h2 : Nat.card (H ⊔ K : Subgroup Fˣ) = Nat.card H * Nat.card K := by
    rw [← h1]; exact Nat.card_congr (Set.equivOfEq hHK)
  have hdvd : Nat.card (H ⊔ K : Subgroup Fˣ) ∣ Nat.card Fˣ :=
    Subgroup.card_subgroup_dvd_card _
  have hcardH : Nat.card H = Nat.card A :=
    (Nat.card_congr (Equiv.ofInjective _ injective_unitsHom)).symm
  rw [h2, hcardH, hK, natCard_envelopingScalars, Nat.card_units (α := F)] at hdvd
  exact hdvd

theorem natCard_dvd_natCard_add_one [Finite k] [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] (hV : finrank k V = 2)
    (hA : A ⊓ scalarSubgroup k V = ⊥) : Nat.card A ∣ Nat.card k + 1 := by
  have hfd : FiniteDimensional k V := FiniteDimensional.of_finrank_pos (by omega)
  have hq2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have hF : Nat.card ↥(envelopingSubalgebra A) = Nat.card k ^ 2 := by
    rw [natCard_envelopingSubalgebra, hV]
  have h := natCard_mul_natCard_sub_one_dvd hA
  rw [hF, sq_sub_one_eq _ (by omega)] at h
  exact (Nat.mul_dvd_mul_iff_right (show 0 < Nat.card k - 1 by omega)).mp h

theorem isCyclic_and_natCard_dvd_add_one_zmod {p : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {A : Subgroup (V ≃ₗ[ZMod p] V)} [IsMulCommutative A]
    [(linearGroupRep A).IsIrreducible] (hV : finrank (ZMod p) V = 2)
    (hA : A ⊓ scalarSubgroup (ZMod p) V = ⊥) : IsCyclic A ∧ Nat.card A ∣ p + 1 := by
  have hfd : FiniteDimensional (ZMod p) V := FiniteDimensional.of_finrank_pos (by omega)
  refine ⟨isCyclic_of_abelian_irreducible, ?_⟩
  simpa [Nat.card_zmod] using natCard_dvd_natCard_add_one hV hA

end

end CFSG.FeitThompson
