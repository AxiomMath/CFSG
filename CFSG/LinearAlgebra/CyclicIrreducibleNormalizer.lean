module

public import CFSG.LinearAlgebra.PrimeDegreeCommutant
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFieldNormalizer

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem innerAut_mem_commutant_of_normal
    {G H : Subgroup (GL (Fin n) K)} (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    {g : GL (Fin n) K} (hg : g ∈ G) {M : Matrix (Fin n) (Fin n) K}
    (hM : M ∈ commutant H) :
    Matrix.GeneralLinearGroup.innerAut g M ∈ commutant H := by
  rw [mem_commutant] at hM ⊢
  intro h hh
  rw [Matrix.GeneralLinearGroup.innerAut_apply, ← Matrix.coe_units_inv]
  have hunit1 : (g * (g⁻¹ * h * g) : GL (Fin n) K) = h * g := by group
  have hmat1 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((g⁻¹ * h * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_mul, hunit1, Units.val_mul]
  have hunit2 : ((g⁻¹ * h * g) * g⁻¹ : GL (Fin n) K) = g⁻¹ * h := by group
  have hmat2 : (((g⁻¹ * h * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [← Units.val_mul, hunit2, Units.val_mul]
  have hxh := hM (g⁻¹ * h * g) (hHn g⁻¹ (G.inv_mem hg) h hh)
  calc
    (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * M *
          (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
        = ((((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * M *
              (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            simp only [mul_assoc]
    _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((g⁻¹ * h * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) * M *
              (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hmat1]
    _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((((g⁻¹ * h * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * M) *
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            simp only [mul_assoc]
    _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (M * (((g⁻¹ * h * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) *
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hxh]
    _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M) *
          ((((g⁻¹ * h * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
            simp only [mul_assoc]
    _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M) *
          ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by rw [hmat2]
    _ = ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M *
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) *
              (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            simp only [mul_assoc]

omit [Finite K] in
theorem centralizer_le_commutant_units {H : Subgroup (GL (Fin n) K)} :
    Subgroup.centralizer (H : Set (GL (Fin n) K)) ≤
      (commutant H).toSubmonoid.units := by
  intro g hg
  refine Submonoid.mem_units_of_val_mem_inv_val_mem (commutant H).toSubmonoid ?_ ?_
  · change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ commutant H
    rw [mem_commutant]
    intro h hh
    exact congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
      (Subgroup.mem_centralizer_iff.mp hg h hh)
  · change (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∈ commutant H
    rw [mem_commutant]
    intro h hh
    exact congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
      (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hg) h hh)

@[expose] def cyclicCentralizerSubgroupToCentralizer {G H : Subgroup (GL (Fin n) K)} :
    (Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G →*
      Subgroup.centralizer (H : Set (GL (Fin n) K)) where
  toFun g := ⟨(g : G), g.property⟩
  map_one' := Subtype.ext rfl
  map_mul' := fun _ _ => Subtype.ext rfl

@[expose] def cyclicCentralizerToCommutantUnits {G H : Subgroup (GL (Fin n) K)} :
    (Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G →*
      (commutant H)ˣ :=
  (Submonoid.unitsEquivUnitsType (commutant H).toSubmonoid).toMonoidHom.comp
    ((Subgroup.inclusion (centralizer_le_commutant_units (H := H))).comp
      cyclicCentralizerSubgroupToCentralizer)

omit [Finite K] in
theorem cyclicCentralizerToCommutantUnits_apply {G H : Subgroup (GL (Fin n) K)}
    (g : (Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G) :
    (((cyclicCentralizerToCommutantUnits (G := G) (H := H) g : (commutant H)ˣ) : commutant H) :
      Matrix (Fin n) (Fin n) K) = ((g : G) : GL (Fin n) K) := rfl

omit [Finite K] in
theorem cyclicCentralizerToCommutantUnits_injective {G H : Subgroup (GL (Fin n) K)} :
    Function.Injective (cyclicCentralizerToCommutantUnits (G := G) (H := H)) := by
  intro a b h
  have h' := congrArg (fun u : (commutant H)ˣ => ((u : commutant H) : Matrix (Fin n) (Fin n) K)) h
  rw [cyclicCentralizerToCommutantUnits_apply, cyclicCentralizerToCommutantUnits_apply] at h'
  exact Subtype.ext (Subtype.ext (Units.ext h'))

@[expose] def cyclicCommutantAction {G H : Subgroup (GL (Fin n) K)}
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    G →* (commutant H ≃ₐ[K] commutant H) :=
  invariantSubalgebraAction (Matrix.GeneralLinearGroup.innerAut.comp G.subtype) (commutant H)
    (fun g _ hx => innerAut_mem_commutant_of_normal hHn g.2 hx)

omit [Finite K] in
theorem cyclicCommutantAction_apply_coe {G H : Subgroup (GL (Fin n) K)}
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (g : G) (x : commutant H) :
    (((cyclicCommutantAction (G := G) (H := H) hHn g) x : commutant H) :
      Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) K) *
          (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ := by
  change Matrix.GeneralLinearGroup.innerAut (g : GL (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) = _
  rw [Matrix.GeneralLinearGroup.innerAut_apply]

theorem cyclicCommutantAction_mem_ker_iff (hn : n.Prime) {G H : Subgroup (GL (Fin n) K)}
    (hHcyc : IsCyclic H) (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (g : G) :
    g ∈ (cyclicCommutantAction (G := G) (H := H) hHn).ker ↔
      ((g : G) : GL (Fin n) K) ∈ Subgroup.centralizer (H : Set (GL (Fin n) K)) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  letI : Field (commutant H) := commutantField (isIrreducibleOn_iff.mpr hHirr)
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhR : ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ commutant H :=
      mem_commutant_of_mem_of_isCyclic hHcyc hh
    have hfix : (((cyclicCommutantAction (G := G) (H := H) hHn g)
        ⟨((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hhR⟩ : commutant H) :
          Matrix (Fin n) (Fin n) K) = ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun e : commutant H ≃ₐ[K] commutant H =>
        ((e ⟨((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hhR⟩ : commutant H) :
          Matrix (Fin n) (Fin n) K)) hg
      simpa using h
    have hconj : (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹) =
        ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      calc
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹)
            = (((cyclicCommutantAction (G := G) (H := H) hHn g)
                ⟨((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hhR⟩ :
                  commutant H) : Matrix (Fin n) (Fin n) K) := by
              rw [cyclicCommutantAction_apply_coe]
        _ = ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := hfix
    rw [← Matrix.coe_units_inv] at hconj
    have hge : (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hthis := congrArg
      (fun X : Matrix (Fin n) (Fin n) K => X * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hconj
    rw [mul_assoc (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
        hge, mul_one] at hthis
    exact Units.ext hthis.symm
  · intro hmem
    change cyclicCommutantAction (G := G) (H := H) hHn g = 1
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [cyclicCommutantAction_apply_coe, ← Matrix.coe_units_inv]
    have hgR : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ commutant H := by
      rw [mem_commutant]
      intro h hh
      exact congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
        (Subgroup.mem_centralizer_iff.mp hmem h hh)
    have hxg : ((x : commutant H) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : commutant H) : Matrix (Fin n) (Fin n) K) :=
      congrArg (fun y : commutant H => ((y : commutant H) : Matrix (Fin n) (Fin n) K))
        (mul_comm x ⟨((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hgR⟩)
    have hge : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : commutant H) : Matrix (Fin n) (Fin n) K) *
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          = (((x : commutant H) : Matrix (Fin n) (Fin n) K) *
              ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
                (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            rw [hxg.symm]
      _ = ((x : commutant H) : Matrix (Fin n) (Fin n) K) *
              (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
            simp only [mul_assoc]
      _ = ((x : commutant H) : Matrix (Fin n) (Fin n) K) := by rw [hge, mul_one]

theorem cyclicCommutantAction_ker_eq (hn : n.Prime) {G H : Subgroup (GL (Fin n) K)}
    (hHcyc : IsCyclic H) (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    (cyclicCommutantAction (G := G) (H := H) hHn).ker =
      (Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G := by
  ext g
  exact cyclicCommutantAction_mem_ker_iff hn hHcyc hHirr hHn g

omit [Finite K] in
theorem cyclicCommutantAction_ker_index_dvd {G H : Subgroup (GL (Fin n) K)}
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    (cyclicCommutantAction (G := G) (H := H) hHn).ker.index ∣
      Nat.card (commutant H ≃ₐ[K] commutant H) :=
  invariantSubalgebraAction_ker_index_dvd
    (Matrix.GeneralLinearGroup.innerAut.comp G.subtype) (commutant H)
    (fun g _ hx => innerAut_mem_commutant_of_normal hHn g.2 hx)

theorem cyclicCentralizer_subgroupOf_normal (hn : n.Prime) {G H : Subgroup (GL (Fin n) K)}
    (hHcyc : IsCyclic H) (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ((Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G).Normal := by
  rw [← cyclicCommutantAction_ker_eq hn hHcyc hHirr hHn]
  infer_instance

theorem isCyclic_cyclicCentralizer_subgroupOf (hn : n.Prime) {G H : Subgroup (GL (Fin n) K)}
    (hHirr : IsIrreducibleMatrixRep H.subtype) :
    IsCyclic ((Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  letI : Field (commutant H) := commutantField (isIrreducibleOn_iff.mpr hHirr)
  letI : Finite (commutant H) := inferInstance
  haveI : Finite (commutant H)ˣ := inferInstance
  haveI : IsCyclic (commutant H)ˣ := inferInstance
  exact isCyclic_of_injective (cyclicCentralizerToCommutantUnits (G := G) (H := H))
    (cyclicCentralizerToCommutantUnits_injective (G := G) (H := H))

theorem card_cyclicCentralizer_subgroupOf_dvd (hn : n.Prime) {G H : Subgroup (GL (Fin n) K)}
    (hHcyc : IsCyclic H) (hHirr : IsIrreducibleMatrixRep H.subtype) :
    Nat.card ((Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G) ∣
      Nat.card K ^ n - 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  letI : Field (commutant H) := commutantField (isIrreducibleOn_iff.mpr hHirr)
  letI : Finite (commutant H) := inferInstance
  have h := Subgroup.card_dvd_of_injective (cyclicCentralizerToCommutantUnits (G := G) (H := H))
    (cyclicCentralizerToCommutantUnits_injective (G := G) (H := H))
  rwa [Nat.card_units (commutant H),
    natCard_commutant_eq_pow_of_prime_of_cyclic_irreducible hn hHirr hHcyc] at h

theorem index_cyclicCentralizer_subgroupOf_dvd (hn : n.Prime) {G H : Subgroup (GL (Fin n) K)}
    (hHcyc : IsCyclic H) (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ((Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G).index ∣ n := by
  have h := cyclicCommutantAction_ker_index_dvd (G := G) (H := H) hHn
  rw [cyclicCommutantAction_ker_eq hn hHcyc hHirr hHn,
    natCard_algEquiv_commutant_eq_of_prime_of_cyclic_irreducible hn hHirr hHcyc] at h
  exact h

theorem card_dvd_prime_mul_commutant_units (hn : n.Prime) {G H : Subgroup (GL (Fin n) K)}
    (hHcyc : IsCyclic H) (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    Nat.card G ∣ n * (Nat.card K ^ n - 1) := by
  rw [← Subgroup.card_mul_index
    ((Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G)]
  have hcard := card_cyclicCentralizer_subgroupOf_dvd hn (G := G) hHcyc hHirr
  have hidx := index_cyclicCentralizer_subgroupOf_dvd hn (G := G) hHcyc hHirr hHn
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul hcard hidx

theorem cyclic_centralizer_structure_of_cyclic_irreducible_normal (hn : n.Prime)
    {G H : Subgroup (GL (Fin n) K)} (hHG : H ≤ G)
    (hHn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hHcyc : IsCyclic H) (hHirr : IsIrreducibleMatrixRep H.subtype) :
    let Kc := (Subgroup.centralizer (H : Set (GL (Fin n) K))).subgroupOf G
    Kc.Normal ∧ IsCyclic Kc ∧ Nat.card Kc ∣ Nat.card K ^ n - 1 ∧
      Kc.index ∣ n ∧ Nat.card G ∣ n * (Nat.card K ^ n - 1) :=
  ⟨cyclicCentralizer_subgroupOf_normal hn hHcyc hHirr hHn,
    isCyclic_cyclicCentralizer_subgroupOf hn hHirr,
    card_cyclicCentralizer_subgroupOf_dvd hn hHcyc hHirr,
    index_cyclicCentralizer_subgroupOf_dvd hn hHcyc hHirr hHn,
    card_dvd_prime_mul_commutant_units hn hHcyc hHirr hHn⟩

end CFSG.LinearAlgebra
