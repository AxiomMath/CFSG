module

public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagTorus

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TwistedDiag


variable {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)

@[expose] def n0 (Ω : Type) [Field Ω] : ModGL Tag.E6 Ω :=
  canonicalRep (coxeterSystem Tag.E6) Ω twE6W0

@[expose] def theta : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj (n0 Ω)).toMonoidHom.comp (twistE6 Ω Fr)

@[expose] def thetaFixed : Subgroup (ModGL Tag.E6 Ω) :=
  adjointGroup Tag.E6 Ω ⊓ MonoidHom.eqLocus (theta Fr) (MonoidHom.id _)

theorem theta_apply (g : ModGL Tag.E6 Ω) :
    theta Fr g = n0 Ω * twistE6 Ω Fr g * (n0 Ω)⁻¹ := rfl

theorem mem_thetaFixed {g : ModGL Tag.E6 Ω} :
    g ∈ thetaFixed Fr ↔ g ∈ adjointGroup Tag.E6 Ω ∧ theta Fr g = g := Iff.rfl

theorem rootChar_inv_tuple' (b : Fin Tag.E6.rank → Ωˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar b⁻¹ v = (rootChar b v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow', zpow_neg, Finset.prod_inv_distrib]

theorem theta_rootDiagUnit {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (b : Fin Tag.E6.rank → Ωˣ) :
    theta Fr (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 (b ^ q)⁻¹ := by
  have hb' : (fun i => Units.map Fr.toMonoidHom (b (e6Rho.symm i))) =
      (fun i => b (e6Rho.symm i)) ^ q := by
    funext i
    refine Units.ext ?_
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hFr]
    rfl
  rw [theta_apply, twistE6_rootDiagUnit, hb', eq_comm]
  refine (rootDiagUnit_eq_conj_canonicalRep_iff (K := Ω) _ _ twE6W0).2 fun v => ?_
  have hchar : rootChar ((fun i => b (e6Rho.symm i)) ^ q) v =
      rootChar b (permLattice e6Rho v) ^ q := by
    rw [CFSG.RankThree.Chevalley.rootChar_pow_tuple, ← rootChar_permLattice, CFSG.RankThree.E6.e6Rho_symm]
  rw [twE6W0_smul, rootChar_neg', rootChar_inv_tuple', CFSG.RankThree.Chevalley.rootChar_pow_tuple,
    inv_inv, hchar]

theorem theta_rootDiagUnit_eq_iff {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (b : Fin Tag.E6.rank → Ωˣ) :
    theta Fr (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b ↔ ∀ i, b i ^ (q + 1) = 1 := by
  rw [theta_rootDiagUnit Fr hFr]
  constructor
  · intro h i
    have h' := DiagTorus.rootDiagUnit_injective h
    have hi := congrFun h' i
    simp only [Pi.inv_apply, Pi.pow_apply] at hi
    rw [pow_succ, mul_eq_one_iff_eq_inv]
    exact inv_eq_iff_eq_inv.1 hi
  · intro h
    congr 1
    funext i
    simp only [Pi.inv_apply, Pi.pow_apply]
    rw [inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv, ← pow_succ]
    exact h i

@[expose] def powTuples (Ω : Type) [Field Ω] (n : ℕ) : Subgroup (Fin Tag.E6.rank → Ωˣ) :=
  Subgroup.pi Set.univ fun _ => rootsOfUnity n Ω

theorem mem_powTuples {n : ℕ} [NeZero n] {b : Fin Tag.E6.rank → Ωˣ} :
    b ∈ powTuples Ω n ↔ ∀ i, b i ^ n = 1 := by
  simp [powTuples, Subgroup.mem_pi, mem_rootsOfUnity]

theorem natCard_powTuples [IsAlgClosed Ω] {n : ℕ} (hn : (n : Ω) ≠ 0) :
    Nat.card (powTuples Ω n) = n ^ 6 := by
  have : NeZero (n : Ω) := ⟨hn⟩
  have : NeZero n := ⟨fun h => hn (by rw [h]; simp)⟩
  have := IsSepClosed.hasEnoughRootsOfUnity Ω n
  have hr : Nat.card (rootsOfUnity n Ω) = n := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n
  let e : powTuples Ω n ≃ (Fin Tag.E6.rank → rootsOfUnity n Ω) :=
    { toFun := fun b i => ⟨b.1 i, (Subgroup.mem_pi _).1 b.2 i (Set.mem_univ i)⟩
      invFun := fun c => ⟨fun i => (c i).1, (Subgroup.mem_pi _).2 fun i _ => (c i).2⟩
      left_inv := fun b => rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e, Nat.card_fun, hr]
  simp
  rfl

@[expose] def thetaTorus (Ω : Type) [Field Ω] (q : ℕ) : Subgroup (ModGL Tag.E6 Ω) :=
  (powTuples Ω (q + 1)).map (rootDiagUnitHom Tag.E6 Ω)

theorem natCard_thetaTorus [IsAlgClosed Ω] {q : ℕ} (hq : (q : Ω) = 0) :
    Nat.card (thetaTorus Ω q) = (q + 1) ^ 6 := by
  have hne : ((q + 1 : ℕ) : Ω) ≠ 0 := by
    rw [Nat.cast_add, hq, zero_add, Nat.cast_one]
    exact one_ne_zero
  rw [thetaTorus, Subgroup.card_map_of_injective DiagTorus.rootDiagUnit_injective,
    natCard_powTuples hne]

theorem mem_thetaTorus {q : ℕ} {x : ModGL Tag.E6 Ω} :
    x ∈ thetaTorus Ω q ↔ ∃ b : Fin Tag.E6.rank → Ωˣ, (∀ i, b i ^ (q + 1) = 1) ∧
      x = rootDiagUnit Tag.E6 b := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, mem_powTuples.1 hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, mem_powTuples.2 hb, rfl⟩

theorem torus_inf_thetaFixed [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) :
    torusGroup Tag.E6 Ω ⊓ thetaFixed Fr = thetaTorus Ω q := by
  ext x
  constructor
  · rintro ⟨hT, -, hx⟩
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
    exact mem_thetaTorus.2 ⟨b, (theta_rootDiagUnit_eq_iff Fr hFr b).1 hx, rfl⟩
  · intro hx
    obtain ⟨b, hb, rfl⟩ := mem_thetaTorus.1 hx
    exact ⟨rootDiagUnit_mem_torusGroup b, torusGroup_le_adjointGroup_E6
      (rootDiagUnit_mem_torusGroup b), (theta_rootDiagUnit_eq_iff Fr hFr b).2 hb⟩

end TwistedDiag

end CFSG.HardMathSupport.Lang.E6Descent
