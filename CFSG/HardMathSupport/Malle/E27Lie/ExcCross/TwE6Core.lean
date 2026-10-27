module

public import CFSG.LieType.Chevalley.LongestElement
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.RankThree.PartOne.KE.CTTwisted
public import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.Monster.B.Geometry.CoxeterWords

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CoxeterSystem

open scoped Matrix

set_option linter.unusedSectionVars false

section TwCore


local notation "ρ6" => TwistTag.E6.perm

theorem height_permLattice6 (v : Fin TwistTag.E6.tag.rank → ℤ) :
    height (permLattice ρ6 v) = height v := by
  simp only [height, permLattice, Function.comp_apply]
  exact Equiv.sum_comp TwistTag.E6.perm.symm v

theorem reversesSigns_of_negPerm {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u) :
    ReversesSigns w0 := fun α _ hpos => by
  rw [hw0, height_neg, height_permLattice6]
  exact neg_neg_of_pos hpos

theorem perm6_perm6 (i : Fin TwistTag.E6.tag.rank) : ρ6 (ρ6 i) = i := by
  have := e6_perm_symm_apply i
  rw [← this]
  exact TwistTag.E6.perm.apply_symm_apply i

theorem cartan_perm6 (i j : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.tag.cartan (ρ6 i) (ρ6 j) = TwistTag.E6.tag.cartan i j :=
  TwistTag.E6.cartan_perm i j

theorem reflect_neg6 (i : Fin TwistTag.E6.tag.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    reflect TwistTag.E6.tag i (-v) = -reflect TwistTag.E6.tag i v := by
  simp only [reflect, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_smul]
  abel

theorem weylGroup_comm_perm6 {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    (j : Fin TwistTag.E6.tag.rank) :
    w0 * (coxeterSystem TwistTag.E6.tag).simple j =
      (coxeterSystem TwistTag.E6.tag).simple (ρ6 j) * w0 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.E6.tag.rank → ℤ) fun u => ?_
  rw [mul_smul, mul_smul, hw0, simple_smul, simple_smul, hw0, reflect_neg6]
  congr 1
  exact permLattice_reflect cartan_perm6 j u

theorem canonicalRep_twist_comm6 {R : Type} [CommRing R] {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    (i : Fin TwistTag.E6.tag.rank) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) R w0 *
        weylElt TwistTag.E6.tag R (ρ6 i) 1 =
      weylElt TwistTag.E6.tag R i 1 * canonicalRep (coxeterSystem TwistTag.E6.tag) R w0 := by
  obtain ⟨wL, hmax, -, -, -, hlenL, hmul⟩ := weyl_longest_element TwistTag.E6.tag
  have hL : w0 = wL :=
    (reversesSigns_of_negPerm hw0).eq (reversesSigns_of_forall_length_le hmax)
  set cs := coxeterSystem TwistTag.E6.tag
  have hcomm : cs.simple i * w0 = w0 * cs.simple (ρ6 i) := by
    have := weylGroup_comm_perm6 hw0 (ρ6 i)
    rw [perm6_perm6] at this
    exact this.symm
  have hpos : 1 ≤ {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧
      0 < height α}.ncard := by
    have h1 := hmul (cs.simple i)
    rw [cs.length_simple] at h1
    rw [← hlenL]
    by_contra hlt
    have hz : cs.length wL = 0 := by omega
    rw [cs.length_eq_zero_iff] at hz
    have hsw : cs.length (cs.simple i * wL) = 1 := by rw [hz, mul_one, cs.length_simple]
    omega
  have hlen0 : cs.length w0 = {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧
      0 < height α}.ncard := by
    rw [hL, hlenL]
  have hlenu : cs.length (cs.simple i * w0) + 1 = cs.length w0 := by
    have h1 := hmul (cs.simple i)
    rw [cs.length_simple, ← hL] at h1
    omega
  obtain ⟨ω, hω, hωu⟩ := cs.exists_isReduced (cs.simple i * w0)
  have hω' : cs.length (cs.wordProd ω) = ω.length := hω
  have hw1 : cs.wordProd (i :: ω) = w0 := by
    rw [wordProd_cons, ← hωu, ← mul_assoc, cs.simple_mul_simple_self, one_mul]
  have hw2 : cs.wordProd (ω ++ [ρ6 i]) = w0 := by
    rw [wordProd_append, wordProd_singleton, ← hωu, hcomm, mul_assoc, cs.simple_mul_simple_self,
      mul_one]
  have hred1 : cs.IsReduced (i :: ω) := by
    show cs.length (cs.wordProd (i :: ω)) = (i :: ω).length
    rw [hw1, List.length_cons, ← hω', ← hωu]
    omega
  have hred2 : cs.IsReduced (ω ++ [ρ6 i]) := by
    show cs.length (cs.wordProd (ω ++ [ρ6 i])) = (ω ++ [ρ6 i]).length
    rw [hw2, List.length_append, List.length_singleton, ← hω', ← hωu]
    omega
  have h1 := canonicalRep_wordProd (R := R) hred1
  have h2 := canonicalRep_wordProd (R := R) hred2
  rw [hw1] at h1
  rw [hw2] at h2
  rw [List.map_cons, List.prod_cons] at h1
  rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton] at h2
  calc canonicalRep cs R w0 * weylElt TwistTag.E6.tag R (ρ6 i) 1 =
      (weylElt TwistTag.E6.tag R i 1 * (ω.map fun j => weylElt TwistTag.E6.tag R j 1).prod) *
        weylElt TwistTag.E6.tag R (ρ6 i) 1 := by rw [← h1]
    _ = weylElt TwistTag.E6.tag R i 1 *
        ((ω.map fun j => weylElt TwistTag.E6.tag R j 1).prod *
          weylElt TwistTag.E6.tag R (ρ6 i) 1) := mul_assoc _ _ _
    _ = weylElt TwistTag.E6.tag R i 1 * canonicalRep cs R w0 := by rw [← h2]


variable {L : Type} [Field L]

variable (L) in
@[expose] def tits6 : Subgroup (ModGL TwistTag.E6.tag L) :=
  Subgroup.closure (Set.range fun i : Fin TwistTag.E6.tag.rank => weylElt TwistTag.E6.tag L i 1)

theorem weylElt_mem_tits6 (i : Fin TwistTag.E6.tag.rank) :
    weylElt TwistTag.E6.tag L i 1 ∈ tits6 L :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem tits6_le_monomial : tits6 L ≤ monomialSubgroup TwistTag.E6.tag L :=
  (Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => weylElt_mem_monomialSubgroup i)

theorem canonicalRep_mem_tits6 (w : WeylGroup TwistTag.E6.tag) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∈ tits6 L :=
  canonicalRep_mem_closure _ L w

theorem weylElt_twistFixed6 (Fr : L →+* L) {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    (i : Fin TwistTag.E6.tag.rank) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) L w0 *
        twistHom TwistTag.E6 L Fr (weylElt TwistTag.E6.tag L i 1) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)⁻¹ = weylElt TwistTag.E6.tag L i 1 := by
  rw [twistHom_weylElt_one, canonicalRep_twist_comm6 hw0 i, mul_inv_cancel_right]

variable (L) in
@[expose] def X6 (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) : Subgroup (ModGL TwistTag.E6.tag L) :=
  twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)
    (twistHom TwistTag.E6 L Fr) ⊔ tits6 L

theorem X6_fix {Fr : L →+* L} {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u)
    {x : ModGL TwistTag.E6.tag L} (hx : x ∈ X6 L Fr w0) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) L w0 * twistHom TwistTag.E6 L Fr x *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)⁻¹ = x := by
  let Φ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)).toMonoidHom.comp
      (twistHom TwistTag.E6 L Fr)
  have hle : X6 L Fr w0 ≤ Φ.eqLocus (MonoidHom.id _) := by
    refine sup_le (fun y hy => (mem_twistedTorusOf.1 hy).2) ?_
    refine (Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => ?_)
    exact weylElt_twistFixed6 Fr hw0 i
  exact hle hx

theorem X6_le_monomial (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) :
    X6 L Fr w0 ≤ monomialSubgroup TwistTag.E6.tag L :=
  sup_le (fun y hy => (le_sup_left : torusGroup TwistTag.E6.tag L ≤ monomialSubgroup _ L)
    (mem_twistedTorusOf.1 hy).1) tits6_le_monomial

theorem X6_le_adjoint (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) :
    X6 L Fr w0 ≤ adjointGroup TwistTag.E6.tag L :=
  (X6_le_monomial Fr w0).trans monomialSubgroup_le_adjointGroup'

theorem tits6_le_X6 (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) : tits6 L ≤ X6 L Fr w0 :=
  le_sup_right

theorem twistedTorus_le_X6 (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) :
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)
      (twistHom TwistTag.E6 L Fr) ≤ X6 L Fr w0 :=
  le_sup_left


theorem card_rootsOfUnity_alg' [IsAlgClosed L] {n : ℕ} (hn : ((n : ℕ) : L) ≠ 0) :
    Nat.card (rootsOfUnity n L) = n := by
  have : NeZero n := ⟨fun h => hn (by rw [h]; simp)⟩
  have : NeZero (n : L) := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L n
  exact hζ.card_rootsOfUnity

theorem rootChar_neg6 (a : Fin TwistTag.E6.tag.rank → Lˣ) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

theorem mem_fixedCharTuples_neg_iff {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (a : Fin TwistTag.E6.tag.rank → Lˣ) :
    a ∈ fixedCharTuples (-1 : Matrix (Fin TwistTag.E6.tag.rank)
      (Fin TwistTag.E6.tag.rank) ℤ) Fr ↔ ∀ i, a i ^ (q + 1) = 1 := by
  have hF : ∀ u : Lˣ, (Units.map Fr.toMonoidHom u : Lˣ) = u ^ q := fun u =>
    Units.ext (by simp [hFr])
  have hneg : ∀ u : Fin TwistTag.E6.tag.rank → ℤ,
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) *ᵥ u = -u := fun u => by
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  constructor
  · intro h i
    have h1 := h (Pi.single i 1)
    rw [hneg, rootChar_neg6, CTTorus.rootChar_single, hF] at h1
    calc a i ^ (q + 1) = a i ^ q * a i := pow_succ _ _
      _ = a i ^ q * (a i ^ q)⁻¹ := by rw [← h1, inv_inv]
      _ = 1 := mul_inv_cancel _
  · intro h u
    have h1 : rootChar a u ^ (q + 1) = 1 := CTTorus.rootChar_pow_eq_one h u
    rw [hneg, rootChar_neg6, hF]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ']
    exact h1


theorem twistedTorus6_eq [IsAlgClosed L] (Fr : L →+* L) {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u) :
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)
        (twistHom TwistTag.E6 L Fr) =
      (fixedCharTuples (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
        Fr).map (rootDiagUnitHom TwistTag.E6.tag L) :=
  twistedTorus_E6_eq_map Fr w0 (-1) (fun x => by rw [hw0, Matrix.neg_mulVec, Matrix.one_mulVec])

theorem card_twistedTorus6 [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : (((q + 1 : ℕ)) : L) ≠ 0) {w0 : WeylGroup TwistTag.E6.tag}
    (hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w0 • u = -permLattice ρ6 u) :
    Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)
      (twistHom TwistTag.E6 L Fr)) = (q + 1) ^ 6 := by
  rw [twistedTorus6_eq Fr hw0,
    Nat.card_congr (Subgroup.equivMapOfInjective _ (rootDiagUnitHom TwistTag.E6.tag L)
      (rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L))).toEquiv.symm]
  let ψ : (Fin TwistTag.E6.tag.rank → rootsOfUnity (q + 1) L) →*
      (Fin TwistTag.E6.tag.rank → Lˣ) :=
    MonoidHom.pi fun i => (rootsOfUnity (q + 1) L).subtype.comp (Pi.evalMonoidHom _ i)
  have hψ : Function.Injective ψ := by
    intro f g h
    funext i
    exact Subtype.ext (congrFun h i)
  have hrange : ψ.range = fixedCharTuples (-1 : Matrix (Fin TwistTag.E6.tag.rank)
      (Fin TwistTag.E6.tag.rank) ℤ) Fr := by
    ext a
    rw [mem_fixedCharTuples_neg_iff hFr]
    constructor
    · rintro ⟨f, rfl⟩ i
      exact (mem_rootsOfUnity _ _).1 (f i).2
    · intro h
      exact ⟨fun i => ⟨a i, (mem_rootsOfUnity _ _).2 (h i)⟩, rfl⟩
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm, Nat.card_fun,
    card_rootsOfUnity_alg' hq, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end TwCore

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
