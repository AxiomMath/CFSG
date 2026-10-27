module

public import CFSG.LieType.Chevalley.TwistedE6FieldTwoLeviCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoTailMaps

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.FourthResidue CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
open scoped commutatorElement

universe u

theorem twisted_E6_field_two_relative_root_and_Levi_cover_data :
    Function.Bijective (fun O : TwistTag.E6.diagramRootOrbits =>
      (⟨relRoot O, isRoot_relRoot O⟩ : {r // IsRoot Tag.F4 r})) ∧
    (∀ O : TwistTag.E6.diagramRootOrbits, ((O : Finset (Fin TwistTag.E6.tag.rank → ℤ)) :
        Set (Fin TwistTag.E6.tag.rank → ℤ)) = relFibre (relRoot O) ∧
      ∀ β ∈ (O : Finset (Fin TwistTag.E6.tag.rank → ℤ)),
        relRoot O = relProj β ∧ height (relRoot O) = height β) ∧
    (∀ (i : Fin 4) (v : Fin TwistTag.E6.tag.rank → ℤ),
      relProj (nativeReflT i • v) = simple .F4 i • relProj v) ∧
    (∀ i : Fin 4, nativeRep i ∈ graphFixedRootGroup TwistTag.E6 K barHom ∧
      ∀ r, (relRootGroup r).map (MulAut.conj (nativeRep i)).toMonoidHom =
        relRootGroup (simple .F4 i • r)) ∧
    (∀ w : WeylGroup .F4, ∃ w', IsLift w w' ∧
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w' ∈ graphFixedRootGroup TwistTag.E6 K barHom ∧
      ∀ r, (relRootGroup r).map
          (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom =
        relRootGroup (w • r)) ∧
    (∀ r, IsRoot .F4 r →
      Nat.card (relRootGroup r) = if f4Euclid r ⬝ᵥ f4Euclid r = 2 then 2 else 4) ∧
    (∀ r, IsRoot .F4 r → (∀ x ∈ relRootGroup r, ∀ y ∈ relRootGroup r, x * y = y * x) ∧
      ∀ x ∈ relRootGroup r, x * x = 1) ∧
    (∀ {k : ℕ} (e : Fin k → Fin Tag.F4.rank → ℤ), Function.Injective e →
      Set.range e = {r | IsRoot Tag.F4 r ∧ 0 < height r} →
      Set.BijOn (fun u : (j : Fin k) → relRootGroup (e j) =>
          (List.ofFn fun j => (u j : ModGL TwistTag.E6.tag K)).prod)
        Set.univ (graphFixedPosUnipotent TwistTag.E6 K barHom)) ∧
    Nat.card (graphFixedPosUnipotent TwistTag.E6 K barHom) = 2 ^ 36 ∧
    {r : Fin Tag.F4.rank → ℤ | IsRoot .F4 r ∧ 0 < height r ∧
      f4Euclid r ⬝ᵥ f4Euclid r = 2}.ncard = 12 ∧
    {r : Fin Tag.F4.rank → ℤ | IsRoot .F4 r ∧ 0 < height r ∧
      f4Euclid r ⬝ᵥ f4Euclid r = 1}.ncard = 12 ∧
    (∀ r s r' s' : Fin Tag.F4.rank → ℤ, IsRoot .F4 r → IsRoot .F4 s → IsRoot .F4 r' →
      IsRoot .F4 s' → r ≠ s → r ≠ -s → r' ≠ s' → r' ≠ -s' →
      f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid r' ⬝ᵥ f4Euclid r' →
      f4Euclid s ⬝ᵥ f4Euclid s = f4Euclid s' ⬝ᵥ f4Euclid s' →
      f4Euclid r ⬝ᵥ f4Euclid s = f4Euclid r' ⬝ᵥ f4Euclid s' →
      ∃ w : WeylGroup .F4, w • r = r' ∧ w • s = s' ∧ ∃ w', IsLift w w' ∧
        canonicalRep (coxeterSystem TwistTag.E6.tag) K w' ∈
          graphFixedRootGroup TwistTag.E6 K barHom ∧
        ∀ t, (relRootGroup t).map
            (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom =
          relRootGroup (w • t)) ∧
    (∀ r s : Fin Tag.F4.rank → ℤ, IsRoot .F4 r → IsRoot .F4 s → r ≠ s → r ≠ -s →
      ⁅relRootGroup r, relRootGroup s⁆ ≤ relSpan (relSupport r s) ∧
      (((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
            2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∨
          (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = 0)) → relSupport r s = {r + s}) ∧
      ((f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1) → relSupport r s = {r + s, r + 2 • s}) ∧
      ((f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1) → relSupport r s = {r + s, 2 • r + s}) ∧
      (¬((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
            2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∨
          (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = 0)) →
        ¬(f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1) →
        ¬(f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1) → relSupport r s = ∅)) ∧
    stdLevi fourthJ = groupD ⊓ stdFixedGroup ∧ Group.IsPerfect (stdLevi fourthJ) ∧
    LieModel (stdLevi fourthJ) .POmegaMinus 4 2 1 ∧
    (∀ r : Fin Tag.F4.rank → ℤ, r ⟨3, by decide⟩ = 0 → relRootGroup r ≤ leviT) ∧
    (∀ r : Fin Tag.F4.rank → ℤ, f4Euclid r 0 = 0 → relRootGroup r ≤ leviT) ∧
    (∀ r, IsRoot .F4 r → ∃ n ∈ graphFixedRootGroup TwistTag.E6 K barHom,
      relRootGroup r ≤ leviConj n) ∧
    (∀ r s, IsRoot .F4 r → IsRoot .F4 s →
      ((f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2) ∨
        f4Euclid r ⬝ᵥ f4Euclid r ≠ f4Euclid s ⬝ᵥ f4Euclid s ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = 0)) →
      ∃ n ∈ graphFixedRootGroup TwistTag.E6 K barHom,
        relRootGroup r ≤ leviConj n ∧ relRootGroup s ≤ leviConj n) ∧
    (∀ (g : stdGroup), (leviG.map (MulAut.conj g).toMonoidHom).map stdGroup.subtype =
      leviConj (g : ModGL Tag.E6 K)) ∧
    (∀ {E : Type u} [Group E] [Finite E] (η : E →* stdGroup), Function.Surjective η →
      η.ker ≤ Subgroup.center E → IsPGroup 2 η.ker → ∀ g : stdGroup,
        ∃ F : Subgroup E, F.map η = leviG.map (MulAut.conj g).toMonoidHom ∧
          (∀ x ∈ F, η x = 1 → x = 1) ∧ F ⊓ η.ker = ⊥ ∧
          (leviG.map (MulAut.conj g).toMonoidHom).comap η = F ⊔ η.ker) ∧
    (∀ {i j : Fin 4}, i < j → ∀ a b u d : Fin Tag.F4.rank → ℤ, IsRoot .F4 a → IsRoot .F4 b →
      f4Euclid a = Pi.single i 1 - Pi.single j 1 → f4Euclid b = Pi.single j 1 →
      f4Euclid u = Pi.single i 1 → f4Euclid d = Pi.single i 1 + Pi.single j 1 →
      ∀ x ∈ relRootGroup a, x ≠ 1 → ∃ φ : relRootGroup b ≃* relRootGroup u,
        ∀ v : relRootGroup b, ((φ v : ModGL TwistTag.E6.tag K))⁻¹ *
          ⁅x, (v : ModGL TwistTag.E6.tag K)⁆ ∈ relRootGroup d) :=
  ⟨relRoot_bijective, fun O => ⟨coe_eq_relFibre O, fun _ hβ => ⟨relRoot_eq hβ,
      height_relRoot O hβ⟩⟩,
    relProj_nativeRefl_smul, fun i => ⟨nativeRep_mem_root i, map_conj_nativeRep_relRootGroup i⟩,
    fun w => by
      obtain ⟨w', hw'⟩ := exists_relWeylTwist_lift w
      exact ⟨w', hw', canonicalRep_mem_root hw'.1, map_conj_relRootGroup hw'⟩,
    fun _ hr => card_relRootGroup hr, fun _ hr => relRootGroup_elementary hr,
    fun e he hrange => bijOn_prod_relRootGroup e he hrange, card_graphFixedPosUnipotent,
    ncard_posRoots_long, ncard_posRoots_short,
    fun _ _ _ _ hr hs hr' hs' hne hne' hne₂ hne₂' hl₁ hl₂ hip =>
      exists_pair_conj hr hs hr' hs' hne hne' hne₂ hne₂' hl₁ hl₂ hip,
    fun _ _ hr hs hne hne' => ⟨commutator_relRootGroup_le hr hs hne hne',
      relSupport_cases hr hs hne hne'⟩,
    stdLevi_fourthJ, isPerfect_stdLevi_fourthJ, lieModel_stdLevi_fourthJ,
    fun _ h3 => relRootGroup_le_leviT h3, fun _ h => relRootGroup_le_leviT_of_euclid h,
    fun _ hr => by
      obtain ⟨n, hn, h, -⟩ := exists_conj_levi_root hr
      exact ⟨n, hn, h⟩,
    fun _ _ hr hs htype => exists_conj_levi_pair hr hs htype, map_subtype_leviG_conj,
    fun η hη hC h2 g => exists_split_conj_stdLevi η hη hC h2 g,
    fun hij _ _ _ _ ha hb ea eb eu ed x hx hx1 =>
      exists_tail_commutator_equiv_euclid hij ha hb ea eb eu ed hx hx1⟩

end CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover
