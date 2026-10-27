module

public import CFSG.RankThree.PartOne.KD4L.TriDescent
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem excTri_twistedFixedGroup_D4_perfect {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {f : ℕ} (hf : 1 ≤ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) :
    Group.IsPerfect ↥(twistedFixedGroup TwistTag.D4 L Fr) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfin, hcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.ncard_pow_eq_self (L := L) 2 (3 * f)
      (by omega)
  let K : Subfield L := (iterateFrobenius L 2 (3 * f)).eqLocusField (RingHom.id L)
  have hset : (K : Set L) = {c : L | c ^ (2 ^ (3 * f)) = c} := by
    ext c
    change iterateFrobenius L 2 (3 * f) c = c ↔ _
    rw [iterateFrobenius_def]
    rfl
  have hfinK : Finite K := by
    have h1 : (K : Set L).Finite := by rw [hset]; exact hfin
    exact h1.to_subtype
  have hKcard : Nat.card K = (2 ^ f) ^ 3 := by
    have h1 : Nat.card K = (K : Set L).ncard := Nat.card_coe_set_eq (K : Set L)
    rw [h1, hset, hcard, ← pow_mul, mul_comm]
  haveI : CharP K 2 := (Algebra.charP_iff K L 2).2 inferInstance
  let σ : K →+* K := iterateFrobenius K 2 f
  have hσ : ∀ c, σ c = c ^ ((2 ^ f) ^ 1) := fun c => by
    change iterateFrobenius K 2 f c = _
    rw [iterateFrobenius_def, pow_one]
  let C₀ : Subgroup (ModGL TwistTag.D4.tag K) := graphFixedRootGroup TwistTag.D4 K σ
  have hsimple := CFSG.RankThree.PartOne.KD4L.isSimple_graphFixedRootGroup_triality
    (ℓ := 2) (d := f) Nat.prime_two hf (K := K) hKcard 1 (Or.inl rfl) σ hσ
  haveI : IsSimpleGroup C₀ := hsimple.1
  have hnc : ¬ IsMulCommutative C₀ := by
    intro hcomm
    obtain ⟨x, y, hxy⟩ := hsimple.2
    exact hxy (isMulCommutative_iff.1 hcomm x y)
  haveI : Group.IsPerfect C₀ :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  have hfixed₀ := CFSG.RankThree.PartOne.KD4L.d4_fixed_set_eq_map_general
    (ℓ := 2) (d := f) Nat.prime_two hf (K := K) hKcard (Ω := L) 1 (Or.inl rfl) σ hσ Fr hFr
  have hfixed : {g : ModGL TwistTag.D4.tag L | g ∈ adjointGroup TwistTag.D4.tag L ∧
      diagramMap TwistTag.D4 L ^ 1 * Units.map (entrywiseHom Fr) g *
        (diagramMap TwistTag.D4 L ^ 1)⁻¹ = g} =
      (C₀.map (baseChangeGL (algebraMap K L)) : Set (ModGL TwistTag.D4.tag L)) := by
    simpa only [C₀] using hfixed₀
  have hmap : twistedFixedGroup TwistTag.D4 L Fr =
      C₀.map (baseChangeGL (algebraMap K L)) := by
    ext g
    constructor
    · intro hg
      have hg' : g ∈ {g : ModGL TwistTag.D4.tag L | g ∈ adjointGroup TwistTag.D4.tag L ∧
          diagramMap TwistTag.D4 L ^ 1 * Units.map (entrywiseHom Fr) g *
            (diagramMap TwistTag.D4 L ^ 1)⁻¹ = g} := by
        rw [mem_twistedFixedGroup_iff_twistHom] at hg
        refine ⟨hg.1, ?_⟩
        have h := hg.2
        rwa [twistHom_apply] at h
      have hmem : g ∈ (C₀.map (baseChangeGL (algebraMap K L)) : Set _) := hfixed ▸ hg'
      exact hmem
    · intro hg
      rw [mem_twistedFixedGroup_iff_twistHom]
      have hg' : g ∈ {g : ModGL TwistTag.D4.tag L | g ∈ adjointGroup TwistTag.D4.tag L ∧
          diagramMap TwistTag.D4 L ^ 1 * Units.map (entrywiseHom Fr) g *
            (diagramMap TwistTag.D4 L ^ 1)⁻¹ = g} := hfixed.symm ▸ hg
      refine ⟨hg'.1, ?_⟩
      rw [twistHom_apply]
      simpa only [pow_one] using hg'.2
  let e₀ := Subgroup.equivMapOfInjective C₀ (baseChangeGL (algebraMap K L))
    (baseChangeGL_injective (algebraMap K L))
  let e : C₀ ≃* ↥(twistedFixedGroup TwistTag.D4 L Fr) :=
    e₀.trans (MulEquiv.subgroupCongr hmap.symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
