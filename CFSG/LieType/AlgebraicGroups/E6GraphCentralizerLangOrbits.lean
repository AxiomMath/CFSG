module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LieType.Chevalley.E6SignedGraphRankOneGroups
public import CFSG.LieType.Chevalley.E6SignedGraphPerfect
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.Monster.B.Geometry.CoxeterWords

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv

open scoped CFSG.ConvolutionPoints

section Unsigned

variable {t : TwistTag}

variable (t) in
@[expose] def orbitConjWord
    (R : Type) [CommRing R] (w : WeylGroup t.tag)
    (a : Fin t.foldedTag.rank) (c : R) : List (Letter t.tag × R) :=
  canonicalWord t.tag R w ++
    (List.range (t.orbit a).card).map (fun m => (((t.perm ^ m) (t.orbitMin a), true), c)) ++
    invWord (canonicalWord t.tag R w)

variable {R S : Type} [CommRing R] [CommRing S]

theorem mapWord_orbitConjWord
    (f : R →+* S) (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank)
    (c : R) : mapWord f (orbitConjWord t R w a c) = orbitConjWord t S w a (f c) := by
  rw [orbitConjWord, orbitConjWord, mapWord_append, mapWord_append, mapWord_invWord,
    mapWord_canonicalWord]
  simp [mapWord]

theorem wordUnit_orbitConjWord
    (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank) (c : R) :
    wordUnit t.tag R (orbitConjWord t R w a c) = canonicalRep (coxeterSystem t.tag) R w *
      ((List.range (t.orbit a).card).map fun m =>
        xUnit t.tag R ((t.perm ^ m) (t.orbitMin a)) c).prod *
        (canonicalRep (coxeterSystem t.tag) R w)⁻¹ := by
  rw [orbitConjWord, wordUnit_append, wordUnit_append, wordUnit_invWord, wordUnit_canonicalWord]
  congr 2
  simp [wordUnit, letterUnit, List.map_map, Function.comp_def]

variable {k : Type} [Field k]

theorem coe_orbitX_ringHomId
    (a : Fin t.foldedTag.rank) (c : orbitField t k (RingHom.id k) a) :
    (orbitX t k (RingHom.id k) a c : ModGL t.tag k) =
      ((List.range (t.orbit a).card).map fun m =>
        xUnit t.tag k ((t.perm ^ m) (t.orbitMin a)) (c : k)).prod := by
  rw [orbitX, Subgroup.val_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp [xElement]

theorem mem_orbitField_ringHomId (a : Fin t.foldedTag.rank) (c : k) :
    c ∈ orbitField t k (RingHom.id k) a := by
  change ((RingHom.id k) ^ (t.orbit a).card) c = (RingHom.id k) c
  simp

variable [IsAlgClosed k]

variable (k) in
@[expose] def orbitConjCurve
    (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank) :
    WordCurve t.tag k :=
  WordCurve.ofWord (Polynomial k) (orbitConjWord t (Polynomial k) w a Polynomial.X)
    (Polynomial.aeval 0) (by
      rw [mapWord_orbitConjWord, wordUnit_orbitConjWord]
      simp [xUnit_zero])

theorem values_orbitConjCurve
    (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank) :
    (orbitConjCurve k w a).values = Set.range fun c : orbitField t k (RingHom.id k) a =>
      canonicalRep (coxeterSystem t.tag) k w * (orbitX t k (RingHom.id k) a c : ModGL t.tag k) *
        (canonicalRep (coxeterSystem t.tag) k w)⁻¹ := by
  rw [orbitConjCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z Polynomial.X, mem_orbitField_ringHomId a _⟩, ?_⟩
    beta_reduce
    rw [coe_orbitX_ringHomId, mapWord_orbitConjWord, wordUnit_orbitConjWord]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨Polynomial.aeval (c : k), ?_⟩
    beta_reduce
    rw [coe_orbitX_ringHomId, mapWord_orbitConjWord, wordUnit_orbitConjWord]
    simp

theorem values_orbitConjCurve_eq
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (a : Fin t.foldedTag.rank) :
    (orbitConjCurve k w a).values = ((rootSpan t.tag k ((fun i => w • (Pi.single i 1 :
      Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓ twistedFixedGroup t k (RingHom.id k) :
        Subgroup (ModGL t.tag k)) : Set (ModGL t.tag k)) := by
  obtain ⟨e, he⟩ := (fixed_root_orbit_parametrization t k (RingHom.id k)).1 a w hw
  rw [values_orbitConjCurve]
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    beta_reduce
    rw [← he c]
    exact (e (Multiplicative.ofAdd c)).2
  · intro hg
    obtain ⟨c, hc⟩ := e.surjective ⟨g, hg⟩
    refine ⟨Multiplicative.toAdd c, ?_⟩
    beta_reduce
    rw [← he, ofAdd_toAdd, hc]

end Unsigned

section Signed

open E6SignedGraph

variable {R S : Type} [CommRing R] [CommRing S]

@[expose] def signedOrbitWord
    (R : Type) [CommRing R] (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (s c : R) : List (Letter TwistTag.E6.tag × R) :=
  canonicalWord TwistTag.E6.tag R w ++
    (if TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a then
      [((TwistTag.E6.orbitMin a, true), c)]
    else [((TwistTag.E6.orbitMin a, true), c),
      ((TwistTag.E6.perm (TwistTag.E6.orbitMin a), true), s * c)]) ++
    invWord (canonicalWord TwistTag.E6.tag R w)

theorem mapWord_signedOrbitWord
    (f : R →+* S) (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (s c : R) :
    mapWord f (signedOrbitWord R w a s c) = signedOrbitWord S w a (f s) (f c) := by
  unfold signedOrbitWord
  rw [mapWord_append, mapWord_append, mapWord_invWord, mapWord_canonicalWord]
  split_ifs <;> simp [mapWord]

variable {k : Type} [Field k]

theorem wordUnit_signedOrbitWord
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : k) :
    wordUnit TwistTag.E6.tag k (signedOrbitWord k w a (orbitSign k w a : k) c) =
      orbitSL2 k w a (uSL c) := by
  unfold signedOrbitWord
  rw [wordUnit_append, wordUnit_append, wordUnit_invWord, wordUnit_canonicalWord]
  split_ifs with h
  · rw [orbitSL2_uSL_single w h]
    simp [wordUnit, letterUnit]
  · rw [orbitSL2_uSL_pair w h]
    simp [wordUnit, letterUnit]

variable [IsAlgClosed k]

variable (k) in
@[expose] def signedOrbitCurve
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) : WordCurve TwistTag.E6.tag k :=
  WordCurve.ofWord (Polynomial k)
    (signedOrbitWord (Polynomial k) w a (Polynomial.C (orbitSign k w a : k)) Polynomial.X)
    (Polynomial.aeval 0) (by
      rw [mapWord_signedOrbitWord]
      simp only [AlgHom.coe_toRingHom, Polynomial.aeval_C, Polynomial.aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [wordUnit_signedOrbitWord, uSL_zero, map_one])

theorem values_signedOrbitCurve
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    (signedOrbitCurve k w a).values = Set.range fun c : k => orbitSL2 k w a (uSL c) := by
  rw [signedOrbitCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z Polynomial.X, ?_⟩
    beta_reduce
    rw [mapWord_signedOrbitWord]
    simp only [AlgHom.coe_toRingHom, ← wordUnit_signedOrbitWord]
    congr 2
    rw [← Polynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨Polynomial.aeval c, ?_⟩
    beta_reduce
    rw [mapWord_signedOrbitWord]
    simp only [AlgHom.coe_toRingHom, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact wordUnit_signedOrbitWord w a c

theorem values_signedOrbitCurve_eq
    (hk : ringChar k ≠ 2) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : orbitImage w a ∈ orbits) :
    (signedOrbitCurve k w a).values =
      ((orbitFixed k (orbitImage w a) : Subgroup (ModGL TwistTag.E6.tag k)) :
        Set (ModGL TwistTag.E6.tag k)) := by
  rw [values_signedOrbitCurve]
  exact ((E6_signed_graph_orbit_rank_one_groups k hk).2.2.2.2.2 w hw a ha).2.2.2.2.2.2.2.1

end Signed

end CFSG.LieType.AlgebraicGroups
