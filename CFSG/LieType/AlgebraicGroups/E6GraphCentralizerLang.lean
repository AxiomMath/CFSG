module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangOrbits
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.GraphFixedRootNormal
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.E6SignedGraphBruhat
public import CFSG.LieType.Chevalley.E6SignedGraphCollection
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  WithConv

open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k]

theorem twistedFixedGroup_id_eq (t : TwistTag) :
    twistedFixedGroup t k (RingHom.id k) = graphCentralizer t.tag k (diagramMap t k) := by
  ext g
  rw [twistedFixedGroup, Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr Iff.rfl ?_
  rw [mem_centralizer_singleton_iff_conj_eq]
  have h : twistHom t k (RingHom.id k) g = diagramMap t k * g * (diagramMap t k)⁻¹ := by
    apply Units.ext
    rw [coe_twistHom, entrywise_id]
    rfl
  change twistHom t k (RingHom.id k) g = g ↔ _
  rw [h]

variable [IsAlgClosed k]

theorem isPointIrreducible_e6DiagramCentralizer :
    IsPointIrreducible k (transportPoints (modGLPoint TwistTag.E6.tag k)
      (graphCentralizer TwistTag.E6.tag k (diagramMap TwistTag.E6 k))) := by
  have hZ := twistedFixedGroup_id_eq (k := k) TwistTag.E6
  let H : Option ({w // w ∈ relWeylTwist TwistTag.E6} × Fin TwistTag.E6.foldedTag.rank) →
      Subgroup (ModGL TwistTag.E6.tag k) := fun o => match o with
    | none => torusGroup TwistTag.E6.tag k ⊓
        graphCentralizer TwistTag.E6.tag k (diagramMap TwistTag.E6 k)
    | some i => rootSpan TwistTag.E6.tag k ((fun j => i.1.1 • (Pi.single j 1 :
        Fin TwistTag.E6.tag.rank → ℤ)) '' ↑(TwistTag.E6.orbit i.2)) ⊓
          twistedFixedGroup TwistTag.E6 k (RingHom.id k)
  let F : Option ({w // w ∈ relWeylTwist TwistTag.E6} × Fin TwistTag.E6.foldedTag.rank) →
      WordCurve TwistTag.E6.tag k := fun o => match o with
    | none => e6FixedTorusCurve k
    | some i => orbitConjCurve k i.1.1 i.2
  have hFH : ∀ o, (F o).values = (H o : Set (ModGL TwistTag.E6.tag k)) := by
    rintro (_ | ⟨⟨w, hw⟩, a⟩)
    · change (e6FixedTorusCurve k).values = _
      rw [values_e6FixedTorusCurve 1, rootDiagUnit_one, one_mul]
    · exact values_orbitConjCurve_eq hw a
  have hset := (fixed_root_generated_normal_subgroup TwistTag.E6 k (RingEquiv.refl k)).2.1
  have hgen := (fixed_positive_orbit_collection TwistTag.E6 k (RingEquiv.refl k)).2
  rw [RingEquiv.toRingHom_refl'] at hset hgen
  have hsup : graphCentralizer TwistTag.E6.tag k (diagramMap TwistTag.E6 k) = ⨆ o, H o := by
    refine le_antisymm (fun g hg => ?_) (iSup_le fun o => ?_)
    · rw [← hZ, ← SetLike.mem_coe, hset] at hg
      obtain ⟨h, hh, c, hc, rfl⟩ := Set.mem_mul.1 hg
      refine mul_mem (Subgroup.mem_iSup_of_mem none ?_) ?_
      · obtain ⟨hhT, hhZ⟩ := Subgroup.mem_inf.1 hh
        refine Subgroup.mem_inf.2 ⟨hhT, ?_⟩
        rw [← hZ]
        exact hhZ
      · rw [SetLike.mem_coe, hgen] at hc
        refine (Subgroup.closure_le _).2 ?_ hc
        rintro _ ⟨w, hw, a, c', rfl⟩
        refine Subgroup.mem_iSup_of_mem (some (⟨w, hw⟩, a)) ?_
        obtain ⟨e, he⟩ := (fixed_root_orbit_parametrization TwistTag.E6 k (RingHom.id k)).1 a w hw
        rw [← he c']
        exact (e _).2
    · rcases o with _ | ⟨⟨w, hw⟩, a⟩
      · exact inf_le_right
      · rw [← hZ]
        exact inf_le_right
  rw [hsup]
  exact isPointIrreducible_iSup_wordCurves F H hFH

open E6SignedGraph in
theorem isPointIrreducible_e6SignedCentralizer
    (hk : ringChar k ≠ 2) :
    IsPointIrreducible k (transportPoints (modGLPoint TwistTag.E6.tag k)
      (graphCentralizer TwistTag.E6.tag k
        (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k))) := by
  obtain ⟨-, -, -, hexists, -, -⟩ := E6_signed_graph_orbit_rank_one_groups k hk
  choose w hw a ha using hexists
  let H : Option {O // O ∈ orbits} → Subgroup (ModGL TwistTag.E6.tag k) := fun o => match o with
    | none => torusGroup TwistTag.E6.tag k ⊓ graphCentralizer TwistTag.E6.tag k
        (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k)
    | some O => orbitFixed k O.1
  let F : Option {O // O ∈ orbits} → WordCurve TwistTag.E6.tag k := fun o => match o with
    | none => e6FixedTorusCurve k
    | some O => signedOrbitCurve k (w O.1 O.2) (a O.1 O.2)
  have hFH : ∀ o, (F o).values = (H o : Set (ModGL TwistTag.E6.tag k)) := by
    rintro (_ | ⟨O, hO⟩)
    · exact values_e6FixedTorusCurve (signTuple k)
    · change (signedOrbitCurve k (w O hO) (a O hO)).values = (orbitFixed k O : Set _)
      rw [values_signedOrbitCurve_eq hk (hw O hO) (by rw [ha]; exact hO), ha]
  have hset := (E6_signed_graph_centralizer_Bruhat_structure k hk).1
  have hroot := (E6_signed_graph_positive_orbit_collection k hk).2.2.2.2.1
  have hsup : graphCentralizer TwistTag.E6.tag k
      (rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) = ⨆ o, H o := by
    refine le_antisymm (fun g hg => ?_) (iSup_le fun o => ?_)
    · change g ∈ fixedGroup k at hg
      rw [← SetLike.mem_coe, hset] at hg
      obtain ⟨h, hh, c, hc, rfl⟩ := Set.mem_mul.1 hg
      refine mul_mem (Subgroup.mem_iSup_of_mem none hh) ?_
      rw [SetLike.mem_coe, hroot] at hc
      refine (iSup₂_le fun O hO => ?_ : (⨆ O ∈ orbits, orbitFixed k O) ≤ ⨆ o, H o) hc
      exact le_iSup_of_le (some ⟨O, hO⟩) le_rfl
    · rcases o with _ | ⟨O, hO⟩
      · exact inf_le_right
      · exact inf_le_right
  rw [hsup]
  exact isPointIrreducible_iSup_wordCurves F H hFH

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem frobTwistGL_diagramMap_pow_mem
    {c : Fin TwistTag.E6.tag.rank → kˣ}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hcρ : (fun i => c (TwistTag.E6.perm.symm i)) = c)
    (e ε : ℕ) {g : ModGL TwistTag.E6.tag k}
    (hg : g ∈ graphCentralizer TwistTag.E6.tag k
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k)) :
    frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε) g ∈
      graphCentralizer TwistTag.E6.tag k
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k) := by
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  have hFrP : entrywiseFrobGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) =
      diagramMap TwistTag.E6 k := by
    simpa using entrywiseFrobGL_diagramMap_zpow TwistTag.E6 p e 1
  have hFrA : entrywiseFrobGL TwistTag.E6.tag k p e
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k) =
        rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k := by
    rw [map_mul, entrywiseFrobGL_rootDiagUnit p e hc, hFrP]
  have hPA : Commute (diagramMap TwistTag.E6 k)
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k) := by
    change _ * _ = _ * _
    rw [← mul_assoc, diagramMap_mul_rootDiagUnit, hcρ, mul_assoc]
  have hPεA := hPA.pow_left ε
  have hFg : Commute (entrywiseFrobGL TwistTag.E6.tag k p e g)
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k) := by
    change _ * _ = _ * _
    rw [← hFrA, ← map_mul, ← map_mul, hgc]
  rw [frobTwistGL_apply]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hQ := conj_mem_adjointGroup_of_map_eq
      (map_conj_diagramMap_zpow TwistTag.E6 k (ε : ℤ))
    rw [zpow_natCast] at hQ
    exact hQ _ (entrywiseFrobGL_mem p e hgG)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hPεA.mul_left hFg).mul_left hPεA.inv_left).eq

end Frobenius

open E6SignedGraph in
theorem E6_geometric_graph_centralizers_connected_Lang
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (A : ModGL TwistTag.E6.tag k)
    (hA : A = diagramMap TwistTag.E6 k ∨
      A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k) :
    (IsConnectedAlgebraicSubgroup k
        ((graphCentralizer TwistTag.E6.tag k A).map (modGLPoint TwistTag.E6.tag k).toMonoidHom) ∧
      subgroupIdeal (adjointPointSubgroup TwistTag.E6.tag k) ≤
        subgroupIdeal ((graphCentralizer TwistTag.E6.tag k A).map
          (modGLPoint TwistTag.E6.tag k).toMonoidHom) ∧
      Algebra.Smooth k (GLCoord k (Label TwistTag.E6.tag) ⧸
        subgroupIdeal ((graphCentralizer TwistTag.E6.tag k A).map
          (modGLPoint TwistTag.E6.tag k).toMonoidHom)) ∧
      ∃ eZ : WithConv ((GLCoord k (Label TwistTag.E6.tag) ⧸
          subgroupIdeal ((graphCentralizer TwistTag.E6.tag k A).map
            (modGLPoint TwistTag.E6.tag k).toMonoidHom)) →ₐ[k] k) ≃*
              graphCentralizer TwistTag.E6.tag k A, ∀ φ,
        ((eZ φ : graphCentralizer TwistTag.E6.tag k A) : ModGL TwistTag.E6.tag k) =
          (modGLPoint TwistTag.E6.tag k).symm
            (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) ∧
    ∀ e : ℕ, 1 ≤ e → ∀ ε : ℕ,
      ∃ σ : (GLCoord k (Label TwistTag.E6.tag) ⧸ subgroupIdeal ((graphCentralizer
          TwistTag.E6.tag k A).map (modGLPoint TwistTag.E6.tag k).toMonoidHom)) →ₐc[k]
            (GLCoord k (Label TwistTag.E6.tag) ⧸ subgroupIdeal ((graphCentralizer
              TwistTag.E6.tag k A).map (modGLPoint TwistTag.E6.tag k).toMonoidHom)),
        (∀ φ, (modGLPoint TwistTag.E6.tag k).symm (toConv ((pointMap σ φ).ofConv.comp
            (Ideal.Quotient.mkₐ k _))) =
          diagramMap TwistTag.E6 k ^ ε * Units.map (entrywiseHom (iterateFrobenius k p e))
            ((modGLPoint TwistTag.E6.tag k).symm
              (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) *
            (diagramMap TwistTag.E6 k ^ ε)⁻¹) ∧
        (∀ D ∈ tangentSpace k _ (Bialgebra.counitAlgHom k
            (GLCoord k (Label TwistTag.E6.tag) ⧸ subgroupIdeal ((graphCentralizer
              TwistTag.E6.tag k A).map (modGLPoint TwistTag.E6.tag k).toMonoidHom))),
          D ∘ₗ (σ : (GLCoord k (Label TwistTag.E6.tag) ⧸ subgroupIdeal ((graphCentralizer
            TwistTag.E6.tag k A).map (modGLPoint TwistTag.E6.tag k).toMonoidHom)) →ₐ[k]
              (GLCoord k (Label TwistTag.E6.tag) ⧸ subgroupIdeal ((graphCentralizer
                TwistTag.E6.tag k A).map
                  (modGLPoint TwistTag.E6.tag k).toMonoidHom))).toLinearMap = 0) ∧
        ∀ c ∈ graphCentralizer TwistTag.E6.tag k A, ∃ z ∈ graphCentralizer TwistTag.E6.tag k A,
          z⁻¹ * (diagramMap TwistTag.E6 k ^ ε *
            Units.map (entrywiseHom (iterateFrobenius k p e)) z *
              (diagramMap TwistTag.E6 k ^ ε)⁻¹) = c := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨c, hc, hcρ, rfl, hirr⟩ : ∃ c : Fin TwistTag.E6.tag.rank → kˣ,
      (∀ i, c i = 1 ∨ c i = -1) ∧ (fun i => c (TwistTag.E6.perm.symm i)) = c ∧
      A = rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k ∧
      IsPointIrreducible k (transportPoints (modGLPoint TwistTag.E6.tag k)
        (graphCentralizer TwistTag.E6.tag k A)) := by
    rcases hA with rfl | rfl
    · refine ⟨1, fun _ => Or.inl rfl, rfl, by rw [rootDiagUnit_one, one_mul],
        isPointIrreducible_e6DiagramCentralizer⟩
    · refine ⟨signTuple k, fun i => ?_, ?_, rfl, isPointIrreducible_e6SignedCentralizer hk⟩
      · by_cases hi : i = ⟨1, by decide⟩
        · rw [hi]
          exact Or.inr rfl
        · exact Or.inl (signTuple_of_ne hi)
      · funext i
        by_cases hi : i = ⟨1, by decide⟩
        · rw [hi]
          rfl
        · have hi' : TwistTag.E6.perm.symm i ≠ ⟨1, by decide⟩ := by
            intro h
            apply hi
            rw [← h]
            revert h
            revert i
            decide
          rw [signTuple_of_ne hi, signTuple_of_ne hi']
  obtain ⟨hZ, hGZ, hsm, heZ⟩ := graphCentralizer_realization _ hirr
  refine ⟨⟨hZ, hGZ, hsm, heZ⟩, fun e he ε => ?_⟩
  obtain ⟨σ, hpt, hzero, hlang⟩ := exists_frobTwist_restriction p hZ he
    (diagramMap TwistTag.E6 k ^ ε) fun g hg => frobTwistGL_diagramMap_pow_mem p hc hcρ e ε hg
  exact ⟨σ, hpt, hzero, hlang⟩

end CFSG.LieType.AlgebraicGroups
