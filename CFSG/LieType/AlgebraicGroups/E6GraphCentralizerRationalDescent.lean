module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalBase
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLang

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {k : Type} [Field k] [IsAlgClosed k] {p : ℕ} [Fact p.Prime] [CharP k p] (e : ℕ)

theorem signTuple_eq_one_or (K : Type) [Field K] (i : Fin TwistTag.E6.tag.rank) :
    E6SignedGraph.signTuple K i = 1 ∨ E6SignedGraph.signTuple K i = -1 := by
  by_cases hi : i = ⟨1, by decide⟩
  · rw [hi]
    exact Or.inr rfl
  · exact Or.inl (E6SignedGraph.signTuple_of_ne hi)

theorem signTuple_perm_symm (K : Type) [Field K] :
    (fun i => E6SignedGraph.signTuple K (TwistTag.E6.perm.symm i)) =
      E6SignedGraph.signTuple K := by
  funext i
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
    rw [E6SignedGraph.signTuple_of_ne hi, E6SignedGraph.signTuple_of_ne hi']

theorem units_map_signTuple {K L : Type} [Field K] [Field L] (f : K →+* L) :
    (fun i => Units.map f.toMonoidHom (E6SignedGraph.signTuple K i)) =
      E6SignedGraph.signTuple L := by
  funext i
  by_cases hi : i = ⟨1, by decide⟩
  · rw [hi]
    apply Units.ext
    show f ((-1 : Kˣ) : K) = ((-1 : Lˣ) : L)
    rw [Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, map_neg, map_one]
  · rw [E6SignedGraph.signTuple_of_ne hi, E6SignedGraph.signTuple_of_ne hi, map_one]

theorem iterateFrobeniusEquiv_toRingHom :
    (iterateFrobeniusEquiv k p e).toRingHom = iterateFrobenius k p e :=
  RingHom.ext fun _ => rfl

theorem rationalFixedGroup_subset_diagram :
    (rationalFixedGroup (iterateFrobeniusEquiv k p e)
      (rootDiagUnit TwistTag.E6.tag 1 *
        diagramMap TwistTag.E6 (fixSubfield (iterateFrobeniusEquiv k p e))) :
          Set (ModGL TwistTag.E6.tag k)) ⊆
      (rationalFixedTorus (iterateFrobeniusEquiv k p e)
        (rootDiagUnit TwistTag.E6.tag 1 *
          diagramMap TwistTag.E6 (fixSubfield (iterateFrobeniusEquiv k p e))) :
            Set (ModGL TwistTag.E6.tag k)) *
        (rationalRootGroup (iterateFrobeniusEquiv k p e)
          (rootDiagUnit TwistTag.E6.tag 1 *
            diagramMap TwistTag.E6 (fixSubfield (iterateFrobeniusEquiv k p e))) :
              Set (ModGL TwistTag.E6.tag k)) := by
  set σq := iterateFrobeniusEquiv k p e with hσq
  set Kq := fixSubfield σq
  set AK := rootDiagUnit TwistTag.E6.tag (1 : Fin TwistTag.E6.tag.rank → Kqˣ) *
    diagramMap TwistTag.E6 Kq with hAK
  have hA : CFSG.LieType.Chevalley.baseChangeGL Kq.subtype AK = diagramMap TwistTag.E6 k := by
    rw [hAK, baseChangeGL_rootDiagUnit_mul_diagramMap]
    have h1 : (fun i => Units.map Kq.subtype.toMonoidHom
        ((1 : Fin TwistTag.E6.tag.rank → Kqˣ) i)) = 1 := by
      funext i
      exact map_one _
    rw [h1, rootDiagUnit_one, one_mul]
  have hZk : graphCentralizer TwistTag.E6.tag k
      (CFSG.LieType.Chevalley.baseChangeGL Kq.subtype AK) =
        twistedFixedGroup TwistTag.E6 k (RingHom.id k) := by
    rw [hA, twistedFixedGroup_id_eq]
  have hZK : graphCentralizer TwistTag.E6.tag Kq AK =
      twistedFixedGroup TwistTag.E6 Kq (RingHom.id Kq) := by
    rw [twistedFixedGroup_id_eq, hAK, rootDiagUnit_one, one_mul]
  intro g hg
  obtain ⟨hgZ, hgF⟩ := Subgroup.mem_inf.1 hg
  rw [hZk] at hgZ
  have hgF' : Units.map (entrywiseHom σq.toRingHom) g = g := hgF
  have hσ : Function.Surjective (RingHom.id k) := Function.surjective_id
  have hgC : g ∈ (adjointGroup TwistTag.E6.tag k : Set (ModGL TwistTag.E6.tag k)) := hgZ.1
  rw [adjointGroup_eq_iUnion_bruhatCell] at hgC
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hgC
  obtain ⟨hδ, b, hb, u, hu, rfl⟩ := exists_fixed_bruhat_factor hσ hgZ hw
  obtain ⟨hbB, -⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨huI, huZ⟩ := Subgroup.mem_inf.1 hu
  have h1 : Units.map (entrywiseHom σq.toRingHom) b *
      canonicalRep (coxeterSystem TwistTag.E6.tag) k w * Units.map (entrywiseHom σq.toRingHom) u =
        b * canonicalRep (coxeterSystem TwistTag.E6.tag) k w * u := by
    calc Units.map (entrywiseHom σq.toRingHom) b *
          canonicalRep (coxeterSystem TwistTag.E6.tag) k w *
            Units.map (entrywiseHom σq.toRingHom) u =
        Units.map (entrywiseHom σq.toRingHom) b *
          Units.map (entrywiseHom σq.toRingHom) (canonicalRep (coxeterSystem TwistTag.E6.tag) k w) *
            Units.map (entrywiseHom σq.toRingHom) u := by rw [entrywise_canonicalRep σq w]
      _ = _ := by rw [← map_mul, ← map_mul, hgF']
  have h2 := (bijOn_bruhatCell (K := k) w).2.1
    (Set.mk_mem_prod (entrywise_mem_borelGroup (σ := σq) hbB)
      (entrywise_mem_rootSpan (σ := σq) huI))
    (Set.mk_mem_prod hbB huI) h1
  simp only [Prod.mk.injEq] at h2
  obtain ⟨hFb, hFu⟩ := h2
  rw [← SetLike.mem_coe, graphFixedBorel_eq_mul hσ] at hb
  obtain ⟨h, hh, u', hu', rfl⟩ := Set.mem_mul.1 hb
  obtain ⟨hhT, hhZ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨hu'U, hu'Z⟩ := Subgroup.mem_inf.1 hu'
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := triangular_borel_structure.{0, 0} TwistTag.E6.tag k
  rw [map_mul] at hFb
  obtain ⟨hFh, hFu'⟩ := huniq _ (entrywise_mem_torusGroup (σ := σq) hhT) _ hhT _
    (entrywise_mem_rootSpan (σ := σq) hu'U) _ hu'U hFb
  have hJ : ∀ {x}, x ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) →
      Units.map (entrywiseHom σq.toRingHom) x = x → x ∈ rationalFixedGroup σq AK :=
    fun hx hxF => Subgroup.mem_inf.2 ⟨by rw [hZk]; exact hx, hxF⟩
  have hhT' : h ∈ rationalFixedTorus σq AK := Subgroup.mem_inf.2 ⟨hhT, hJ hhZ hFh⟩
  have hu'S := mem_rationalRootGroup_of_posUnipotent σq AK hu'U (hJ hu'Z hFu')
  have huS := mem_rationalRootGroup_of_inversionSet σq AK huI (hJ huZ hFu)
  have hnS : canonicalRep (coxeterSystem TwistTag.E6.tag) k w ∈ rationalRootGroup σq AK := by
    refine ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) Kq w, ?_,
      baseChangeGL_canonicalRep Kq.subtype w⟩
    have hmem := canonicalRep_mem_graphFixedRootGroup (K := Kq) (σ := RingHom.id Kq)
      ((mem_relWeylTwist TwistTag.E6).2 hδ)
    rw [hZK]
    exact hmem
  exact Set.mem_mul.2 ⟨h, hhT', u' * canonicalRep (coxeterSystem TwistTag.E6.tag) k w * u,
    mul_mem (mul_mem hu'S hnS) huS, by simp only [mul_assoc]⟩

open E6SignedGraph in
theorem rationalFixedGroup_subset_signed
    (hp2 : p ≠ 2) :
    (rationalFixedGroup (iterateFrobeniusEquiv k p e)
      (rootDiagUnit TwistTag.E6.tag (signTuple (fixSubfield (iterateFrobeniusEquiv k p e))) *
        diagramMap TwistTag.E6 (fixSubfield (iterateFrobeniusEquiv k p e))) :
          Set (ModGL TwistTag.E6.tag k)) ⊆
      (rationalFixedTorus (iterateFrobeniusEquiv k p e)
        (rootDiagUnit TwistTag.E6.tag (signTuple (fixSubfield (iterateFrobeniusEquiv k p e))) *
          diagramMap TwistTag.E6 (fixSubfield (iterateFrobeniusEquiv k p e))) :
            Set (ModGL TwistTag.E6.tag k)) *
        (rationalRootGroup (iterateFrobeniusEquiv k p e)
          (rootDiagUnit TwistTag.E6.tag (signTuple (fixSubfield (iterateFrobeniusEquiv k p e))) *
            diagramMap TwistTag.E6 (fixSubfield (iterateFrobeniusEquiv k p e))) :
              Set (ModGL TwistTag.E6.tag k)) := by
  set σq := iterateFrobeniusEquiv k p e with hσq
  set Kq := fixSubfield σq
  set AK := rootDiagUnit TwistTag.E6.tag (signTuple Kq) * diagramMap TwistTag.E6 Kq with hAK
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  have hKq : ringChar Kq ≠ 2 := ringChar_fixSubfield_ne_two hk σq
  have hA : CFSG.LieType.Chevalley.baseChangeGL Kq.subtype AK = twistA k := by
    rw [hAK, baseChangeGL_rootDiagUnit_mul_diagramMap, units_map_signTuple]
    rfl
  have hZk : graphCentralizer TwistTag.E6.tag k
      (CFSG.LieType.Chevalley.baseChangeGL Kq.subtype AK) = fixedGroup k := by
    rw [hA]
    rfl
  intro g hg
  obtain ⟨hgZ, hgF⟩ := Subgroup.mem_inf.1 hg
  rw [hZk] at hgZ
  have hgF' : Units.map (entrywiseHom σq.toRingHom) g = g := hgF
  have hgC : g ∈ (adjointGroup TwistTag.E6.tag k : Set (ModGL TwistTag.E6.tag k)) :=
    (Subgroup.mem_inf.1 hgZ).1
  rw [adjointGroup_eq_iUnion_bruhatCell] at hgC
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hgC
  have hw0 : w ∈ weylGroup := mem_weylGroup_of_mem_fixedGroup hk hgZ hw
  have hwρ : w ∈ relWeylTwist TwistTag.E6 := (weylGroup_le_parityGroup hw0).1
  obtain ⟨-, -, -, hexists, -, -⟩ := E6_signed_graph_orbit_rank_one_groups Kq hKq
  choose v hv a ha using fun i => hexists (simpleOrbit i) (simpleOrbit_spec i).1
  have hva : ∀ i, v i ∈ relWeylTwist TwistTag.E6 ∧ orbitImage (v i) (a i) = simpleOrbit i :=
    fun i => ⟨hv i, ha i⟩
  obtain ⟨n, hn, hnw⟩ := exists_mem_liftGroup_of_mem_weylGroup (K := Kq) hva hw0
  have hnS : n ∈ rootGenerated Kq := liftGroup_le_rootGenerated hva hn
  have hnN : n ∈ monomialSubgroup TwistTag.E6.tag Kq := liftGroup_le_monomialSubgroup v a hn
  have hdS : CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n ∈ rationalRootGroup σq AK :=
    ⟨n, hnS, rfl⟩
  have hdJ := rationalRootGroup_le σq AK hdS
  have hdΓ : CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n ∈ fixedGroup k := by
    rw [← hZk]
    exact (Subgroup.mem_inf.1 hdJ).1
  have hdN := baseChangeGL_mem_monomialSubgroup Kq.subtype hnN
  have hdw : MapsRootLines (CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n) w :=
    MapsRootLines.baseChangeGL Kq.subtype hnw
  have hdF := entrywise_baseChangeGL_fixSubfield σq n
  have hbij := fixed_cell_bijOn hwρ hdΓ hdN hdw
  obtain ⟨⟨u, h, v'⟩, ⟨hu, hh, hv'⟩, rfl⟩ := hbij.2.2 ⟨hgZ, hw⟩
  simp only at hu hh hv'
  have hFΓ : ∀ {x}, x ∈ fixedGroup k →
      Units.map (entrywiseHom σq.toRingHom) x ∈ fixedGroup k := fun {x} hx => by
    have h1 := frobTwistGL_diagramMap_pow_mem p (signTuple_eq_one_or k) (signTuple_perm_symm k)
      e 0 hx
    rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one] at h1
    rw [hσq, iterateFrobeniusEquiv_toRingHom]
    exact h1
  obtain ⟨huU, huΓ⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨hvI, hvΓ⟩ := Subgroup.mem_inf.1 hv'
  have heq : Units.map (entrywiseHom σq.toRingHom) u * Units.map (entrywiseHom σq.toRingHom) h *
      CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n * Units.map (entrywiseHom σq.toRingHom) v' =
        u * h * CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n * v' := by
    calc Units.map (entrywiseHom σq.toRingHom) u * Units.map (entrywiseHom σq.toRingHom) h *
          CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n *
            Units.map (entrywiseHom σq.toRingHom) v' =
        Units.map (entrywiseHom σq.toRingHom) u * Units.map (entrywiseHom σq.toRingHom) h *
          Units.map (entrywiseHom σq.toRingHom)
            (CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n) *
            Units.map (entrywiseHom σq.toRingHom) v' := by rw [hdF]
      _ = _ := by rw [← map_mul, ← map_mul, ← map_mul, hgF']
  have hinj := hbij.2.1
    (x₁ := (Units.map (entrywiseHom σq.toRingHom) u, Units.map (entrywiseHom σq.toRingHom) h,
      Units.map (entrywiseHom σq.toRingHom) v')) (x₂ := (u, h, v'))
    ⟨Subgroup.mem_inf.2 ⟨entrywise_mem_rootSpan (σ := σq) huU, hFΓ huΓ⟩,
      Subgroup.mem_inf.2 ⟨entrywise_mem_torusGroup (σ := σq) hhT, hFΓ hhΓ⟩,
      Subgroup.mem_inf.2 ⟨entrywise_mem_rootSpan (σ := σq) hvI, hFΓ hvΓ⟩⟩ ⟨hu, hh, hv'⟩ heq
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨hFu, hFh, hFv⟩ := hinj
  have hJ : ∀ {x}, x ∈ fixedGroup k → Units.map (entrywiseHom σq.toRingHom) x = x →
      x ∈ rationalFixedGroup σq AK :=
    fun hx hxF => Subgroup.mem_inf.2 ⟨by rw [hZk]; exact hx, hxF⟩
  have hhT' : h ∈ rationalFixedTorus σq AK := Subgroup.mem_inf.2 ⟨hhT, hJ hhΓ hFh⟩
  have huS := mem_rationalRootGroup_of_posUnipotent σq AK huU (hJ huΓ hFu)
  have hvS := mem_rationalRootGroup_of_inversionSet σq AK hvI (hJ hvΓ hFv)
  have hcS := conj_mem_rationalRootGroup σq (signTuple Kq) (inv_mem hhT') huS
  refine Set.mem_mul.2 ⟨h, hhT',
    h⁻¹ * u * h⁻¹⁻¹ * CFSG.LieType.Chevalley.baseChangeGL Kq.subtype n * v',
    mul_mem (mul_mem hcS hdS) hvS, ?_⟩
  simp only [mul_assoc, mul_inv_cancel_left, inv_inv]

end CFSG.LieType.AlgebraicGroups
