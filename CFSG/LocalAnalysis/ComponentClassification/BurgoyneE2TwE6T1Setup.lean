module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Core
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Inner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Cent

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.RankThree.Chevalley (baseChangeGL_simpleRootSL2 trace_baseChangeGL)
open scoped commutatorElement MatrixGroups


variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {L : Type} [Field L]
  [Algebra K L] [IsAlgClosure K L] [CharP L p]

omit [Finite K] in
theorem t1_derived_eq (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L))⁆ =
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K L)) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, -, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.E6
    hp hf hodd K hK σ.toRingHom hσ L (iterateFrobenius L p f) (fun c => iterateFrobenius_def p f c)
  have hRtw : fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) =
      twistedFixedGroup TwistTag.E6 L (iterateFrobenius L p f) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) y = y ↔
      twistHom TwistTag.E6 L (iterateFrobenius L p f) y = y
    rw [frobTwistGL_apply, twistHom_apply]
  rw [hRtw]
  exact hder

omit
  [Finite K] in
theorem baseChangeGL_rootDiagUnit_mem_t1R (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (b i)) :
    baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.E6.tag b) ∈
      fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  rw [baseChangeGL_rootDiagUnit]
  refine mem_fixedPointsIn.2 ⟨torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup _), ?_⟩
  rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map, diagramMap_mul_rootDiagUnit,
    mul_inv_cancel_right]
  congr 1
  funext i
  have h := hb (TwistTag.E6.perm.symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  ext
  simp [hσ]

theorem three_le_q_e6 {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k) : 3 ≤ D.q := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h D.odd
    · have := hp.two_le
      obtain ⟨m, hm⟩ := h
      omega
  calc 3 ≤ p := h3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ D.e := Nat.pow_le_pow_right hp.pos D.one_le_e

theorem rootDiagUnit_commute_toralCentralizer_d20 {k : Type} [Field k] [IsAlgClosed k]
    (hk2 : ringChar k ≠ 2) {c : Fin TwistTag.E6.tag.rank → kˣ} (h0 : c (t1Node 0) = 1)
    (h1 : c (t1Node 1) = 1) (h3 : c (t1Node 3) = 1) (h5 : c (t1Node 5) = 1)
    (h24 : c (t1Node 2) * c (t1Node 4) = 1) {y : ModGL TwistTag.E6.tag k}
    (hy : y ∈ toralCentralizer TwistTag.E6.tag k
      (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag 20))) :
    rootDiagUnit TwistTag.E6.tag c * y = y * rootDiagUnit TwistTag.E6.tag c := by
  rw [← CFSG.ClassicalInvolution.ModelFacts.e6_toralRootGroup_eq hk2 (signCharTuple_sign _),
    toralRootGroup, rootCharKernel_signCharTuple hk2] at hy
  exact rootDiagUnit_commute_levi_twenty h0 h1 h3 h5 h24 hy

theorem exists_t1_layer (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀R : g₀ ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L))) :
    ∃ C' : Subgroup (ModGL TwistTag.E6.tag L), CFSG.IsQuasisimple C' ∧
      C' ≤ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L))⁆ ⊓
        Subgroup.centralizer {(rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)))} ∧
      (∀ y ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) ⊓
        Subgroup.centralizer {(rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)))},
        ∀ v ∈ C', y * v * y⁻¹ ∈ C') ∧
      ∀ β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom), Odd (orderOf β) →
        (∀ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
          g₀ * baseChangeGL (algebraMap K L) (s : ModGL TwistTag.E6.tag K) * g₀⁻¹ ∈ C' →
            β s = s) →
        ∃ c : Fin TwistTag.E6.tag.rank → Lˣ, c (t1Node 0) = 1 ∧ c (t1Node 1) = 1 ∧
          c (t1Node 3) = 1 ∧ c (t1Node 5) = 1 ∧ c (t1Node 2) * c (t1Node 4) = 1 ∧
          rootDiagUnit TwistTag.E6.tag c ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) ∧
          ∀ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
            g₀ * baseChangeGL (algebraMap K L) ((β s : graphFixedRootGroup TwistTag.E6 K
              σ.toRingHom) : ModGL TwistTag.E6.tag K) * g₀⁻¹ =
            rootDiagUnit TwistTag.E6.tag c *
              (g₀ * baseChangeGL (algebraMap K L) (s : ModGL TwistTag.E6.tag K) * g₀⁻¹) *
                (rootDiagUnit TwistTag.E6.tag c)⁻¹ := by
  classical
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP K p := finite_field_prime_power_characteristic hp (show 1 ≤ f * 2 by omega)
    (by rw [hK, ← pow_mul])
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L p]; exact hp2
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L) with hι
  have hH : ⁅R, R⁆ = (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map ι :=
    t1_derived_eq hp2 hf hK σ hσ
  have hRR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hRc : ∀ y ∈ R, ∀ v ∈ ⁅R, R⁆, y * v * y⁻¹ ∈ ⁅R, R⁆ := by
    intro y hy v hv
    have hRy : R.map (MulAut.conj y).toMonoidHom = R := by
      refine le_antisymm ?_ fun x hx => ⟨y⁻¹ * x * y, mul_mem (mul_mem (inv_mem hy) hx) hy, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact mul_mem (mul_mem hy hx) (inv_mem hy)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have h := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hv
    rw [Subgroup.map_commutator, hRy] at h
    exact h
  have hpre : ∀ v ∈ ⁅R, R⁆, ∃ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      g₀ * ι (s : ModGL TwistTag.E6.tag K) * g₀⁻¹ = v := by
    intro v hv
    have h := hRc _ (inv_mem hg₀R) v hv
    rw [inv_inv, hH] at h
    obtain ⟨y, hy, hyv⟩ := h
    refine ⟨⟨y, hy⟩, ?_⟩
    change g₀ * ι y * g₀⁻¹ = v
    rw [hyv]
    group
  obtain ⟨D, u, hDe, hDχ, hDθ, hsub, hqs, hu, hCH, hCn⟩ := exists_twenty_layer (k := L) hp2 hf hk
  set C' := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC'
  refine ⟨C', CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (D.orbitGroup.equivMapOfInjective _ (MulAut.conj u).injective) hqs, hCH,
    fun y hy v hv => ?_, fun β hβ hfix => ?_⟩
  · have h := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hv
    rw [hCn y hy] at h
    exact h
  have hcardk : Nat.card (fixSubfield σ) = p ^ D.e := by
    rw [hDe]
    exact CFSG.ComponentClassification.CatLeafProof.card_fixSubfield_of_sq_pow hp hf hK σ hσ
  let _ : Algebra (fixSubfield σ) L := ((algebraMap K L).comp (fixSubfield σ).subtype).toAlgebra
  have hΔ4 : Pi.single (t1Node 3) 1 ∈ D.simpleRootsJ := by
    rw [simpleRootsJ_eq_simpleUnion_e6, hDχ]
    change _ ∈ simpleUnion (signMaskChar .E6 20)
    rw [CFSG.ComponentClassification.CatLeafProof.simpleUnion_e6_twenty]
    exact ⟨0, rfl⟩
  have htr : ∀ A : SL2 (fixSubfield σ), ∃ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      β y = y ∧ LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((y : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) =
        LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((simpleRootSL2 TwistTag.E6.tag K (t1Node 3)
            (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) :
              ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) := by
    intro A
    have hρ := rootSL2_mem_orbitGroup_four D hcardk hDθ hΔ4 A
    have hvC : u * rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 3) 1)
        (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) L) A) * u⁻¹ ∈ C' :=
      ⟨_, hρ, rfl⟩
    obtain ⟨y, hy⟩ := hpre _ (hCH hvC).1
    refine ⟨y, hfix y (by rw [hy]; exact hvC), ?_⟩
    apply (algebraMap K L).injective
    rw [← trace_baseChangeGL, ← trace_baseChangeGL, baseChangeGL_simpleRootSL2]
    have hιy : ι (y : ModGL TwistTag.E6.tag K) = (g₀⁻¹ * u) *
        simpleRootSL2 TwistTag.E6.tag L (t1Node 3)
          (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) L) A) * (g₀⁻¹ * u)⁻¹ := by
      rw [← rootSL2_simple_eq]
      calc ι (y : ModGL TwistTag.E6.tag K) =
          g₀⁻¹ * (g₀ * ι (y : ModGL TwistTag.E6.tag K) * g₀⁻¹) * g₀ := by group
        _ = _ := by rw [hy]; group
    have hSL : Matrix.SpecialLinearGroup.map (algebraMap K L)
        (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) =
          Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) L) A := by
      ext i j
      rfl
    change LinearMap.trace L _ ((ι (y : ModGL TwistTag.E6.tag K) : ModGL TwistTag.E6.tag L) :
      Module.End L (RootModule TwistTag.E6.tag L)) = _
    rw [hιy, hSL, Units.val_mul, Units.val_mul, LinearMap.trace_conj]
  obtain ⟨g, b, hb, hβg⟩ := exists_inndiag_of_odd_fix_traces hp hp2 hf hK σ hσ hβ htr
  set z₁ := g₀ * ι ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b) * g₀⁻¹
    with hz₁
  have hιg : ι (g : ModGL TwistTag.E6.tag K) ∈ R := hRR (by rw [hH]; exact ⟨_, g.2, rfl⟩)
  have hz₁R : z₁ ∈ R := mul_mem (mul_mem hg₀R (by
    rw [map_mul]
    exact mul_mem hιg (baseChangeGL_rootDiagUnit_mem_t1R σ hσ hb))) (inv_mem hg₀R)
  have hz₁β : ∀ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      g₀ * ι ((β s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) *
        g₀⁻¹ = z₁ * (g₀ * ι (s : ModGL TwistTag.E6.tag K) * g₀⁻¹) * z₁⁻¹ := by
    intro s
    rw [hβg s, map_mul, map_mul, map_inv, hz₁, map_mul]
    group
  have hz₁C : ∀ v ∈ C', z₁ * v = v * z₁ := by
    intro v hv
    obtain ⟨y, hy⟩ := hpre _ (hCH hv).1
    have h := hz₁β y
    rw [hfix y (by rw [hy]; exact hv), hy] at h
    calc z₁ * v = (z₁ * v * z₁⁻¹) * z₁ := by group
      _ = v * z₁ := by rw [← h]
  have hz₁G : z₁ ∈ adjointGroup TwistTag.E6.tag L := (mem_fixedPointsIn.1 hz₁R).1
  have huG : u ∈ adjointGroup TwistTag.E6.tag L :=
    sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _) hu
  have hcomm : ∀ w ∈ D.orbitGroup, (u⁻¹ * z₁ * u) * w = w * (u⁻¹ * z₁ * u) := by
    intro w hw
    have h := hz₁C (u * w * u⁻¹) ⟨w, hw, rfl⟩
    calc u⁻¹ * z₁ * u * w = u⁻¹ * (z₁ * (u * w * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * w * u⁻¹) * z₁) * u := by rw [h]
      _ = w * (u⁻¹ * z₁ * u) := by group
  have := hsub
  obtain ⟨c, hc, h0, h1, h3, h5, h24⟩ := eq_of_commute_orbitGroup_twenty D (three_le_q_e6 D) hDχ
    hDθ (mul_mem (mul_mem (inv_mem huG) hz₁G) huG) hcomm
  have hz₁c : z₁ = rootDiagUnit TwistTag.E6.tag c := by
    have hcu := rootDiagUnit_commute_levi_twenty h0 h1 h3 h5 h24 hu
    calc z₁ = u * (u⁻¹ * z₁ * u) * u⁻¹ := by group
      _ = u * rootDiagUnit TwistTag.E6.tag c * u⁻¹ := by rw [← hc]
      _ = rootDiagUnit TwistTag.E6.tag c := by rw [← hcu]; group
  refine ⟨c, h0, h1, h3, h5, h24, hz₁c ▸ hz₁R, fun s => ?_⟩
  rw [hz₁β s, hz₁c]

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
