module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InCore
public import CFSG.ClassicalInvolution.Q3.Q3ExcE6Tw

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ClassicalInvolution
open scoped commutatorElement Pointwise

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem fixedPointsIn_eq_twistedFixedGroup
    (f : ℕ) :
    fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)) =
      twistedFixedGroup TwistTag.E6 k (iterateFrobenius k p f) := by
  ext y
  refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
  change frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) y = y ↔
    twistHom TwistTag.E6 k (iterateFrobenius k p f) y = y
  rw [frobTwistGL_apply, CFSG.LieType.Chevalley.twistHom_apply]

omit [IsAlgClosed k] in
theorem twE6_lift_facts
    {f : ℕ} (hf : 1 ≤ f) (hodd : Odd (p ^ f))
    (K : Type) [Field K] [Finite K] [Algebra K k] [IsAlgClosure K k]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k))⁆ =
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K k)) ∧
    ∀ g ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)),
      ∃ u ∈ torusGroup TwistTag.E6.tag k,
        frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) u = u ∧
        ∃ a ∈ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k))⁆, g = u * a := by
  have hR := fixedPointsIn_eq_twistedFixedGroup (p := p) (k := k) f
  have hKo : Nat.card K = (p ^ f) ^ TwistTag.E6.order := hK
  obtain ⟨-, -, -, -, hset, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group
    TwistTag.E6 (Fact.out : p.Prime) hf hodd K hKo σ.toRingHom hσ k (iterateFrobenius k p f)
    (fun c => iterateFrobenius_def p f c)
  rw [hR]
  refine ⟨hder, fun g hg => ?_⟩
  have hg' : g ∈ (twistedFixedGroup TwistTag.E6 k (iterateFrobenius k p f) :
      Set (ModGL TwistTag.E6.tag k)) := hg
  rw [hset] at hg'
  obtain ⟨u, hu, a, ha, rfl⟩ := Set.mem_mul.1 hg'
  obtain ⟨huT, huR⟩ := Subgroup.mem_inf.1 hu
  refine ⟨u, huT, ?_, a, hder ▸ ha, rfl⟩
  rw [← hR] at huR
  exact (mem_fixedPointsIn.1 huR).2

theorem twE6_orbitGroups_le
    {e : ℕ} {x : ModGL TwistTag.E6.tag k}
    (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k) (h w : ModGL TwistTag.E6.tag k)
    (hhT : h ∈ torusGroup TwistTag.E6.tag k) (hDe : D.e = e)
    (hDF : ∀ y : adjointGroup TwistTag.E6.tag k, (D.F y : ModGL TwistTag.E6.tag k) =
      frobTwistGL TwistTag.E6.tag k p e (h * diagramMap TwistTag.E6 k) y)
    (hcent : (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ⊓
          Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype)
    (hq : (p ^ e = 3 ∧ ∀ g ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
      ∃ u ∈ torusGroup TwistTag.E6.tag k,
        frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) u = u ∧
        ∃ a ∈ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆, g = u * a) ∨
      (5 ≤ p ^ e ∧ D.χ = signMaskChar TwistTag.E6.tag 2 ∧
        ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ)))
    (J' : Set.range D.classOrbit) :
    (D.withOrbit J').orbitGroup ≤ (⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
        Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom := by
  classical
  set F := frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set Xh := D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype with hXh
  set C := (D.withOrbit J').orbitGroup with hC
  have hpull : ∀ y ∈ Xh, ∃ z ∈ R ⊓ Subgroup.centralizer ({x} : Set (ModGL _ k)),
      y = w * z * w⁻¹ := by
    intro y hy
    rw [← hcent] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, rfl⟩
  have hCX : ∀ y ∈ C, y ∈ Xh := by
    intro y hy
    have h1 := (D.withOrbit J').orbitGroupC_le_fixedGroup
      ((D.withOrbit J').mk_mem_orbitGroupC hy)
    have h2 := D.kernelFixedGroup_le_totalFixedGroup
      (D.fixedGroup_withOrbit_le_kernelFixedGroup J' h1)
    exact ⟨_, h2, rfl⟩
  have hperf : ⁅C, C⁆ = C → C ≤ (⁅R, R⁆).map (MulAut.conj w).toMonoidHom := by
    intro hperf
    set P := C.map (MulAut.conj w⁻¹).toMonoidHom with hP
    have hPR : P ≤ R := by
      rintro _ ⟨y', hy', rfl⟩
      obtain ⟨z', hz', hyz'⟩ := hpull y' (hCX y' hy')
      have e : (MulAut.conj w⁻¹).toMonoidHom y' = z' := by
        rw [hyz']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_inf.1 hz').1
    have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hperf]
    have hPH : P ≤ ⁅R, R⁆ := by
      rw [← hPperf]
      exact Subgroup.commutator_mono hPR hPR
    intro y hy
    refine ⟨w⁻¹ * y * w, hPH ⟨y, hy, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hCHw : C ≤ (⁅R, R⁆).map (MulAut.conj w).toMonoidHom := by
    rcases hq with ⟨hq3, hdec⟩ | ⟨hq5, hDχ, hDθ⟩
    ·
      set c := h * diagramMap TwistTag.E6 k with hc_def
      have hdn : diagramMap TwistTag.E6 k ∈
          Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL TwistTag.E6.tag k)) :=
        diagramMap_mem_normalizer TwistTag.E6
      have hd2 : diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k ∈
          torusGroup TwistTag.E6.tag k := by
        have h1 := diagramMap_pow_order TwistTag.E6 k
        rw [show TwistTag.E6.order = 2 from rfl, pow_two] at h1
        rw [h1]
        exact one_mem _
      have hcT : c ∈ Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL _ k)) :=
        mul_mem (Subgroup.le_normalizer hhT) hdn
      have hc2 : c * c ∈ torusGroup TwistTag.E6.tag k := by
        have e : c * c = h * (diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) *
            (diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k) := by
          rw [hc_def]
          group
        rw [e]
        exact mul_mem (mul_mem hhT ((Subgroup.mem_normalizer_iff.1 hdn h).1 hhT)) hd2
      have hfrob : Q3.Exc3Frob D c := ⟨fun y => by rw [hDe]; exact hDF y, hcT, hc2⟩
      have hcJ : Q3.Exc3Frob (D.withOrbit J') c :=
        ⟨hfrob.frob, hfrob.normalizes, hfrob.sq_mem⟩
      have hq3D : p ^ D.e = 3 := by rw [hDe]; exact hq3
      have hRconj : ∀ g ∈ R, R.map (MulAut.conj g).toMonoidHom = R := by
        intro g hg
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact R.mul_mem (R.mul_mem hg hz) (R.inv_mem hg)
        · intro hy
          refine ⟨g⁻¹ * y * g, R.mul_mem (R.mul_mem (R.inv_mem hg) hy) hg, ?_⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
      have hHn : ∀ g ∈ R, ∀ a ∈ ⁅R, R⁆, g * a * g⁻¹ ∈ ⁅R, R⁆ := by
        intro g hg a ha
        have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha
        rwa [Subgroup.map_commutator, hRconj g hg] at this
      have hdec' : ∀ g ∈ R, ∃ u' ∈ R, u' ^ 8 = 1 ∧ ∃ a ∈ ⁅R, R⁆, g = u' * a := by
        intro g hg
        obtain ⟨u', hu'T, hu'F, a, ha, rfl⟩ := hdec g hg
        refine ⟨u', mem_fixedPointsIn.2 ⟨torusGroup_le_adjointGroup hu'T, hu'F⟩, ?_, a, ha, rfl⟩
        have := Q3.exc3_pow_eq_one_of_fixed_torus e hdn hd2 hu'T hu'F
        rw [hq3] at this
        simpa using this
      rcases Q3.exc3_orbitGroup_big_or_small hcJ hq3D with hBig | ⟨hSm, -⟩
      · exact hperf (Subgroup.isPerfect_iff.1 hBig.1.1)
      · obtain ⟨e⟩ := hSm
        have hgen := Q3.exc3_closure_pow_three_of_equiv e
        have hle : Subgroup.closure {y : C | y ^ 3 = 1} ≤
            ((⁅R, R⁆).map (MulAut.conj w).toMonoidHom).subgroupOf C := by
          refine (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2 ?_
          have hy3 : (y : ModGL TwistTag.E6.tag k) ^ 3 = 1 := by
            have := congrArg Subtype.val hy
            simpa using this
          obtain ⟨z, hz, hyz⟩ := hpull y.1 (hCX y.1 y.2)
          have hz3 : z ^ 3 = 1 := by
            have h1 : w * z ^ 3 * w⁻¹ = 1 := by
              rw [← conj_pow, ← hyz]
              exact hy3
            calc z ^ 3 = w⁻¹ * (w * z ^ 3 * w⁻¹) * w := by group
              _ = 1 := by rw [h1]; group
          exact ⟨z, Q3.exc3_pow_three_mem hHn hdec' (Subgroup.mem_inf.1 hz).1 hz3, hyz.symm⟩
        intro y hy
        exact Subgroup.mem_subgroupOf.1 (hle (hgen ▸ Subgroup.mem_top (⟨y, hy⟩ : C)))
    ·
      have hθ : ∀ γ, D.θ (toReal γ) =
          toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ) := fun γ =>
        (hDθ γ).trans (congrArg toReal (thetaMap_e6_nil_apply γ).symm)
      have hq5' : 5 ≤ D.q := by
        change 5 ≤ p ^ D.e
        rw [hDe]
        exact hq5
      rcases orbitGroup_two_cases D hq5' hDχ hθ J' with hbot | ⟨hqs, -⟩
      · intro y hy
        rw [Subgroup.mem_bot.1 (hbot.le hy)]
        exact one_mem _
      · exact hperf (Subgroup.isPerfect_iff.1 hqs.1)
  intro y hy
  obtain ⟨z, hz, hyz⟩ := hpull y (hCX y hy)
  obtain ⟨a, ha, hay⟩ := hCHw hy
  have haz : a = z := by
    have h1 : w * a * w⁻¹ = w * z * w⁻¹ := hay.trans hyz
    exact (MulAut.conj w).injective h1
  refine ⟨z, ⟨haz ▸ ha, (Subgroup.mem_inf.1 hz).2⟩, ?_⟩
  rw [hyz]
  rfl

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In
