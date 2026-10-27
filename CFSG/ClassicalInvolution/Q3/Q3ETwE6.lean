module

public import CFSG.ClassicalInvolution.Q3.Q3PlanDatumMeta
public import CFSG.ClassicalInvolution.Q3.Q3EReduce
public import CFSG.ClassicalInvolution.Q3.Q3ExcE6Conj
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups commutatorElement

section Core

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]


theorem tw6_derived (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (h3 : 3 < p ^ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    {R : Subgroup (ModGL TwistTag.E6.tag k)}
    (hR : R = fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))) (hRfin : Finite R)
    {x : ModGL TwistTag.E6.tag k} (hxR : x ∈ R) (hx2 : x ^ 2 = 1)
    {J : Subgroup (ModGL TwistTag.E6.tag k)}
    (hJs : IsSubnormal J (⁅R, R⁆ ⊓ Subgroup.centralizer {x}))
    (hsolv : Group.IsSolvable J) (hodd : IsOddGenerated J) : derivedSeries ↥J 2 = ⊥ := by
  classical
  have hxR' := hxR
  rw [hR] at hxR'
  obtain ⟨r, hr, D, h, g₁, s, hg₁G, hhT, hFg₁, hFs, hg₁x, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    exc3_e6_datum_conj p hp2 hk he hxR' hx2
  have h3D : 3 < D.q := by
    change 3 < p ^ D.e
    rw [hDe]
    exact h3
  set w := rootDiagUnit TwistTag.E6.tag s * g₁ with hw
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  set G := ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)) with hG
  set Y := G.map (MulAut.conj w).toMonoidHom with hY
  set Xh := D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype with hXh
  have hcent' : (R ⊓ Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom = Xh := by
    rw [hR]
    exact hcent
  have hGfin : Finite G := Finite.of_injective
    (fun y : G => (⟨y.1, hRsub (Subgroup.mem_inf.1 y.2).1⟩ : R))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hYfin : Finite Y :=
    Finite.of_equiv _ (G.equivMapOfInjective _ (MulAut.conj w).injective).toEquiv
  have hYX : Y ≤ Xh := by
    rw [← hcent']
    exact Subgroup.map_mono (inf_le_inf_right _ hRsub)
  have hY2 : ∀ y ∈ Y, y ^ 2 ∈ Xh := fun y hy => Xh.pow_mem (hYX hy) 2
  have hYn : ∀ y ∈ Y, ∀ v ∈ Xh, y * v * y⁻¹ ∈ Xh := fun y hy v hv =>
    Xh.mul_mem (Xh.mul_mem (hYX hy) hv) (Xh.inv_mem (hYX hy))
  have hpull : ∀ y ∈ Xh, ∃ z ∈ R ⊓ Subgroup.centralizer ({x} : Set (ModGL _ k)),
      y = w * z * w⁻¹ := by
    intro y hy
    rw [← hcent'] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, rfl⟩
  have hid : (MulAut.conj (1 : ModGL TwistTag.E6.tag k)).toMonoidHom =
      MonoidHom.id (ModGL TwistTag.E6.tag k) := by
    ext y
    simp
  have hCY : ∀ J' : Set.range D.classOrbit,
      ((D.withOrbit J').orbitGroup).map (MulAut.conj (1 : ModGL TwistTag.E6.tag k)).toMonoidHom ≤
        Y := by
    intro J'
    rw [hid, Subgroup.map_id]
    set C := (D.withOrbit J').orbitGroup with hC
    have hCX : C ≤ Xh :=
      CFSG.ClassicalInvolution.isSubnormal_le (orbitGroup_isSubnormal D J')
    have hperf : ⁅C, C⁆ = C := by
      rcases orbitGroup_eq_bot_or_isQuasisimple D h3D J' with hbot | hqs
      · have hbot' : C = ⊥ := hbot
        rw [hbot']
        exact Subgroup.commutator_bot_left _
      · exact Subgroup.isPerfect_iff.1 ⟨hqs.1⟩
    set P := C.map (MulAut.conj w⁻¹).toMonoidHom with hP
    have hPR : P ≤ R := by
      rintro _ ⟨y', hy', rfl⟩
      obtain ⟨z', hz', hyz'⟩ := hpull y' (hCX hy')
      have e : (MulAut.conj w⁻¹).toMonoidHom y' = z' := by
        rw [hyz']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_inf.1 hz').1
    have hPC : P ≤ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)) := by
      rintro _ ⟨y', hy', rfl⟩
      obtain ⟨z', hz', hyz'⟩ := hpull y' (hCX hy')
      have e : (MulAut.conj w⁻¹).toMonoidHom y' = z' := by
        rw [hyz']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_inf.1 hz').2
    have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hperf]
    have hPH : P ≤ ⁅R, R⁆ := by
      rw [← hPperf]
      exact Subgroup.commutator_mono hPR hPR
    intro y hy
    refine ⟨w⁻¹ * y * w, ⟨hPH ⟨y, hy, rfl⟩, hPC ⟨y, hy, rfl⟩⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hJsub : IsSubnormal (J.map (MulAut.conj w).toMonoidHom) Y :=
    CFSG.ClassicalInvolution.isSubnormal_map_mulEquiv (MulAut.conj w) hJs
  have hJsolv : Group.IsSolvable ↥(J.map (MulAut.conj w).toMonoidHom) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (J.equivMapOfInjective _ (MulAut.conj w).injective).symm.toMonoidHom)
      (J.equivMapOfInjective _ (MulAut.conj w).injective).symm.injective
  have hconj1 : Xh.map (MulAut.conj (1 : ModGL TwistTag.E6.tag k)).toMonoidHom = Xh := by
    rw [hid, Subgroup.map_id]
  exact derivedSeries_eq_bot_of_map (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
    (derivedSeries_two_eq_bot_of_datum D h3D 1 rfl hconj1 (Y := Y) hCY hY2 hYn hJsub hJsolv
      (hodd.map _ (MulAut.conj w).injective))

end Core

section Tag

variable {p e : ℕ} [Fact p.Prime]

theorem false_of_isClassicalMember3_twE6 (hp2 : p ≠ 2) (he : 1 ≤ e) (h5 : 5 ≤ p ^ e)
    [Finite (twistedE6Group p e)] {X : Type} [Group X] [Finite X]
    (ψ : twistedE6Group p e →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _) {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) :
    False := by
  classical
  set K0 := GaloisField p (2 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  have hCharK : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  set F := frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set Φ := twistedE6Phi p e k with hΦ
  have hrange : Φ.range = ⁅R, R⁆ := range_twistedE6Phi p e hp2 he
  have hkerΦ : Φ.ker ≤ Subgroup.center (twistedE6Group p e) := ker_twistedE6Phi_le_center p e k
  have hqs := CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 p e he
  let Φ' : twistedE6Group p e →* ↥⁅R, R⁆ :=
    Φ.codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hker' : Φ'.ker ≤ Subgroup.center (twistedE6Group p e) := by
    rw [MonoidHom.ker_codRestrict]
    exact hkerΦ
  have hXq : CFSG.Open.IsQuasisimple X := by
    obtain ⟨k₀, hk₀⟩ := hψ z
    exact CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
      (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqs hψ ⟨k₀, by rw [hk₀]; exact h.ne_one⟩)
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p he (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (iterateFrobenius k p e))
    (diagramMap_pow_order TwistTag.E6 k)
  have hkalg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k :=
    isAlgebraic_zmod_of_isAlgClosure p K0 k
  refine false_of_isClassicalMember3_of_central_cover Φ' hΦ'surj hker' ψ hψ hker ?_ h
    (h.not_mem_center_of_quasisimple hXq)
  intro w hw N hNC hNs hsolv hodd
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hι : Function.Injective (⁅R, R⁆).subtype := (⁅R, R⁆).subtype_injective
  have hxR : (w : ModGL TwistTag.E6.tag k) ∈ R := hRsub w.2
  have hx2 : (w : ModGL TwistTag.E6.tag k) ^ 2 = 1 := by
    have := congrArg Subtype.val hw
    rw [pow_two]
    exact this
  have hcent : (Subgroup.centralizer ({w} : Set ↥⁅R, R⁆)).map (⁅R, R⁆).subtype =
      ⁅R, R⁆ ⊓ Subgroup.centralizer {(w : ModGL TwistTag.E6.tag k)} := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
    · rintro ⟨hy, hyc⟩
      exact ⟨⟨y, hy⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyc)), rfl⟩
  have hJs : IsSubnormal (N.map (⁅R, R⁆).subtype) (⁅R, R⁆ ⊓ Subgroup.centralizer
      {(w : ModGL TwistTag.E6.tag k)}) := by
    have h1 := CFSG.ComponentClassification.Components.chain_map (⁅R, R⁆).subtype hNs
    rw [hcent] at h1
    exact h1
  have hJsolv : Group.IsSolvable ↥(N.map (⁅R, R⁆).subtype) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (N.equivMapOfInjective (⁅R, R⁆).subtype hι).symm.toMonoidHom)
      (N.equivMapOfInjective (⁅R, R⁆).subtype hι).symm.injective
  exact derivedSeries_eq_bot_of_map (⁅R, R⁆).subtype hι
    (tw6_derived hp2 he (by omega) hkalg rfl hRfin hxR hx2 hJs hJsolv (hodd.map _ hι))

theorem classicalMemberParameters3At_twistedE6 : ClassicalMemberParameters3At .twistedE6 := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .twistedE6 0 r e hr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv_twistedE6 hr
  have : Finite (twistedE6Group r e) := hfin
  exact false_of_isClassicalMember3_twE6 hr2 hadm.2.1
    (five_le_pow_of_odd_prime_of_ne_three hr hr2 hadm.2.1 hne) ψ hψ hker h

end Tag

end CFSG.ClassicalInvolution.Q3
