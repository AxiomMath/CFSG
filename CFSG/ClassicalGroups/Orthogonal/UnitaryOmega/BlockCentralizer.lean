module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorusNormalizer
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Simple
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Cent
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.ClassicalGroups.Orthogonal.Small
open QuadraticMap
open scoped commutatorElement

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {p : ℕ} [Fact p.Prime]

private noncomputable abbrev outsideTorus
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr2 : 2 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (S : Finset (Fin r)) :
    Subgroup (normOmega E r) :=
  (Subgroup.pi (S : Set (Fin r))
    (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map
      (normPlaneTorus E hr2 hpq ξ)

private noncomputable abbrev outsideCentralizer
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr2 : 2 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (S : Finset (Fin r)) :
    Subgroup (normOmega E r) :=
  Subgroup.centralizer (outsideTorus E hr2 hpq ξ S : Set (normOmega E r))



private theorem centralizer_coord_subset
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) {j : Fin r} (hj : j ∉ S)
    {a : normOmega E r}
    (ha : a ∈ Subgroup.centralizer
      (((Subgroup.pi (S : Set (Fin r))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map
          (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ)) :
        Set (normOmega E r)))
    (x : K) :
    (a.1 (((0, 0) : F × F), Pi.single j x)).1 = 0 ∧
      ∀ l, l ≠ j → (a.1 (((0, 0) : F × F), Pi.single j x)).2 l = 0 := by
  classical
  let s : Fin r → Multiplicative (ZMod p) :=
    Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))
  have hs : s j ≠ 1 := by
    dsimp [s]
    rw [Pi.mulSingle_eq_same]
    intro h
    have h1 : (1 : ZMod p) = 0 := by simpa using congrArg Multiplicative.toAdd h
    exact one_ne_zero h1
  have hρT : (normPlaneTorus E (by omega : 2 ≤ r)
      hpq ξ) s ∈
      (Subgroup.pi (S : Set (Fin r))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map
        (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ) := by
    refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
    exact (Subgroup.mem_pi (S : Set (Fin r))).mpr fun i hi => by
      by_cases hij : i = j
      · exact absurd (hij ▸ hi) hj
      · have hs_i : s i = 1 := by
          dsimp [s]
          rw [Pi.mulSingle_eq_of_ne hij]
        exact Subgroup.mem_bot.mpr hs_i
  have hcomm : (normPlaneTorus E (by omega : 2 ≤ r)
      hpq ξ) s * a = a * (normPlaneTorus E (by omega : 2 ≤ r)
        hpq ξ) s :=
    (Subgroup.mem_centralizer_iff.mp ha) _ hρT
  have hconj : a * (normPlaneTorus E (by omega : 2 ≤ r)
      hpq ξ) s * a⁻¹ =
      (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ) s := by
    calc a * (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ) s * a⁻¹ =
        (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ) s * a * a⁻¹ := by
          rw [hcomm.symm]
      _ = (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ) s := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
  have hsub := normPlaneTorus_image_coord_subset (E := E) (p := p)
    (m := r) (by omega : 2 ≤ r) hpq hξ
    (a := a) hconj hs x
  refine ⟨hsub.1, ?_⟩
  intro l hl
  exact hsub.2 l (by
    dsimp [s]
    rw [Pi.mulSingle_eq_of_ne hl])

private theorem centralizer_mem_stabSub_coordPlane
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) {j : Fin r} (hj : j ∉ S)
    {a : normOmega E r}
    (ha : a ∈ Subgroup.centralizer
      (((Subgroup.pi (S : Set (Fin r))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map
          (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ)) :
        Set (normOmega E r))) :
    a.1 ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin r → K))) j) := by
  classical
  rw [CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub]
  intro x
  constructor
  · intro hx
    obtain ⟨e, he⟩ := mem_coordPlane.mp hx
    rw [← he]
    change a.1 (((0, 0) : F × F), Pi.single j e) ∈
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin r → K))) j
    rw [mem_coordPlane]
    refine ⟨(a.1 (((0, 0) : F × F), Pi.single j e)).2 j, ?_⟩
    have hsub := centralizer_coord_subset E hr hpq ξ hξ S hj ha e
    exact (normPlaneTorus_eq_single_of_coord hsub.1 hsub.2).symm
  · intro hx
    have hinv : a⁻¹ ∈ Subgroup.centralizer
        (((Subgroup.pi (S : Set (Fin r))
          (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map
            (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ)) :
          Set (normOmega E r)) := inv_mem ha
    obtain ⟨e, he⟩ := mem_coordPlane.mp hx
    have he' : a.1 x = ((0 : F × F), Pi.single j e) := by
      simpa using he.symm
    have hpinv : (a⁻¹).1 ((0 : F × F), Pi.single j e) ∈
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin r → K))) j := by
      rw [mem_coordPlane]
      refine ⟨((a⁻¹).1 ((0 : F × F), Pi.single j e)).2 j, ?_⟩
      have hsub := centralizer_coord_subset E hr hpq ξ hξ S hj hinv e
      exact (normPlaneTorus_eq_single_of_coord hsub.1 hsub.2).symm
    have hxmem : x = (a⁻¹).1 ((0 : F × F), Pi.single j e) := by
      calc x = (a⁻¹).1 (a.1 x) := (LinearEquiv.inv_apply_apply' a.1 x).symm
        _ = (a⁻¹).1 ((0 : F × F), Pi.single j e) := by rw [he']
    rw [hxmem]
    exact hpinv

private theorem planeTorus_mulSingle_mem
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr2 : 2 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (S : Finset (Fin r))
    {j : Fin r} (hj : j ∉ S) :
    normPlaneTorus E hr2 hpq ξ
        (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))) ∈
      outsideTorus E hr2 hpq ξ S := by
  classical
  refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
  refine (Subgroup.mem_pi (S : Set (Fin r))).mpr fun i hi => ?_
  by_cases hij : i = j
  · exact absurd (hij ▸ hi) hj
  · have hs_i : Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) j
        (Multiplicative.ofAdd (1 : ZMod p)) i = 1 := by
      rw [Pi.mulSingle_eq_of_ne hij]
    exact Subgroup.mem_bot.mpr hs_i

private theorem commutator_coordPlane_apply_eq_self
    (E : QuadExt F K (unitaryInvolution K 2 f))
    {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) {j : Fin r} (hj : j ∉ S)
    {a b : normOmega E r}
    (ha : a ∈ outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S)
    (hb : b ∈ outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S) :
    ∀ v ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin r → K))) j,
      (⁅a, b⁆).1 v = v := by
  classical
  let V := (F × F) × (Fin r → K)
  let P : Submodule F V := coordPlane (LinearEquiv.refl F V) j
  let s : Fin r → Multiplicative (ZMod p) :=
    Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))
  let ρ : normOmega E r :=
    normPlaneTorus E (by omega : 2 ≤ r) hpq ξ s
  have hρT : ρ ∈ outsideTorus E (by omega : 2 ≤ r) hpq ξ S := by
    simpa only [ρ, s, outsideTorus] using planeTorus_mulSingle_mem E (by omega : 2 ≤ r) hpq ξ S hj
  have hρmap : ∀ v ∈ P, ρ.1 v ∈ P := by
    intro v hv
    obtain ⟨x, rfl⟩ := mem_coordPlane.mp hv
    change ρ.1 (((0, 0) : F × F), Pi.single j x) ∈ P
    rw [mem_coordPlane]
    refine ⟨(ξ (s j) : K) * x, ?_⟩
    change (((0, 0) : F × F), Pi.single j ((ξ (s j) : K) * x)) =
      (((0, 0) : F × F), fun i => (ξ (s i) : K) * (Pi.single (M := fun _ => K) j x i))
    have hpv : ρ.1 (((0, 0) : F × F), Pi.single j x) =
        (((0, 0) : F × F), fun i => (ξ (s i) : K) * (Pi.single (M := fun _ => K) j x i)) := by
      dsimp [ρ]
      rw [normPlaneTorus_apply E (by omega : 2 ≤ r) hpq ξ s]
    refine Prod.ext rfl (funext fun i => ?_)
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]

  let y : Module.End F P :=
    { toFun := fun v => ⟨ρ.1 (v : V), hρmap v v.2⟩
      map_add' := fun v w => Subtype.ext (map_add (ρ.1 : V →ₗ[F] V) (v : V) (w : V))
      map_smul' := fun c v => Subtype.ext (map_smul (ρ.1 : V →ₗ[F] V) c (v : V)) }
  have haP : a.1 ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub P :=
    centralizer_mem_stabSub_coordPlane E hr hpq ξ hξ S hj ha
  have hbP : b.1 ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub P :=
    centralizer_mem_stabSub_coordPlane E hr hpq ξ hξ S hj hb
  let aP : P ≃ₗ[F] P := CFSG.ClassicalGroups.Orthogonal.Small.resHom P ⟨a.1, haP⟩
  let bP : P ≃ₗ[F] P := CFSG.ClassicalGroups.Orthogonal.Small.resHom P ⟨b.1, hbP⟩
  have hρcomm_a : ρ * a = a * ρ :=
    (Subgroup.mem_centralizer_iff.mp ha) ρ hρT
  have hρcomm_b : ρ * b = b * ρ :=
    (Subgroup.mem_centralizer_iff.mp hb) ρ hρT
  have hcomm_a : Commute (aP : Module.End F P) y := by
    show (aP : Module.End F P) * y = y * (aP : Module.End F P)
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change a.1 (ρ.1 (v : V)) = ρ.1 (a.1 (v : V))
    have hlin : (ρ.1 : V ≃ₗ[F] V) * a.1 = a.1 * ρ.1 := by
      simpa using congrArg (fun e : normOmega E r => (e : V ≃ₗ[F] V)) hρcomm_a
    have h := congrArg (fun e : V ≃ₗ[F] V => e (v : V)) hlin
    simpa only [LinearEquiv.mul_apply] using h.symm
  have hcomm_b : Commute (bP : Module.End F P) y := by
    show (bP : Module.End F P) * y = y * (bP : Module.End F P)
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change b.1 (ρ.1 (v : V)) = ρ.1 (b.1 (v : V))
    have hlin : (ρ.1 : V ≃ₗ[F] V) * b.1 = b.1 * ρ.1 := by
      simpa using congrArg (fun e : normOmega E r => (e : V ≃ₗ[F] V)) hρcomm_b
    have h := congrArg (fun e : V ≃ₗ[F] V => e (v : V)) hlin
    simpa only [LinearEquiv.mul_apply] using h.symm
  have hlam_ne_one : (ξ (Multiplicative.ofAdd (1 : ZMod p)) : K) ≠ 1 := by
    intro h
    have h1 : ξ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := Units.ext h
    have h2 : Multiplicative.ofAdd (1 : ZMod p) = 1 := hξ (by rw [h1, map_one])
    have h3 : (1 : ZMod p) = 0 := by simpa using congrArg Multiplicative.toAdd h2
    exact one_ne_zero h3
  have hy : ∀ c : F, y ≠ c • (1 : Module.End F P) := by
    intro c hcy
    let v0 : P := ⟨(((0, 0) : F × F), Pi.single j (1 : K)),
      mem_coordPlane.mpr ⟨1, rfl⟩⟩
    have hval := congrArg
      (fun e : Module.End F P => ((e v0 : P) : V)) hcy
    have hleft : ((y v0 : P) : V) =
        (((0, 0) : F × F), Pi.single j ((ξ (s j) : K) * 1)) := by
      change ρ.1 (((0, 0) : F × F), Pi.single j (1 : K)) = _
      dsimp [ρ]
      rw [normPlaneTorus_apply E (by omega : 2 ≤ r) hpq ξ s]
      refine Prod.ext rfl (funext fun i => ?_)
      by_cases hi : i = j
      · subst hi
        simp
      · simp [Pi.single_eq_of_ne hi]
    have hright : ((((c • (1 : Module.End F P)) v0 : P) : V)) =
        (((0, 0) : F × F), fun i => algebraMap F K c * (Pi.single (M := fun _ => K) j (1 : K) i)) := by
      rw [LinearMap.smul_apply, Module.End.one_apply]
      change (c • (v0 : V) : V) = (((0, 0) : F × F),
        fun i => algebraMap F K c * (Pi.single (M := fun _ => K) j (1 : K) i))
      refine Prod.ext ?_ (funext fun i => ?_)
      · change (c • (v0 : V)).1 = ((0, 0) : F × F)
        rw [Prod.smul_fst]
        change c • ((0, 0) : F × F) = ((0, 0) : F × F)
        simp
      · change (c • (v0 : V)).2 i = algebraMap F K c * (Pi.single (M := fun _ => K) j (1 : K) i)
        rw [Prod.smul_snd, Pi.smul_apply, Algebra.smul_def]
    have hcoord := congrArg (fun w : V => w.2 j) hval
    rw [hleft, hright] at hcoord
    simp only [Pi.single_eq_same, mul_one] at hcoord
    have hσ : (ξ (s j) : K) ^ 2 ^ f = (ξ (s j) : K) := by
      rw [← unitaryInvolution_apply, hcoord]
      exact E.fix c
    have hpow : (ξ (s j) : K) ^ (2 ^ f + 1) = 1 := by
      have h := congrArg Units.val (zmodHom_pow_eq_one_of_dvd hpq ξ (s j))
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
    have hsq : (ξ (s j) : K) * (ξ (s j) : K) = 1 := by
      calc (ξ (s j) : K) * (ξ (s j) : K) = (ξ (s j) : K) ^ 2 ^ f * (ξ (s j) : K) := by
            rw [hσ]
        _ = 1 := by rw [← pow_succ, hpow]
    have hone : (ξ (s j) : K) = 1 := by
      rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact h
      · rw [h, CharTwo.neg_eq]
    have hone' : ξ (s j) = 1 := Units.ext hone
    have hs_eq : s j = 1 := hξ (by rw [hone', map_one])
    have hs_ne : s j ≠ 1 := by
      dsimp [s]
      rw [Pi.mulSingle_eq_same]
      intro h
      have h1 : (1 : ZMod p) = 0 := by simpa using congrArg Multiplicative.toAdd h
      exact one_ne_zero h1
    exact hs_ne hs_eq
  have hdimP : Module.finrank F P = 2 := by
    have hdim' : Module.finrank F P = Module.finrank F K := by
      dsimp only [P, coordPlane]
      let L : K →ₗ[F] (Fin r → K) := LinearMap.single F (fun _ => K) j
      have hL : Function.Injective L := by
        intro x y hxy
        have := congrFun hxy j
        simpa [L] using this
      have hinj : Function.Injective
          ((LinearMap.inr F (F × F) (Fin r → K)).comp L) :=
        LinearMap.inr_injective.comp hL
      exact LinearMap.finrank_range_of_inj hinj
    rw [hdim', E.finrank_eq]
  have hcomm_ab_end : Commute (aP : Module.End F P) (bP : Module.End F P) :=
    CFSG.LocalAnalysis.GLTheoremA.H81Orth.commute_of_finrank_two hdimP hy hcomm_a hcomm_b
  have hcomm_ab : aP * bP = bP * aP := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun e : Module.End F P => e v) hcomm_ab_end.eq
  let ga : CFSG.ClassicalGroups.Orthogonal.Small.stabSub P := ⟨a.1, haP⟩
  let gb : CFSG.ClassicalGroups.Orthogonal.Small.stabSub P := ⟨b.1, hbP⟩
  let cP : CFSG.ClassicalGroups.Orthogonal.Small.stabSub P := ⁅ga, gb⁆
  have hres : CFSG.ClassicalGroups.Orthogonal.Small.resHom P cP = ⁅aP, bP⁆ := by
    dsimp only [cP, aP, bP]
    rw [map_commutatorElement]
  have hres_one : CFSG.ClassicalGroups.Orthogonal.Small.resHom P cP = 1 := by
    rw [hres, commutatorElement_eq_one_iff_mul_comm.mpr hcomm_ab]
  have hcP1 : cP.1 = (⁅a, b⁆).1 := by
    simp only [cP, ga, gb, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  intro v hv
  have h1 : ((CFSG.ClassicalGroups.Orthogonal.Small.resHom P cP) ⟨v, hv⟩ : P) =
      ⟨v, hv⟩ := by
    rw [hres_one]
    rfl
  have h2 : ((CFSG.ClassicalGroups.Orthogonal.Small.resHom P cP) ⟨v, hv⟩ : V) =
      (⁅a, b⁆).1 v := by
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply]
    exact congrArg (fun e : V ≃ₗ[F] V => e v) hcP1
  calc (⁅a, b⁆).1 v = ((CFSG.ClassicalGroups.Orthogonal.Small.resHom P cP) ⟨v, hv⟩ : V) :=
        h2.symm
    _ = v := by rw [h1]

private theorem centralizer_maps_coordSupport
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) {a : normOmega E r}
    (ha : a ∈ outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S) :
    ∀ x, x ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin r → K))) S →
      a.1 x ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin r → K))) S := by
  classical
  intro x hx
  rw [mem_coordSupport_refl_iff E S]
  intro j hj
  let s : Fin r → Multiplicative (ZMod p) :=
    Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))
  let ρ : normOmega E r :=
    normPlaneTorus E (by omega : 2 ≤ r) hpq ξ s
  have hρT : ρ ∈ outsideTorus E (by omega : 2 ≤ r) hpq ξ S := by
    simpa only [ρ, s, outsideTorus] using planeTorus_mulSingle_mem E (by omega : 2 ≤ r) hpq ξ S hj
  have hcomm : ρ * a = a * ρ := (Subgroup.mem_centralizer_iff.mp ha) ρ hρT
  have hlin : (ρ.1 : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))) * a.1 =
      a.1 * ρ.1 := by
    simpa using congrArg (fun e : normOmega E r =>
      (e : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K)))) hcomm
  have hρx : ρ.1 x = x := by
    dsimp [ρ]
    rw [normPlaneTorus_apply E (by omega : 2 ≤ r) hpq ξ s]
    refine Prod.ext rfl (funext fun i => ?_)
    change (ξ (s i) : K) * x.2 i = x.2 i
    by_cases hi : i = j
    · have hsi : s i = Multiplicative.ofAdd (1 : ZMod p) := by
        dsimp [s]
        rw [hi, Pi.mulSingle_eq_same]
      have hxj : x.2 i = 0 := by
        rw [hi]
        exact (mem_coordSupport_refl_iff E S x).mp hx j hj
      rw [hsi, hxj, mul_zero]
    · simp [s, Pi.mulSingle_eq_of_ne hi]
  have happ : ρ.1 (a.1 x) = a.1 x := by
    have h := congrArg
      (fun e : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K)) => e x) hlin
    simpa only [LinearEquiv.mul_apply, hρx] using h
  have hcoord : (ξ (s j) : K) * (a.1 x).2 j = (a.1 x).2 j := by
    have h := congrArg (fun w : (F × F) × (Fin r → K) => w.2 j) happ
    dsimp [ρ] at h
    rw [normPlaneTorus_apply E (by omega : 2 ≤ r) hpq ξ s] at h
    simpa using h
  have hlam : (ξ (s j) : K) ≠ 1 := by
    have hs : s j = Multiplicative.ofAdd (1 : ZMod p) := by
      dsimp [s]
      rw [Pi.mulSingle_eq_same]
    rw [hs]
    intro h
    have h1 : ξ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := Units.ext h
    have h2 : Multiplicative.ofAdd (1 : ZMod p) = 1 := hξ (by rw [h1, map_one])
    have h3 : (1 : ZMod p) = 0 := by simpa using congrArg Multiplicative.toAdd h2
    exact one_ne_zero h3
  have hsub : ((ξ (s j) : K) - 1) * (a.1 x).2 j = 0 := by
    rw [sub_mul, one_mul, hcoord, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hlam)

private theorem centralizer_mem_stabSub_coordSupport
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) {a : normOmega E r}
    (ha : a ∈ outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S) :
    a.1 ∈ stabSub (coordSupport (LinearEquiv.refl F ((F × F) × (Fin r → K))) S) := by
  rw [mem_stabSub]
  intro x
  constructor
  · intro hx
    exact centralizer_maps_coordSupport E hr hpq ξ hξ S ha x hx
  · intro hx
    have h := centralizer_maps_coordSupport E hr hpq ξ hξ S (inv_mem ha) (a.1 x) hx
    simpa using h

private theorem commutator_apply_eq_self_of_mem_suppPerp
    (E : QuadExt F K (unitaryInvolution K 2 f))
    {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) {a b : normOmega E r}
    (ha : a ∈ outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S)
    (hb : b ∈ outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S) :
    ∀ v ∈ suppPerp (normHypForm E r)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin r → K))) S),
      (⁅a, b⁆).1 v = v := by
  classical
  intro v hv
  obtain ⟨hv1, hv2⟩ := (mem_suppPerp_coordSupport_refl_iff E S v).mp hv
  have hvdecomp : v = ∑ j ∈ Sᶜ,
      ((((0, 0) : F × F), Pi.single j (v.2 j)) : (F × F) × (Fin r → K)) := by
    refine Prod.ext ?_ ?_
    · rw [hv1, Prod.fst_sum]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      change (((0, 0) : F × F)) = 0
      rfl
    · funext i
      rw [Prod.snd_sum, Finset.sum_apply]
      by_cases hi : i ∈ Sᶜ
      · rw [Finset.sum_eq_single i]
        · change v.2 i = Pi.single (M := fun _ => K) i (v.2 i) i
          rw [Pi.single_eq_same]
        · intro j _ hji
          change Pi.single (M := fun _ => K) j (v.2 j) i = 0
          rw [Pi.single_eq_of_ne hji.symm]
        · intro hnot
          exact absurd hi hnot
      · have hiS : i ∈ S := by simpa using hi
        rw [hv2 i hiS]
        symm
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hji : j ≠ i := by
          intro h
          subst h
          exact hi hj
        change Pi.single (M := fun _ => K) j (v.2 j) i = 0
        rw [Pi.single_eq_of_ne hji.symm]
  rw [hvdecomp, map_sum]
  have hterms : ∀ j ∈ Sᶜ,
      (⁅a, b⁆).1 ((((0, 0) : F × F), Pi.single j (v.2 j)) :
        (F × F) × (Fin r → K)) =
      ((((0, 0) : F × F), Pi.single j (v.2 j)) : (F × F) × (Fin r → K)) := by
    intro j hj
    exact commutator_coordPlane_apply_eq_self E hr hpq ξ hξ S (by simpa using hj) ha hb _
      (mem_coordPlane.mpr ⟨v.2 j, rfl⟩)
  rw [Finset.sum_congr rfl hterms]

private theorem commutator_centralizer_le_normBlock
    (E : QuadExt F K (unitaryInvolution K 2 f))
    {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) :
    ⁅outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S,
      outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S⁆ ≤ normBlock E r S := by
  classical
  rw [Subgroup.commutator_le]
  intro a ha b hb
  let V := (F × F) × (Fin r → K)
  let W : Submodule F V := coordSupport (LinearEquiv.refl F V) S
  have hfix : ∀ v ∈ suppPerp (normHypForm E r) W,
      (⁅a, b⁆ : normOmega E r).1 v = v := by
    intro v hv
    exact commutator_apply_eq_self_of_mem_suppPerp E hr hpq ξ hξ S ha hb v hv
  have haW : a.1 ∈ stabSub W :=
    centralizer_mem_stabSub_coordSupport E hr hpq ξ hξ S ha
  have hbW : b.1 ∈ stabSub W :=
    centralizer_mem_stabSub_coordSupport E hr hpq ξ hξ S hb
  let ga : stabSub W := ⟨a.1, haW⟩
  let gb : stabSub W := ⟨b.1, hbW⟩
  let aW : W ≃ₗ[F] W := resHom W ga
  let bW : W ≃ₗ[F] W := resHom W gb
  let h : W ≃ₗ[F] W := ⁅aW, bW⁆
  have haO : a.1 ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r) :=
    orthDerived_le_orthogonalGroup_of_commutator (normHypForm E r) a.2
  have hbO : b.1 ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r) :=
    orthDerived_le_orthogonalGroup_of_commutator (normHypForm E r) b.2
  have hhO : h ∈ orthDerived ((normHypForm E r).comp W.subtype) := by
    dsimp only [h, aW, bW]
    exact Subgroup.commutator_mem_commutator
      (resHom_mem_orthogonalGroup haO haW) (resHom_mem_orthogonalGroup hbO hbW)
  have hact : ∀ w : W, ((h w : W) : V) = (⁅a, b⁆ : normOmega E r).1 w := by
    intro w
    dsimp only [h, aW, bW]
    rw [← map_commutatorElement (resHom W) ga gb, resHom_apply]
    have hval : ((⁅ga, gb⁆ : stabSub W) : V ≃ₗ[F] V) = (⁅a, b⁆ : normOmega E r).1 := rfl
    rw [hval]
  have hgSD : ((⁅a, b⁆ : normOmega E r).1 : V ≃ₗ[F] V) ∈
      supportedDerived (normHypForm E r) W :=
    mem_supportedDerived.mpr ⟨hfix, h, hhO, hact⟩
  rw [normBlock]
  exact Subgroup.mem_subgroupOf.mpr hgSD

private theorem normBlock_le_centralizer
    (E : QuadExt F K (unitaryInvolution K 2 f))
    {r : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (ξ : Multiplicative (ZMod p) →* Kˣ) (S : Finset (Fin r)) :
    normBlock E r S ≤ Subgroup.centralizer
      (((Subgroup.pi (S : Set (Fin r))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map
          (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ)) :
        Set (normOmega E r)) := by
  classical
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let V := (F × F) × (Fin r → K)
  let Q : QuadraticForm F V := normHypForm E r
  let W : Submodule F V := coordSupport (LinearEquiv.refl F V) S
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
  have hmSD : (m : V ≃ₗ[F] V) ∈ supportedDerived Q W := by
    rw [normBlock] at hm
    exact Subgroup.mem_subgroupOf.mp hm
  have huS : ∀ i, i ∈ S → u i = 1 := fun i hi =>
    (Subgroup.mem_pi (S : Set (Fin r))).mp hu i hi
  have hWnd : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate := by
    simpa only [Q, W] using
      coordSupport_nondegenerate (ψ := LinearEquiv.refl F V)
        (hψ := normHypForm_apply_coord E r)
        (hQ := normHypForm_polarBilin_nondegenerate E r)
        (hQE := normQuad_polarBilin_nondegenerate E) S
  have htO : ((normPlaneTorus E (by omega : 2 ≤ r)
      hpq ξ u : normOmega E r) : V ≃ₗ[F] V) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup_of_commutator Q
      (normPlaneTorus E (by omega : 2 ≤ r) hpq ξ u).2
  have htW : ∀ x ∈ W,
      ((normPlaneTorus E (by omega : 2 ≤ r) hpq ξ u :
        normOmega E r) : V ≃ₗ[F] V) x = x := by
    intro x hx
    rw [normPlaneTorus_apply E (by omega : 2 ≤ r) hpq ξ u]
    refine Prod.ext rfl (funext fun i => ?_)
    change (ξ (u i) : K) * x.2 i = x.2 i
    by_cases hi : i ∈ S
    · rw [huS i hi, map_one, Units.val_one, one_mul]
    · rw [(mem_coordSupport_refl_iff E S x).mp hx i hi, mul_zero]
  have hmW : ∀ x ∈ W, (m : V ≃ₗ[F] V) x ∈ W := fun x hx =>
    supportedDerived_apply_mem hmSD hx
  have hmP : ∀ x ∈ CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q W,
      (m : V ≃ₗ[F] V) x = x := by
    intro x hx
    exact hmSD.1 x (by
      simpa only [suppPerp, CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp] using hx)
  have hcomm := CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq
    (Q := Q) (U := W) hWnd htO htW hmW hmP
  exact Subtype.ext hcomm

theorem normPlaneTorus_mem_normBlock_of_support
    (E : QuadExt F K (unitaryInvolution K 2 1)) {r : ℕ} (hr2 : 2 ≤ r)
    (xi : Multiplicative (ZMod 3) →* Kˣ) (S : Finset (Fin r))
    (u : Fin r → Multiplicative (ZMod 3)) (hu : ∀ i, i ∉ S → u i = 1) :
    normPlaneTorus E hr2 (by decide : 3 ∣ 2 ^ 1 + 1) xi u ∈ normBlock E r S := by
  classical
  have hpq : 3 ∣ 2 ^ 1 + 1 := by decide
  let V := (F × F) × (Fin r → K)
  let W : Submodule F V := coordSupport (LinearEquiv.refl F V) S
  let b : V ≃ₗ[F] V := normBar E S
  let t0 : normOmega E r := normPlaneTorus E hr2 hpq xi u
  let t : V ≃ₗ[F] V := t0
  have hbapply : ∀ v : V,
      b v = (v.1, fun i => if i ∈ S then unitaryInvolution K 2 1 (v.2 i) else v.2 i) :=
    fun v => rfl
  have htapply : ∀ v : V, t v = (v.1, fun i => (xi (u i) : K) * v.2 i) :=
    fun v => normPlaneTorus_apply E hr2 hpq xi u v
  have hfix : ∀ v ∈ suppPerp (normHypForm E r) W, t v = v := by
    intro v hv
    obtain ⟨-, hv2⟩ := (mem_suppPerp_coordSupport_refl_iff E S v).mp hv
    rw [htapply]
    refine Prod.ext rfl (funext fun i => ?_)
    change (xi (u i) : K) * v.2 i = v.2 i
    by_cases hi : i ∈ S
    · rw [hv2 i hi, mul_zero]
    · simp [hu i hi]
  have hbW : b ∈ stabSub W := by
    rw [mem_stabSub]
    intro x
    rw [mem_coordSupport_refl_iff E S x, mem_coordSupport_refl_iff E S (b x)]
    constructor
    · intro hx j hj
      rw [hbapply]
      simp [hj, hx j hj]
    · intro hx j hj
      simpa [hbapply, hj] using hx j hj
  have htW : t ∈ stabSub W := by
    rw [mem_stabSub]
    intro x
    rw [mem_coordSupport_refl_iff E S x, mem_coordSupport_refl_iff E S (t x)]
    constructor
    · intro hx j hj
      change (xi (u j) : K) * x.2 j = 0
      simp [hu j hj, hx j hj]
    · intro hx j hj
      simpa [htapply, hu j hj] using hx j hj
  have hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r) :=
    normBar_mem_orthogonalGroup E S
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r) :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
      (Q := normHypForm E r) t0.2
  have hu3 : u ^ 3 = 1 := by
    funext i
    simpa using pow_card_eq_one' (x := u i)
  have ht3 : t ^ 3 = 1 := by
    have h := map_pow (normPlaneTorus E hr2 hpq xi) u 3
    rw [hu3, map_one] at h
    simpa [t, t0] using (congrArg (fun e : normOmega E r => (e : V ≃ₗ[F] V)) h).symm
  have hinv_fun : (fun i => if i ∈ S then (u i)⁻¹ else u i) = u⁻¹ := by
    funext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, hu i hi]
  have hconj0 : normOmegaConj E (normBar_mem_orthogonalGroup E S)
      (normPlaneTorus E hr2 hpq xi u) = (normPlaneTorus E hr2 hpq xi u)⁻¹ := by
    rw [normOmegaConj_normBar_normPlaneTorus E hr2 hpq xi S u, hinv_fun, map_inv]
  have hconj : b * t * b⁻¹ = t⁻¹ := by
    have h := congrArg (fun e : normOmega E r => (e : V ≃ₗ[F] V)) hconj0
    rw [normOmegaConj_apply] at h
    simpa [b, t, t0] using h
  have ht2 : t ^ 2 * t = 1 := by
    simpa [pow_succ] using ht3
  have ht_inv_inv : t⁻¹ * t⁻¹ = t := by
    calc t⁻¹ * t⁻¹ = (t ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
      _ = t := inv_eq_of_mul_eq_one_right ht2
  have hcomm : ⁅b, t⁆ = t := by
    rw [commutatorElement_def, hconj, ht_inv_inv]
  let hb : stabSub W := ⟨b, hbW⟩
  let ht : stabSub W := ⟨t, htW⟩
  let hW : W ≃ₗ[F] W := ⁅resHom W hb, resHom W ht⁆
  have hhO : hW ∈ orthDerived ((normHypForm E r).comp W.subtype) := by
    dsimp only [hW]
    exact Subgroup.commutator_mem_commutator
      (resHom_mem_orthogonalGroup hbO hbW)
      (resHom_mem_orthogonalGroup htO htW)
  change t ∈ supportedDerived (normHypForm E r) W
  refine mem_supportedDerived.mpr ⟨hfix, hW, hhO, ?_⟩
  intro w
  change (((hW w : W) : V)) = t w
  dsimp only [hW]
  rw [← map_commutatorElement (resHom W) hb ht]
  rw [resHom_apply]
  have hval : ((⁅hb, ht⁆ : stabSub W) : V ≃ₗ[F] V) = ⁅b, t⁆ := rfl
  rw [hval, hcomm]

theorem commutator_centralizer_normPlaneTorus_eq_normBlock_of_dvd
    {r : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (ξ : Multiplicative (ZMod p) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) (hS : S.Nonempty) :
    let τ := normPlaneTorus E (by omega : 2 ≤ r) hpq ξ
    let T := (Subgroup.pi (S : Set (Fin r))
      (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map τ
    ⁅Subgroup.centralizer (T : Set (normOmega E r)),
      Subgroup.centralizer (T : Set (normOmega E r))⁆ = normBlock E r S := by
  classical
  change ⁅outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S,
      outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S⁆ = normBlock E r S
  have hCperf : Group.IsPerfect ↥(normBlock E r S) := isPerfect_normBlock E hr S hS
  have hMC : normBlock E r S ≤ outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S :=
    normBlock_le_centralizer E hr hpq ξ S
  have hupper : ⁅outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S,
      outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S⁆ ≤ normBlock E r S :=
    commutator_centralizer_le_normBlock E hr hpq ξ hξ S
  have hlower : normBlock E r S ≤
      ⁅outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S,
        outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S⁆ := by
    calc normBlock E r S = ⁅normBlock E r S, normBlock E r S⁆ :=
          (Subgroup.isPerfect_iff.mp hCperf).symm
      _ ≤ ⁅outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S,
            outsideCentralizer E (by omega : 2 ≤ r) hpq ξ S⁆ :=
          Subgroup.commutator_mono hMC hMC
  exact le_antisymm hupper hlower

theorem commutator_centralizer_normPlaneTorus_eq_normBlock
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (E : QuadExt F K (unitaryInvolution K 2 1)) (_hF : Nat.card F = 2)
    {r : ℕ} (hr : 3 ≤ r)
    (ξ : Multiplicative (ZMod 3) →* Kˣ) (hξ : Function.Injective ξ)
    (S : Finset (Fin r)) (hS : S.card = 1 ∨ S.card = 2)
    (_hproper : S ≠ Finset.univ) :
    let τ := normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) ξ
    let T := (Subgroup.pi (S : Set (Fin r))
      (fun _ => (⊥ : Subgroup (Multiplicative (ZMod 3))))).map τ
    ⁅Subgroup.centralizer (T : Set (normOmega E r)),
      Subgroup.centralizer (T : Set (normOmega E r))⁆ = normBlock E r S :=
  commutator_centralizer_normPlaneTorus_eq_normBlock_of_dvd E hr (by decide) ξ hξ S
    (Finset.card_pos.mp (by omega))

theorem commutator_normBlock_pair_inf_centralizer_planeTorus_eq
    (E : QuadExt F K (unitaryInvolution K 2 f)) {m p : ℕ} [Fact p.Prime]
    (hm : 3 ≤ m) (hpq : p ∣ 2 ^ f + 1) (χ : Multiplicative (ZMod p) →* Kˣ)
    (hχ : Function.Injective χ) {s s' : Fin m} (hss' : s ≠ s') :
    ⁅normBlock E m {s, s'} ⊓ Subgroup.centralizer
        {normPlaneTorus E (by omega) hpq χ (Pi.mulSingle s' (Multiplicative.ofAdd 1))},
      normBlock E m {s, s'} ⊓ Subgroup.centralizer
        {normPlaneTorus E (by omega) hpq χ (Pi.mulSingle s' (Multiplicative.ofAdd 1))}⁆ =
      normBlock E m {s} := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hm2 : 2 ≤ m := by omega
  let τ := normPlaneTorus E hm2 hpq χ
  let t := τ (Pi.mulSingle s' (Multiplicative.ofAdd (1 : ZMod p)))
  let M := normBlock E m {s, s'} ⊓ Subgroup.centralizer {t}
  change ⁅M, M⁆ = normBlock E m {s}
  have hMC : M ≤ outsideCentralizer E hm2 hpq χ {s} := by
    intro g hg
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hus : u s = 1 :=
      (Subgroup.mem_pi ((({s} : Finset (Fin m)) : Set (Fin m)))).mp hu s (by simp)
    let v : Fin m → Multiplicative (ZMod p) := Pi.mulSingle s' (u s')
    have hw : (v⁻¹ * u) ∈ Subgroup.pi ((({s, s'} : Finset (Fin m)) : Set (Fin m)))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p)))) := by
      refine (Subgroup.mem_pi _).mpr fun i hi => Subgroup.mem_bot.mpr ?_
      have hi' : i = s ∨ i = s' := by simpa using hi
      rcases hi' with rfl | rfl
      · simp [v, Pi.mulSingle_eq_of_ne hss', hus]
      · simp [v]
    have hcw : τ (v⁻¹ * u) * g = g * τ (v⁻¹ * u) :=
      Subgroup.mem_centralizer_iff.mp (normBlock_le_centralizer E hm hpq χ {s, s'} hg.1) _
        (Subgroup.mem_map_of_mem τ hw)
    have hvt : τ v = t ^ (Multiplicative.toAdd (u s')).val := by
      have hpow : Multiplicative.ofAdd (1 : ZMod p) ^ (Multiplicative.toAdd (u s')).val = u s' := by
        rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
      rw [← map_pow, ← Pi.mulSingle_pow, hpow]
    have hct : t * g = g * t := Subgroup.mem_centralizer_iff.mp hg.2 t (Set.mem_singleton t)
    have hcv : Commute (τ v) g := by
      rw [hvt]
      exact (Commute.pow_left hct _)
    have hu_eq : u = v * (v⁻¹ * u) := by rw [mul_inv_cancel_left]
    rw [hu_eq, map_mul]
    exact (hcv.mul_left hcw).eq
  have hlow : normBlock E m {s} ≤ M := by
    intro g hg
    refine ⟨normBlock_mono E m (by simp) hg, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ rfl
    have ht : t ∈ outsideTorus E hm2 hpq χ {s} := by
      refine Subgroup.mem_map_of_mem τ ((Subgroup.mem_pi _).mpr fun i hi => ?_)
      have hi' : i = s := by simpa using hi
      subst hi'
      exact Subgroup.mem_bot.mpr (Pi.mulSingle_eq_of_ne hss' _)
    exact Subgroup.mem_centralizer_iff.mp (normBlock_le_centralizer E hm hpq χ {s} hg) t ht
  have hperf : Group.IsPerfect ↥(normBlock E m {s}) :=
    isPerfect_normBlock E hm {s} (Finset.singleton_nonempty s)
  refine le_antisymm ((Subgroup.commutator_mono hMC hMC).trans
    (commutator_centralizer_le_normBlock E hm hpq χ hχ {s})) ?_
  calc normBlock E m {s} = ⁅normBlock E m {s}, normBlock E m {s}⁆ :=
        (Subgroup.isPerfect_iff.mp hperf).symm
    _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hlow hlow

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
