module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoAut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bCover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Zstar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section PiE

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem hΩ_of (hc : P23Cfg n Y R S t K' W u e g) : HypOmegaGen (Om R) :=
  (CoreData.of_S hc.std.perp.core).hyp

theorem hc2e_of (hc : P23Cfg n Y R S t K' W u e g) : IsPGroup 2 (Subgroup.zpowers e) :=
  CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2

theorem h2_of (hc : P23Cfg n Y R S t K' W u e g) :
    ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := by
  have hC := CoreData.of_S hc.std.perp.core
  exact TwinADescent3.isPGroup_two_quotient_conjClass
    (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)

theorem hmap_of (hc : P23Cfg n Y R S t K' W u e g) :
    (coreHull (Om R) e).map (Subgroup.centralizer ({e} : Set Y)).subtype = rLayer (Om R) e :=
  TwinPerpV3.coreHull_map_eq_rLayer (hΩ_of hc) (hc2e_of hc) (h2_of hc)

@[expose] noncomputable def piE (hc : P23Cfg n Y R S t K' W u e g) :
    ↥(rLayer (Om R) e) →* SecQ R e :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))).comp
    (TwinPerpV3.hullEquiv (hmap_of hc)).symm.toMonoidHom

theorem piE_surjective (hc : P23Cfg n Y R S t K' W u e g) : Function.Surjective (piE hc) := by
  intro q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨TwinPerpV3.hullEquiv (hmap_of hc) h, by simp [piE]⟩

theorem piE_eq_one_iff (hc : P23Cfg n Y R S t K' W u e g) (x : ↥(rLayer (Om R) e)) :
    piE hc x = 1 ↔ (x : Y) ∈ oddCoreOf (rLayer (Om R) e) := by
  set h := (TwinPerpV3.hullEquiv (hmap_of hc)).symm x with hh
  have hx : (x : Y) = (((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) := by
    have := TwinPerpV3.hullEquiv_coe (hmap_of hc) h
    rw [hh, MulEquiv.apply_symm_apply] at this
    exact this
  show (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))) h = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hx]
  constructor
  · intro hn
    have := mem_oddCoreOf_coreLayer (hΩ_of hc) (hc2e_of hc) hn
    rwa [show coreLayer (Om R) e = rLayer (Om R) e from hmap_of hc] at this
  · intro hn
    exact R56.mem_oddCore_coreHull_of_mem_oddCoreOf_coreLayer
      (by rwa [show coreLayer (Om R) e = rLayer (Om R) e from hmap_of hc])

theorem piE_eq_iff (hc : P23Cfg n Y R S t K' W u e g) (x x' : ↥(rLayer (Om R) e)) :
    piE hc x = piE hc x' ↔ ((x⁻¹ * x' : ↥(rLayer (Om R) e)) : Y) ∈ oddCoreOf (rLayer (Om R) e) := by
  rw [← piE_eq_one_iff hc, map_mul, map_inv, inv_mul_eq_one, eq_comm]

theorem secAut_piE (hc : P23Cfg n Y R S t K' W u e g) {c : Y} (hcC : c ∈ Subgroup.centralizer ({e} : Set Y))
    (x : ↥(rLayer (Om R) e)) (hcx : c * (x : Y) * c⁻¹ ∈ rLayer (Om R) e) :
    TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨c, hcC⟩ (piE hc x) =
      piE hc ⟨c * (x : Y) * c⁻¹, hcx⟩ := by
  set h := (TwinPerpV3.hullEquiv (hmap_of hc)).symm x with hh
  have hx : (x : Y) = (((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) := by
    have := TwinPerpV3.hullEquiv_coe (hmap_of hc) h
    rw [hh, MulEquiv.apply_symm_apply] at this
    exact this
  have hnorm := TwinExitPf6.normal_coreHull (hΩ_of hc) (hc2e_of hc)
  set h' : ↥(coreHull (Om R) e) :=
    ⟨⟨c, hcC⟩ * (h : ↥(Subgroup.centralizer ({e} : Set Y))) * ⟨c, hcC⟩⁻¹, hnorm.conj_mem _ h.2 _⟩ with hh'
  have h1 : piE hc x = QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h := rfl
  rw [h1, TwinExitPf6.secAut_mk (hΩ_of hc) (hc2e_of hc) ⟨c, hcC⟩ h h' rfl]
  have h3 : ((h' : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = c * (x : Y) * c⁻¹ := by
    show c * (((h : ↥(Subgroup.centralizer ({e} : Set Y)))) : Y) * c⁻¹ = _
    rw [← hx]
  have h2 : (TwinPerpV3.hullEquiv (hmap_of hc)).symm ⟨c * (x : Y) * c⁻¹, hcx⟩ = h' := by
    apply (TwinPerpV3.hullEquiv (hmap_of hc)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [TwinPerpV3.hullEquiv_coe]
    exact h3.symm
  show _ = QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))
    ((TwinPerpV3.hullEquiv (hmap_of hc)).symm ⟨c * (x : Y) * c⁻¹, hcx⟩)
  rw [h2]

end PiE

section Cover

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

@[expose] noncomputable def AEData.ofIdent {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (I : AEIdent Φ 6) (hgen : pSpan Φ = ⊤) : AEData X Φ where
  φ := I.φ.comp ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv).symm.toMonoidHom
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv).symm.surjective, Subgroup.map_top]
    exact I.range_eq
  ker_le := by
    intro x hx
    have hx' : ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv).symm x ∈ I.φ.ker := hx
    have hz := Subgroup.mem_center_iff.mp (I.ker_le hx')
    rw [Subgroup.mem_center_iff]
    intro g
    have := hz (((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv).symm g)
    have h2 := congrArg ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv) this
    simpa using h2
  label := by
    intro L hL
    obtain ⟨β, h, b, hlab⟩ := I.label L hL
    refine ⟨β, h, b, ?_⟩
    rw [← hlab]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, le_pSpan hL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : X), Subgroup.mem_subgroupOf.mp hx, rfl⟩
  label_surj := by
    intro β h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj β h b
    refine ⟨L, hL, ?_⟩
    rw [← hlab]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, le_pSpan hL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : X), Subgroup.mem_subgroupOf.mp hx, rfl⟩

structure AECover (Q : Type) [Group Q] (Φ : Set (Subgroup Q)) extends AEData Q Φ where
  card8 : ∀ L ∈ Φ, Nat.card L = 8
  inj : ∀ L ∈ Φ, ∀ x ∈ L, ∀ x' ∈ L, φ x = φ x' → x = x'
  label_inj : ∀ L ∈ Φ, ∀ L' ∈ Φ, L.map φ = L'.map φ → L = L'
  twin_comm : ∀ (α : Finset (Fin 6)) (h : α.card = 4), ∀ L ∈ Φ, ∀ L' ∈ Φ,
    L.map φ = memBar α h true → L'.map φ = memBar α h false → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x
  perfect : Group.IsPerfect Q
  oddFree : classicalInvolutionOddCore Q = ⊥
  ker_card : Nat.card φ.ker ≤ 2

theorem AEData.ofIdent_map {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (I : AEIdent Φ 6) (hgen : pSpan Φ = ⊤) (L : Subgroup X) :
    L.map (AEData.ofIdent I hgen).φ = (L.subgroupOf (pSpan Φ)).map I.φ := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, by rw [hgen]; exact Subgroup.mem_top x⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : X), Subgroup.mem_subgroupOf.mp hx, rfl⟩

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem twins_tq (hc : P23Cfg n Y R S t K' W u e g) :
    tightCore R ∈ tqMembers3 (Om R) e ∧ K' ∈ tqMembers3 (Om R) e := by
  have hd := hc.data
  have hΩ := hΩ_of hc
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  exact ⟨⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ (h2_of hc) hK ⟨R₁, hR₁, hR₁e⟩⟩,
    ⟨hc.std.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ (h2_of hc) hc.std.hK'.1 ⟨R₁', hR₁', hR₁'e⟩⟩⟩

theorem exists_cover (hc : P23Cfg n Y R S t K' W u e g)
    (hAE : SecAE R e 6) : Nonempty (AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) := by
  classical
  obtain ⟨I⟩ := hAE
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ := hΩ_of hc
  have hc2' := hc2e_of hc
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hS := p23_q8Section hc.std.perp hd.he2
  have hgen : pSpan (TwinDisc.secFam (Om R) e) = ⊤ := TwinDisc.AE5.hgen_of hS
  have hn5 : 5 ≤ 6 := by norm_num
  have h8 := TwinDisc.AE5.members_card8 hn5 hS I
  have hKtq := (twins_tq hc).1
  have hK'tq := (twins_tq hc).2
  obtain ⟨htC, htY, hzA⟩ := isUniqueInvolution_secImg hΩ hc2' hKtq hz
  obtain ⟨htC', htY', hzA'⟩ := isUniqueInvolution_secImg hΩ hc2' hK'tq hz'
  have hne_img := secImg_ne_of_twins hΩ hc2' hKtq hK'tq hc.std.hne hz hz'
  have hH : TL4.AECoverHyp I :=
    TwinPerpV3.A6b.aeCoverHyp_of_twins hn5 (by norm_num) hS I (secImg_mem_secFam hKtq)
      (secImg_mem_secFam hK'tq) hne_img.symm hzA hzA'
  have hconj : ∀ L ∈ TwinDisc.secFam (Om R) e, ∀ x ∈ pSpan (TwinDisc.secFam (Om R) e),
      conjSub x L ∈ TwinDisc.secFam (Om R) e := fun L hL x _ => hS.hyp.conjInvariant x L hL
  have hinj : ∀ L ∈ TwinDisc.secFam (Om R) e, ∀ L' ∈ TwinDisc.secFam (Om R) e,
      (L.subgroupOf (pSpan (TwinDisc.secFam (Om R) e))).map I.φ =
        (L'.subgroupOf (pSpan (TwinDisc.secFam (Om R) e))).map I.φ → L = L' :=
    fun L hL L' hL' h => TwinDisc.AE5.same_of_image_n hn5 hS I hL hL' h
  have hperf := TL4.AECov.isPerfect_pSpan I hn5 h8 hconj hinj
  let eqv : ↥(pSpan (TwinDisc.secFam (Om R) e)) ≃* SecQ R e :=
    (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  refine ⟨{ toAEData := AEData.ofIdent I hgen
            card8 := h8
            inj := ?_
            label_inj := ?_
            twin_comm := ?_
            perfect := ?_
            oddFree := hS.oddFree
            ker_card := ?_ }⟩
  · intro L hL x hx x' hx' he
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact I.injOn hn5 hL (h8 L hL) hlab hx hx' he
  · intro L hL L' hL' h
    rw [AEData.ofIdent_map, AEData.ofIdent_map] at h
    exact hinj L hL L' hL' h
  · intro α h L hL L' hL' hl hl' x hx y hy
    rw [AEData.ofIdent_map] at hl hl'
    exact hH.twin_comm α h L hL L' hL' hl hl' x hx y hy
  · refine ⟨?_⟩
    have h1 := hperf.commutator_eq_top
    have h2 := congrArg (Subgroup.map eqv.toMonoidHom) h1
    have hmt : Subgroup.map eqv.toMonoidHom ⊤ = ⊤ :=
      Subgroup.map_top_of_surjective eqv.toMonoidHom eqv.surjective
    rw [commutator, Subgroup.map_commutator, hmt] at h2
    rw [commutator]
    exact h2
  · have hk := (Sec13.aeCover_ker hH hn5).1
    have hker : (AEData.ofIdent I hgen).φ.ker = I.φ.ker.map eqv.toMonoidHom := by
      ext x
      constructor
      · intro hx
        exact ⟨eqv.symm x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        show (AEData.ofIdent I hgen).φ (eqv y) = 1
        have : (AEData.ofIdent I hgen).φ (eqv y) = I.φ y := by
          show I.φ (eqv.symm (eqv y)) = _
          rw [MulEquiv.symm_apply_apply]
        rw [this]
        exact hy
    rw [hker, Subgroup.card_map_of_injective eqv.injective]
    exact hk

end Cover

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
