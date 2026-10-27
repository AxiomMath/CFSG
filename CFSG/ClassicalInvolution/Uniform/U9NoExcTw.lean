module

public import CFSG.ClassicalInvolution.Uniform.U9NoExcCore
public import CFSG.ClassicalInvolution.Uniform.U8Twist

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.ModelFacts (Gen3 gen3_of_equiv_sl2)
open scoped MatrixGroups commutatorElement



section TwistedNormalizer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.Q3 (Exc3Frob exc3_two_orbit_data exc3_multi_structure
  exc3_two_orbit_exp e6_twoClass_two exc3_isSubnormal_orbitGroup_totalFixedGroup)

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem twistedR_normalizes_rankOneFix (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (hq : p ^ e = 3) (eR : SL(2, ZMod 3) ≃* ↥(rankOneFix p k e))
    {y : ModGL TwistTag.E6.tag k} (hyR : y ∈ twistedR p k e) (hyx : involX k * y = y * involX k) :
    (rankOneFix p k e).map (MulAut.conj y).toMonoidHom = rankOneFix p k e := by
  classical
  obtain ⟨D, s, h, hhT, hDχ, hDe, hDθ, hDF, hconj⟩ := exists_mask2_datum3 p hp hk he
  obtain ⟨J₁, J₂, hne, hJ, h1, h2⟩ := exists_two_orbits D hDχ hDθ
  have hC₁ := orbitGroup_J₁_eq D hDχ hDθ h1 he hDe hconj
  have hq3D : p ^ D.e = 3 := by rw [hDe]; exact hq
  set u := rootDiagUnit TwistTag.E6.tag s with hu
  set Mk := torusGroup TwistTag.E6.tag k ⊔
    rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)) with hMk
  set Fk := frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) with hFk
  have hMG : Mk ≤ adjointGroup TwistTag.E6.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
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
  have hfrob : Exc3Frob D c := ⟨fun y => by rw [hDe]; exact hDF y, hcT, hc2⟩
  obtain ⟨β₀, γ₁, hβ₀, hγ₁, hfix, hiso, hne1, hne2, hrest, hns⟩ := e6_twoClass_two
  have hθβ₀ : D.θ (toReal β₀) = toReal β₀ := (hDθ β₀).trans (congrArg toReal hfix)
  obtain ⟨J₀, J₁', hne', hall', hsq', hone⟩ := exc3_two_orbit_data (D := D)
    (τ := TwistTag.E6.tag) (Or.inr (Or.inl rfl)) hfrob hq3D hDχ hβ₀ hγ₁ hiso hθβ₀ ⟨hne1, hne2⟩
    (fun γ hγ h1 h2 => ⟨0, γ₁, hγ₁, by simp, hrest γ hγ h1 h2⟩) (Or.inl hns)
  set Xh := D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype with hXh
  have hRfin : Finite (twistedR p k e) := finite_fixedPointsIn_frobTwistGL p he (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (iterateFrobenius k p e))
    (diagramMap_pow_order TwistTag.E6 k)
  have hXhR : Xh ≤ (twistedR p k e).map (MulAut.conj u).toMonoidHom := by
    rw [← hconj]
    exact Subgroup.map_mono (inf_le_inf_right _ hMG)
  have hRfin' : Finite ↥((twistedR p k e).map (MulAut.conj u).toMonoidHom) :=
    Finite.of_equiv _ ((twistedR p k e).equivMapOfInjective (MulAut.conj u).toMonoidHom
      (MulAut.conj u).injective).toEquiv
  have hXhfin : Finite Xh :=
    Finite.of_injective (fun x : Xh => (⟨x.1, hXhR x.2⟩ :
      ↥((twistedR p k e).map (MulAut.conj u).toMonoidHom))) fun a b hab => by
      apply Subtype.ext
      have := congrArg Subtype.val hab
      exact this
  have hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤ Xh :=
    fun J' => orbitGroup_le_totalFixed D J'
  have hstruct := exc3_multi_structure hfrob hq3D hone
    (exc3_two_orbit_exp hfrob hq3D hne' hall' hsq') (Y := Xh) hCY
    (fun y hy => Xh.pow_mem hy 2)
    (fun y hy v hv => Xh.mul_mem (Xh.mul_mem hy hv) (Xh.inv_mem hy))
  obtain ⟨hyG, hyF⟩ := mem_fixedPointsIn.1 hyR
  have hyM : y ∈ fixedPointsIn Mk Fk := mem_fixedPointsIn_of_commutes_involX hp hyG hyF hyx
  have hy'Xh : u * y * u⁻¹ ∈ Xh := by
    rw [← hconj]
    exact ⟨y, hyM, rfl⟩
  set R := rankOneFix p k e with hR
  set C₁ := (D.withOrbit J₁).orbitGroup with hC₁def
  have hC₁' : C₁ = conjSub u R := hC₁
  have hC₁Y : C₁ ≤ Xh := hCY J₁
  have hC₁sub : CFSG.Open.IsSubnormal C₁ Xh := exc3_isSubnormal_orbitGroup_totalFixedGroup D J₁
  let eC₁ : SL(2, ZMod 3) ≃* C₁ := eR.trans
    ((R.equivMapOfInjective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective).trans
      (MulEquiv.subgroupCongr hC₁.symm))
  set y' := u * y * u⁻¹ with hy'
  set C' := C₁.map (MulAut.conj y').toMonoidHom with hC'
  have hC'Y : C' ≤ Xh := by
    rintro _ ⟨x, hx, rfl⟩
    exact Xh.mul_mem (Xh.mul_mem hy'Xh (hC₁Y hx)) (Xh.inv_mem hy'Xh)
  have hC'sub : CFSG.Open.IsSubnormal C' Xh := isSubnormal_map_conj_of_mem hC₁sub hy'Xh
  let eC' : SL(2, ZMod 3) ≃* C' := eC₁.trans
    (C₁.equivMapOfInjective (MulAut.conj y').toMonoidHom (MulAut.conj y').injective)
  obtain ⟨Ja, hJa, hCa⟩ := hstruct.2 C₁ hC₁Y ⟨eC₁⟩ hC₁sub
  obtain ⟨Jb, hJb, hCb⟩ := hstruct.2 C' hC'Y ⟨eC'⟩ hC'sub
  have hJab : Ja = Jb := hone Ja Jb hJa hJb
  have hC'C₁ : C' = C₁ := by rw [hCb, hCa, hJab]
  have hconjC : C' = conjSub u (conjSub y R) := by
    rw [hC', hC₁']
    change conjSub y' (conjSub u R) = conjSub u (conjSub y R)
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    rw [hy']
    group
  have hfin : conjSub u (conjSub y R) = conjSub u R := by
    rw [← hconjC, hC'C₁, hC₁']
  exact conjSub_injective u hfin

end TwistedNormalizer

section TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (conjSub_mem_fundamentalSubgroups)

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem involX_orderOf_eq_two3 (hk2 : ringChar k ≠ 2) : orderOf (involX k) = 2 := by
  have hsq : involX k * involX k = 1 := by
    unfold involX
    rw [← rootDiagUnit_mul]
    have : signMaskTuple TwistTag.E6.tag k 2 * signMaskTuple TwistTag.E6.tag k 2 = 1 := by
      funext j
      simp only [Pi.mul_apply, Pi.one_apply, signMaskTuple]
      rw [← mul_pow]
      simp
    rw [this]
    exact rootDiagUnit_one
  have hne : involX k ≠ 1 := by
    intro h
    have h1 := rootDiagUnit_injective (K := k) (h.trans rootDiagUnit_one.symm)
    have h2 := congrFun h1 ⟨1, by decide⟩
    simp only [signMaskTuple, Pi.one_apply] at h2
    norm_num at h2
    have h3 : ((-1 : kˣ) : k) = ((1 : kˣ) : k) := congrArg Units.val h2
    simp only [Units.val_neg, Units.val_one] at h3
    exact hk2 (by rw [← neg_one_eq_one_iff]; exact h3)
  exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne

theorem involX_mem_rankOneFix3 (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e) :
    involX k ∈ rankOneFix p k e := by
  obtain ⟨D, s, h, hhT, hDχ, hDe, hDθ, hDF, hconj⟩ := exists_mask2_datum3 p hp hk he
  obtain ⟨J₁, J₂, hne, hJ, h1, h2⟩ := exists_two_orbits D hDχ hDθ
  exact involX_mem_rankOneFix D hDχ hDθ h1 he hDe hconj

variable {n : ℕ}

theorem noTwinExc3_twistedE6 (hadm : StatedLieAdmissible .twistedE6 n 3 1) :
    ∀ R₁ ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 3 1 Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 3 1 Fact.out).D, R₁ ≠ R₂ →
    ∀ (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)),
      sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center (modelUniv .twistedE6 0 3 1 Fact.out).K := by
  classical
  obtain rfl : n = 0 := hadm.2.2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  have hfund : IsFundTag .twistedE6 := trivial
  have hfin : Finite (modelUniv .twistedE6 0 3 1 Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  set K0 := GaloisField 3 (2 * 1) with hK0
  set k := AlgebraicClosure K0 with hk
  have hChark : CharP k 3 := charP_of_injective_algebraMap (algebraMap K0 k).injective 3
  have halg := CFSG.LieType.AlgebraicGroups.isAlgebraic_zmod_of_isAlgClosure 3 K0 k
  set Φ := CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi 3 1 k with hΦ
  set Rθ : Subgroup (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 3 1) :=
    twistedRootGroup K0 (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) (proj e6Theta) ⊔
      twistedRootGroup K0 (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) (-proj e6Theta)
    with hRθ
  have hRθmem : Rθ ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 3 1 Fact.out).D :=
    ⟨1, proj e6Theta, Or.inl (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_twistedDatum_proj
      (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) isRoot_e6Theta perm_e6Theta),
      (conjSub_one _).symm⟩
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 0 3 1
    Fact.out trivial hadm (by decide) (by decide)
  have hmap : Rθ.map Φ = rankOneFix 3 k 1 := map_twistedRootGroup_theta hp2 hf
  have hker := CFSG.ClassicalInvolution.ModelFacts.ker_twistedE6Phi_le_center 3 1 k
  have hZ := CFSG.ClassicalInvolution.Q3.exc3_center_twistedE6
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hΦR : ∀ x, Φ x ∈ twistedR 3 k 1 :=
    fun x => CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi_mem_fixedPointsIn 3 1 hp2 hf x
  have hgen : ∀ R ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 3 1 Fact.out).D,
      Gen3 R := by
    intro R hR
    obtain ⟨φ⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm (by decide) (by decide) hR
    exact gen3_of_equiv_sl2 φ
  obtain ⟨e₀⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRθmem
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_natCard_galoisField_three_one
  have hK3 : Nat.card (GaloisField 3 1) = 3 := natCard_galoisField_three_one
  let e'' : ↥(rankOneFix 3 k 1) ≃* SL(2, GaloisField 3 1) :=
    (MulEquiv.subgroupCongr hmap).symm.trans
      (((Rθ.equivMapOfInjective Φ hΦinj).symm).trans e₀)
  obtain ⟨eR⟩ := CFSG.ClassicalInvolution.Q3.exc3_nonempty_equiv_sl2Three hK3 e''.symm
  intro R₁ h₁ R₂ h₂ hne e₁ e₂
  refine twinRatio_notMem_center_of_normalizes Φ hker (fun x hx _ => ?_) (fun c hc => ?_) hsingle
    hgen hodd hRθmem e₀ (fun g hg => ?_) h₁ h₂ hne e₁ e₂
  · exact hΦinj (by rw [MonoidHom.mem_ker.1 hx, map_one])
  · have hcb := (Subgroup.eq_bot_iff_forall _).1 hZ c hc
    rw [hcb, map_one]
  ·
    have hmem : Φ (sl2Inv e₀) ∈ rankOneFix 3 k 1 :=
      hmap ▸ Subgroup.mem_map_of_mem Φ (sl2Inv_mem e₀)
    have hord : orderOf (Φ (sl2Inv e₀)) = 2 := by
      rw [orderOf_injective Φ hΦinj]
      exact orderOf_sl2Inv hodd e₀
    have hx : involX k ∈ rankOneFix 3 k 1 := involX_mem_rankOneFix3 hp2 halg hf
    have hxord : orderOf (involX k) = 2 :=
      involX_orderOf_eq_two3 (by rw [ringChar.eq k 3]; exact hp2)
    have hz : Φ (sl2Inv e₀) = involX k :=
      (eq_sl2Inv_of_orderOf_eq_two hodd e'' hmem hord).trans
        (eq_sl2Inv_of_orderOf_eq_two hodd e'' hx hxord).symm
    have hnorm := twistedR_normalizes_rankOneFix hp2 halg hf (by norm_num) eR (hΦR g)
      (by rw [← hz]; exact hg.symm)
    have h1 : (conjSub g Rθ).map Φ = (rankOneFix 3 k 1).map (MulAut.conj (Φ g)).toMonoidHom := by
      rw [← hmap]
      change (Rθ.map (MulAut.conj g).toMonoidHom).map Φ = _
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [map_mul, map_inv]
    rw [h1, hnorm, hmap]

end TwistedE6

end CFSG.ClassicalInvolution.Uniform
