module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Y
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Lay
public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent phi_map_eq_zBar)

section Cit3


variable {r n m : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isPGroup_secImg_of_aeIdent (hL : TightLargeHypR r n Y R S t)
    (I : AEIdent (coreLinkFam R t) m)
    {Lb : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t)}
    (hLb : Lb ∈ coreLinkFam R t) : IsPGroup 2 ↥Lb := by
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker (oddCore_linkGrp_eq_bot hL)
  obtain ⟨α, hα, b, hlab⟩ := I.label Lb hLb
  have hM : IsPGroup 2 ↥(AE.memBar α hα b) :=
    (IsPGroup.of_card (n := 3) (by rw [AE.natCard_memAt]; norm_num)).map (AE.mkQ m)
  have h1 : IsPGroup 2 ↥(Lb.subgroupOf (pSpan (coreLinkFam R t))) :=
    (hM.comap_of_ker_isPGroup I.φ hk).to_le (Subgroup.map_le_iff_le_comap.mp hlab.le)
  exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hLb))

theorem natCard_secImg_of_aeIdent (hL : TightLargeHypR 3 n Y R S t)
    (I : AEIdent (coreLinkFam R t) m)
    {Lb : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t)}
    (hLb : Lb ∈ coreLinkFam R t) : Nat.card ↥Lb = 8 := by
  have h2 := isPGroup_secImg_of_aeIdent hL I hLb
  have hS : IsSylow2In Lb Lb := ⟨le_rfl, h2, fun V hV _ hLV => le_antisymm hV hLV⟩
  obtain ⟨e⟩ := (typeRFam_coreLinkFam hL).quat Lb hLb Lb hS
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem exists_linkY_of_aeIdent (hL : TightLargeHypR r n Y R S t) (hm : 5 ≤ m)
    (I : AEIdent (coreLinkFam R t) m) {M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ yb ∈ linkGrp R t, yb ^ 3 = 1 ∧
      yb ∈ Subgroup.normalizer (secImg (CoreAssembly.conjClass (tightCore R)) t M :
        Set (SecQuot (CoreAssembly.conjClass (tightCore R)) t)) ∧
      (∃ xb ∈ secImg (CoreAssembly.conjClass (tightCore R)) t M, yb * xb ≠ xb * yb) ∧
      ∀ k ∈ secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R), yb * k = k * yb := by
  have h := TightLargeHypR.typeRFam hL
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker (oddCore_linkGrp_eq_bot hL)
  have hMx := xMem_of_mem_omegaNbr_core hL hM
  have hMP : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈ coreLinkFam R t := ⟨M, hM, rfl⟩
  obtain ⟨α, hα, c, hlab⟩ := I.label _ hMP
  have hrange : AE.yBar α hα ∈ I.φ.range := by
    rw [I.range_eq]
    exact AE.yBar_mem α hα
  obtain ⟨y, hy, a, hya⟩ := I.exists_lift_pow_three hrange (AE.yBar_pow_three α hα)
  have hy3 : y ^ 3 = 1 := by
    have hker : y ^ 3 ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hy, AE.yBar_pow_three]
    obtain ⟨j, hj⟩ := hk ⟨y ^ 3, hker⟩
    have hj' : (y ^ 3) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow] at this
    have h3 : (y ^ 3) ^ 3 ^ a = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hya, one_pow]
    have h1 : orderOf (y ^ 3) = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow a j (by norm_num)) (orderOf_dvd_of_pow_eq_one h3)
      (orderOf_dvd_of_pow_eq_one hj')
    exact orderOf_eq_one_iff.mp h1
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hM.1
  have hvb := isUniqueInvolution_secImg h hMx hv
  have hvP := le_pSpan hMP hvb.mem
  have hφv : I.φ ⟨_, hvP⟩ ∈ AE.memBar α hα c := by
    rw [← hlab]
    exact ⟨⟨_, hvP⟩, Subgroup.mem_subgroupOf.mpr hvb.mem, rfl⟩
  have hφv2 : I.φ ⟨_, hvP⟩ * I.φ ⟨_, hvP⟩ = 1 := by
    rw [← map_mul, ← map_one I.φ]
    congr 1
    exact Subtype.ext hvb.sq
  have hyv : y * ⟨_, hvP⟩ = ⟨_, hvP⟩ * y := by
    refine I.comm_of_pow_three hk hya ?_
    rw [hy]
    rcases AE.eq_of_mem_memBar_mul_self hm hφv hφv2 with h1 | h1
    · rw [h1, mul_one, one_mul]
    · rw [h1]
      exact AE.yBar_comm_zBar α hα
  have h2 : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t J) :=
    fun J hJ => isPGroup_secImg_of_aeIdent hL I ⟨J, hJ, rfl⟩
  refine ⟨(y : SecQuot (CoreAssembly.conjClass (tightCore R)) t), y.2, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]
  · refine (h.secFam (x := t)).tight _ (secImg_mem hMx) _ hvb ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hyv
  · obtain ⟨x, hx, hxy⟩ := AE.yBar_not_comm_memBar hm α hα c
    rw [← hlab] at hx
    obtain ⟨xb, hxb, rfl⟩ := hx
    refine ⟨(xb : SecQuot (CoreAssembly.conjClass (tightCore R)) t),
      Subgroup.mem_subgroupOf.mp hxb, fun he => hxy ?_⟩
    rw [← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext he
  · intro k hk'
    exact (Subgroup.mem_centralizer_iff.mp (linkGrp_le_centralizer hL h2 y.2) k hk').symm

theorem map_eq_memBar_not_of_mul_eq (hL : TightLargeHypR 3 n Y R S t) (hm : 5 ≤ m) (hm7 : m ≤ 7)
    (I : AEIdent (coreLinkFam R t) m) {M₁ M₂ : Subgroup Y}
    (h₁ : M₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h₂ : M₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u₁ u₂ : Y}
    (hu₁ : IsUniqueInvolution M₁ u₁) (hu₂ : IsUniqueInvolution M₂ u₂) (he : u₂ = t * u₁)
    {α : Finset (Fin m)} {hα : α.card = 4} {b : Bool}
    (hlab : ((secImg (CoreAssembly.conjClass (tightCore R)) t M₁).subgroupOf
      (pSpan (coreLinkFam R t))).map I.φ = AE.memBar α hα b) :
    ((secImg (CoreAssembly.conjClass (tightCore R)) t M₂).subgroupOf
      (pSpan (coreLinkFam R t))).map I.φ = AE.memBar α hα (!b) := by
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have ht := hd.isUniqueInvolution_core
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker (oddCore_linkGrp_eq_bot hL)
  have hx₁ := xMem_of_mem_omegaNbr_core hL h₁
  have hx₂ := xMem_of_mem_omegaNbr_core hL h₂
  have hP₁ : secImg (CoreAssembly.conjClass (tightCore R)) t M₁ ∈ coreLinkFam R t := ⟨M₁, h₁, rfl⟩
  have hP₂ : secImg (CoreAssembly.conjClass (tightCore R)) t M₂ ∈ coreLinkFam R t := ⟨M₂, h₂, rfl⟩
  obtain ⟨β, hβ, c, hlab₂⟩ := I.label _ hP₂
  have hv₁ := isUniqueInvolution_secImg h hx₁ hu₁
  have hv₂ := isUniqueInvolution_secImg h hx₂ hu₂
  have hz₁ := phi_map_eq_zBar I.φ hm hP₁ (natCard_secImg_of_aeIdent hL I hP₁) hlab hv₁
  have hz₂ := phi_map_eq_zBar I.φ hm hP₂ (natCard_secImg_of_aeIdent hL I hP₂) hlab₂ hv₂
  have htY := mem_layerY_of_isUniqueInvolution h (xMem_core hL) ht
  have hu₁Y := mem_layerY_of_isUniqueInvolution h hx₁ hu₁
  have hu₂Y := mem_layerY_of_isUniqueInvolution h hx₂ hu₂
  have hprod : (⟨u₂, hu₂Y⟩ : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) =
      ⟨t, htY⟩ * ⟨u₁, hu₁Y⟩ := Subtype.ext he
  set a₁ : ↥(pSpan (coreLinkFam R t)) := ⟨_, le_pSpan hP₁ hv₁.mem⟩ with ha₁
  set a₂ : ↥(pSpan (coreLinkFam R t)) := ⟨_, le_pSpan hP₂ hv₂.mem⟩ with ha₂
  have hcen : a₂ * a₁⁻¹ ∈ Subgroup.center ↥(pSpan (coreLinkFam R t)) := by
    have hval : ((a₂ * a₁⁻¹ : ↥(pSpan (coreLinkFam R t))) :
        SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
        QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨t, htY⟩ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ha₁, ha₂]
      simp only
      rw [hprod, map_mul, mul_inv_cancel_right]
    have hc := mk_mem_center_secQuot htY rfl
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    rw [Subgroup.coe_mul _ w (a₂ * a₁⁻¹), Subgroup.coe_mul _ (a₂ * a₁⁻¹) w, hval]
    exact Subgroup.mem_center_iff.mp hc (w : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
  have hker := I.center_le_ker hm hcen
  have hφ : I.φ a₂ = I.φ a₁ := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
    exact hker
  have hβα : β = α := AE.eq_of_zBar_eq (by omega) (hz₂.symm.trans (hφ.trans hz₁))
  subst hβα
  have hne : secImg (CoreAssembly.conjClass (tightCore R)) t M₁ ≠
      secImg (CoreAssembly.conjClass (tightCore R)) t M₂ := by
    have htu : t * u₁ = u₁ * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hd.hypOmegaGen ht h₁ hu₁
    refine secImg_ne h hx₁ hx₂ hu₁ hu₂ ?_ ?_
    · rw [he]
      calc u₁ * (t * u₁) = (u₁ * t) * u₁ := by group
        _ = (t * u₁) * u₁ := by rw [htu]
    · intro e
      apply ht.ne_one
      calc t = t * u₁ * u₁⁻¹ := by group
        _ = 1 := by rw [← he, ← e, mul_inv_cancel]
  have hc : c = !b := by
    by_contra hcb
    have hcb' : c = b := by cases b <;> cases c <;> simp_all
    subst hcb'
    apply hne
    refine eq_of_map_le_memBar (typeRFam_coreLinkFam hL).hyp
      (fun _ hJ => isPGroup_secImg_of_aeIdent hL I hJ) hm I.φ hk hP₁ hP₂ (le_pSpan hP₁)
      (le_pSpan hP₂) hlab ?_
    rw [hlab, hlab₂]
  rw [hlab₂, hc]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
