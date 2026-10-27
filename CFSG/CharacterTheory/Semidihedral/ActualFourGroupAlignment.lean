module

public import CFSG.CharacterTheory.Semidihedral.KleinFourOddKernel
public import CFSG.CharacterTheory.Semidihedral.MatrixTorus
public import CFSG.CharacterTheory.Semidihedral.CentralizerResidual

public section

namespace CFSG.Semidihedral.ActualFourGroupAlignment

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual

variable {G : Type*} [Group G]

@[expose] def actualInvolution (t : G) : Subgroup.centralizer {t} :=
  ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem actualInvolution_mem_center (t : G) :
    actualInvolution t ∈ Subgroup.center (Subgroup.centralizer {t}) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp x.property

theorem actualInvolution_order (t : G) (ht : orderOf t = 2) :
    orderOf (actualInvolution t) = 2 :=
  (Subgroup.orderOf_coe (actualInvolution t)).symm.trans ht

theorem centered_involution_isConj_s [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (x : involutionCentralizer n S f) (hx : orderOf x = 2)
    (hxt : x ≠ centralInvolution n S f) :
    IsConj x (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) := by
  let P := centralizerSylow n hn S f
  let e := centralizerCoordinates n hn S f
  have htwo : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow P x htwo
  have hy : orderOf y = 2 :=
    (Subgroup.orderOf_coe y).symm.trans ((conjugate_orderOf_eq hxy).symm.trans hx)
  have ha : orderOf (e.symm y) = 2 := (equiv_orderOf e.symm y).trans hy
  rcases (involution_iff n (by omega) (e.symm y)).mp ha with hz | ⟨j, hj⟩
  · have hyz : (y : involutionCentralizer n S f) = centralInvolution n S f := by
      calc
        (y : involutionCentralizer n S f) =
            (e (e.symm y) : involutionCentralizer n S f) := by rw [e.apply_symm_apply]
        _ = (e (z n) : involutionCentralizer n S f) := by rw [hz]
        _ = centralInvolution n S f := centralizerCoordinates_z n hn S f
    rw [hyz] at hxy
    exact (hxt ((conjugate_to_central_iff (centralInvolution_mem_center n S f)).mp hxy)).elim
  · have hs : IsConj (s n) (e.symm y) := by
      rw [hj]
      have h := even_outside_conjugate n hn (j.val : ℤ)
      change IsConj (s n) (r n ^ ((2 : ℕ) * j.val : ℤ) * s n) at h
      rw [← Int.natCast_mul, zpow_natCast] at h
      exact h
    have hsy := (P : Subgroup (involutionCentralizer n S f)).subtype.map_isConj
      (e.toMonoidHom.map_isConj hs)
    change IsConj (e (s n) : involutionCentralizer n S f)
      (e (e.symm y) : involutionCentralizer n S f) at hsy
    rw [e.apply_symm_apply] at hsy
    exact hxy.trans hsy.symm

theorem exists_actual_noncentral_involution [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2) :
    ∃ s : Subgroup.centralizer {t}, orderOf s = 2 ∧ s ≠ actualInvolution t := by
  obtain ⟨S, f, hz⟩ :=
    InvolutionFusion.exists_centered_semidihedral_sylow n hn S0 f0 hG t ht
  have hC : involutionCentralizer n S f = Subgroup.centralizer {t} := by
    change Subgroup.centralizer {(f (z n) : G)} = _
    rw [hz]
  let e := MulEquiv.subgroupCongr hC
  have het : e (centralInvolution n S f) = actualInvolution t := Subtype.ext hz
  refine ⟨e (centralizerCoordinates n hn S f (s n)), ?_, ?_⟩
  · exact (equiv_orderOf e _).trans (s_order n hn S f)
  · intro h
    have he := e.injective (h.trans het.symm)
    exact centralizer_s_not_fused n hn S f (by
      rw [centralizerCoordinates_z]
      rw [he])

theorem actual_noncentral_involutions_isConj [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (x y : Subgroup.centralizer {t}) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxt : x ≠ actualInvolution t) (hyt : y ≠ actualInvolution t) : IsConj x y := by
  obtain ⟨S, f, hz⟩ :=
    InvolutionFusion.exists_centered_semidihedral_sylow n hn S0 f0 hG t ht
  have hC : involutionCentralizer n S f = Subgroup.centralizer {t} := by
    change Subgroup.centralizer {(f (z n) : G)} = _
    rw [hz]
  let e := MulEquiv.subgroupCongr hC
  have het : e (centralInvolution n S f) = actualInvolution t := Subtype.ext hz
  have hx' : orderOf (e.symm x) = 2 := (equiv_orderOf e.symm x).trans hx
  have hy' : orderOf (e.symm y) = 2 := (equiv_orderOf e.symm y).trans hy
  have hxt' : e.symm x ≠ centralInvolution n S f := by
    intro h
    apply hxt
    rw [← e.apply_symm_apply x, h, het]
  have hyt' : e.symm y ≠ centralInvolution n S f := by
    intro h
    apply hyt
    rw [← e.apply_symm_apply y, h, het]
  have hxy := (centered_involution_isConj_s n hn S f (e.symm x) hx' hxt').trans
    (centered_involution_isConj_s n hn S f (e.symm y) hy' hyt').symm
  have h := e.toMonoidHom.map_isConj hxy
  change IsConj (e (e.symm x)) (e (e.symm y)) at h
  simpa only [e.apply_symm_apply] using h

theorem exists_actual_noncentral_involution_conjugator [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (x y : Subgroup.centralizer {t}) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxt : x ≠ actualInvolution t) (hyt : y ≠ actualInvolution t) :
    ∃ c : Subgroup.centralizer {t}, c * x * c⁻¹ = y :=
  isConj_iff.mp (actual_noncentral_involutions_isConj n hn S0 f0 hG t ht x y hx hy hxt hyt)

theorem odd_kernel_involution_lift {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    (v : H ⧸ N) (hv : orderOf v = 2) :
    ∃ x : H, orderOf x = 2 ∧ QuotientGroup.mk' N x = v := by
  let nu := QuotientGroup.mk' N
  let P := (Subgroup.zpowers v).comap nu
  let phi : P →* Subgroup.zpowers v :=
    (nu.comp P.subtype).codRestrict (Subgroup.zpowers v) (fun x => x.property)
  have hphi : Function.Surjective phi := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (y : H ⧸ N)
    have hxP : x ∈ P := by
      change nu x ∈ Subgroup.zpowers v
      rw [hx]
      exact y.property
    exact ⟨⟨x, hxP⟩, Subtype.ext hx⟩
  have hcard : 2 ∣ Nat.card P := by
    have h := Subgroup.card_dvd_of_surjective hphi
    simpa only [Nat.card_zpowers, hv] using h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hxH : orderOf (x : H) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hxN : (x : H) ∉ N := by
    intro h
    have hdiv := N.orderOf_dvd_natCard h
    rw [hxH] at hdiv
    exact hN.not_two_dvd_nat hdiv
  have hnontrivial : nu (x : H) ≠ 1 := by
    intro h
    exact hxN ((QuotientGroup.eq_one_iff _).mp h)
  have hmem : nu (x : H) ∈ Subgroup.zpowers v := x.property
  rcases (KleinFourOddKernel.mem_zpowers_involution v (nu (x : H)) hv).mp hmem with h | h
  · exact (hnontrivial h).elim
  · exact ⟨(x : H), hxH, h⟩

theorem actual_quotient_noncentral_involution_lift [Finite G] (t : G)
    (v : Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t}))
    (hv : orderOf v = 2)
    (hvt : v ≠ QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t}))
      (actualInvolution t)) :
    ∃ x : Subgroup.centralizer {t}, orderOf x = 2 ∧ x ≠ actualInvolution t ∧
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) x = v := by
  have hN : Odd (Nat.card (pPrimeCore 2 (Subgroup.centralizer {t}))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨x, hx, hxv⟩ := odd_kernel_involution_lift
    (pPrimeCore 2 (Subgroup.centralizer {t})) hN v hv
  refine ⟨x, hx, ?_, hxv⟩
  intro h
  apply hvt
  rw [← hxv, h]


section OriginalModel

variable (F : Type*) [Field F] (a : Fˣ) (A : Subgroup (F ≃+* F))
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)

theorem originalU_ne_one : MatrixTorus.originalU F a A hfix ≠ 1 := by
  intro h
  have he := congrArg (fun g : MatrixTorus.OriginalH F a A hfix => g.left.right) h
  change (Multiplicative.ofAdd (1 : ZMod 2) : MatrixCoverData.C2) = 1 at he
  have h10 : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd he
  exact one_ne_zero h10

theorem originalU_square : (MatrixTorus.originalU F a A hfix) ^ 2 = 1 := by
  change (SemidirectProduct.inl (MatrixCoverData.u F a) :
    MatrixTorus.OriginalH F a A hfix) ^ 2 = 1
  rw [← map_pow, MatrixCoverData.u_square, map_one]

theorem originalU_order : orderOf (MatrixTorus.originalU F a A hfix) = 2 :=
  orderOf_eq_prime_iff.mpr ⟨originalU_square F a A hfix, originalU_ne_one F a A hfix⟩

theorem originalU_ne_originalZ :
    MatrixTorus.originalU F a A hfix ≠ MatrixTorus.originalZ F a A hfix := by
  intro h
  have he := congrArg (fun g : MatrixTorus.OriginalH F a A hfix => g.left.right) h
  change (Multiplicative.ofAdd (1 : ZMod 2) : MatrixCoverData.C2) = 1 at he
  have h10 : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd he
  exact one_ne_zero h10

theorem originalZ_order [Finite F] (hodd : Odd (Nat.card F)) :
    orderOf (MatrixTorus.originalZ F a A hfix) = 2 := by
  have hi : Function.Injective (MatrixTorus.originalSlInH F a A hfix) :=
    SemidirectProduct.inl_injective.comp (MatrixCoverData.inclusion_injective F a)
  change orderOf (MatrixTorus.originalSlInH F a A hfix (OddFieldSL2.minusIdentity F)) = 2
  rw [orderOf_injective _ hi]
  exact OddFieldSL2.minusIdentity_orderOf F (OddFieldSL2.two_ne_zero_of_odd_card F hodd)

@[expose] noncomputable def conjugatedOriginalEquiv (t : G)
    (psi0 : MatrixTorus.OriginalH F a A hfix ≃*
      (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})))
    (c : Subgroup.centralizer {t}) : MatrixTorus.OriginalH F a A hfix ≃*
      (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})) :=
  psi0.trans (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c))

theorem conjugatedOriginalEquiv_apply (t : G)
    (psi0 : MatrixTorus.OriginalH F a A hfix ≃*
      (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})))
    (c : Subgroup.centralizer {t}) (g : MatrixTorus.OriginalH F a A hfix) :
    conjugatedOriginalEquiv F a A hfix t psi0 c g =
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c * psi0 g *
        (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c)⁻¹ := rfl

theorem conjugatedOriginalEquiv_originalZ (t : G)
    (psi0 : MatrixTorus.OriginalH F a A hfix ≃*
      (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})))
    (hz : psi0 (MatrixTorus.originalZ F a A hfix) =
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t))
    (c : Subgroup.centralizer {t}) :
    conjugatedOriginalEquiv F a A hfix t psi0 c (MatrixTorus.originalZ F a A hfix) =
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t) := by
  let nu := QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t}))
  have htbar : nu (actualInvolution t) ∈
      Subgroup.center (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
      (Subgroup.mem_map_of_mem _ (actualInvolution_mem_center t))
  rw [conjugatedOriginalEquiv_apply, hz]
  change nu c * nu (actualInvolution t) * (nu c)⁻¹ = nu (actualInvolution t)
  rw [Subgroup.mem_center_iff.mp htbar (nu c), mul_assoc, mul_inv_cancel, mul_one]

theorem exists_original_aligned_equiv [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (psi0 : MatrixTorus.OriginalH F a A hfix ≃*
      (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})))
    (hz : psi0 (MatrixTorus.originalZ F a A hfix) =
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t))
    (s : Subgroup.centralizer {t}) (hs : orderOf s = 2) (hst : s ≠ actualInvolution t) :
    ∃ (c : Subgroup.centralizer {t})
      (psi : MatrixTorus.OriginalH F a A hfix ≃*
        (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t}))),
      psi (MatrixTorus.originalZ F a A hfix) =
        QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t) ∧
      psi (MatrixTorus.originalU F a A hfix) =
        QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) s ∧
      ∀ g : MatrixTorus.OriginalH F a A hfix,
        psi g = QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c * psi0 g *
          (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c)⁻¹ := by
  let nu := QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t}))
  have hv : orderOf (psi0 (MatrixTorus.originalU F a A hfix)) = 2 :=
    (equiv_orderOf psi0 _).trans (originalU_order F a A hfix)
  have hvt : psi0 (MatrixTorus.originalU F a A hfix) ≠ nu (actualInvolution t) := by
    intro h
    exact originalU_ne_originalZ F a A hfix (psi0.injective (h.trans hz.symm))
  obtain ⟨x, hx, hxt, hxv⟩ := actual_quotient_noncentral_involution_lift t _ hv hvt
  obtain ⟨c, hc⟩ :=
    exists_actual_noncentral_involution_conjugator n hn S0 f0 hG t ht x s hx hs hxt hst
  refine ⟨c, conjugatedOriginalEquiv F a A hfix t psi0 c,
    conjugatedOriginalEquiv_originalZ F a A hfix t psi0 hz c, ?_, ?_⟩
  · rw [conjugatedOriginalEquiv_apply, ← hxv]
    simpa only [map_mul, map_inv] using congrArg nu hc
  · intro g
    exact conjugatedOriginalEquiv_apply F a A hfix t psi0 c g


theorem aligned_originalFieldAction_pair (sigma : A) (x : MatrixCoverData.M F a) :
    MatrixTorus.originalFieldAction F a A hfix sigma x =
      ⟨Matrix.SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom x.left, x.right⟩ :=
  MatrixTorus.originalFieldAction_pair F a A hfix sigma x

theorem exists_matrixFieldModel_aligned_equiv [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (psi0 : MatrixCover.MatrixFieldModel F A (MatrixTorus.originalCoefficient F a A hfix) ≃*
      (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})))
    (hz : psi0 (MatrixTorus.zInH F A (MatrixTorus.originalCoefficient F a A hfix)) =
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t))
    (s : Subgroup.centralizer {t}) (hs : orderOf s = 2) (hst : s ≠ actualInvolution t) :
    ∃ (c : Subgroup.centralizer {t})
      (psi : MatrixCover.MatrixFieldModel F A (MatrixTorus.originalCoefficient F a A hfix) ≃*
        (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t}))),
      psi (MatrixTorus.zInH F A (MatrixTorus.originalCoefficient F a A hfix)) =
        QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t) ∧
      psi (MatrixTorus.uInH F A (MatrixTorus.originalCoefficient F a A hfix)) =
        QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) s ∧
      ∀ g : MatrixCover.MatrixFieldModel F A (MatrixTorus.originalCoefficient F a A hfix),
        psi g = QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c * psi0 g *
          (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c)⁻¹ := by
  let e := MatrixTorus.originalModelEquiv F a A hfix
  let originalPsi := e.symm.trans psi0
  have hz' : originalPsi (MatrixTorus.originalZ F a A hfix) =
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t) := by
    change psi0 (e.symm (MatrixTorus.originalZ F a A hfix)) = _
    rw [← MatrixTorus.originalModelEquiv_z F a A hfix, e.symm_apply_apply]
    exact hz
  obtain ⟨c, psi, hzpsi, hupsi, hpoint⟩ :=
    exists_original_aligned_equiv F a A hfix n hn S0 f0 hG t ht originalPsi hz' s hs hst
  refine ⟨c, e.trans psi, ?_, ?_, ?_⟩
  · change psi (e (MatrixTorus.zInH F A (MatrixTorus.originalCoefficient F a A hfix))) = _
    rw [MatrixTorus.originalModelEquiv_z]
    exact hzpsi
  · change psi (e (MatrixTorus.uInH F A (MatrixTorus.originalCoefficient F a A hfix))) = _
    rw [MatrixTorus.originalModelEquiv_u]
    exact hupsi
  · intro g
    change psi (e g) = _
    rw [hpoint]
    change _ * psi0 (e.symm (e g)) * _ = _
    rw [e.symm_apply_apply]


theorem actual_four_group_involution_alignment [Finite G] [Finite F]
    (hodd : Odd (Nat.card F)) (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (psi0 : MatrixTorus.OriginalH F a A hfix ≃*
      (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t})))
    (hz : psi0 (MatrixTorus.originalZ F a A hfix) =
      QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t))
    (s : Subgroup.centralizer {t}) (hs : orderOf s = 2) (hst : s ≠ actualInvolution t) :
    (∃ s' : Subgroup.centralizer {t}, orderOf s' = 2 ∧ s' ≠ actualInvolution t) ∧
    (∀ x y : Subgroup.centralizer {t}, orderOf x = 2 → orderOf y = 2 →
      x ≠ actualInvolution t → y ≠ actualInvolution t →
      IsConj x y ∧ ∃ c : Subgroup.centralizer {t}, c * x * c⁻¹ = y) ∧
    (∀ v : Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t}),
      orderOf v = 2 → v ≠ QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t}))
        (actualInvolution t) →
      ∃ x : Subgroup.centralizer {t}, orderOf x = 2 ∧ x ≠ actualInvolution t ∧
        QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) x = v) ∧
    orderOf (MatrixTorus.originalU F a A hfix) = 2 ∧
    MatrixTorus.originalU F a A hfix ≠ MatrixTorus.originalZ F a A hfix ∧
    orderOf (MatrixTorus.originalZ F a A hfix) = 2 ∧
    (∃ (c : Subgroup.centralizer {t})
      (psi : MatrixTorus.OriginalH F a A hfix ≃*
        (Subgroup.centralizer {t} ⧸ pPrimeCore 2 (Subgroup.centralizer {t}))),
      psi (MatrixTorus.originalZ F a A hfix) =
        QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) (actualInvolution t) ∧
      psi (MatrixTorus.originalU F a A hfix) =
        QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) s ∧
      ∀ g : MatrixTorus.OriginalH F a A hfix,
        psi g = QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c * psi0 g *
          (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer {t})) c)⁻¹) ∧
    ∀ (sigma : A) (x : MatrixCoverData.M F a),
      MatrixTorus.originalFieldAction F a A hfix sigma x =
        ⟨Matrix.SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom x.left, x.right⟩ := by
  refine ⟨exists_actual_noncentral_involution n hn S0 f0 hG t ht, ?_,
    actual_quotient_noncentral_involution_lift t,
    originalU_order F a A hfix, originalU_ne_originalZ F a A hfix,
    originalZ_order F a A hfix hodd,
    exists_original_aligned_equiv F a A hfix n hn S0 f0 hG t ht psi0 hz s hs hst,
    aligned_originalFieldAction_pair F a A hfix⟩
  intro x y hx hy hxt hyt
  exact ⟨actual_noncentral_involutions_isConj n hn S0 f0 hG t ht x y hx hy hxt hyt,
    exists_actual_noncentral_involution_conjugator n hn S0 f0 hG t ht x y hx hy hxt hyt⟩

end OriginalModel
end CFSG.Semidihedral.ActualFourGroupAlignment
