module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelLocal
public import CFSG.GH74.M12.HypT2
import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift

public section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup CFSG.GH74.M12 CFSG.GH74.M12.Hyp CFSG.Blueprint

theorem bfS'_central_involution
    {y : G12} (hy : y ∈ bfS') (hc : ∀ w ∈ bfS', w * y = y * w)
    (h2 : y * y = 1) (h1 : y ≠ 1) : y = Jelt := by
  have hty : tbl y.1 ∈ BT := mem_bfS_iff.1 hy
  have hcent' : ∀ t ∈ BT, tmul (tbl y.1) t = tmul t (tbl y.1) := by
    intro t ht
    obtain ⟨n, -, hn⟩ := mem_BT_iff.1 ht
    have hσ : bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8) ∈ bfS := bfElt_mem _ _ _ _
    have hs : (⟨_, bfS_le_M12 hσ⟩ : G12) ∈ bfS' := hσ
    have h3 := congrArg tbl (congrArg Subtype.val (hc _ hs))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, tbl_mul, tbl_mul, tbl_bfElt, ← hn] at h3
    exact h3.symm
  have hsq' : tmul (tbl y.1) (tbl y.1) = tid := by
    rw [← tbl_mul, ← tbl_one]
    exact congrArg tbl (congrArg Subtype.val h2)
  have hne' : tbl y.1 ≠ tid := by
    intro h
    rw [← tbl_one] at h
    exact h1 (Subtype.ext (tbl_injective h))
  have hJ := BT_central_involution _ hty hcent' hsq' hne'
  rw [← tbl_bfJ] at hJ
  exact Subtype.ext (tbl_injective hJ)

theorem cj_central_involution
    {P : Subgroup CJ} (hP : Nat.card P = 64) {y : CJ} (hy : y ∈ P)
    (hc : ∀ w ∈ P, w * y = y * w) (h2 : y * y = 1) (h1 : y ≠ 1) : y = zJ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup G12 := P.map CJ.subtype with hP'
  have hcard : Nat.card P' = 2 ^ (Nat.card G12).factorization 2 := by
    rw [hP', card_map_of_injective CJ.subtype_injective, hP, card_G12, factorization_95040]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_sylow_iff bfSylow (Sylow.ofCard P' hcard)
  rw [Sylow.coe_ofCard, coe_bfSylow] at hg
  have hJP : zJ ∈ P := by
    have hn : (zpowers zJ).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hc : g * zJ = zJ * g := Subtype.ext (Subtype.ext (mem_CJ.1 g.2).symm)
      rw [show g * n * g⁻¹ = n by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
        rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]]
      exact hn
    have hPp : IsPGroup 2 P := (IsPGroup.iff_card).2 ⟨6, by rw [hP]; norm_num⟩
    have hPS : Nat.card P = 2 ^ (Nat.card CJ).factorization 2 := by
      rw [hP, card_CJ, factorization_192_two]
      norm_num
    have hzp : IsPGroup 2 (zpowers zJ) := by
      rw [isPGroup_zpowers_iff]
      exact ⟨1, by rw [pow_one, ← Subgroup.orderOf_coe]; exact orderOf_Jelt⟩
    have := IsPGroup.le_sylow_of_normal hzp (Sylow.ofCard P hPS)
    rw [Sylow.coe_ofCard] at this
    exact this (mem_zpowers zJ)
  have key : ∀ x : CJ, x ∈ P → (∀ w ∈ P, w * x = x * w) → x * x = 1 → x ≠ 1 →
      g⁻¹ * (x : G12) * g = Jelt := by
    intro x hx hxc hx2 hx1
    refine bfS'_central_involution ((hg x).1 (mem_map_of_mem _ hx)) ?_ ?_ ?_
    · intro w hw
      have hw' : g * w * g⁻¹ ∈ P' := (hg _).2 (by group; exact hw)
      obtain ⟨w', hw'P, hww⟩ := mem_map.1 hw'
      have h1 := congrArg Subtype.val (hxc w' hw'P)
      simp only [Subgroup.coe_mul] at h1
      rw [show (w'.1 : G12) = g * w * g⁻¹ from hww] at h1
      calc w * (g⁻¹ * ↑x * g) = g⁻¹ * ((g * w * g⁻¹) * ↑x) * g := by group
        _ = g⁻¹ * (↑x * (g * w * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * ↑x * g * w := by group
    · calc g⁻¹ * ↑x * g * (g⁻¹ * ↑x * g) = g⁻¹ * ↑(x * x) * g := by
            rw [Subgroup.coe_mul]; group
        _ = 1 := by rw [hx2]; simp
    · intro h
      apply hx1
      apply Subtype.ext
      calc (x : G12) = g * (g⁻¹ * ↑x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
  have hzJc : ∀ w ∈ P, w * zJ = zJ * w := fun w _ =>
    Subtype.ext (Subtype.ext (mem_CJ.1 w.2).symm)
  have hzJ2 : zJ * zJ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact Jelt_mul_self)
  have hzJ1 : zJ ≠ 1 := fun h => Jelt_ne_one (by
    have h' := congrArg Subtype.val h
    rwa [Subgroup.coe_one] at h')
  have e1 := key y hy hc h2 h1
  have e2 := key zJ hJP hzJc hzJ2 hzJ1
  apply Subtype.ext
  have e3 : g⁻¹ * (y : G12) * g = g⁻¹ * (zJ : G12) * g := e1.trans e2.symm
  simpa using e3

theorem localHyp_eq_bot_of_odd {X : Type*} [Group X] [Finite X] {z : X} (h : LocalHyp X z)
    (N : Subgroup X) [N.Normal] (hN : Odd (Nat.card N)) : N = ⊥ := by
  set Q := CFSG.pCore 2 X with hQ
  have hQn : Q.Normal := CFSG.pCore_normal
  have hNQ : ∀ n ∈ N, ∀ q ∈ Q, n * q = q * n := by
    intro n hn q hq
    have hc : n * q * n⁻¹ * q⁻¹ = 1 := by
      have h1 : n * q * n⁻¹ * q⁻¹ ∈ N := by
        rw [mul_assoc, mul_assoc]
        exact N.mul_mem hn (by rw [← mul_assoc]; exact ‹N.Normal›.conj_mem _ (N.inv_mem hn) q)
      have h2 : n * q * n⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQn.conj_mem q hq n) (Q.inv_mem hq)
      have d1 := N.orderOf_dvd_natCard h1
      have d2 := Q.orderOf_dvd_natCard h2
      rw [h.card_core] at d2
      have hodd : Odd (orderOf (n * q * n⁻¹ * q⁻¹)) := Odd.of_dvd_nat hN d1
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf _ ∣ 2 ^ 5 from d2)
      rcases k with _ | k
      · exact orderOf_eq_one_iff.1 (by simpa using hk)
      · rw [hk, pow_succ] at hodd
        exact absurd hodd (by simp [Nat.not_odd_iff_even])
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc
  by_contra hne
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hno : orderOf (n : X) = 3 := by
    have d1 := N.orderOf_dvd_natCard n.2
    have d2 := orderOf_dvd_natCard (n : X)
    rw [h.card_eq] at d2
    have hodd : Odd (orderOf (n : X)) := Odd.of_dvd_nat hN d1
    have h3 : orderOf (n : X) ∣ 3 := by
      have hcop : Nat.Coprime (orderOf (n : X)) (2 ^ 6) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
      exact hcop.dvd_of_dvd_mul_left (by simpa using d2)
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) (fun h' => hn1 (Subtype.ext h'))
    · exact h1
  have hQz : Q ≤ zpowers z := fun q hq =>
    h.centralizer_X n hno q hq (hNQ n n.2 q hq)
  have hcomm : ∀ x y : Q, x * y = y * x := by
    intro x y
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (hQz x.2)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hQz y.2)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hcen : center Q = ⊤ := eq_top_iff.2 fun x _ => mem_center_iff.2 fun y => hcomm y x
  have := h.extraspecial
  have h2 := IsExtraspecial.center_order_p 2 Q
  rw [hcen, card_top, h.card_core] at h2
  omega

structure FendelM12Data (C0 : Type*) [Group C0] (z a t0 : C0) where
  κ : centralizer ({t0} : Set C0) →* CJ
  surj : Function.Surjective κ
  ker : ∀ k, κ k = 1 ↔ (k : C0) = 1 ∨ (k : C0) = t0
  κ_z : ∀ h : z ∈ centralizer ({t0} : Set C0), κ ⟨z, h⟩ = zJ
  nwc : ∃ y : centralizer ({t0} : Set C0), IsConj a (y : C0) ∧ κ y ∈ Qsub ∧ κ y ≠ zJ
  fpf : ∃ y : centralizer ({t0} : Set C0), IsConj a (y : C0) ∧ IsConj a (z * y)
  gens : ∃ Y : Set (centralizer ({t0} : Set C0)), (∀ y ∈ Y, IsConj a (y : C0)) ∧
    closure (κ '' Y) = ⊤
  comm : ∃ k₁ k₂ : C0, k₁ * t0 = t0 * k₁ ∧ k₂ * t0 = t0 * k₂ ∧ k₁ * k₂ * k₁⁻¹ * k₂⁻¹ = z

section Hbar

variable {C0 : Type*} [Group C0] {G : Type} [Group G] {s : G}
  (θ : C0 ≃* centralizer ({s} : Set G)) (t0 : C0)

@[expose] def fendelT1 : centralizer ({(θ t0 : G)} : Set G) :=
  ⟨θ t0, mem_centralizer_singleton_iff.2 rfl⟩

theorem fendelT1_comm (h : centralizer ({(θ t0 : G)} : Set G)) :
    h * fendelT1 θ t0 = fendelT1 θ t0 * h :=
  Subtype.ext (mem_centralizer_singleton_iff.1 h.2)

instance fendelT1_normal : (zpowers (fendelT1 θ t0)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
  rw [((Commute.zpow_right (fendelT1_comm θ t0 g) k)).eq, mul_inv_cancel_right]
  exact hn

abbrev FendelHbar : Type := centralizer ({(θ t0 : G)} : Set G) ⧸ zpowers (fendelT1 θ t0)

@[expose] def fendelSH : centralizer ({(θ t0 : G)} : Set G) :=
  ⟨s, mem_centralizer_singleton_iff.2 (fendel_comm_s θ t0).symm⟩

@[expose] def fendelSbar : FendelHbar θ t0 := QuotientGroup.mk (fendelSH θ t0)

@[expose] def fendelToH :
    centralizer ({t0} : Set C0) →* centralizer ({(θ t0 : G)} : Set G) :=
  ((fendelHom θ).comp (centralizer ({t0} : Set C0)).subtype).codRestrict _ fun k => by
    rw [mem_centralizer_singleton_iff, MonoidHom.comp_apply, fendelHom_apply, fendel_comm_iff]
    exact mem_centralizer_singleton_iff.1 k.2

theorem fendelToH_coe (k : centralizer ({t0} : Set C0)) :
    ((fendelToH θ t0 k : centralizer ({(θ t0 : G)} : Set G)) : G) = θ k := rfl

theorem fendelToH_comm (k : centralizer ({t0} : Set C0)) :
    fendelToH θ t0 k * fendelSH θ t0 = fendelSH θ t0 * fendelToH θ t0 k :=
  Subtype.ext (fendel_comm_s θ k)

@[expose] def fendelPhi :
    centralizer ({t0} : Set C0) →* centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0)) :=
  ((QuotientGroup.mk' _).comp (fendelToH θ t0)).codRestrict _ fun k => by
    rw [mem_centralizer_singleton_iff, MonoidHom.comp_apply, QuotientGroup.mk'_apply, fendelSbar,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, fendelToH_comm]

theorem fendelPhi_coe (k : centralizer ({t0} : Set C0)) :
    ((fendelPhi θ t0 k : centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0))) :
      FendelHbar θ t0) = QuotientGroup.mk (fendelToH θ t0 k) := rfl

theorem mem_zpowers_fendelT1 {C0 : Type*} [Group C0] {z a t0 : C0}
    (hD : FendelLocalData C0 z a t0) (θ : C0 ≃* centralizer ({s} : Set G))
    (h : centralizer ({(θ t0 : G)} : Set G)) :
    h ∈ zpowers (fendelT1 θ t0) ↔ (h : G) = 1 ∨ (h : G) = θ t0 := by
  have ho : orderOf (fendelT1 θ t0) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact fendel_orderOf_t1 θ hD
  constructor
  · intro hh
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two ho hh with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h1 | h1)
    · rw [show h = 1 from Subtype.ext h1]
      exact one_mem _
    · rw [show h = fendelT1 θ t0 from Subtype.ext h1]
      exact mem_zpowers _

end Hbar

section Psi

variable {C0 : Type*} [Group C0] {z a t0 : C0} {G : Type} [Group G] {s : G}
  (θ : C0 ≃* centralizer ({s} : Set G))

theorem fendelPhi_surjective (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    Function.Surjective (fendelPhi θ t0) := by
  rintro ⟨q, hq⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hc : h * fendelSH θ t0 * h⁻¹ * (fendelSH θ t0)⁻¹ ∈ zpowers (fendelT1 θ t0) := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 := mem_centralizer_singleton_iff.1 hq
    rw [fendelSbar] at h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h1]
    group
  have hsH : ((fendelSH θ t0 : centralizer ({(θ t0 : G)} : Set G)) : G) = s := rfl
  rcases (mem_zpowers_fendelT1 hD θ _).1 hc with h1 | h1
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsH] at h1
    have hs : (h : G) * s = s * h := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    obtain ⟨k, hk⟩ := fendel_exists_eq θ hs
    have hkt : k * t0 = t0 * k := by
      rw [← fendel_comm_iff θ, hk]
      exact mem_centralizer_singleton_iff.1 h.2
    refine ⟨⟨k, mem_centralizer_singleton_iff.2 hkt⟩, Subtype.ext ?_⟩
    rw [fendelPhi_coe]
    congr 1
    exact Subtype.ext hk
  · exfalso
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsH] at h1
    apply fendel_not_conj_mul θ hD hθ (mem_centralizer_singleton_iff.1 h.2)
    calc (h : G) * s * (h : G)⁻¹ = ((h : G) * s * (h : G)⁻¹ * s⁻¹) * s := by group
      _ = θ t0 * s := by rw [h1]
      _ = s * θ t0 := fendel_comm_s θ t0

theorem fendelPhi_eq_one_iff (hD : FendelLocalData C0 z a t0)
    (k : centralizer ({t0} : Set C0)) :
    fendelPhi θ t0 k = 1 ↔ (k : C0) = 1 ∨ (k : C0) = t0 := by
  rw [← Subtype.coe_inj, fendelPhi_coe, OneMemClass.coe_one, QuotientGroup.eq_one_iff,
    mem_zpowers_fendelT1 hD θ, fendelToH_coe]
  constructor
  · rintro (h | h)
    · exact Or.inl (fendel_inj θ (h.trans (by simp)))
    · exact Or.inr (fendel_inj θ h)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [h])

theorem fendelPhi_ker_eq
    (hD : FendelLocalData C0 z a t0) (hM : FendelM12Data C0 z a t0) :
    (fendelPhi θ t0).ker = hM.κ.ker := by
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hM.ker, fendelPhi_eq_one_iff θ hD]

noncomputable def fendelPsi
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s)
    (hM : FendelM12Data C0 z a t0) :
    centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0)) ≃* CJ :=
  ((QuotientGroup.quotientKerEquivOfSurjective _ (fendelPhi_surjective θ hD hθ)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (fendelPhi_ker_eq θ hD hM))).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hM.surj)

theorem fendelPsi_phi
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s)
    (hM : FendelM12Data C0 z a t0) (k : centralizer ({t0} : Set C0)) :
    fendelPsi θ hD hθ hM (fendelPhi θ t0 k) = hM.κ k := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ (fendelPhi_surjective θ hD hθ)).symm
      (fendelPhi θ t0 k) = QuotientGroup.mk k := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [fendelPsi, MulEquiv.trans_apply, MulEquiv.trans_apply, h1,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem fendelSbar_eq_phi (hθ : (θ z : G) = s) (hz : z ∈ centralizer ({t0} : Set C0)) :
    zElt' (fendelSbar θ t0) = fendelPhi θ t0 ⟨z, hz⟩ := by
  apply Subtype.ext
  rw [fendelPhi_coe]
  show QuotientGroup.mk (fendelSH θ t0) = _
  congr 1
  exact Subtype.ext hθ.symm

theorem fendelPsi_sbar
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s)
    (hM : FendelM12Data C0 z a t0) : fendelPsi θ hD hθ hM (zElt' (fendelSbar θ t0)) = zJ := by
  have hz : z ∈ centralizer ({t0} : Set C0) :=
    mem_centralizer_singleton_iff.2 (hD.z_central t0).symm
  rw [fendelSbar_eq_phi θ hθ hz, fendelPsi_phi, hM.κ_z]

theorem fendel_localHyp
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s)
    (hM : FendelM12Data C0 z a t0) :
    LocalHyp (centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0))) (zElt' (fendelSbar θ t0)) :=
  LocalHyp.of_mulEquiv (fendelPsi θ hD hθ hM).symm
    (by rw [MulEquiv.symm_apply_eq, fendelPsi_sbar]) localHyp_CJ

theorem fendel_bar_isConj [Finite C0] [Finite G] (hG : IsSimpleGroup G)
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) (y : centralizer ({t0} : Set C0))
    (hya : IsConj a (y : C0)) :
    IsConj (fendelSbar θ t0) (QuotientGroup.mk (fendelToH θ t0 y) : FendelHbar θ t0) := by
  have hyo : orderOf (y : C0) = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hya
    rw [← hc, fendel_orderOf_conj, hD.orderOf_a]
  have hys : IsConj s (θ y : G) := (fendel_fusion θ hG hD hθ y hyo).2 (Or.inr hya)
  have hyt : (θ y : G) * θ t0 = θ t0 * θ y :=
    (fendel_comm_iff θ _ _).2 (mem_centralizer_singleton_iff.1 y.2)
  obtain ⟨h, hht, hhs⟩ := fendel_conj_in_H θ hG hD hθ hyt hys
  set hH : centralizer ({(θ t0 : G)} : Set G) := ⟨h, mem_centralizer_singleton_iff.2 hht⟩
  refine isConj_iff.2 ⟨QuotientGroup.mk hH, ?_⟩
  rw [fendelSbar, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hhs

end Psi

section Simple

variable {C0 : Type*} [Group C0] [Finite C0] {z a t0 : C0} {G : Type} [Group G] [Finite G]
  {s : G} (θ : C0 ≃* centralizer ({s} : Set G))

omit [Finite C0] [Finite G] in
theorem fendelSbar_ne_one (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    fendelSbar θ t0 ≠ 1 := by
  intro h
  rw [fendelSbar, QuotientGroup.eq_one_iff, mem_zpowers_fendelT1 hD θ] at h
  rcases h with h | h
  · exact fendel_s_ne_one θ hD hθ h
  · exact fendel_t1_ne_s θ hD hθ h.symm

omit [Finite C0] [Finite G] in
theorem fendelSbar_sq (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    fendelSbar θ t0 * fendelSbar θ t0 = 1 := by
  rw [fendelSbar, ← QuotientGroup.mk_mul]
  have : fendelSH θ t0 * fendelSH θ t0 = 1 := Subtype.ext (fendel_s_sq θ hD hθ)
  rw [this, QuotientGroup.mk_one]

omit [Finite C0] [Finite G] in
theorem orderOf_fendelSbar (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    orderOf (fendelSbar θ t0) = 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  orderOf_eq_prime (by rw [pow_two]; exact fendelSbar_sq θ hD hθ) (fendelSbar_ne_one θ hD hθ)

theorem fendel_sylow_bar (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    ∃ R : Subgroup C0, R ≤ centralizer {t0} ∧ IsPGroup 2 R ∧ z ∈ R ∧ t0 ∈ R ∧
      ∃ P : Sylow 2 (centralizer ({(θ t0 : G)} : Set G)),
        (∀ p : centralizer ({(θ t0 : G)} : Set G),
          p ∈ (P : Subgroup (centralizer ({(θ t0 : G)} : Set G))) ↔
            (p : G) ∈ R.map (fendelHom θ)) ∧
      ∃ Pb : Sylow 2 (FendelHbar θ t0),
        (Pb : Subgroup (FendelHbar θ t0)) =
          (P : Subgroup (centralizer ({(θ t0 : G)} : Set G))).map (QuotientGroup.mk' _) ∧
        (Pb : Subgroup (FendelHbar θ t0)) ≤ centralizer {fendelSbar θ t0} ∧
        fendelSbar θ t0 ∈ (Pb : Subgroup (FendelHbar θ t0)) := by
  obtain ⟨R, hRt, hR, -, hzR, ht0R, -, -, P, hP⟩ := fendel_sylow_H θ hD hθ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPm : ∀ p : centralizer ({(θ t0 : G)} : Set G),
      p ∈ (P : Subgroup (centralizer ({(θ t0 : G)} : Set G))) ↔
        (p : G) ∈ R.map (fendelHom θ) := fun p => by
    rw [hP, mem_subgroupOf]
  refine ⟨R, hRt, hR, hzR, ht0R, P, hPm, P.mapSurjective (QuotientGroup.mk'_surjective _),
    Sylow.coe_mapSurjective _ _, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    obtain ⟨x, -, hx⟩ := mem_map.1 ((hPm p).1 hp)
    have hc : p * fendelSH θ t0 = fendelSH θ t0 * p := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx]
      exact fendel_comm_s θ x)
    rw [QuotientGroup.mk'_apply, fendelSbar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
  · rw [Sylow.coe_mapSurjective]
    refine ⟨fendelSH θ t0, (hPm _).2 ?_, rfl⟩
    have h := (fendel_mem_map θ).2 hzR
    rwa [hθ] at h

omit [Finite C0] in
theorem fendel_pbar_central
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s)
    (hM : FendelM12Data C0 z a t0) (Pb : Sylow 2 (FendelHbar θ t0))
    (hPbX : (Pb : Subgroup (FendelHbar θ t0)) ≤ centralizer {fendelSbar θ t0})
    {x : FendelHbar θ t0} (hx : x ∈ (Pb : Subgroup (FendelHbar θ t0)))
    (hxc : ∀ w ∈ (Pb : Subgroup (FendelHbar θ t0)), w * x = x * w)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = fendelSbar θ t0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (((Pb.subtype hPbX : Subgroup _)).map
      (fendelPsi θ hD hθ hM).toMonoidHom) = 64 := by
    rw [card_map_of_injective (fendelPsi θ hD hθ hM).injective,
      (Pb.subtype hPbX).card_eq_multiplicity,
      Nat.card_congr (fendelPsi θ hD hθ hM).toEquiv, card_CJ, factorization_192_two]
    norm_num
  have hxX : x ∈ centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0)) := hPbX hx
  have hx'P : (⟨x, hxX⟩ : centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0))) ∈
      ((Pb.subtype hPbX : Sylow 2 _) : Subgroup _) := by
    rw [Sylow.coe_subtype, mem_subgroupOf]
    exact hx
  have key := cj_central_involution hcard (y := fendelPsi θ hD hθ hM ⟨x, hxX⟩)
    (mem_map_of_mem _ hx'P) ?_ ?_ ?_
  · have h1 : (⟨x, hxX⟩ : centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0))) =
        zElt' (fendelSbar θ t0) :=
      (fendelPsi θ hD hθ hM).injective (key.trans (fendelPsi_sbar θ hD hθ hM).symm)
    exact congrArg Subtype.val h1
  · intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_map.1 hw
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Sylow.coe_subtype, mem_subgroupOf] at hw'
    exact hxc _ hw'
  · rw [← map_mul, show (⟨x, hxX⟩ : centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0))) *
      ⟨x, hxX⟩ = 1 from Subtype.ext hx2, map_one]
  · rw [Ne, MulEquiv.map_eq_one_iff]
    intro h
    exact hx1 (congrArg Subtype.val h)

theorem fendel_hbar_simple
    (hG : IsSimpleGroup G) (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) (hM : FendelM12Data C0 z a t0) : IsSimpleGroup (FendelHbar θ t0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (FendelHbar θ t0) := ⟨⟨_, _, fendelSbar_ne_one θ hD hθ⟩⟩
  refine IsSimpleGroup.mk fun N hN => ?_
  obtain ⟨R, hRt, hR, hzR, ht0R, P, hPm, Pb, hPb, hPbX, hsbP⟩ := fendel_sylow_bar θ hD hθ
  set X := centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0)) with hX
  set ψ := fendelPsi θ hD hθ hM with hψ
  have hz : z ∈ centralizer ({t0} : Set C0) :=
    mem_centralizer_singleton_iff.2 (hD.z_central t0).symm
  rcases Nat.even_or_odd (Nat.card N) with he | ho
  · right
    obtain ⟨n0, hn0⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (even_iff_two_dvd.1 he)
    have hzp : IsPGroup 2 (zpowers (n0 : FendelHbar θ t0)) :=
      (isPGroup_zpowers_iff _).2 ⟨1, by rw [Subgroup.orderOf_coe, hn0, pow_one]⟩
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    obtain ⟨g, hg⟩ := exists_conj_sylow_iff Pb Q
    have hn1P : g⁻¹ * (n0 : FendelHbar θ t0) * g ∈ (Pb : Subgroup _) :=
      (hg _).1 (hQ (mem_zpowers _))
    have hn1N : g⁻¹ * (n0 : FendelHbar θ t0) * g ∈ N := by
      have h1 := hN.conj_mem _ n0.2 g⁻¹
      rwa [inv_inv] at h1
    have hn11 : g⁻¹ * (n0 : FendelHbar θ t0) * g ≠ 1 := by
      intro h
      apply fendel_ne_one hn0
      apply Subtype.ext
      calc (n0 : FendelHbar θ t0) = g * (g⁻¹ * (n0 : FendelHbar θ t0) * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have : Group.IsNilpotent (Pb : Subgroup (FendelHbar θ t0)) := Pb.isPGroup'.isNilpotent
    have hne : N.subgroupOf (Pb : Subgroup (FendelHbar θ t0)) ≠ ⊥ := by
      intro h
      have h1 : (⟨_, hn1P⟩ : (Pb : Subgroup (FendelHbar θ t0))) ∈ N.subgroupOf _ :=
        mem_subgroupOf.2 hn1N
      rw [h, mem_bot] at h1
      exact hn11 (congrArg Subtype.val h1)
    have hne2 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    set M := N.subgroupOf (Pb : Subgroup (FendelHbar θ t0)) ⊓
      center (Pb : Subgroup (FendelHbar θ t0)) with hM'
    have hMp : IsPGroup 2 M := Pb.isPGroup'.to_subgroup M
    have h2M : 2 ∣ Nat.card M := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hMp
      rcases k with _ | k
      · exact absurd (Subgroup.card_eq_one.1 (by rw [hk, pow_zero])) hne2
      · rw [hk]
        exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 h2M
    have hxN : (((x : (Pb : Subgroup (FendelHbar θ t0))) : FendelHbar θ t0)) ∈ N :=
      mem_subgroupOf.1 (mem_inf.1 x.2).1
    have hxc : ∀ w ∈ (Pb : Subgroup (FendelHbar θ t0)),
        w * ((x : (Pb : Subgroup (FendelHbar θ t0))) : FendelHbar θ t0) =
          (x : (Pb : Subgroup (FendelHbar θ t0))) * w := by
      intro w hw
      exact congrArg Subtype.val (mem_center_iff.1 (mem_inf.1 x.2).2 ⟨w, hw⟩)
    have hxo : orderOf (((x : (Pb : Subgroup (FendelHbar θ t0))) : FendelHbar θ t0)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hxs := fendel_pbar_central θ hD hθ hM Pb hPbX (x : (Pb : Subgroup (FendelHbar θ t0))).2 hxc
      (fendel_mul_self_eq_one hxo) (fendel_ne_one hxo)
    have hsbN : fendelSbar θ t0 ∈ N := hxs ▸ hxN
    have hXN : X ≤ N := by
      obtain ⟨Y, hYa, hYc⟩ := hM.gens
      have hle : closure (hM.κ '' Y) ≤ (N.subgroupOf X).map ψ.toMonoidHom := by
        rw [closure_le]
        rintro _ ⟨y, hy, rfl⟩
        refine mem_map.2 ⟨fendelPhi θ t0 y, ?_, fendelPsi_phi θ hD hθ hM y⟩
        rw [mem_subgroupOf, fendelPhi_coe]
        obtain ⟨c, hc⟩ := isConj_iff.1 (fendel_bar_isConj θ hG hD hθ y (hYa y hy))
        rw [← hc]
        exact hN.conj_mem _ hsbN c
      rw [hYc, top_le_iff] at hle
      intro q hq
      have h1 : ψ ⟨q, hq⟩ ∈ (N.subgroupOf X).map ψ.toMonoidHom := by
        rw [hle]
        exact mem_top _
      obtain ⟨q', hq', hqq⟩ := mem_map.1 h1
      have h2 : q' = ⟨q, hq⟩ := ψ.injective hqq
      rw [h2, mem_subgroupOf] at hq'
      exact hq'
    have hPN : (Pb : Subgroup (FendelHbar θ t0)) ≤ N := hPbX.trans hXN
    have hfr := Sylow.normalizer_sup_eq_top' Pb hPN
    have hnorm : normalizer (Pb : Set (FendelHbar θ t0)) ≤ N := by
      intro g hg
      apply hXN
      rw [mem_centralizer_singleton_iff]
      have h1 : g * fendelSbar θ t0 * g⁻¹ ∈ (Pb : Subgroup _) :=
        (mem_normalizer_iff.1 hg _).1 hsbP
      have h2 : ∀ w ∈ (Pb : Subgroup (FendelHbar θ t0)),
          w * (g * fendelSbar θ t0 * g⁻¹) = (g * fendelSbar θ t0 * g⁻¹) * w := by
        intro w hw
        have hw' : g⁻¹ * w * g ∈ (Pb : Subgroup _) :=
          (mem_normalizer_iff.1 hg _).2 (by group; exact hw)
        have h3 := mem_centralizer_singleton_iff.1 (hPbX hw')
        calc w * (g * fendelSbar θ t0 * g⁻¹)
            = g * ((g⁻¹ * w * g) * fendelSbar θ t0) * g⁻¹ := by group
          _ = g * (fendelSbar θ t0 * (g⁻¹ * w * g)) * g⁻¹ := by rw [h3]
          _ = (g * fendelSbar θ t0 * g⁻¹) * w := by group
      have h3 : orderOf (g * fendelSbar θ t0 * g⁻¹) = 2 := by
        rw [fendel_orderOf_conj, orderOf_fendelSbar θ hD hθ]
      have h4 := fendel_pbar_central θ hD hθ hM Pb hPbX h1 h2 (fendel_mul_self_eq_one h3)
        (fendel_ne_one h3)
      rw [mul_inv_eq_iff_eq_mul] at h4
      exact h4
    rw [eq_top_iff, ← hfr]
    exact sup_le hnorm le_rfl
  · left
    have hloc := fendel_localHyp θ hD hθ hM
    have hNX : N.subgroupOf X = ⊥ := by
      refine localHyp_eq_bot_of_odd hloc _ ?_
      have h1 := card_map_of_injective (f := X.subtype) X.subtype_injective (K := N.subgroupOf X)
      rw [subgroupOf_map_subtype] at h1
      rw [← h1]
      exact Odd.of_dvd_nat ho (card_dvd_of_le inf_le_left)
    have hfix : ∀ n ∈ N, fendelSbar θ t0 * n = n * fendelSbar θ t0 → n = 1 := by
      intro n hn hc
      have hnX : n ∈ X := mem_centralizer_singleton_iff.2 hc.symm
      have h1 : (⟨n, hnX⟩ : X) ∈ N.subgroupOf X := mem_subgroupOf.2 hn
      rw [hNX, mem_bot] at h1
      exact congrArg Subtype.val h1
    have hs : ∀ n ∈ N, fendelSbar θ t0 * n * (fendelSbar θ t0)⁻¹ = n⁻¹ := by
      set φ := MulAut.conjNormal (H := N) (fendelSbar θ t0) with hφ
      have hfpf : MonoidHom.FixedPointFree (φ : N → N) := by
        intro n hn
        apply Subtype.ext
        have h1 := congrArg Subtype.val hn
        rw [hφ, MulAut.conjNormal_apply] at h1
        exact hfix n n.2 (by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1)
      have hinvol : Function.Involutive (φ : N → N) := by
        intro n
        apply Subtype.ext
        rw [hφ, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
        have h2 := fendelSbar_sq θ hD hθ
        calc fendelSbar θ t0 * (fendelSbar θ t0 * ↑n * (fendelSbar θ t0)⁻¹) *
              (fendelSbar θ t0)⁻¹
            = (fendelSbar θ t0 * fendelSbar θ t0) * ↑n *
              (fendelSbar θ t0 * fendelSbar θ t0)⁻¹ := by group
          _ = n := by rw [h2]; group
      have h1 := hfpf.coe_eq_inv_of_involutive hinvol
      intro n hn
      have h3 := congrArg Subtype.val (congrFun h1 ⟨n, hn⟩)
      rw [hφ, MulAut.conjNormal_apply] at h3
      exact h3
    have hinv : ∀ x, IsConj (fendelSbar θ t0) x → ∀ n ∈ N, x * n * x⁻¹ = n⁻¹ := by
      rintro x hx n hn
      obtain ⟨g, rfl⟩ := isConj_iff.1 hx
      have h1 := hs (g⁻¹ * n * g) (by
        have h2 := hN.conj_mem n hn g⁻¹
        rwa [inv_inv] at h2)
      calc g * fendelSbar θ t0 * g⁻¹ * n * (g * fendelSbar θ t0 * g⁻¹)⁻¹
          = g * (fendelSbar θ t0 * (g⁻¹ * n * g) * (fendelSbar θ t0)⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * n * g)⁻¹ * g⁻¹ := by rw [h1]
        _ = n⁻¹ := by group
    obtain ⟨y, hya, hzya⟩ := hM.fpf
    have h1 := fendel_bar_isConj θ hG hD hθ y hya
    have hzy : z * (y : C0) ∈ centralizer ({t0} : Set C0) := mul_mem hz y.2
    have h2 := fendel_bar_isConj θ hG hD hθ ⟨z * y, hzy⟩ hzya
    have h3 : (QuotientGroup.mk (fendelToH θ t0 ⟨z * y, hzy⟩) : FendelHbar θ t0) =
        fendelSbar θ t0 * QuotientGroup.mk (fendelToH θ t0 y) := by
      rw [fendelSbar, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      rw [fendelToH_coe, Subgroup.coe_mul, fendelToH_coe]
      show (θ (z * y) : G) = s * θ y
      rw [fendel_mul, hθ]
    rw [h3] at h2
    rw [eq_bot_iff]
    intro n hn
    rw [mem_bot]
    set yb : FendelHbar θ t0 := QuotientGroup.mk (fendelToH θ t0 y) with hyb
    have e1 := hinv _ h2 n hn
    have e2 := hinv _ h1 n hn
    have e3 := hs n hn
    have e4 : n = n⁻¹ := by
      calc n = (fendelSbar θ t0 * n * (fendelSbar θ t0)⁻¹)⁻¹ := by rw [e3, inv_inv]
        _ = fendelSbar θ t0 * n⁻¹ * (fendelSbar θ t0)⁻¹ := by group
        _ = fendelSbar θ t0 * (yb * n * yb⁻¹) * (fendelSbar θ t0)⁻¹ := by rw [e2]
        _ = (fendelSbar θ t0 * yb) * n * (fendelSbar θ t0 * yb)⁻¹ := by group
        _ = n⁻¹ := e1
    have hn2 : n ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [e4]
      exact mul_inv_cancel n
    have hd1 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one hn2
    have hodd : Odd (orderOf n) := Odd.of_dvd_nat ho (N.orderOf_dvd_natCard hn)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at hodd
      exact absurd hodd (by decide)

end Simple

section Ident

variable {C0 : Type*} [Group C0] [Finite C0] {z a t0 : C0} {G : Type} [Group G] [Finite G]
  {s : G} (θ : C0 ≃* centralizer ({s} : Set G))

theorem fendel_hbar_asc03
    (hG : IsSimpleGroup G) (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) (hM : FendelM12Data C0 z a t0) :
    Asc03Hyp (FendelHbar θ t0) (fendelSbar θ t0) := by
  refine asc03Hyp_of_local _ (orderOf_fendelSbar θ hD hθ) (fendel_localHyp θ hD hθ hM) ?_
  obtain ⟨y, hya, hyQ, hyJ⟩ := hM.nwc
  obtain ⟨c, hc⟩ := isConj_iff.1 (fendel_bar_isConj θ hG hD hθ y hya)
  refine ⟨c, ?_, fendelPhi θ t0 y, ?_, ?_⟩
  · rw [hc]
    intro h
    apply hyJ
    rw [← fendelPsi_phi θ hD hθ hM, ← fendelPsi_sbar θ hD hθ hM]
    congr 1
    apply Subtype.ext
    rw [fendelPhi_coe]
    exact h
  · rw [← pCore_map_iso 2 (fendelPsi θ hD hθ hM).symm, pCore_CJ]
    refine mem_map.2 ⟨hM.κ y, hyQ, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, fendelPsi_phi]
  · rw [fendelPhi_coe, hc]

omit [Finite C0] [Finite G] in
theorem fendel_hbar_q8
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s)
    (hM : FendelM12Data C0 z a t0) :
    ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({fendelSbar θ t0} : Set (FendelHbar θ t0)))),
      K.Normal :=
  exists_q8_normal_of_mulEquiv (fendelPsi θ hD hθ hM).symm exists_q8_normal_CJ

theorem fendel_hbar_m12
    (hAsc : S_Asc03_simple) (hG : IsSimpleGroup G)
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) (hM : FendelM12Data C0 z a t0) :
    Nonempty (FendelHbar θ t0 ≃* G12) :=
  hAsc _ (fendel_hbar_simple θ hG hD hθ hM) _ (fendel_hbar_asc03 θ hG hD hθ hM)
    (fendel_hbar_q8 θ hD hθ hM)

theorem fendel_H_split
    (hAsc : S_Asc03_simple) (hG : IsSimpleGroup G)
    (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) (hM : FendelM12Data C0 z a t0) :
    ∃ (π : centralizer ({(θ t0 : G)} : Set G) →* G12)
      (B : Subgroup (centralizer ({(θ t0 : G)} : Set G))),
      Function.Surjective π ∧ π.ker = zpowers (fendelT1 θ t0) ∧
      IsComplement' (zpowers (fendelT1 θ t0)) B ∧ fendelSH θ t0 ∈ B ∧
      CFSG.GH74.IsCentralInvolution (π (fendelSH θ t0)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := fendel_hbar_m12 θ hAsc hG hD hθ hM
  set H := centralizer ({(θ t0 : G)} : Set G) with hH
  set π : H →* G12 := e.toMonoidHom.comp (QuotientGroup.mk' (zpowers (fendelT1 θ t0))) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = zpowers (fendelT1 θ t0) := by
    ext h
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπ1 : ∀ h : H, π h = 1 ↔ (h : G) = 1 ∨ (h : G) = θ t0 := by
    intro h
    rw [← MonoidHom.mem_ker, hπk, mem_zpowers_fendelT1 hD θ]
  have ht1o : orderOf (fendelT1 θ t0) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact fendel_orderOf_t1 θ hD
  have ht1Z : fendelT1 θ t0 ∈ center H := mem_center_iff.2 (fendelT1_comm θ t0)
  obtain ⟨R, hRt, -, hzR, -, P, hPm, -⟩ := fendel_sylow_bar θ hD hθ
  have hPθ : ∀ p : H, p ∈ (P : Subgroup H) → ∃ r ∈ R, (θ r : G) = p := by
    intro p hp
    obtain ⟨r, hr, hrp⟩ := mem_map.1 ((hPm p).1 hp)
    exact ⟨r, hr, hrp⟩
  have hall : ∀ w : H, orderOf (π w) = 2 → orderOf w = 2 := by
    intro w hw
    have hw2 : π (w * w) = 1 := by rw [map_mul, fendel_mul_self_eq_one hw]
    have hw1 : w ≠ 1 := fun h => fendel_ne_one hw (by rw [h, map_one])
    rcases (hπ1 _).1 hw2 with h | h
    · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext h) hw1
    · exfalso
      have hw4 : w ^ 4 = 1 := by
        have h1 : w ^ 2 = fendelT1 θ t0 := by rw [pow_two]; exact Subtype.ext h
        have h2 : fendelT1 θ t0 ^ 2 = 1 := by rw [← ht1o]; exact pow_orderOf_eq_one _
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h1, h2]
      have hwp : IsPGroup 2 (zpowers w) := by
        rw [isPGroup_zpowers_iff]
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
          (show orderOf w ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one hw4)
        exact ⟨k, hk⟩
      obtain ⟨Q, hQ⟩ := hwp.exists_le_sylow
      obtain ⟨g, hg⟩ := exists_conj_sylow_iff P Q
      obtain ⟨r, hrR, hr⟩ := hPθ _ ((hg w).1 (hQ (mem_zpowers w)))
      have hrr : (θ (r * r) : G) = θ t0 := by
        rw [fendel_mul, hr]
        have hc := fendelT1_comm θ t0 g
        calc ((g⁻¹ * w * g : H) : G) * ((g⁻¹ * w * g : H) : G)
            = ((g⁻¹ * (w * w) * g : H) : G) := by
              rw [← Subgroup.coe_mul]
              congr 1
              group
          _ = ((g⁻¹ * fendelT1 θ t0 * g : H) : G) := by rw [show w * w = fendelT1 θ t0 from
              Subtype.ext h]
          _ = θ t0 := by
              rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
              rfl
      exact hD.not_sq_t0 r (mem_centralizer_singleton_iff.1 (hRt hrR)) (fendel_inj θ hrr)
  obtain ⟨B, hB⟩ := CFSG.ComponentClassification.M12Cover.exists_isComplement'_of_forall_lift
    ht1o ht1Z π hπs hπk hall
  have hBi : B.index = 2 := by
    rw [hB.index_eq_card, Nat.card_zpowers, ht1o]
  have hsB : fendelSH θ t0 ∈ B := by
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hM.comm
    set u₁ := fendelToH θ t0 ⟨k₁, mem_centralizer_singleton_iff.2 hk₁⟩
    set u₂ := fendelToH θ t0 ⟨k₂, mem_centralizer_singleton_iff.2 hk₂⟩
    have h1 := comm_mem_of_index_two B hBi u₁⁻¹ u₂
    have h2 : u₁⁻¹⁻¹ * u₂ * u₁⁻¹ * u₂⁻¹ = fendelSH θ t0 := by
      apply Subtype.ext
      rw [inv_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, u₁, u₂, fendelToH_coe]
      rw [← fendel_inv, ← fendel_inv, ← fendel_mul, ← fendel_mul, ← fendel_mul, hk, hθ]
      rfl
    rw [← h2]
    exact h1
  refine ⟨π, B, hπs, hπk, hB, hsB, ?_⟩
  have hsP : fendelSH θ t0 ∈ (P : Subgroup H) := by
    rw [hPm]
    have h := (fendel_mem_map θ).2 hzR
    rwa [hθ] at h
  have hso : orderOf (π (fendelSH θ t0)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul, show fendelSH θ t0 * fendelSH θ t0 = 1 from
        Subtype.ext (fendel_s_sq θ hD hθ), map_one]
    · intro h
      rcases (hπ1 _).1 h with h' | h'
      · exact fendel_s_ne_one θ hD hθ h'
      · exact fendel_t1_ne_s θ hD hθ h'.symm
  refine ⟨hso, P.mapSurjective hπs, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact mem_map_of_mem _ hsP
  · intro x hx
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨p, hp, rfl⟩ := mem_map.1 hx
    obtain ⟨r, -, hr⟩ := hPθ p hp
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hr]
    exact fendel_comm_s θ r

end Ident

end CFSG.EvenSmallLie.SympSix
