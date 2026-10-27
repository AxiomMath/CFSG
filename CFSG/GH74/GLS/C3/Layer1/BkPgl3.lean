module

public import CFSG.GH74.GLS.C3.Layer1.BkPgl2
public import CFSG.GH74.GLS.C3.Layer1.BkIv10
public import CFSG.GH74.GLS.C3.Layer1.BkL92
public import CFSG.GH74.GLS.C3.Layer1.BkPglStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barImg_mono {L S S' : Subgroup G} (h : S ≤ S') : barImg L S ≤ barImg L S' := by
  intro kb hkb
  obtain ⟨l, hl, rfl⟩ := mem_barImg_iff.1 hkb
  exact mem_barImg_iff.2 ⟨l, h hl, rfl⟩

theorem b_prop91_PGL_of
    (h92 : B_lemma92) (h10 : B_ivk_10_2L) (hK : B_pgl_K) :
    B_prop91_PGL := by
  intro G _ _ _ x y K L M T Q g hh hV2 hout hqm hgM hgQM hLg hQc hgR hgQ
  obtain ⟨hVe, hV4⟩ := hQc
  obtain ⟨p, f, hp, hf, hq79, hLie⟩ := hqm
  have hKq : HasL2Model (kBar K) (fun r => r = p ^ f) := ⟨p, f, hp, hf, rfl, hLie⟩
  have hfm9 : IsFM9 (p ^ f) := by
    rcases hq79 with h | h
    · rw [h]
      exact Or.inr ⟨by norm_num, Or.inr ⟨3, by norm_num⟩⟩
    · rw [h]
      exact Or.inl rfl
  have hsK : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hKq
  have hnK : ∃ a b : kBar K, a * b ≠ b * a :=
    Back.nonab_of_quasisimple (TwoThin.isQuasisimple_hat hh.twoTerminal.1.2.2)
  obtain ⟨θ, hθ⟩ : ∃ θ : kBar K ≃* kBar L, ∀ k : ↥K,
      θ (QuotientGroup.mk k) = QuotientGroup.mk (Subgroup.inclusion hh.K_le_L k) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Setup91.ker_toLBar hh).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (Setup91.toLBar_surjective hh)),
      fun k => rfl⟩
  have hLq : HasL2Model (kBar L) (fun r => r = p ^ f) := TwoThin.hasL2Model_of_mulEquiv θ hKq
  have hsL : IsSimpleGroup (kBar L) := (MulEquiv.isSimpleGroup_congr θ).1 hsK
  have hnL : ∃ a b : kBar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnK
    refine ⟨θ a, θ b, fun h => hab ?_⟩
    apply θ.injective
    rw [map_mul, map_mul]
    exact h
  have hlu : IsLocallyUnbalancing x y K := hV2.1
  have hy2 : orderOf y = 2 := hlu.2.1
  have hyC : y ∈ centralizer ({x} : Set G) := hlu.2.2.1
  have hyNK : y ∈ normalizer (K : Set G) := hlu.2.2.2.1
  have hyM : y ∈ M := hh.centralizer_le hyC
  have hLM : L ≤ M := hh.L_normal.1
  have hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := hh.L_normal.2
  obtain ⟨hnotK, hPGLK⟩ := ivk10_bridge h10 hlu hfm9 hKq
  have hyeq : ∀ kb : kBar K, Back.actHom hLn ⟨y, hyM⟩ (θ kb) =
      θ (Back.actHom (hLn_normalizer K) ⟨y, hyNK⟩ kb) := by
    intro kb
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
    rw [hθ, Back.actHom_mk, Back.actHom_mk, hθ]
    rfl
  have hcongr : MulAut.congr θ (Back.actHom (hLn_normalizer K) ⟨y, hyNK⟩) =
      Back.actHom hLn ⟨y, hyM⟩ := by
    ext lb
    rw [MulAut.congr_apply]
    have := hyeq (θ.symm lb)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hnotL : Back.actHom hLn ⟨y, hyM⟩ ∉ (MulAut.conj : kBar L →* MulAut (kBar L)).range := by
    rw [← hcongr, congr_mem_range_iff]
    exact hnotK
  have hPGLL : IVK.IsPGL2 ↥((MulAut.conj : kBar L →* MulAut (kBar L)).range ⊔
      zpowers (Back.actHom hLn ⟨y, hyM⟩)) (fun r => r = p ^ f) := by
    rw [← hcongr]
    exact isPGL2_congr θ _ hPGLK
  have hyL2 : (Back.actHom hLn ⟨y, hyM⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyM⟩ : ↥M) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hy2]
      exact pow_orderOf_eq_one y
    rw [this, map_one]
  set V : Subgroup G := CFSG.conjugate Q g with hVdef
  have hVM : V ≤ M := hgQM
  have hVp : IsPGroup 2 ↥V := by
    have := hVe
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  have hV2r : 2 ≤ CFSG.pRank 2 ↥V := by
    rw [TwoThin.pRank_two_subgroup_eq_open V]
    exact CFSG.SectionRank.le_pRank one_lt_two le_rfl
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).1 hVe) (by rw [hV4]; norm_num)
  have hgam : gammaIn L V ≤ conjugate M g :=
    iSup₂_le fun E hEV => iSup_le fun hE1 =>
      inf_le_of_left_le (Back.normalizer_le_conjugate hh.gamma hEV hE1)
  have hΓ : gammaIn L V ≠ L := by
    intro hL
    apply hLg
    rw [← hL]
    exact hgam
  have hlistL : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)) := by
    refine Or.inl (Back.hasL2Model_mono (fun r hr => ?_) hLq)
    subst hr
    rcases hq79 with h | h <;> rw [h] <;> decide
  obtain ⟨-, -, hVL, hVC⟩ := h92 G L M V hLM hLn hlistL hVp hVM hV2r hΓ
  have hψ := actV_injective hLn hVM hVC
  have eV : ↥V ≃* ↥(actV hLn V hVM).range := MonoidHom.ofInjective hψ
  have hVinn := range_le_conj_of_le_sup hLM hLn hVM hVL
  have hVbel : CFSG.IsElementaryAbelian 2 ↥(actV hLn V hVM).range := by
    have := hVe
    exact C3.Layer2.isElementaryAbelian_of_mulEquiv eV
  have hVbcard : Nat.card ↥(actV hLn V hVM).range = 4 := by
    rw [← Nat.card_congr eV.toEquiv]
    exact hV4
  obtain ⟨hmax, hnorm, hcent⟩ := hK (kBar L) (p ^ f) hq79 hLq (Back.actHom hLn ⟨y, hyM⟩) hnotL
    hyL2 hPGLL (actV hLn V hVM).range hVinn hVbel hVbcard
  set I' : Subgroup G := L ⊓ conjugate M g with hI'
  have hgI : gammaIn L V ≤ I' := le_inf (gammaIn_le L V) hgam
  have hOI : pPrimeCoreOf 2 L ≤ I' := (pPrimeCoreOf_le_gammaIn hLn hVM hV2r).trans hgI
  have hle1 : gammaAut (kBar L) (actV hLn V hVM).range ≤ barImg L I' :=
    (gammaAut_le_barImg hLn hVM hψ).trans (barImg_mono hgI)
  have hne1 : barImg L I' ≠ ⊤ := by
    intro htop
    exact hLg (le_of_barImg_eq_top hOI htop |>.trans inf_le_right)
  have hGam : gammaAut (kBar L) (actV hLn V hVM).range = barImg L I' := by
    by_contra hne
    exact hne1 (hmax.2 _ (lt_of_le_of_ne hle1 hne))
  obtain ⟨hR, hcomm, hPQ⟩ := hh.R_eq hsL hnL
  have hQ4 : Nat.card ↥Q = 4 := by
    rw [← card_conjugate' Q g]
    exact hV4
  have hx2 : orderOf x = 2 := hh.orderOf_x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2
    omega
  obtain ⟨v, hvV, hv1, hvcase⟩ := exists_good_element hh.x_mem_Q hx1 hcomm hPQ hgR hV4 hQ4
  obtain ⟨hVab, hVsq⟩ := forall_of_isElementaryAbelian hVe
  have hvM : v ∈ M := hVM hvV
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hVsq v hvV) hv1
  set X : Subgroup G := L ⊔ zpowers y with hXdef
  have hyNL : y ∈ normalizer (L : Set G) := U1a.mem_normalizer_of_norm hLn hyM
  have hKL : K ≤ L := hh.K_le_L
  have hvX : ∀ k ∈ X, v * k * v⁻¹ ∈ X := by
    rcases hvcase with hvP | ⟨p', hp', hvp⟩
    · have hvL : v ∈ X := Subgroup.mem_sup_left (hKL hvP.2)
      intro k hk
      exact X.mul_mem (X.mul_mem hvL hk) (X.inv_mem hvL)
    · have hp'X : p' ∈ X := Subgroup.mem_sup_left (hKL hp'.2)
      have hxy : x * y = y * x := by
        have := mem_centralizer_singleton_iff.1 hyC
        exact this.symm
      have hxM : x ∈ M := hh.centralizer_le (mem_centralizer_singleton_iff.2 rfl)
      have hxX : ∀ k ∈ X, x * k * x⁻¹ ∈ X := by
        intro k hk
        rcases (mem_sup_zpowers_two hy2 hyNL).1 hk with hkL | ⟨l, hl, rfl⟩
        · exact Subgroup.mem_sup_left (hLn x hxM k hkL)
        · have e : x * (l * y) * x⁻¹ = (x * l * x⁻¹) * y := by
            calc x * (l * y) * x⁻¹ = (x * l * x⁻¹) * (x * y * x⁻¹) := by group
              _ = (x * l * x⁻¹) * y := by rw [hxy]; group
          rw [e]
          exact (mem_sup_zpowers_two hy2 hyNL).2 (Or.inr ⟨_, hLn x hxM l hl, rfl⟩)
      intro k hk
      rw [hvp]
      have e : p' * x * k * (p' * x)⁻¹ = p' * (x * k * x⁻¹) * p'⁻¹ := by group
      rw [e]
      exact X.mul_mem (X.mul_mem hp'X (hxX k hk)) (X.inv_mem hp'X)
  have hvne : actV hLn V hVM ⟨v, hvV⟩ ≠ 1 := by
    intro h1
    apply hv1
    have := (injective_iff_map_eq_one (actV hLn V hVM)).1 hψ ⟨v, hvV⟩ h1
    exact congrArg Subtype.val this
  obtain ⟨φ, hφD, hφnot, hφcomm⟩ :=
    hcent (actV hLn V hVM ⟨v, hvV⟩) (MonoidHom.mem_range.2 ⟨⟨v, hvV⟩, rfl⟩) hvne
  have : ((MulAut.conj : kBar L →* MulAut (kBar L)).range).Normal := conj_range_normal
  obtain ⟨i, hi, c, hc, hic⟩ := Subgroup.mem_sup_of_normal_left.1 hφD
  obtain ⟨lb, rfl⟩ := MonoidHom.mem_range.1 hi
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hc
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
  have hlL : (l : G) ∈ L := l.2
  have hlM : (l : G) ∈ M := hLM hlL
  have hyjM : y ^ j ∈ M := zpow_mem hyM j
  have hz₀M : (l : G) * y ^ j ∈ M := M.mul_mem hlM hyjM
  have hz₀X : (l : G) * y ^ j ∈ X :=
    X.mul_mem (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right (zpow_mem (mem_zpowers y) j))
  have hρz₀ : Back.actHom hLn ⟨(l : G) * y ^ j, hz₀M⟩ = φ := by
    have e : (⟨(l : G) * y ^ j, hz₀M⟩ : ↥M) = ⟨l, hlM⟩ * ⟨y, hyM⟩ ^ j := by
      apply Subtype.ext
      simp
    rw [e, map_mul, map_zpow, Back.actHom_of_mem hLn hlL hlM, ← hic]
  have hcomm' : Back.actHom hLn ⟨(l : G) * y ^ j, hz₀M⟩ * Back.actHom hLn ⟨v, hvM⟩ =
      Back.actHom hLn ⟨v, hvM⟩ * Back.actHom hLn ⟨(l : G) * y ^ j, hz₀M⟩ := by
    rw [hρz₀]
    exact hφcomm
  obtain ⟨z, hzX, hzM, hzv, hρz⟩ :=
    exists_lift_commute hLM hLn hyM hy2 hsL hnL hnotL hvM hv2 hvX hz₀X hz₀M hcomm'
  have hzN : z ∈ normalizer ((zpowers v : Subgroup G) : Set G) := by
    refine mem_normalizer_of_commute fun r hr => ?_
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hr
    have : Commute z v := hzv
    exact (this.zpow_right m).eq
  have hzconj : z ∈ conjugate M g :=
    Back.normalizer_le_conjugate hh.gamma (zpowers_le.mpr hvV) (U1a.one_le_pRank_zpowers hv2) hzN
  have hall : ∀ k ∈ gammaAut (kBar L) (actV hLn V hVM).range, φ k ∈ gammaAut (kBar L)
      (actV hLn V hVM).range := by
    intro k hk
    rw [hGam] at hk ⊢
    obtain ⟨i', hi'I, rfl⟩ := mem_barImg_iff.1 hk
    have hzi : z * (i' : G) * z⁻¹ ∈ L := hLn z hzM i' i'.2
    have hzi' : z * (i' : G) * z⁻¹ ∈ conjugate M g :=
      (conjugate M g).mul_mem ((conjugate M g).mul_mem hzconj hi'I.2)
        ((conjugate M g).inv_mem hzconj)
    rw [← hρz₀, ← hρz, Back.actHom_mk]
    exact mem_barImg_iff.2 ⟨⟨z * (i' : G) * z⁻¹, hzi⟩, ⟨hzi, hzi'⟩, rfl⟩
  exact hφnot (hnorm φ hφD hall)

end CFSG.GH74.GLS.C3.Layer1.Bk
