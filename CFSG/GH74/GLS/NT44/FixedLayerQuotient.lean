module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
import CFSG.GH74.GLS.C3.Layer1.St1RigDiag3
public import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.TwoThin

variable {G : Type} [Group G] [Finite G]

theorem exists_fixedLayerQuotientEquiv {x t : G} {K Λ : Subgroup G} (hΛ : IsLam x t K Λ)
    (hcard : Nat.card (bar t Λ) ≤ Nat.card (kBar K)) :
    let hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
    let hΛY : Λ ≤ centralizer ({t} : Set G) := hΛ.le.trans inf_le_right
    let rho : Λ →* bar t Λ :=
      ((barMk ↥(centralizer ({t} : Set G))).comp
          (Subgroup.inclusion hΛY)).codRestrict (bar t Λ) fun l =>
        ⟨⟨l, hΛY l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    let f : Λ →* kBar K := hatMap hΛK
    Function.Surjective rho ∧ rho.ker = pPrimeCore 2 ↥Λ ∧ f.ker = pPrimeCore 2 ↥Λ ∧
    ∃ e : bar t Λ ≃* kBar K,
      (∀ l : Λ, e (rho l) = f l) ∧
      (∀ e' : bar t Λ ≃* kBar K, (∀ l : Λ, e' (rho l) = f l) → e' = e) ∧
      (∀ (a : G) (haT : a ∈ centralizer ({t} : Set G))
        (haK : a ∈ normalizer (K : Set G)),
        a ∈ normalizer (Λ : Set G) ∧
        ∃ haBar : sbar a haT ∈
            normalizer (bar t Λ : Set (barQ ↥(centralizer ({t} : Set G)))),
          let beta : MulAut (bar t Λ) :=
            (bar t Λ).normalizerMonoidHom ⟨sbar a haT, haBar⟩
          let alpha : MulAut (kBar K) :=
            MulAut.mapQuotient (pPrimeCore 2 ↥K)
              (K.normalizerMonoidHom ⟨a, haK⟩)
          (∀ w : bar t Λ, e (beta w) = alpha (e w)) ∧
          MulAut.congr e beta = alpha) := by
  classical
  dsimp only
  let hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  let hΛY : Λ ≤ centralizer ({t} : Set G) := hΛ.le.trans inf_le_right
  let rho : Λ →* bar t Λ :=
    ((barMk ↥(centralizer ({t} : Set G))).comp
        (Subgroup.inclusion hΛY)).codRestrict (bar t Λ) fun l =>
      ⟨⟨l, hΛY l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  let f : Λ →* kBar K := hatMap hΛK
  obtain ⟨phi, hphi_surj, _hphi_odd, hphi_formula⟩ :=
    exists_phi (y := t) (K := K) (Λ := Λ) hΛK hΛY hΛ.cover
  let e : bar t Λ ≃* kBar K :=
    MulEquiv.ofBijective phi (hphi_surj.bijective_of_nat_card_le hcard)
  have hformula : ∀ l : Λ, e (rho l) = f l := by
    intro l
    have harg : rho l =
        ⟨barMk ↥(centralizer ({t} : Set G)) ⟨(l : G), hΛY l.2⟩,
          ⟨⟨(l : G), hΛY l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩⟩ := by
      apply Subtype.ext
      rfl
    rw [harg]
    simpa only [e, f, hatMap, MulEquiv.ofBijective_apply, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply] using hphi_formula (l : G) l.2
  have hrho_surj : Function.Surjective rho := by
    intro w
    obtain ⟨c, hc, hcw⟩ := w.2
    let l : Λ := ⟨(c : G), Subgroup.mem_subgroupOf.mp hc⟩
    refine ⟨l, ?_⟩
    apply Subtype.ext
    have hrho_l : (rho l : barQ ↥(centralizer ({t} : Set G))) =
        barMk ↥(centralizer ({t} : Set G))
          ⟨(c : G), hΛY (Subgroup.mem_subgroupOf.mp hc)⟩ := rfl
    rw [hrho_l]
    rw [show (⟨(c : G), hΛY (Subgroup.mem_subgroupOf.mp hc)⟩ :
        ↥(centralizer ({t} : Set G))) = c from Subtype.ext rfl]
    exact hcw
  have hker_f : f.ker = pPrimeCore 2 ↥Λ :=
    ker_hatMap_eq_pPrimeCore hΛK hΛ.cover
  have hker_rho : rho.ker = pPrimeCore 2 ↥Λ := by
    have hker_eq : rho.ker = f.ker := by
      ext l
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro hl
        rw [← hformula l, hl, map_one]
      · intro hl
        apply e.injective
        rw [hformula l, hl, map_one]
    rw [hker_eq, hker_f]
  refine ⟨hrho_surj, hker_rho, hker_f, e, hformula, ?_, ?_⟩
  · intro e' he'
    ext w
    obtain ⟨l, rfl⟩ := hrho_surj w
    rw [he' l, hformula l]
  · intro a haT haK
    have haΛ : a ∈ normalizer (Λ : Set G) :=
      CFSG.GH74.GLS.C3.Layer1.PumpRigid.mem_normalizer_lam hΛ haT haK
    refine ⟨haΛ, ?_⟩
    let haBar : sbar a haT ∈
        normalizer (bar t Λ : Set (barQ ↥(centralizer ({t} : Set G)))) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_bar_of_normalizes (u := t) (X := Λ) haT haΛ)
    refine ⟨haBar, ?_⟩
    let beta : MulAut (bar t Λ) :=
      (bar t Λ).normalizerMonoidHom ⟨sbar a haT, haBar⟩
    let alpha : MulAut (kBar K) :=
      MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨a, haK⟩)
    let gamma : MulAut Λ := Λ.normalizerMonoidHom ⟨a, haΛ⟩
    have hbeta : ∀ l : Λ, beta (rho l) = rho (gamma l) := by
      intro l
      change ((bar t Λ).normalizerMonoidHom ⟨sbar a haT, haBar⟩ (rho l) : bar t Λ) =
        rho (gamma l)
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change sbar a haT * (rho l : barQ ↥(centralizer ({t} : Set G))) *
          (sbar a haT)⁻¹ =
        (rho (gamma l) : barQ ↥(centralizer ({t} : Set G)))
      have h1 : sbar a haT * (rho l : barQ ↥(centralizer ({t} : Set G))) *
            (sbar a haT)⁻¹ =
          barMk ↥(centralizer ({t} : Set G))
            ((⟨a, haT⟩ : ↥(centralizer ({t} : Set G))) *
              ⟨l, hΛY l.2⟩ * (⟨a, haT⟩ : ↥(centralizer ({t} : Set G)))⁻¹) := by
        change barMk ↥(centralizer ({t} : Set G)) ⟨a, haT⟩ *
            barMk ↥(centralizer ({t} : Set G)) ⟨(l : G), hΛY l.2⟩ *
            (barMk ↥(centralizer ({t} : Set G)) ⟨a, haT⟩)⁻¹ =
          barMk ↥(centralizer ({t} : Set G))
            ((⟨a, haT⟩ : ↥(centralizer ({t} : Set G))) *
              ⟨l, hΛY l.2⟩ * (⟨a, haT⟩ : ↥(centralizer ({t} : Set G)))⁻¹)
        simp only [map_mul, map_inv]
      rw [h1]
      have h2 : (rho (gamma l) : barQ ↥(centralizer ({t} : Set G))) =
          barMk ↥(centralizer ({t} : Set G))
            ⟨gamma l, hΛY (gamma l).2⟩ := rfl
      rw [h2]
      have hconj : (⟨a, haT⟩ : ↥(centralizer ({t} : Set G))) *
            ⟨l, hΛY l.2⟩ * (⟨a, haT⟩ : ↥(centralizer ({t} : Set G)))⁻¹ =
          ⟨gamma l, hΛY (gamma l).2⟩ := by
        apply Subtype.ext
        dsimp only [gamma]
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simp
      exact congrArg (barMk ↥(centralizer ({t} : Set G))) hconj
    have halpha : ∀ l : Λ, alpha (f l) = f (gamma l) := by
      intro l
      have hconj : (K.normalizerMonoidHom ⟨a, haK⟩)
            (Subgroup.inclusion hΛK l) = Subgroup.inclusion hΛK (gamma l) := by
        ext
        simp [gamma, Subgroup.normalizerMonoidHom_apply_apply_coe]
      calc alpha (f l) = QuotientGroup.mk ((K.normalizerMonoidHom ⟨a, haK⟩)
            (Subgroup.inclusion hΛK l)) := by
            simp only [alpha, f, hatMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
            exact MulAut.mapQuotient_mk _ _ _
        _ = QuotientGroup.mk (Subgroup.inclusion hΛK (gamma l)) := by rw [hconj]
        _ = f (gamma l) := by
            simp only [f, hatMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    have hequiv : ∀ w : bar t Λ, e (beta w) = alpha (e w) := by
      intro w
      obtain ⟨l, rfl⟩ := hrho_surj w
      calc e (beta (rho l)) = e (rho (gamma l)) := by rw [hbeta l]
        _ = f (gamma l) := hformula (gamma l)
        _ = alpha (f l) := (halpha l).symm
        _ = alpha (e (rho l)) := by rw [hformula l]
    have hcongr : MulAut.congr e beta = alpha := by
      ext w
      obtain ⟨q, rfl⟩ := e.surjective w
      obtain ⟨l, rfl⟩ := hrho_surj q
      calc MulAut.congr e beta (e (rho l)) = e (beta (rho l)) := by
              simp [MulAut.congr_apply]
        _ = alpha (e (rho l)) := hequiv (rho l)
    change (∀ w : bar t Λ, e (beta w) = alpha (e w)) ∧
      MulAut.congr e beta = alpha
    exact ⟨hequiv, hcongr⟩

end CFSG.GH74.GLS.NT44

