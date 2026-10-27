module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Config
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreLie
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAFromDefs

import CFSG.GH74.KGroups.PSL2
public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Field

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

theorem exists_perfect_residual' {B S : Type*} [Group B] [Finite B] [Group S] (ρ : B →* S)
    (hρ : Function.Surjective ρ) (hS : commutator S = ⊤) :
    ∃ P : Subgroup B, ⁅P, P⁆ = P ∧ P.map ρ = ⊤ ∧ (∀ f : B ≃* B, P.map f.toMonoidHom = P) ∧
      ∀ Q : Subgroup B, ⁅Q, Q⁆ = Q → Q ≤ P := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (derivedSeries_antitone B)
  refine ⟨derivedSeries B n, ?_, ?_, ?_, ?_⟩
  · rw [← derivedSeries_succ]
    exact (hn (n + 1) (Nat.le_succ n)).symm
  · rw [map_derivedSeries_eq hρ n]
    exact derivedSeries_eq_top_of_commutator_eq_top hS n
  · exact characteristic_iff_map_eq.mp (derivedSeries_characteristic B n)
  · intro Q hQ
    have key : ∀ k : ℕ, Q ≤ derivedSeries B k := by
      intro k
      induction k with
      | zero => exact le_top
      | succ k ih =>
        rw [derivedSeries_succ]
        calc Q = ⁅Q, Q⁆ := hQ.symm
          _ ≤ ⁅derivedSeries B k, derivedSeries B k⁆ := Subgroup.commutator_mono ih ih
    exact key n

namespace Setup27

variable {G : Type} [Group G] [Finite G] {A R X O Sy Wt P : Subgroup G} {t : G}
  (H : Setup27 A R X O Sy Wt P t)

include H

theorem fpf27
    (κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2))
    (ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2))
    (hρ : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)),
      κ (alpha27 (Sy ⊓ Wt) h w) = Multiplicative.ofAdd
        ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (κ w)))) :
    ∀ x ∈ H.piHP.range, orderOf x = 3 → ∀ w : Fin 8 → ZMod 2,
      (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w → w = 0 := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥P →* MulAut ↥R, σ = conjAct27 R P H.hP.le_norm := ⟨_, rfl⟩
  have hker : H.piHP.ker = σ.ker := hσ ▸ H.ker_piHP_eq
  have hcard60 : Nat.card ↥σ.range = 60 := hσ ▸ H.hP.card
  have htrans' : ∀ r s : ↥R, r ≠ 1 → s ≠ 1 → ∃ g ∈ σ.range, g r = s := by
    intro r s hr hs
    obtain ⟨p, hp, hps⟩ := H.hP.trans r.1 r.2 s.1 s.2 (fun h => hr (Subtype.ext h))
      (fun h => hs (Subtype.ext h))
    refine ⟨σ ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, Subtype.ext ?_⟩
    rw [hσ]
    exact hps
  have hRc : Nat.card ↥R = 16 := hS.W_card
  intro x hx hx3 w hw
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥(Sy ⊓ Wt), w₀ = κ.symm (Multiplicative.ofAdd w) := ⟨_, rfl⟩
  have hκw : κ w₀ = Multiplicative.ofAdd w := by rw [hw₀]; exact MulEquiv.apply_symm_apply _ _
  have hfix : alpha27 (Sy ⊓ Wt) (H.piHP q) w₀ = w₀ := by
    apply κ.injective
    rw [hρ, hκw, toAdd_ofAdd, hw]
  have hpw : (q : G) * (w₀ : G) * (q : G)⁻¹ = (w₀ : G) := congrArg Subtype.val hfix
  have hq3 : (σ q) ^ 3 = 1 := by
    have h1 : (H.piHP q) ^ 3 = 1 := by
      rw [← hx3]
      exact pow_orderOf_eq_one _
    have h2 : q ^ 3 ∈ H.piHP.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact h1
    rw [hker, MonoidHom.mem_ker, map_pow] at h2
    exact h2
  have hkey : ∀ r : ↥R, r ≠ 1 → σ q r = r → False := by
    intro r hr1 hfixr
    have h1 : σ q = 1 := stab_of_trans_sixty hRc σ.range hcard60 htrans' (σ q) ⟨q, rfl⟩ hq3 r
      hr1 hfixr
    have h2 : q ∈ H.piHP.ker := by
      rw [hker]
      exact h1
    rw [MonoidHom.mem_ker] at h2
    rw [h2, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  have hσapply : ∀ r : ↥R, ((σ q r : ↥R) : G) = (q : G) * (r : G) * (q : G)⁻¹ := by
    intro r
    rw [hσ]
    rfl
  have hcR : t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ ∈ R :=
    hS.commutator_t_mem_W (hSy.le (mem_inf.mp w₀.2).1)
  have hqt : (q : G) * t = t * (q : G) := H.P_comm_t q.2
  have hrfix : σ q ⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ =
      ⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ := by
    apply Subtype.ext
    rw [hσapply]
    show (q : G) * (t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹) * (q : G)⁻¹ = _
    have e1 : (q : G) * t * (q : G)⁻¹ = t := by rw [hqt]; group
    calc (q : G) * (t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹) * (q : G)⁻¹
        = ((q : G) * t * (q : G)⁻¹) * ((q : G) * (w₀ : G) * (q : G)⁻¹) *
          ((q : G) * t * (q : G)⁻¹)⁻¹ * ((q : G) * (w₀ : G) * (q : G)⁻¹)⁻¹ := by group
      _ = t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ := by rw [e1, hpw]
  have hr1 : (⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ : ↥R) = 1 := by
    by_contra hne
    exact hkey _ hne hrfix
  have hw₀R : (w₀ : G) ∈ R := by
    have h1 : t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ = 1 := congrArg Subtype.val hr1
    have h2 : (w₀ : G) * t = t * (w₀ : G) := by
      have := mul_inv_eq_one.mp h1
      calc (w₀ : G) * t = (t * (w₀ : G) * t⁻¹) * t := by rw [this]
        _ = t * (w₀ : G) := by group
    rw [← hS.inf_Wt_inf_centralizer_t hSy hWt]
    exact mem_inf.mpr ⟨w₀.2, mem_centralizer_singleton_iff.mpr h2⟩
  have hw₀1 : w₀ = 1 := by
    by_contra hne
    apply hkey ⟨(w₀ : G), hw₀R⟩ (fun h => hne (Subtype.ext (by
      have h' : (w₀ : G) = 1 := congrArg Subtype.val h
      exact h')))
    apply Subtype.ext
    rw [hσapply]
    exact hpw
  rw [hw₀1, map_one] at hκw
  have h0 := congrArg Multiplicative.toAdd hκw
  simpa using h0.symm

end Setup27

namespace Setup27

variable {G : Type} [Group G] [Finite G] {A R X O Sy Wt P : Subgroup G} {t : G}
  (H : Setup27 A R X O Sy Wt P t)

include H

theorem centralizer_W_of_mem_A {a : G} (haA : a ∈ A)
    (haN : a ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))
    (haR : a ∈ centralizer (R : Set G)) :
    a ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt hSy hWt
  obtain ⟨r, hr, k, hk, hae⟩ := mem_sup_centralizer hS.W_le_A
    (H.sit.F.cent a (le_normalizer haA) (fun w hw => (mem_centralizer_iff.mp haR w hw).symm))
  have hka : k = r⁻¹ * a := by rw [hae]; group
  have hkA : k ∈ A := by
    rw [hka]
    exact A.mul_mem (A.inv_mem (hS.W_le_A hr)) haA
  have hkO : k ∈ O := hS.inf_centralizer_A_le_O (mem_inf.mpr ⟨hkA, hk⟩)
  have hkN : k ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
    rw [hka]
    exact mul_mem (inv_mem (le_normalizer (hRW hr))) haN
  have hkC := hS.centralizes_of_mem_O_normalizer hSy hkO hkN
  have hrC : r ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun x hx =>
      L34.comm_of_isElemAbelian (hS.elem_inf_Wt hSy hWt) hx (hRW hr)
  rw [hae]
  exact mul_mem hrC hkC

end Setup27

theorem Hyp.exists_mul_mem_centralizer
    {G : Type} [Group G] [Finite G] {A V₁ V₂ W P : Subgroup G} (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) (hP : PStruct27 A W P) :
    ∀ a ∈ A, a ∈ normalizer (W : Set G) → ∃ p ∈ P, p⁻¹ * a ∈ centralizer (W : Set G) := by
  obtain ⟨hWV, hWe, hW16⟩ := hR.property hW
  have hWA : W ≤ A := hWV.trans d.V_isSylow.le
  obtain ⟨c, φ, i, hφs, hφk, hmap, -⟩ := exists_cover_data h.standard.1
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h.model) h.odd
    d.V_isSylow hWV hWe hW16
  obtain ⟨Λ, hΛs, hΛk⟩ := exists_levi_hom hWA hWe c.card_k i φ hφs hφk.le
    (by rw [hφk]; exact h.odd) hmap
  obtain ⟨e⟩ := sl2_mulEquiv_alt5 c.k c.card_k
  have hBn : A ⊓ normalizer (W : Set G) ≤ normalizer (W : Set G) := inf_le_right
  have hPB : P ≤ A ⊓ normalizer (W : Set G) := fun p hp => mem_inf.mpr ⟨hP.le_A hp, hP.le_norm hp⟩
  set ρB : ↥(A ⊓ normalizer (W : Set G)) →* MulAut ↥W :=
    conjAct27 W (A ⊓ normalizer (W : Set G)) hBn
  have hρk : ∀ a : ↥(A ⊓ normalizer (W : Set G)), ρB a = 1 ↔ (a : G) ∈ centralizer (W : Set G) := by
    intro a
    have : ρB a = W.normalizerMonoidHom ⟨a, hBn a.2⟩ := rfl
    rw [this, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have hker : ρB.ker = Λ.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρk, hΛk]
  obtain ⟨e₁⟩ := rangeEquiv_of_ker_eq ρB Λ hker
  have e₂ : Λ.range ≃* Matrix.SpecialLinearGroup (Fin 2) c.k :=
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hΛs)).trans Subgroup.topEquiv
  have hcardB : Nat.card ↥ρB.range = 60 :=
    (Nat.card_congr (e₁.trans (e₂.trans e)).toEquiv).trans s27_nat_card_alt5
  have hcomp : conjAct27 W P hP.le_norm = ρB.comp (Subgroup.inclusion hPB) := rfl
  have hle : (conjAct27 W P hP.le_norm).range ≤ ρB.range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨Subgroup.inclusion hPB p, by rw [hcomp]; rfl⟩
  have heq : (conjAct27 W P hP.le_norm).range = ρB.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hP.card, hcardB])
  intro a haA haN
  have haB : a ∈ A ⊓ normalizer (W : Set G) := mem_inf.mpr ⟨haA, haN⟩
  have hmem : ρB ⟨a, haB⟩ ∈ (conjAct27 W P hP.le_norm).range := by
    rw [heq]
    exact ⟨_, rfl⟩
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, p.2, mem_centralizer_iff.mpr fun w hw => ?_⟩
  have h1 := congrArg (fun m : MulAut ↥W => ((m ⟨w, hw⟩ : ↥W) : G)) hp
  have h1' : (p : G) * w * (p : G)⁻¹ = a * w * a⁻¹ := h1
  calc w * ((p : G)⁻¹ * a) = (p : G)⁻¹ * (p * w * (p : G)⁻¹) * a := by group
    _ = (p : G)⁻¹ * (a * w * a⁻¹) * a := by rw [h1']
    _ = (p : G)⁻¹ * a * w := by group

theorem Setup27.V_le_normalizer {G : Type} [Group G] [Finite G]
    {A V₁ V₂ R X O Sy Wt P : Subgroup G} (d : Datum A) (H : Setup27 A R X O Sy Wt P d.t)
    (hR : Radicals d.V V₁ V₂) (hRV : R = V₁ ∨ R = V₂) :
    d.P ⊓ A ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hRV' : R ≤ d.V := (hR.property hRV).1
  have hRnorm : (R.subgroupOf d.V).Normal := by
    rcases hRV with h | h
    · rw [h]
      exact hR.normal₁
    · rw [h]
      exact hR.normal₂
  have hVR : ∀ v ∈ d.V, v ∈ normalizer (R : Set G) := by
    intro v hv
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hr' : r ∈ R := hr
    exact mem_subgroupOf.mp (hRnorm.conj_mem ⟨r, hRV' hr'⟩ (mem_subgroupOf.mpr hr') ⟨v, hv⟩)
  have hVE : d.V ≤ normalizer ((R ⊔ zpowers d.t : Subgroup G) : Set G) := by
    intro p hp
    have hpt := d.V_comm_t hp
    have hpR : p ∈ normalizer (R : Set G) := hVR p hp
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    have he' : e ∈ R ⊔ zpowers d.t := he
    rcases hS.mem_E_iff.mp he' with heR | ⟨r, hr, rfl⟩
    · exact mem_sup_left ((mem_normalizer_iff.mp hpR e).mp heR)
    · have : p * (r * d.t) * p⁻¹ = (p * r * p⁻¹) * d.t := by
        calc p * (r * d.t) * p⁻¹ = p * r * p⁻¹ * (p * d.t * p⁻¹) := by group
          _ = (p * r * p⁻¹) * d.t := by rw [hpt]; group
      show p * (r * d.t) * p⁻¹ ∈ R ⊔ zpowers d.t
      rw [this]
      exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp hpR r).mp hr)) (mem_sup_right
        (mem_zpowers d.t))
  have hVWt : d.V ≤ normalizer (Wt : Set G) := by
    intro p hp
    exact Subgroup.mem_normalizer_fintype fun x hx => hWt.norm p (hVE hp) x hx
  have hO' : ∀ o ∈ O, (∃ k : ℕ, o ^ 2 ^ k = 1) → o = 1 := by
    rintro o ho ⟨k, hk⟩
    have h1 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O ho
    have h3 : Nat.Coprime (2 ^ k) (Nat.card O) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hS.O_odd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  have hW2 : ∀ w ∈ Sy ⊓ Wt, ∃ k : ℕ, w ^ 2 ^ k = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hSy.isPGroup.to_inf_left ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hV2 : ∀ v ∈ d.V, ∃ k : ℕ, v ^ 2 ^ k = 1 := fun v hv => by
    obtain ⟨k, hk⟩ := d.hP.isPGroup ⟨v, hv.1⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have key := perfect_le_normalizer_sylow_two_subgroup (O := O) (W := Sy ⊓ Wt) (T := d.V)
    (fun w hw o ho => hS.O_norm w (hSy.le (mem_inf.mp hw).1) o ho) hO' hW2 hV2
    (by
      rw [hS.sup_O_inf_Wt hSy hWt]
      exact hVWt)
    (fun v hv o ho => mem_centralizer_iff.mp (hS.O_le_centralizer_A H.sit.F ho) v hv.2)
  intro v hv
  exact Subgroup.mem_normalizer_fintype fun w hw => key v hv w hw

section LayerSL

open Matrix MatrixGroups

theorem nonempty_layer_equiv_SL {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (hOut : Out27A N X t) : Nonempty (↥(layer N) ≃* SL(2, GaloisField 2 4)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 4) 2 4
    (by norm_num) (GaloisField.card 2 4 (by norm_num)) hOut.layer_model
  have hcenter : Subgroup.center (SL(2, GaloisField 2 4)) = ⊥ :=
    Subgroup.card_eq_one.mp
      (CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
        (K := GaloisField 2 4) (CharTwo.neg_eq 1))
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)⟩

theorem commutator_SL_eq_top : commutator (SL(2, GaloisField 2 4)) = ⊤ := by
  obtain ⟨z, hz⟩ := Weights16.exists_pow_four_eq (F := GaloisField 2 4)
    Weights16.nat_card_galoisField
  have hord : orderOf z = 15 :=
    Weights16.orderOf_eq_fifteen_of_pow_four Weights16.nat_card_galoisField hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hord
    simp at hord
  have hz2 : z ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  exact SL2.commutator_eq_top hz0 hz2

end LayerSL

theorem Radicals.mem_normalizer {G : Type*} [Group G] [Finite G] {V V₁ V₂ R : Subgroup G}
    (hR : Radicals V V₁ V₂) (hRV : R = V₁ ∨ R = V₂) {v : G} (hv : v ∈ V) :
    v ∈ normalizer (R : Set G) := by
  have hRV' : R ≤ V := by
    rcases hRV with h | h
    · rw [h]; exact hR.le₁
    · rw [h]; exact hR.le₂
  have hRnorm : (R.subgroupOf V).Normal := by
    rcases hRV with h | h
    · rw [h]
      exact hR.normal₁
    · rw [h]
      exact hR.normal₂
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  exact mem_subgroupOf.mp (hRnorm.conj_mem ⟨r, hRV' hr⟩ (mem_subgroupOf.mpr hr) ⟨v, hv⟩)


namespace Setup27

variable {G : Type} [Group G] [Finite G] {A R X O Sy Wt P : Subgroup G} {t : G}
  (H : Setup27 A R X O Sy Wt P t)

open Matrix MatrixGroups in
theorem exists_hat (hOut : Out27A (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27)
    (ρh : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)) (hρinj : Function.Injective ρh) :
    ∃ Hhat : Subgroup (Hh27 (Sy ⊓ Wt)),
      (∀ (g x : Hh27 (Sy ⊓ Wt)), x ∈ Hhat → g * x * g⁻¹ ∈ Hhat) ∧ H.piHP.range ≤ Hhat ∧
        Nonempty (↥Hhat ≃* SL(2, GaloisField 2 4)) := by
  obtain ⟨eS⟩ := nonempty_layer_equiv_SL hOut
  have hperf : commutator ↥(layer (Ntil27 (Sy ⊓ Wt))) = ⊤ := by
    have h1 : Group.IsPerfect SL(2, GaloisField 2 4) := ⟨commutator_SL_eq_top⟩
    have h2 : Group.IsPerfect ↥(layer (Ntil27 (Sy ⊓ Wt))) :=
      Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective
    exact h2.commutator_eq_top
  have : (layer (Ntil27 (Sy ⊓ Wt))).Characteristic := LocalCores.layer_characteristic
  set Hl : Subgroup (Hh27 (Sy ⊓ Wt)) := (layer (Ntil27 (Sy ⊓ Wt))).comap H.piH27 with hHl
  have hHlN : Hl.Normal := Subgroup.Normal.comap inferInstance _
  let πL : ↥Hl →* ↥(layer (Ntil27 (Sy ⊓ Wt))) :=
    (H.piH27.comp Hl.subtype).codRestrict _ (fun x => x.2)
  have hπL : Function.Surjective πL := by
    intro y
    obtain ⟨h, hh⟩ := H.piH27_surjective y.1
    exact ⟨⟨h, by rw [hHl, Subgroup.mem_comap, hh]; exact y.2⟩, Subtype.ext hh⟩
  obtain ⟨Hb, hHbperf, hHbmap, hHbchar, hHbmax⟩ := exists_perfect_residual' πL hπL hperf
  have hHhatperf : ⁅Hb.map Hl.subtype, Hb.map Hl.subtype⁆ = Hb.map Hl.subtype := by
    rw [← Subgroup.map_commutator, hHbperf]
  have hHhatmap : (Hb.map Hl.subtype).map H.piH27 = layer (Ntil27 (Sy ⊓ Wt)) := by
    have h1 : H.piH27.comp Hl.subtype = (layer (Ntil27 (Sy ⊓ Wt))).subtype.comp πL := rfl
    rw [Subgroup.map_map, h1, ← Subgroup.map_map, hHbmap, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hX : H.piHP.range ≤ Hl := by
    rintro _ ⟨p, rfl⟩
    show H.piH27 (H.piHP p) ∈ layer (Ntil27 (Sy ⊓ Wt))
    have h1 : H.piH27 (H.piHP p) ∈ H.X27 := ⟨p, rfl⟩
    rw [hOut.X_eq] at h1
    exact (Subgroup.mem_inf.mp h1).2
  have hXperf : ⁅H.piHP.range, H.piHP.range⁆ = H.piHP.range := by
    have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr H.hP.perfect
    have : Group.IsPerfect ↥H.piHP.range := Group.IsPerfect.range H.piHP
    exact Subgroup.isPerfect_iff.mp this
  have hXperf' : ⁅H.piHP.range.subgroupOf Hl, H.piHP.range.subgroupOf Hl⁆ =
      H.piHP.range.subgroupOf Hl := by
    apply Subgroup.map_injective Hl.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX, hXperf]
  refine ⟨Hb.map Hl.subtype, ?_, ?_, ?_⟩
  · rintro g x ⟨y, hy, rfl⟩
    have h1 := hHbchar (MulAut.conjNormal g : MulAut ↥Hl)
    have h2 : (MulAut.conjNormal g : MulAut ↥Hl) y ∈ Hb := by
      rw [← h1]
      exact ⟨y, hy, rfl⟩
    exact ⟨_, h2, by simp [MulAut.conjNormal_apply]⟩
  · intro x hx
    have h1 := hHbmax _ hXperf' (show (⟨x, hX hx⟩ : ↥Hl) ∈ H.piHP.range.subgroupOf Hl from hx)
    exact ⟨_, h1, rfl⟩
  · have hperfHat : commutator ↥(Hb.map Hl.subtype) = ⊤ :=
      (Subgroup.isPerfect_iff.mpr hHhatperf).commutator_eq_top
    obtain ⟨-, ⟨e⟩⟩ := odd_core_inf_ker_eq_bot_A_of_lieModel ρh hρinj H.piH27 (Hb.map Hl.subtype)
      hperfHat H.odd_card_ker_piH27 hOut.layer_model (MulEquiv.subgroupCongr hHhatmap)
    exact ⟨e.trans eS⟩

end Setup27

open Matrix MatrixGroups in
theorem exists_modInput_of_setup27
    {G : Type} [Group G] [Finite G] {A V₁ V₂ R X O Sy Wt P : Subgroup G} (h : Hyp G A)
    (d : Datum A) (hR : Radicals d.V V₁ V₂) (hRV : R = V₁ ∨ R = V₂)
    (H : Setup27 A R X O Sy Wt P d.t) (hOut : Out27A (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27) :
    ∃ (κ₀ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2))
      (ρ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) →* GL (Fin 8) (ZMod 2))
      (Hgl Xgl : Subgroup (GL (Fin 8) (ZMod 2))), ModInput d (Sy ⊓ Wt) κ₀ ρ Hgl Xgl := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hWab := hS.elem_inf_Wt hSy hWt
  have hWc : Nat.card ↥(Sy ⊓ Wt) = 2 ^ 8 := hS.card_inf_Wt hSy hWt
  obtain ⟨κ₀, ρh, hρinj, hρ⟩ := exists_gl_rep (W := ↥(Sy ⊓ Wt))
    (fun a b => Subtype.ext (L34.comm_of_isElemAbelian hWab a.2 b.2))
    (fun a => Subtype.ext (by
      have := hWab.2 a.1 a.2
      rwa [sq] at this)) hWc (alpha27 (Sy ⊓ Wt)) (alpha27_injective _)
  obtain ⟨Hhat, hHnorm, hXle, ⟨eH⟩⟩ := H.exists_hat hOut ρh hρinj
  set ρ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) →* GL (Fin 8) (ZMod 2) :=
    ρh.comp (QuotientGroup.mk' (KW27 (Sy ⊓ Wt))) with hρdef
  have hρapply : ∀ n, ρ n = ρh (QuotientGroup.mk n) := fun n => rfl
  have hXgl : ∀ p : ↥P, ρ ⟨p, H.le_normalizer_W p.2⟩ = ρh (H.piHP p) := fun p => rfl
  have hVN : d.P ⊓ A ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := H.V_le_normalizer d hR hRV
  have htN : d.t ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
    hS.t_mem_normalizer_inf_Wt hSy hWt
  refine ⟨κ₀, ρ, Hhat.map ρh, H.piHP.range.map ρh, ?_⟩
  refine ⟨hWab, hWc, hS.isSylowOf_centralizer_W hSy hWt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hVN, ?_,
    htN, ?_, ?_⟩
  ·
    intro n w w' hw'
    have h1 := hρ (QuotientGroup.mk n) w
    have h2 : alpha27 (Sy ⊓ Wt) (QuotientGroup.mk n) w = w' := Subtype.ext hw'.symm
    rw [h2] at h1
    exact h1
  · rintro n _ ⟨x, hx, rfl⟩
    refine ⟨QuotientGroup.mk n * x * (QuotientGroup.mk n)⁻¹, hHnorm _ _ hx, ?_⟩
    rw [hρapply, map_mul, map_mul, map_inv]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨n, rfl⟩
  · exact ⟨eH.symm.trans (Subgroup.equivMapOfInjective Hhat ρh hρinj)⟩
  · exact Subgroup.map_mono hXle
  · obtain ⟨e⟩ := H.Xh_equiv
    rw [Subgroup.card_map_of_injective hρinj, Nat.card_congr e.toEquiv, s27_nat_card_alt5]
  · rintro _ ⟨x, hx, rfl⟩ hord v hv
    have hord' : orderOf x = 3 := by
      rw [← orderOf_injective ρh hρinj x]
      exact hord
    exact H.fpf27 κ₀ ρh hρ x hx hord' v hv
  ·
    intro v hv
    obtain ⟨p, hp, hpc⟩ := Hyp.exists_mul_mem_centralizer h d hR hRV H.hP v hv.2
      (Radicals.mem_normalizer hR hRV hv)
    have hcA : p⁻¹ * v ∈ A := A.mul_mem (A.inv_mem (H.hP.le_A hp)) hv.2
    have hcN : p⁻¹ * v ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      mul_mem (inv_mem (H.le_normalizer_W hp)) (hVN hv)
    have hcC := H.centralizer_W_of_mem_A hcA hcN hpc
    have h1 : ρ ⟨p⁻¹ * v, hcN⟩ = 1 := by
      rw [hρapply]
      have : (QuotientGroup.mk (⟨p⁻¹ * v, hcN⟩ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) :
          Hh27 (Sy ⊓ Wt)) = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hcC)
      rw [this, map_one]
    have h2 : (⟨v, hVN hv⟩ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) =
        ⟨p, H.le_normalizer_W hp⟩ * ⟨p⁻¹ * v, hcN⟩ := Subtype.ext (by simp)
    rw [h2, map_mul, h1, mul_one, hXgl ⟨p, hp⟩]
    exact ⟨H.piHP ⟨p, hp⟩, hXle ⟨⟨p, hp⟩, rfl⟩, rfl⟩
  ·
    rintro _ ⟨x, ⟨p, rfl⟩, rfl⟩
    have h1 : ρ ⟨d.t, htN⟩ = ρh (QuotientGroup.mk ⟨d.t, htN⟩) := rfl
    rw [h1, ← map_mul, ← map_mul]
    congr 1
    exact congrArg QuotientGroup.mk (Subtype.ext (H.P_comm_t p.2))
  ·
    intro h1
    have h2 : (QuotientGroup.mk ⟨d.t, htN⟩ : Hh27 (Sy ⊓ Wt)) = 1 :=
      hρinj (by rw [map_one]; exact h1)
    have h3 : d.t ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    have h4 : Sy ⊓ Wt ≤ R := by
      rw [← hS.inf_Wt_inf_centralizer_t hSy hWt]
      intro w hw
      exact mem_inf.mpr ⟨hw, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp h3 w hw)⟩
    have h5 := Subgroup.card_le_of_le h4
    rw [hWc, hS.W_card] at h5
    omega


end CFSG.OddStandard.Seitz77
