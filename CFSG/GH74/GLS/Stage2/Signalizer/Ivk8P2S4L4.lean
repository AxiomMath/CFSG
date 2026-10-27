module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Facts
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Comp
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L4Aux
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aFit
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B
import CFSG.GH74.AS16.Standard
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

theorem lemma18_4ac_of_KA (h171 : Prop17_1) (hL31 : Lemma31Narrow) (h183 : Lemma18_3a)
    (hKA : IVK_8_13_lift) (hKA2 : IVK_8_13_two) : Lemma18_4ac := by
  intro G _ _ z k S M p E t hctx X hXv hXM hXtop J hJ
  obtain ⟨hMz, hz2', hz2, hp, hp2, hMc, hsimple, hzV, hVle, hZP, hZV, hZodd, hMZ, hZbot, hNZ, hEO,
    hZO⟩ := P2S4.CtxFacts.of_ctx h171 hctx
  set Z : Subgroup G := Final.Thm4.omega1Z p (Op p M) with hZdef
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hzX : z ∈ normalizer (X : Set G) := hXv z hzV
  have hVX : Vof M E ≤ normalizer (X : Set G) := fun v hv => hXv v hv
  have hJq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  have hnebot : ∀ D : Subgroup G, IsQuasisimple ↥D → D ≠ ⊥ := fun D hD =>
    (Subgroup.nontrivial_iff_ne_bot D).mp (CFSG.LocalCores.isQuasisimple_nontrivial hD)
  have hMc' : ∀ c : G, c * z = z * c → c ∈ M := fun c hc => by
    rw [hMz]
    exact Subgroup.mem_centralizer_singleton_iff.2 hc
  have hZnormM : ∀ c : G, c * z = z * c → c ∈ normalizer (Z : Set G) := fun c hc =>
    hMZ (hMc' c hc)
  set H : Subgroup G := X ⊔ Vof M E ⊔ zpowers z with hH
  have hXH : X ≤ H := le_sup_left.trans le_sup_left
  have hVH : Vof M E ≤ H := le_sup_right.trans le_sup_left
  have hzH : z ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hHN : H ≤ normalizer (X : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hVX) (Subgroup.zpowers_le.mpr hzX)
  have hXbot : X ≠ ⊥ := fun h => hnebot J hJq (le_bot_iff.mp (h ▸ hJ.1))
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hn : X.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_le_iff.mp (htop ▸ hHN)
    rcases hsimple.eq_bot_or_eq_top_of_normal X with h | h
    · exact hXbot h
    · exact hXtop h
  have hcomp : ∀ K : Subgroup G, IsCompIn X K → IsCompIn H K := fun K hK =>
    P2S4.isCompIn_of_normal hXH hHN hK
  have hno3 : ∀ K₁ K₂ K₃ : Subgroup ↥H, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun K₁ K₂ K₃ h₁ h₂ h₃ =>
    P2S3.comps_le_two hL31 hS2 hHtop hzH h₁ h₂ h₃
  have hoddN : ∀ v ∈ H, Odd (orderOf v) → ∀ J' : Subgroup G, IsCompIn H J' →
      v ∈ normalizer (J' : Set G) := fun v hv hodd J' hJ' =>
    P2S3.mem_normalizer_of_odd hno3 hJ' hv hodd
  have hJH : IsCompIn H J := hcomp J hJ
  have h3 := fun K (hK : IsCompIn X K) => h183 G z k S M p E t hctx X hXv hXM hXtop K hK
  have hncard : Set.ncard {K : Subgroup G | IsCompIn X K} ≤ 2 := (h3 J hJ).1
  have hKz : ∀ K : Subgroup G, IsCompIn X K → ⁅K, zpowers z⁆ = K := fun K hK => (h3 K hK).2.1
  have hKZ : ∀ K : Subgroup G, IsCompIn X K → ⁅K, Z⁆ = K := fun K hK =>
    (h3 K hK).2.2
  have hzN : ∀ K : Subgroup G, IsCompIn X K → z ∈ normalizer (K : Set G) := fun K hK =>
    P2S4.mem_normalizer_of_commutator_eq (hKz K hK)
  have hZN : ∀ K : Subgroup G, IsCompIn X K → Z ≤ normalizer (K : Set G) :=
    fun K hK x hx => hoddN x (hVH (hZV hx)) (hZodd x hx) K (hcomp K hK)
  have hZnc : ∀ K : Subgroup G, IsCompIn X K → ¬ Z ≤ centralizer (K : Set G) := by
    intro K hK hle
    have h1 : ⁅Z, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [Subgroup.commutator_comm, hKZ K hK] at h1
    exact hnebot K (P2S3.quasisimple_of_isCompIn (hcomp K hK)) h1
  have hKAfor : ∀ K : Subgroup G, IsCompIn X K →
      ((∀ x ∈ H ⊓ normalizer (K : Set G), ⁅x, z⁆ ∈ K ⊔ centralizer (K : Set G)) ∧
        ((∃ y ∈ Op p M ⊓ H ⊓ normalizer (K : Set G),
            Op p M ⊓ H ⊓ normalizer (K : Set G) ≤ zpowers y ⊔ centralizer (K : Set G)) ∨
          (IsL34Quotient ↥K ∧ p = 3 ∧
            ((Op p M ⊓ H ⊓ normalizer (K : Set G)) ⊓ centralizer (K : Set G)).relIndex
              (Op p M ⊓ H ⊓ normalizer (K : Set G)) = 9 ∧ InducesUnitaryAut z K))) := by
    intro K hK
    refine hKA G z k S hS2 H K hHtop (hcomp K hK) hz2' (hzN K hK) (hKz K hK) p
      (Op p M ⊓ H ⊓ normalizer (K : Set G)) hp hp2
      ((isPGroup_Op p hp M).to_le (inf_le_left.trans inf_le_left))
      (fun x hx => ⟨hx.1.2, hx.2⟩) (fun x hx => ?_) (fun c hc hcz => ?_) ?_
    · exact (Subgroup.mem_centralizer_singleton_iff.1
        (hMz ▸ Op_le p M hx.1.1 : x ∈ centralizer ({z} : Set G))).symm
    · exact P2S4.mem_normalizer_inf3 (le_normalizer_Op p M (hMc' c hcz))
        (Subgroup.le_normalizer hc.1) (Subgroup.le_normalizer hc.2)
    · exact fun hle => hZnc K hK fun x hx =>
        hle ⟨⟨hZP hx, hVH (hZV hx)⟩, hZN K hK hx⟩
  have hw : ∀ x ∈ X, x * z * x⁻¹ * z⁻¹ ∈ X := by
    intro x hx
    have h1 : z * x⁻¹ * z⁻¹ ∈ X := (mem_normalizer_iff.mp hzX x⁻¹).mp (X.inv_mem hx)
    have := X.mul_mem hx h1
    simpa [mul_assoc] using this
  have ha1 : Em X ≤ ⁅X, zpowers z⁆ := P2S4.Em_le_of_comps_le fun K hK =>
    (hKz K hK).symm.le.trans (Subgroup.commutator_mono hK.1 le_rfl)
  have ha2 : ⁅X, zpowers z⁆ ≤ Em X ⊔ (X ⊓ centralizer (Em X : Set G)) := by
    refine P2S4a.commutator_zpowers_le_of_forall hz2 fun x hx => ?_
    have hconj : ∀ K : Subgroup G, IsCompIn X K →
        IsCompIn X (K.map (MulAut.conj x).toMonoidHom) := fun K hK =>
      P2S3.isCompIn_map_conj_of_mem hK hx
    by_cases hex : ∃ J', IsCompIn X J' ∧ J' ≠ J
    · obtain ⟨J', hJ', hne⟩ := hex
      have hJH' := hcomp J' hJ'
      have hall : ∀ K : Subgroup G, IsCompIn X K → K = J ∨ K = J' := by
        intro K hK
        by_contra hcon
        push Not at hcon
        have h2 : 2 < Set.ncard {K : Subgroup G | IsCompIn X K} :=
          (Set.two_lt_ncard_iff (Set.toFinite _)).mpr
            ⟨J, J', K, hJ, hJ', hK, hne.symm, hcon.1.symm, hcon.2.symm⟩
        omega
      have hEm : Em X = J ⊔ J' := by
        refine le_antisymm (P2S4.Em_le_of_comps_le fun K hK => ?_)
          (sup_le (P2S4.le_Em_of_isCompIn hJ) (P2S4.le_Em_of_isCompIn hJ'))
        rcases hall K hK with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      have hcommJJ' : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a := by
        rcases AS16.isCompIn_commute hJ hJ' with h | h
        · exact absurd h.symm hne
        · intro a ha b hb
          have h1 : ⁅a, b⁆ ∈ ⁅J, J'⁆ := Subgroup.commutator_mem_commutator ha hb
          rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
          calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
            _ = b * a := by rw [h1, one_mul]
      have hInj : Function.Injective (Subgroup.map (MulAut.conj x).toMonoidHom) :=
        Subgroup.map_injective (MulAut.conj x).injective
      rcases hall _ (hconj J hJ) with hxJ | hxJ
      ·
        have hxJ' : J'.map (MulAut.conj x).toMonoidHom = J' := by
          rcases hall _ (hconj J' hJ') with h | h
          · exact absurd (hInj (h.trans hxJ.symm)) hne
          · exact h
        have h1 := (hKAfor J hJ).1 x
          ⟨hXH hx, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxJ⟩
        have h2 := (hKAfor J' hJ').1 x
          ⟨hXH hx, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxJ'⟩
        have h12 := P2S4.mem_sup_centralizer_two hcommJJ' h1 h2
        rw [← hEm] at h12
        exact P2S4.mem_Q_of_mem_sup (P2S4.Em_le X) (hw x hx) h12
      ·
        have hxJ' : J'.map (MulAut.conj x).toMonoidHom = J := by
          rcases hall _ (hconj J' hJ') with h | h
          · exact h
          · exact absurd (hInj (hxJ.trans h.symm)) hne.symm
        have h12 := hKA2 G z k S hS2 H J J' hHtop hJH hJH' hne.symm hz2' (hzN J hJ) (hzN J' hJ')
          (hKz J hJ) (hKz J' hJ') x (hXH hx) hxJ hxJ' p (Z) hp hp2
          ((isPGroup_Op p hp M).to_le hZP)
          (fun y hy => ⟨⟨hVH (hZV hy), hZN J hJ hy⟩, hZN J' hJ' hy⟩)
          (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1
            (hMz ▸ Op_le p M (hZP hy) : y ∈ centralizer ({z} : Set G))).symm)
          (fun c _ hcz => hZnormM c hcz) (hZnc J hJ) (hZnc J' hJ')
        rw [← hEm] at h12
        exact P2S4.mem_Q_of_mem_sup (P2S4.Em_le X) (hw x hx) h12
    · push Not at hex
      have hEm : Em X = J :=
        le_antisymm (P2S4.Em_le_of_comps_le fun K hK => (hex K hK).le) (P2S4.le_Em_of_isCompIn hJ)
      have hxJ : J.map (MulAut.conj x).toMonoidHom = J := hex _ (hconj J hJ)
      have h1 := (hKAfor J hJ).1 x ⟨hXH hx, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxJ⟩
      have h1' : ⁅x, z⁆ ∈ Em X ⊔ centralizer (Em X : Set G) := by
        rw [hEm]
        exact h1
      exact P2S4.mem_Q_of_mem_sup (P2S4.Em_le X) (hw x hx) h1'
  refine ⟨⟨ha1, ha2⟩, ?_⟩
  have hEle : E ≤ Op p M := hctx.E_le
  have hEV : E ≤ Vof M E := fun e he => (Subgroup.map_subtype_le _) (hEO he)
  have hEH : E ≤ H := fun e he => hVH (hEV he)
  have hEN : E ≤ normalizer (J : Set G) := fun e he =>
    hoddN e (hEH he) (P2S4.odd_orderOf_of_mem_pPrimeCoreOf (hEO he)) J hJH
  have hZNJ := hZN J hJ
  have hEZN : E ⊔ Z ≤ normalizer (J : Set G) := sup_le hEN hZNJ
  have hEZP : E ⊔ Z ≤ Op p M ⊓ H ⊓ normalizer (J : Set G) :=
    sup_le (le_inf (le_inf hEle hEH) hEN) (le_inf (le_inf hZP (fun x hx => hVH (hZV hx))) hZNJ)
  have hPN : Op p M ⊓ H ⊓ normalizer (J : Set G) ≤ normalizer (J : Set G) := inf_le_right
  have hperf : Group.IsPerfect ↥J := hJq.1
  have hRle : K0.Pbar J (E ⊔ Z) ≤
      K0.Pbar J (Op p M ⊓ H ⊓ normalizer (J : Set G)) := by
    intro e he
    obtain ⟨x, hx, hxR, rfl⟩ := K0.mem_Pbar.mp he
    exact K0.yAct_mem_Pbar hx (hEZP hxR)
  rcases (hKAfor J hJ).2 with ⟨y, hyP, hPy⟩ | ⟨hL34, hp3, hidx, hU⟩
  · left
    have hcyc : IsCyclic ↥(K0.Pbar J (Op p M ⊓ H ⊓ normalizer (J : Set G))) :=
      P2S4.isCyclic_Pbar_of_le_sup hyP.2 hPy
    have hExp : ∀ u ∈ E ⊔ Z, u ^ p = 1 := by
      have := hctx.E_elem
      refine fun u hu => P2S4.pow_eq_one_of_mem_sup (A := E) (B := Z)
        (fun a ha b hb => ?_) (fun a ha => ?_) (fun b hb => hb.2.2) hu
      · exact (hb.2.1 a (hEle ha)).symm
      · exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) a ha
    have hcycR : IsCyclic ↥(K0.Pbar J (E ⊔ Z)) := P2S4.isCyclic_of_le hRle
    have hRexp : ∀ e ∈ K0.Pbar J (E ⊔ Z), e ^ p = 1 := by
      intro e he
      obtain ⟨x, hx, hxR, rfl⟩ := K0.mem_Pbar.mp he
      have h1 : (⟨x, hx⟩ : ↥(normalizer (J : Set G))) ^ p = 1 :=
        Subtype.ext (hExp x hxR)
      rw [← map_pow, h1, map_one]
    have hRdvd : Nat.card ↥(K0.Pbar J (E ⊔ Z)) ∣ p :=
      P2S4.card_dvd_of_cyclic_pow_eq_one hRexp
    have hZRle : K0.Pbar J (Z) ≤ K0.Pbar J (E ⊔ Z) := by
      intro e he
      obtain ⟨x, hx, hxZ, rfl⟩ := K0.mem_Pbar.mp he
      exact K0.yAct_mem_Pbar hx (Subgroup.mem_sup_right hxZ)
    have hZbar : K0.Pbar J (Z) ≠ ⊥ := K0.Pbar_ne_bot hZNJ (hZnc J hJ)
    have hcZ : Nat.card ↥(K0.Pbar J (Z)) = p := by
      have h1 : Nat.card ↥(K0.Pbar J (Z)) ∣ p :=
        (Subgroup.card_dvd_of_le hZRle).trans hRdvd
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hZbar
      · exact h
    have hcR : Nat.card ↥(K0.Pbar J (E ⊔ Z)) = p := by
      rcases (Nat.dvd_prime hp).mp hRdvd with h | h
      · have h2 := Subgroup.card_le_of_le hZRle
        have h3 := hp.two_le
        omega
      · exact h
    have hRZ : K0.Pbar J (E ⊔ Z) = K0.Pbar J (Z) :=
      (Subgroup.eq_of_le_of_card_ge hZRle (by rw [hcR, hcZ])).symm
    refine ⟨?_, ?_⟩
    · intro e he
      have hmem : YCfg.yAct J ⟨e, hEN he⟩ ∈ K0.Pbar J (Z) := by
        rw [← hRZ]
        exact K0.yAct_mem_Pbar (hEN he) (Subgroup.mem_sup_left he)
      obtain ⟨x, hx, hxZ, hxe⟩ := K0.mem_Pbar.mp hmem
      have h1 : YCfg.yAct J ((⟨x, hx⟩ : ↥(normalizer (J : Set G)))⁻¹ * ⟨e, hEN he⟩) = 1 := by
        rw [map_mul, map_inv, hxe, inv_mul_cancel]
      have hC : x⁻¹ * e ∈ centralizer (J : Set G) := (YCfg.yAct_eq_one_iff J _).mp h1
      have hO : x⁻¹ * e ∈ pPrimeCoreOf 2 (Vof M E) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hZO hxZ)) (hEO he)
      have hmemH : x⁻¹ * e ∈ X ⊔ pPrimeCoreOf 2 (Vof M E) ⊔ zpowers z :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right hO)
      have : e = x * (x⁻¹ * e) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hxZ ⟨hC, hmemH⟩
    · have := K0.relIndex_eq_card_Pbar hZNJ
      rw [inf_comm, this, hcZ]
  · right
    refine ⟨hL34, hp3, ?_, hU⟩
    have h9 : Nat.card ↥(K0.Pbar J (Op p M ⊓ H ⊓ normalizer (J : Set G))) = 9 := by
      rw [← K0.relIndex_eq_card_Pbar hPN]
      exact hidx
    have h10 : Nat.card ↥(K0.Pbar J (E ⊔ Z)) ≤ 9 :=
      h9 ▸ Subgroup.card_le_of_le hRle
    rw [inf_comm, K0.relIndex_eq_card_Pbar hEZN]
    exact h10

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
