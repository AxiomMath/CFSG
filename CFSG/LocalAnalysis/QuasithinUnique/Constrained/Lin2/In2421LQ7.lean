module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ5

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section LQ7

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem false_of_LQ (hc : centerOf L = ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) {a : G} (haT : a ∈ T)
    (haS : a ∉ S) (ha2 : a ^ 2 = 1) (hacent : ∀ y ∈ lin2Z L (thompsonJ S), a * y = y * a) {g z : G}
    (hz : z ∈ lin2Z L (thompsonJ S)) (hg : a = g⁻¹ * z * g) : False := by
  have haR : a ∉ thompsonJ S := fun h => haS (thompsonJ_le_self S h)
  set Z := lin2Z L (thompsonJ S) with hZdef
  have hZR : Z = centerOf (thompsonJ S) :=
    ((lin2Z_cases (Z := Z) rfl).resolve_right fun h => h.1 hc).2
  have hZle : Z ≤ thompsonJ S := hZR ▸ inf_le_left
  have ha1 : a ≠ 1 := fun h => haR (by rw [h]; exact one_mem _)
  have haZg : a ∈ conjR Z g := mem_conjR_iff'.2 ⟨z, hz, hg⟩
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hp2R : IsPGroup 2 ↥(thompsonJ S) := hcfg.sylowT.isPGroup.to_le hRT
  obtain ⟨hZel, hZcard, -⟩ := E.Zbasic hcfg hZdef
  have hTIZ := E.ZTI hcfg hZdef
  obtain ⟨hcomm, hinf, m', hm', hV⟩ := E.exists_V hcfg hc hx hxS haT haR hacent hz hg
  set Z' := conjR Z g with hZ'def
  set V := Z ⊔ Z' with hVdef
  have hTIZ' : fusionIsTI Z' := fusionIsTI_conjR hTIZ g
  have hZ'el : IsElemAbelian 2 Z' := (isElemAbelian_conjR_iff Z g).2 hZel
  have hcommel : ∀ y ∈ Z, ∀ w ∈ Z', y * w = w * y := fun y hy w hw => by
    have := Subgroup.commutator_mem_commutator hw hy
    rw [hcomm, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  have hVel : IsElemAbelian 2 V := isElemAbelian_sup_commute hZel hZ'el hcommel
  have haV : a ∈ V := Subgroup.mem_sup_right haZg
  have hZV : Z ≤ V := le_sup_left
  have hZ'V : Z' ≤ V := le_sup_right
  have hUR : blockU L ≤ thompsonJ S := by
    obtain ⟨hRU, -⟩ := E.RUU hcfg hx hxS
    rw [hRU]; exact le_sup_left
  have hp2V : IsPGroup 2 ↥V := by
    rw [hV]
    exact (isPGroup_conjR_iff 2).2 (hp2R.to_le hUR)
  have hUcard : Nat.card (blockU L) = 2 ^ (2 * n) := by
    rw [E.card_U' hcfg, hc, Subgroup.card_bot, mul_one]
  have hVcard : Nat.card V = Nat.card (blockU L) := by rw [hV, card_conjR]
  have hZc : ∀ z ∈ Z, ∀ r ∈ thompsonJ S, r * z = z * r := fun z hz r hr =>
    Subgroup.mem_centralizer_iff.1 (hZR ▸ hz : z ∈ centerOf (thompsonJ S)).2 r hr
  have hacent' : ∀ z ∈ Z, a * z * a⁻¹ = z := fun z hz => by rw [hacent z hz]; group
  have hnR : ∀ r ∈ thompsonJ S, a * r * a⁻¹ ∈ thompsonJ S := fun r hr =>
    (Subgroup.mem_normalizer_iff.1 (E.TnR hcfg haT) r).1 hr
  have hsq : ∀ y ∈ thompsonJ S, y ^ 2 ∈ Z := fun y hy => hZR ▸ E.R_sq_mem_centerOf hcfg hy
  have hcommR : ∀ x ∈ thompsonJ S, ∀ y ∈ thompsonJ S, ⁅x, y⁆ ∈ Z := fun x hx y hy =>
    hZR ▸ E.R_comm_le_centerOf hcfg (Subgroup.commutator_mem_commutator hx hy)
  set W := Wsub (thompsonJ S) Z a hZc with hWdef
  have hWR : W ≤ thompsonJ S := Wsub_le
  have hZW : Z ≤ W := Z_le_Wsub hZle hacent'
  have hCR : thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G) = Z := by
    have hsq1 : a ^ 2 ∈ thompsonJ S := by rw [ha2]; exact one_mem _
    obtain ⟨-, -, h14'⟩ := E.h14 G T M H S L D n hcfg a haT haS hsq1
    rcases h14' ha2 with ⟨-, hZeq, -⟩ | ⟨-, hev, hcard, hΩ⟩ | ⟨hc', -⟩
    · rw [← hZeq, hZR]
    · exfalso
      have hZle' : Z ≤ omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G)) := by
        intro y hy
        apply Subgroup.subset_closure
        exact ⟨⟨hZle hy, Subgroup.mem_centralizer_singleton_iff.2 (hacent y hy).symm⟩,
          hZel.2 y hy⟩
      have h1 := Subgroup.card_le_of_le hZle'
      rw [hZcard, hΩ] at h1
      have h2 := Nat.pow_lt_pow_right (by norm_num : 1 < 2)
        (show n / 2 < n by have := hcfg.one_lt; omega)
      omega
    · exact absurd hc hc'
  have hRcard : Nat.card (thompsonJ S) = 2 ^ (3 * n) := E.card_R_of_eq_bot hcfg hc
  have hWcard : 2 ^ (2 * n) ≤ Nat.card W := by
    have h := card_R_le_card_Wsub (R := thompsonJ S) (Z := Z) (a := a) (hZc := hZc) ha2 hnR hsq
    rw [hCR, hRcard, hZcard] at h
    have e : 2 ^ (3 * n) = 2 ^ n * 2 ^ (2 * n) := by rw [← pow_add]; congr 1; omega
    rw [e] at h
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have hYV : ∀ w ∈ W, conjR Z' w ≤ V := by
    intro w hw
    obtain ⟨z₀, hz₀, hwa⟩ := conj_eq_mul_of_mem_Wsub hacent' hw
    have haz₀V : a * z₀ ∈ V := V.mul_mem haV (hZV hz₀)
    have haz₀Y : a * z₀ ∈ conjR Z' w := hwa ▸ mem_conjR_iff'.2 ⟨a, haZg, rfl⟩
    have haz₀1 : a * z₀ ≠ 1 := by
      intro h
      apply haR
      have : a = z₀⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact (thompsonJ S).inv_mem (hZle hz₀)
    have hne : conjR Z (g * w) ⊓ conjR (blockU L) m' ≠ ⊥ := by
      intro hbot
      have : a * z₀ ∈ conjR Z (g * w) ⊓ conjR (blockU L) m' :=
        ⟨by rw [← conjR_conjR]; exact haz₀Y, hV ▸ haz₀V⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact haz₀1 this
    have := E.conjR_Z_le_conjR_U hcfg hne
    rw [hZ'def, conjR_conjR, hV]
    exact this
  have hwcz : ∀ w ∈ W, w ∈ Subgroup.centralizer (Z : Set G) := fun w hw =>
    Subgroup.mem_centralizer_iff.2 fun z hz => (hZc z hz w (hWR hw)).symm
  have hWV : ∀ w ∈ W, conjR V w = V := by
    intro w hw
    have hwN : w ∈ Subgroup.normalizer (Z : Set G) :=
      Subgroup.centralizer_le_normalizer (Z : Set G) (hwcz w hw)
    have hle : conjR V w ≤ V := by
      rw [hVdef, conjR_sup, conjR_eq_of_mem_normalizer hwN]
      exact sup_le hZV (hYV w hw)
    exact eq_of_le_of_card_le' hle (by rw [card_conjR])
  have hWN : W ≤ Subgroup.normalizer (V : Set G) := fun w hw => conjR_eq_self_iff.1 (hWV w hw)
  have hW2 : IsPGroup 2 ↥W := hp2R.to_le hWR
  have hP2 : IsPGroup 2 ↥(W ⊔ V) := isPGroup_sup_of_le_normalizer hWN hW2 hp2V
  have hWVle : W ⊓ V ≤ Z := by
    intro y hy
    have := E.inf_R_le_centerOf hcfg hx hxS haT haS hVel haV
      (show y ∈ V ⊓ thompsonJ S from ⟨hy.2, hWR hy.1⟩)
    rwa [← hZR] at this
  have hcardP : 2 ^ (3 * n) ≤ Nat.card (W ⊔ V : Subgroup G) := by
    have h1 := card_sup_mul_card_inf hWN
    have h2 : Nat.card (W ⊓ V : Subgroup G) ≤ 2 ^ n :=
      (Subgroup.card_le_of_le hWVle).trans (le_of_eq hZcard)
    have h3 : 2 ^ (2 * n) * 2 ^ (2 * n) ≤ Nat.card W * Nat.card V :=
      Nat.mul_le_mul hWcard (by rw [hVcard, hUcard])
    have e : 2 ^ n * 2 ^ (3 * n) = 2 ^ (2 * n) * 2 ^ (2 * n) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have h4 : 2 ^ n * 2 ^ (3 * n) ≤ 2 ^ n * Nat.card (W ⊔ V : Subgroup G) := by
      calc 2 ^ n * 2 ^ (3 * n) = 2 ^ (2 * n) * 2 ^ (2 * n) := e
        _ ≤ Nat.card W * Nat.card V := h3
        _ = Nat.card (W ⊔ V : Subgroup G) * Nat.card (W ⊓ V : Subgroup G) := h1.symm
        _ ≤ Nat.card (W ⊔ V : Subgroup G) * 2 ^ n := Nat.mul_le_mul le_rfl h2
        _ = 2 ^ n * Nat.card (W ⊔ V : Subgroup G) := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  have hVC : V ≤ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) := by
    rw [← hZR]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact IsElemAbelian.comm hZel hw hy
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hcommel w hw y hy
  have hWC : W ≤ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) := fun w hw =>
    Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_iff.1 hz.2 w (hWR hw)).symm
  have hP'le : W ⊔ V ≤ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer (centerOf (thompsonJ S) : Set G) :=
    sup_le (le_inf hWN hWC) (le_inf Subgroup.le_normalizer hVC)
  have hSyl0 := E.isSylowTwoOf_conjR_R_inf hcfg hc hm'
  rw [← hV] at hSyl0
  have hcardEq : Nat.card (W ⊔ V : Subgroup G) = twoPart (Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer (centerOf (thompsonJ S) : Set G)) := by
    apply le_antisymm (card_le_twoPart hP'le hP2)
    rw [← hSyl0.card_eq, card_conjR, hRcard]
    exact hcardP
  have hSylP' := isSylowTwoOf_of_card_eq hP'le hP2 hcardEq
  obtain ⟨h', -, hP'eq⟩ := hSyl0.exists_conj hSylP'
  have hP'conj : W ⊔ V = conjR (thompsonJ S) (m' * h'⁻¹) := by
    rw [← conjR_conjR, conjR_def, inv_inv]
    exact hP'eq
  set q₀ := m' * h'⁻¹ with hq₀
  have hconj_mem : ∀ s ∈ thompsonJ S, s⁻¹ * a * s ∈ W ⊔ V := by
    intro s hs
    have hc_mem : a⁻¹ * (s⁻¹ * a * s⁻¹⁻¹) ∈ W :=
      orbit_mem_Wsub ha2 hnR hsq ((thompsonJ S).inv_mem hs)
    have e : s⁻¹ * a * s = a * (a⁻¹ * (s⁻¹ * a * s⁻¹⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right haV) (Subgroup.mem_sup_left hc_mem)
  have hZ's : ∀ s ∈ thompsonJ S, conjR Z' s ≤ W ⊔ V := by
    intro s hs
    have hy : s⁻¹ * a * s ∈ conjR (thompsonJ S) q₀ := hP'conj ▸ hconj_mem s hs
    have hy2 : (s⁻¹ * a * s) ^ 2 = 1 := by
      have : (s⁻¹ * a * s) ^ 2 = s⁻¹ * a ^ 2 * s := by simp only [pow_two]; group
      rw [this, ha2]; group
    have hy1 : s⁻¹ * a * s ≠ 1 := by
      intro h1
      apply ha1
      have : a = s * (s⁻¹ * a * s) * s⁻¹ := by group
      rw [this, h1]; group
    obtain ⟨k, hk, hyk⟩ := E.exists_conjR_Z_of_mem hcfg hc hx hxS hy hy2
    have hyZ's : s⁻¹ * a * s ∈ conjR Z' s := mem_conjR_iff'.2 ⟨a, haZg, rfl⟩
    have hTIk := fusionIsTI_conjR hTIZ k
    have hne : conjR Z k ⊓ conjR (conjR Z k) (k⁻¹ * (g * s)) ≠ ⊥ := by
      intro hbot
      have : s⁻¹ * a * s ∈ conjR Z k ⊓ conjR (conjR Z k) (k⁻¹ * (g * s)) := by
        refine ⟨hyk, ?_⟩
        rw [conjR_conjR, mul_inv_cancel_left, ← conjR_conjR]
        exact hyZ's
      rw [hbot, Subgroup.mem_bot] at this
      exact hy1 this
    have heq := conjR_eq_of_inf_ne_bot hTIk hne
    rw [conjR_conjR, mul_inv_cancel_left] at heq
    rw [hZ'def, conjR_conjR, heq, hP'conj]
    exact hk
  set X : Subgroup G := ⨆ s : ↥(thompsonJ S), conjR Z' (s : G) with hXdef
  have hXP : X ≤ W ⊔ V := iSup_le fun s => hZ's s s.2
  have hRX : ∀ r ∈ thompsonJ S, conjR X r = X := by
    intro r hr
    have hle : conjR X r ≤ X := by
      rw [hXdef, conjR_iSup]
      refine iSup_le fun s => ?_
      rw [conjR_conjR]
      exact le_iSup (fun s : ↥(thompsonJ S) => conjR Z' (s : G))
        ⟨(s : G) * r, (thompsonJ S).mul_mem s.2 hr⟩
    exact eq_of_le_of_card_le' hle (by rw [card_conjR])
  have hZ'X : Z' ≤ X := by
    have := le_iSup (fun s : ↥(thompsonJ S) => conjR Z' (s : G)) ⟨1, (thompsonJ S).one_mem⟩
    simpa using this
  have hVX : V ≤ X := by
    obtain ⟨w₀, hw₀W, hw₀Z⟩ : ∃ w₀ ∈ W, w₀ ∉ Z := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show W ≤ Z from hcon)
      rw [hZcard] at h1
      have h2 := Nat.pow_lt_pow_right (by norm_num : 1 < 2)
        (show n < 2 * n by have := hcfg.one_lt; omega)
      omega
    obtain ⟨z₀, hz₀, hwa⟩ := conj_eq_mul_of_mem_Wsub hacent' hw₀W
    have hz₀1 : z₀ ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hwa
      apply hw₀Z
      have : w₀ ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G) :=
        ⟨hWR hw₀W, Subgroup.mem_centralizer_singleton_iff.2 (by
          calc w₀ * a = w₀ * (w₀⁻¹ * a * w₀) := by rw [hwa]
            _ = a * w₀ := by group)⟩
      rwa [hCR] at this
    have hY₀ne : conjR Z' w₀ ≠ Z' := by
      intro h1
      have h2 : a * z₀ ∈ Z' := by
        rw [← hwa, ← h1]
        exact mem_conjR_iff'.2 ⟨a, haZg, rfl⟩
      have h3 : z₀ ∈ Z' := by
        have := Z'.mul_mem (Z'.inv_mem haZg) h2
        simpa using this
      have : z₀ ∈ Z ⊓ Z' := ⟨hz₀, h3⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact hz₀1 this
    have hinf' : Z' ⊓ conjR Z' w₀ = ⊥ := fusionIsTI_iff_conjR.1 hTIZ' w₀ hY₀ne
    have hY₀V : conjR Z' w₀ ≤ V := hYV w₀ hw₀W
    have hN : Z' ≤ Subgroup.normalizer (conjR Z' w₀ : Set G) :=
      le_normalizer_of_commute fun y hy w hw => IsElemAbelian.comm hVel (hY₀V hy) (hZ'V hw)
    have hZ'card : Nat.card Z' = 2 ^ n := by rw [hZ'def, card_conjR, hZcard]
    have hcardsup : Nat.card (Z' ⊔ conjR Z' w₀ : Subgroup G) = Nat.card V := by
      have h1 := card_sup_mul_card_inf hN
      rw [hinf', Subgroup.card_bot, mul_one, hZ'card, card_conjR Z' w₀, hZ'card] at h1
      rw [h1, hVcard, hUcard, ← pow_add]
      congr 1
      omega
    have hVeq : Z' ⊔ conjR Z' w₀ = V :=
      eq_of_le_of_card_le' (sup_le hZ'V hY₀V) hcardsup.ge
    rw [← hVeq]
    exact sup_le hZ'X
      (le_iSup (fun s : ↥(thompsonJ S) => conjR Z' (s : G)) ⟨w₀, hWR hw₀W⟩)
  have hRNW : thompsonJ S ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_conj_mem fun r hr w hw => conj_mem_Wsub hZle hacent' hcommR hr hw
  have hRP' : thompsonJ S ≤ Subgroup.normalizer ((W ⊔ V : Subgroup G) : Set G) := by
    by_cases hXeq : X = W ⊔ V
    · intro r hr
      rw [← hXeq]
      exact conjR_eq_self_iff.1 (hRX r hr)
    · have hJ : thompsonJ X = V :=
        E.thompsonJ_eq_of_lt hcfg hx hxS (h := q₀) (hP'conj ▸ hXP)
          (fun h1 => hXeq (h1.trans hP'conj.symm)) hVX hVel hVcard
      intro r hr
      have hrX : r ∈ Subgroup.normalizer (X : Set G) := conjR_eq_self_iff.1 (hRX r hr)
      have hrV : conjR V r = V := by
        have := thompsonJ_normalized hrX
        rwa [hJ] at this
      have hrW : conjR W r = W := conjR_eq_self_iff.2 (hRNW hr)
      rw [← conjR_eq_self_iff, conjR_sup, hrW, hrV]
  have hRN : thompsonJ S ≤ Subgroup.normalizer (conjR (thompsonJ S) q₀ : Set G) :=
    hP'conj ▸ hRP'
  have hRh : conjR (thompsonJ S) q₀ = thompsonJ S := E.conjR_R_eq_of_normalizes hcfg hRN
  have haR' : a ∈ thompsonJ S := by
    have h1 : a ∈ W ⊔ V := Subgroup.mem_sup_right haV
    rw [hP'conj, hRh] at h1
    exact h1
  exact haR haR'

end LQ7

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
