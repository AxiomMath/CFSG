module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JWb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S105S

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10W_conj_sup_mem {t z c : G}
    (ht : c * t * c⁻¹ ∈ zpowers t ⊔ zpowers z) (hz : c * z * c⁻¹ ∈ zpowers t ⊔ zpowers z) :
    ∀ x ∈ zpowers t ⊔ zpowers z, c * x * c⁻¹ ∈ zpowers t ⊔ zpowers z := by
  intro x hx
  have hle : (zpowers t ⊔ zpowers z).map (MulAut.conj c).toMonoidHom ≤
      zpowers t ⊔ zpowers z := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · simpa [MulAut.conj_apply] using ht
    · simpa [MulAut.conj_apply] using hz
  simpa [MulAut.conj_apply] using hle (Subgroup.mem_map_of_mem _ hx)

theorem sec10W_mem_normalizer_of {X : Subgroup G} {c : G} (h1 : ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, c⁻¹ * x * c ∈ X) : c ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 x hx
  · intro hx
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    simpa [e] using h2 _ hx

theorem sec10W_hatCent_cases {t z c : G} (hz2 : orderOf z = 2) (ht2 : orderOf t = 2)
    (hzt : z * t = t * z) (htz : t ≠ z) (hc : c ∈ hatCent t z) :
    c * t * c⁻¹ = t ∨ c * t * c⁻¹ = t * z := by
  obtain ⟨hcz, hcn⟩ := Subgroup.mem_inf.mp hc
  have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have htX : t ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hmem : c * t * c⁻¹ ∈ zpowers t ⊔ zpowers z := by
    have := (Subgroup.mem_normalizer_iff.mp hcn t).mp htX
    simpa using this
  have hord : orderOf (c * t * c⁻¹) = 2 := by
    have h1 : orderOf ((MulAut.conj c) t) = orderOf t := MulEquiv.orderOf_eq _ _
    rw [MulAut.conj_apply] at h1
    exact h1.trans ht2
  have hmem' : c * t * c⁻¹ ∈ zpowers z ⊔ zpowers t := by
    rw [sup_comm]
    exact hmem
  rcases sec10_two_elem_cases hzt hz2 ht2 hmem' hord with h | h | h
  · exfalso
    apply htz
    have e : t = c⁻¹ * (c * t * c⁻¹) * c := by group
    rw [e, h]
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hcz']
      _ = z := by group
  · exact Or.inl h
  · exact Or.inr h

theorem sec10W_g_mem_hatCent [Finite G] (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) : g ∈ hatCent t z := by
  obtain ⟨-, hz2, -, -, -, -⟩ := sec10D_basic hb hctx.toSec10Ctx
  have hgz : g * z = z * g := sec10D_g_comm_z hz2 hctx
  have hswap : g⁻¹ * t * g = t * z := hctx.swap
  have e1 : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  have e1' : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  have e2 : t = (g * t * g⁻¹) * z := by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hswap]
      _ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * t * g⁻¹) * z := by rw [e1]
  have e3 : g * t * g⁻¹ = t * z := by
    calc g * t * g⁻¹ = (g * t * g⁻¹) * (z * z) := by rw [hz2, mul_one]
      _ = ((g * t * g⁻¹) * z) * z := by group
      _ = t * z := by rw [← e2]
  have htX : t * z ∈ zpowers t ⊔ zpowers z :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hzX : z ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have h1 : ∀ x ∈ zpowers t ⊔ zpowers z, g * x * g⁻¹ ∈ zpowers t ⊔ zpowers z :=
    sec10W_conj_sup_mem (by rw [e3]; exact htX) (by rw [e1]; exact hzX)
  have h2 : ∀ x ∈ zpowers t ⊔ zpowers z, g⁻¹ * x * g ∈ zpowers t ⊔ zpowers z := by
    intro x hx
    have := sec10W_conj_sup_mem (t := t) (z := z) (c := g⁻¹) (by rw [inv_inv, hswap]; exact htX)
      (by rw [inv_inv, e1']; exact hzX) x hx
    simpa using this
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgz, sec10W_mem_normalizer_of h1 h2⟩

theorem sec10W_T_le_hatCent [Finite G] (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) :
    S ⊔ zpowers g ≤ hatCent t z := by
  refine sup_le ?_ (Subgroup.zpowers_le.mpr (sec10W_g_mem_hatCent hb hctx))
  have hzX : z ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have htX : t ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hfix : ∀ s ∈ S, s * t * s⁻¹ = t ∧ s * z * s⁻¹ = z := by
    intro s hs
    have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs)
    have hsz : s * z = z * s := hctx.central s hs
    constructor
    · calc s * t * s⁻¹ = (t * s) * s⁻¹ := by rw [hst]
        _ = t := by group
    · calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hsz]
        _ = z := by group
  intro s hs
  have hfix' := hfix s hs
  have hfixi := hfix s⁻¹ (S.inv_mem hs)
  have h1 : ∀ x ∈ zpowers t ⊔ zpowers z, s * x * s⁻¹ ∈ zpowers t ⊔ zpowers z :=
    sec10W_conj_sup_mem (by rw [hfix'.1]; exact htX) (by rw [hfix'.2]; exact hzX)
  have h2 : ∀ x ∈ zpowers t ⊔ zpowers z, s⁻¹ * x * s ∈ zpowers t ⊔ zpowers z := by
    intro x hx
    have := sec10W_conj_sup_mem (t := t) (z := z) (c := s⁻¹) (by rw [hfixi.1]; exact htX)
      (by rw [hfixi.2]; exact hzX) x hx
    simpa using this
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hs),
      sec10W_mem_normalizer_of h1 h2⟩

theorem sec10W_T_sylow [Finite G] (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) :
    IsSylow2Of (S ⊔ zpowers g) (hatCent t z) := by
  obtain ⟨ht2, hz2, -, -, htz, hzt⟩ := sec10D_basic hb hctx.toSec10Ctx
  have hz2' : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have ht2' : orderOf t = 2 := hctx.involution
  have hT2 : IsPGroup 2 ↥(S ⊔ zpowers g) := sec10D_T_pgroup hctx
  have hTle : S ⊔ zpowers g ≤ hatCent t z := sec10W_T_le_hatCent hb hctx
  obtain ⟨P, hP, hTP⟩ := exists_isSylow2Of_ge hT2 hTle
  have hSP : S ≤ P := le_sup_left.trans hTP
  have hgP : g ∈ P := hTP (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hPS : P ⊓ centralizer ({t} : Set G) = S :=
    hctx.sylow.eq_of_le inf_le_right hP.2.1.to_inf_left (le_inf hSP hctx.sylow.1)
  have hswap : g⁻¹ * t * g = t * z := hctx.swap
  have hgz : g * z = z * g := sec10D_g_comm_z hz2 hctx
  have e1' : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  have hPT : P ≤ S ⊔ zpowers g := by
    intro p hp
    have hpC : p ∈ hatCent t z := hP.1 hp
    rcases sec10W_hatCent_cases hz2' ht2' hzt.symm htz hpC with h | h
    · have hpt : p * t = t * p := by
        calc p * t = (p * t * p⁻¹) * p := by group
          _ = t * p := by rw [h]
      have hpS : p ∈ S := by
        rw [← hPS]
        exact ⟨hp, Subgroup.mem_centralizer_singleton_iff.mpr hpt⟩
      exact Subgroup.mem_sup_left hpS
    · have hq : g⁻¹ * p ∈ P := P.mul_mem (P.inv_mem hgP) hp
      have hqt : (g⁻¹ * p) * t = t * (g⁻¹ * p) := by
        have e : (g⁻¹ * p) * t * (g⁻¹ * p)⁻¹ = g⁻¹ * (p * t * p⁻¹) * g := by group
        have e' : g⁻¹ * (p * t * p⁻¹) * g = t := by
          rw [h]
          calc g⁻¹ * (t * z) * g = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by group
            _ = (t * z) * z := by rw [hswap, e1']
            _ = t := by rw [mul_assoc, hz2, mul_one]
        calc (g⁻¹ * p) * t = ((g⁻¹ * p) * t * (g⁻¹ * p)⁻¹) * (g⁻¹ * p) := by group
          _ = t * (g⁻¹ * p) := by rw [e, e']
      have hqS : g⁻¹ * p ∈ S := by
        rw [← hPS]
        exact ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hqt⟩
      have hp' : p = g * (g⁻¹ * p) := by group
      rw [hp']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
        (Subgroup.mem_sup_left hqS)
  have hPeq : P = S ⊔ zpowers g := le_antisymm hPT hTP
  rw [← hPeq]
  exact hP

theorem sec10W_conj_le_hatCent [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {h : G} (hh : h ∈ centralizer ({z} : Set G))
    (hmem : h⁻¹ * t * h ∈ secW t K1 K2) : ∀ w ∈ secW t K1 K2, h * w * h⁻¹ ∈ hatCent t z := by
  obtain ⟨hzW, hWmod⟩ := sec10J_W_elem hP5 hC5 hb hctx
  have hWS : secW t K1 K2 ≤ S := sec10J_W_le hP5 hb hctx
  have hzX : z ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have htX : t ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hmain : ∀ w ∈ secW t K1 K2, (h * w * h⁻¹) * t * (h * w * h⁻¹)⁻¹ ∈ zpowers t ⊔ zpowers z ∧
      (h * w * h⁻¹) * z * (h * w * h⁻¹)⁻¹ = z := by
    intro w hw
    have hwz : w * z = z * w := hctx.central w (hWS hw)
    constructor
    · obtain ⟨hε, -⟩ := hWmod w hw (h⁻¹ * t * h) hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hε
      have hεc : h * (w * (h⁻¹ * t * h) * w⁻¹ * (h⁻¹ * t * h)⁻¹) * h⁻¹
          = w * (h⁻¹ * t * h) * w⁻¹ * (h⁻¹ * t * h)⁻¹ := by
        rw [← hk]
        have hc : Commute h z := hhz
        have := (hc.zpow_right k).eq
        calc h * z ^ k * h⁻¹ = (z ^ k * h) * h⁻¹ := by rw [← this]
          _ = z ^ k := by group
      have e : (h * w * h⁻¹) * t * (h * w * h⁻¹)⁻¹
          = (h * (w * (h⁻¹ * t * h) * w⁻¹ * (h⁻¹ * t * h)⁻¹) * h⁻¹) * t := by group
      rw [e, hεc, ← hk]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hzX k) htX
    · calc (h * w * h⁻¹) * z * (h * w * h⁻¹)⁻¹ = h * w * (h⁻¹ * z * h) * w⁻¹ * h⁻¹ := by group
        _ = z := by
          have e1 : h⁻¹ * z * h = z := by
            calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
              _ = h⁻¹ * (h * z) := by rw [hhz]
              _ = z := by group
          rw [e1]
          calc h * w * z * w⁻¹ * h⁻¹ = h * (w * z) * w⁻¹ * h⁻¹ := by group
            _ = h * (z * w) * w⁻¹ * h⁻¹ := by rw [hwz]
            _ = h * z * h⁻¹ := by group
            _ = z := by rw [hhz]; group
  intro w hw
  have hw' : w⁻¹ ∈ secW t K1 K2 := (secW t K1 K2).inv_mem hw
  have hc1 : ∀ x ∈ zpowers t ⊔ zpowers z, (h * w * h⁻¹) * x * (h * w * h⁻¹)⁻¹ ∈
      zpowers t ⊔ zpowers z :=
    sec10W_conj_sup_mem (hmain w hw).1 (by rw [(hmain w hw).2]; exact hzX)
  have hc2 : ∀ x ∈ zpowers t ⊔ zpowers z, (h * w * h⁻¹)⁻¹ * x * (h * w * h⁻¹) ∈
      zpowers t ⊔ zpowers z := by
    intro x hx
    have e : h * w⁻¹ * h⁻¹ = (h * w * h⁻¹)⁻¹ := by group
    have := sec10W_conj_sup_mem (t := t) (z := z) (c := h * w⁻¹ * h⁻¹)
      (by have := (hmain w⁻¹ hw').1; exact this)
      (by rw [(hmain w⁻¹ hw').2]; exact hzX) x hx
    rw [e, inv_inv] at this
    exact this
  refine Subgroup.mem_inf.mpr ⟨?_, sec10W_mem_normalizer_of hc1 hc2⟩
  exact (centralizer ({z} : Set G)).mul_mem
    ((centralizer ({z} : Set G)).mul_mem hh
      (Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central w (hWS hw))))
    ((centralizer ({z} : Set G)).inv_mem hh)

theorem sec10W_norm_center [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {y : G}
    (h1 : ∀ x ∈ secW t K1 K2, y * x * y⁻¹ ∈ secW t K1 K2)
    (h2 : ∀ x ∈ secW t K1 K2, y⁻¹ * x * y ∈ secW t K1 K2) :
    y ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) := by
  obtain ⟨hzW, -⟩ := sec10J_W_elem hP5 hC5 hb hctx
  have hWS : secW t K1 K2 ≤ S := sec10J_W_le hP5 hb hctx
  have htW : t ∈ secW t K1 K2 := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hXW : zpowers t ⊔ zpowers z ≤ secW t K1 K2 :=
    sup_le (Subgroup.zpowers_le.mpr htW) (Subgroup.zpowers_le.mpr hzW)
  have hcen : ∀ x ∈ zpowers t ⊔ zpowers z, ∀ w ∈ secW t K1 K2, x * w = w * x := by
    intro x hx w hw
    have hwt : w ∈ centralizer ({t} : Set G) := hctx.sylow.1 (hWS hw)
    have hwz : w * z = z * w := hctx.central w (hWS hw)
    have hsub : zpowers t ⊔ zpowers z ≤ centralizer ({w} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hwt).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hwz.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hx)
  have aux : ∀ c : G, (∀ x ∈ secW t K1 K2, c * x * c⁻¹ ∈ secW t K1 K2) →
      (∀ x ∈ secW t K1 K2, c⁻¹ * x * c ∈ secW t K1 K2) →
      ∀ x ∈ zpowers t ⊔ zpowers z, c * x * c⁻¹ ∈ zpowers t ⊔ zpowers z := by
    intro c hc1 hc2 x hx
    refine sec10J_W_center hP5 hC5 hb hctx (c * x * c⁻¹) (hc1 x (hXW hx)) ?_
    intro w hw
    have hw' := hc2 w hw
    have hxc := hcen x hx _ hw'
    calc (c * x * c⁻¹) * w = c * (x * (c⁻¹ * w * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * w * c) * x) * c⁻¹ := by rw [hxc]
      _ = w * (c * x * c⁻¹) := by group
  exact sec10W_mem_normalizer_of (aux y h1 h2) (by
    have := aux y⁻¹ (by simpa using h2) (by simpa using h1)
    simpa using this)

theorem asc82Step109W_of (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hB : Asc82Step109B) (hb : Asc82Basic10) : Asc82Step109W := by
  intro G _ _ t L S z K1 K2 g hctx h hh hmem
  obtain ⟨-, hz2, -, -, htz, hzt⟩ := sec10D_basic hb hctx.toSec10Ctx
  have hz2' : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have ht2' : orderOf t = 2 := hctx.involution
  obtain ⟨hzW, -⟩ := sec10J_W_elem hP5 hC5 hb hctx.toSec10Ctx
  have hWS : secW t K1 K2 ≤ S := sec10J_W_le hP5 hb hctx.toSec10Ctx
  have hmemW : h⁻¹ * t * h ∈ secW t K1 K2 := by
    rwa [sup_eq_left.mpr (Subgroup.zpowers_le.mpr hzW)] at hmem
  have hconj := sec10W_conj_le_hatCent hP5 hC5 hb hctx.toSec10Ctx hh hmemW
  let X : Subgroup G := (secW t K1 K2).map (MulAut.conj h).toMonoidHom
  have hW2 : IsPGroup 2 ↥(secW t K1 K2) := hctx.sylow.2.1.to_le hWS
  have hX2 : IsPGroup 2 ↥X := hW2.map _
  have hXle : X ≤ hatCent t z := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using hconj w hw
  obtain ⟨Q, hQ, hXQ⟩ := exists_isSylow2Of_ge hX2 hXle
  obtain ⟨a, haĤ, haQ⟩ := (sec10W_T_sylow hb hctx).exists_conj_mem hQ
  have haH : a ∈ centralizer ({z} : Set G) := (Subgroup.mem_inf.mp haĤ).1
  have hyH : h⁻¹ * a ∈ centralizer ({z} : Set G) :=
    (centralizer ({z} : Set G)).mul_mem ((centralizer ({z} : Set G)).inv_mem hh) haH
  have hcond : CFSG.conjugate (secW t K1 K2) (h⁻¹ * a) ≤ S ⊔ zpowers g := by
    intro x hx
    have hw : (h⁻¹ * a) * x * (h⁻¹ * a)⁻¹ ∈ secW t K1 K2 := mem_conjugate_iff'.mp hx
    have hxQ : h * ((h⁻¹ * a) * x * (h⁻¹ * a)⁻¹) * h⁻¹ ∈ Q :=
      hXQ (Subgroup.mem_map.mpr ⟨_, hw, by simp [MulAut.conj_apply]⟩)
    have := (haQ _).mp hxQ
    have e : a⁻¹ * (h * ((h⁻¹ * a) * x * (h⁻¹ * a)⁻¹) * h⁻¹) * a = x := by group
    rwa [e] at this
  have hconjEq := hB G t L S z K1 K2 g hctx (h⁻¹ * a) hyH hcond
  have h1 : ∀ x ∈ secW t K1 K2, (h⁻¹ * a) * x * (h⁻¹ * a)⁻¹ ∈ secW t K1 K2 := by
    intro x hx
    apply mem_conjugate_iff'.mp
    rw [hconjEq]
    exact hx
  have h2 : ∀ x ∈ secW t K1 K2, (h⁻¹ * a)⁻¹ * x * (h⁻¹ * a) ∈ secW t K1 K2 := by
    intro x hx
    have hm : (h⁻¹ * a)⁻¹ * x * (h⁻¹ * a) ∈ CFSG.conjugate (secW t K1 K2) (h⁻¹ * a) := by
      rw [mem_conjugate_iff']
      have e : (h⁻¹ * a) * ((h⁻¹ * a)⁻¹ * x * (h⁻¹ * a)) * (h⁻¹ * a)⁻¹ = x := by group
      rw [e]
      exact hx
    rwa [hconjEq] at hm
  have hyN : h⁻¹ * a ∈ hatCent t z :=
    Subgroup.mem_inf.mpr ⟨hyH, sec10W_norm_center hP5 hC5 hb hctx.toSec10Ctx h1 h2⟩
  have hhinv : h⁻¹ ∈ hatCent t z := by
    have := (hatCent t z).mul_mem hyN ((hatCent t z).inv_mem haĤ)
    simpa using this
  rcases sec10W_hatCent_cases hz2' ht2' hzt.symm htz hhinv with h' | h'
  · left
    simpa using h'
  · right
    simpa using h'

end CFSG.OddStandard.SmallF3.Omega
