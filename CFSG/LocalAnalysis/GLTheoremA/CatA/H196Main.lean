module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196K
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Group

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie isL2 ambiguousChev)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (LieQConstrained)

variable {K : Type} [Group K] [Finite K]

theorem h196LQ_innerAut {p : ℕ} (hL : LieQConstrained p) (hA : I196AmbLQ p)
    (hK : CFSG.Open.IsQuasisimple K)
    (hchI : CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p ↥(innerAut K) ∨
      catalogIs ↥(innerAut K) (ambiguousChev p))
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) : H196LQ p H (innerAut K) := by
  haveI : Finite (MulAut K) := finite_mulAut K
  have hSn : ((innerAut K).subgroupOf H).Normal :=
    Subgroup.Normal.subgroupOf (innerAut_normal K) H
  have hsimp : IsSimpleGroup ↥((innerAut K).subgroupOf H) :=
    (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hH)).2 (isSimpleGroup_innerAut hK)
  have hna : ∃ a b : ↥((innerAut K).subgroupOf H), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := nonabelian_innerAut hK
    refine ⟨(Subgroup.subgroupOfEquivOfLe hH).symm a, (Subgroup.subgroupOfEquivOfLe hH).symm b, ?_⟩
    intro h
    apply hab
    have := congrArg (Subgroup.subgroupOfEquivOfLe hH) h
    simpa using this
  have hcent : ∀ h ∈ H, (∀ s ∈ innerAut K, h * s = s * h) → h = 1 := by
    intro h _ hc
    have hmem : h ∈ Subgroup.centralizer ((innerAut K : Subgroup (MulAut K)) : Set (MulAut K)) :=
      Subgroup.mem_centralizer_iff.2 (fun s hs => (hc s hs).symm)
    rw [centralizer_innerAut_eq_bot hK, Subgroup.mem_bot] at hmem
    exact hmem
  rcases hchI with hc | ha
  · exact h196LQ_of_lieQConstrained hL hH hSn hsimp hna
      (isChevOfChar_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hH) hc) hcent
  · exact h196LQ_of_ambLQ hA hH hSn hsimp hna
      (h196CatalogIs_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hH) ha) hcent

theorem h196_inner {p : ℕ} [hp : Fact p.Prime]
    (hLQall : ∀ {H : Subgroup (MulAut K)}, innerAut K ≤ H → H196LQ p H (innerAut K))
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H)
    {D : Subgroup (MulAut K)} (hDel : IsElemAbelian p D)
    (hDN : D ≤ Subgroup.normalizer (H : Set (MulAut K)))
    {x : MulAut K} (hxD : x ∈ D) (hxI : x ∈ innerAut K) (hx1 : x ≠ 1) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer (D : Set (MulAut K))) = ⊥ := by
  haveI : Finite (MulAut K) := finite_mulAut K
  have hLQ := hLQall hH
  have hxp : x ^ p = 1 := hDel.2 x hxD
  have hDp : IsPGroup p ↥D := fun g => ⟨1, Subtype.ext (by simpa using hDel.2 g.1 g.2)⟩
  have hDH : ∀ d ∈ D, ∀ h ∈ H, d * h * d⁻¹ ∈ H := fun d hd h hh =>
    (Subgroup.mem_normalizer_iff.1 (hDN hd) h).1 hh
  have hfix : ∀ e ∈ D, ∀ z ∈ Subgroup.zpowers x, e * z * e⁻¹ = z := by
    intro e he z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hex : Commute e x := isElemAbelian_commute hDel he hxD
    have hzk : Commute e (x ^ k) := hex.zpow_right k
    rw [mul_inv_eq_iff_eq_mul]
    exact hzk.eq
  have hQD : ∀ d ∈ D, ∀ y : MulAut K, y ∈ Subgroup.zpowers x ↔ d * y * d⁻¹ ∈ Subgroup.zpowers x := by
    intro d hd y
    constructor
    · intro hy
      rw [hfix d hd y hy]
      exact hy
    · intro hy
      have h2 := hfix d⁻¹ (D.inv_mem hd) (d * y * d⁻¹) hy
      rw [inv_inv] at h2
      have h3 : y = d * y * d⁻¹ := by
        calc y = d⁻¹ * (d * y * d⁻¹) * d := by group
          _ = d * y * d⁻¹ := h2
      rw [h3]
      exact hy
  have hWQ : ∀ w ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer (D : Set (MulAut K))),
      ∀ q ∈ Subgroup.zpowers x, w * q = q * w := by
    intro w hw q hq
    have hwC := GLAPPrimeCoreOf_le p _ hw
    have hwx : x * w = w * x := (Subgroup.mem_centralizer_iff.1 hwC.2) x hxD
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have hcwx : Commute w x := hwx.symm
    exact (hcwx.zpow_right k).eq
  exact h196_core hLQ hDp hDH (GLAPPrimeCoreOf_le p _)
    (fun c hc w hw => GLAPPrimeCoreOf_conj p _ hc hw) (not_dvd_card_GLAPPrimeCoreOf p _)
    (Subgroup.zpowers_le.2 hxI) (by rwa [ne_eq, Subgroup.zpowers_eq_bot])
    (isPGroup_zpowers p hxp) hQD hWQ

theorem GLAPPrimeCoreOf_eq_bot_of_innerAut {p : ℕ} [hp : Fact p.Prime]
    (hK : CFSG.Open.IsQuasisimple K) (hch : IsChevSimple p (K ⧸ Subgroup.center K))
    (hC2 : I196ChevCard p) {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) :
    GLAPPrimeCoreOf p H = ⊥ := by
  haveI : Finite (MulAut K) := finite_mulAut K
  set O := GLAPPrimeCoreOf p H with hO
  set V : Subgroup (MulAut K) := O ⊓ innerAut K with hV
  have hVn : (V.subgroupOf (innerAut K)).Normal := by
    constructor
    intro n hn g
    rw [hV, Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨GLAPPrimeCoreOf_conj p H (hH g.2) hn.1, (innerAut_normal K).conj_mem _ hn.2 g⟩
  rcases (isSimpleGroup_innerAut hK).eq_bot_or_eq_top_of_normal (V.subgroupOf (innerAut K)) with
    hbot | htop
  ·
    have hcent : O ≤ Subgroup.centralizer ((innerAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hmem : ⁅w, s⁆ ∈ V := by
        rw [hV, Subgroup.mem_inf, commutatorElement_def]
        refine ⟨?_, ?_⟩
        · have h2 : s * w⁻¹ * s⁻¹ ∈ O := GLAPPrimeCoreOf_conj p H (hH hs) (O.inv_mem hw)
          have e : w * s * w⁻¹ * s⁻¹ = w * (s * w⁻¹ * s⁻¹) := by group
          rw [e]
          exact O.mul_mem hw h2
        · have h1 : w * s * w⁻¹ ∈ innerAut K := (innerAut_normal K).conj_mem s hs w
          exact (innerAut K).mul_mem h1 ((innerAut K).inv_mem hs)
      have hone : ⁅w, s⁆ = 1 := by
        have hmem' : (⟨⁅w, s⁆, (Subgroup.mem_inf.1 hmem).2⟩ : ↥(innerAut K)) ∈
            V.subgroupOf (innerAut K) :=
          Subgroup.mem_subgroupOf.2 hmem
        rw [hbot, Subgroup.mem_bot] at hmem'
        exact congrArg Subtype.val hmem'
      exact (commutatorElement_eq_one_iff_mul_comm.1 hone).symm
    rw [centralizer_innerAut_eq_bot hK] at hcent
    exact eq_bot_iff.2 hcent
  ·
    exfalso
    have hsub : innerAut K ≤ O := by
      intro s hs
      have hmem : (⟨s, hs⟩ : ↥(innerAut K)) ∈ V.subgroupOf (innerAut K) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
    have hcard1 : Nat.card ↥(innerAut K) ∣ Nat.card ↥O := Subgroup.card_dvd_of_le hsub
    have hnd : ¬ p ∣ Nat.card ↥O := not_dvd_card_GLAPPrimeCoreOf p H
    have hpd : p ∣ Nat.card ↥(innerAut K) := by
      have h := hC2 hp.out (K ⧸ Subgroup.center K) hK.2 hch
      rw [Nat.card_congr (innerAut_equiv K).toEquiv]
      exact h
    exact hnd (dvd_trans hpd hcard1)

theorem h196_outer_aux {p : ℕ} [hp : Fact p.Prime]
    (hLQall : ∀ {H : Subgroup (MulAut K)}, innerAut K ≤ H → H196LQ p H (innerAut K))
    (hp2 : p ≠ 2) (hK : CFSG.Open.IsQuasisimple K) (hch : IsChevSimple p (K ⧸ Subgroup.center K))
    (hF1 : I196OuterFix p) (hF2 : I196OuterCore p)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H)
    {D : Subgroup (MulAut K)} (hDel : IsElemAbelian p D)
    (hDN : D ≤ Subgroup.normalizer (H : Set (MulAut K)))
    (hD1 : D ≠ ⊥) (hDI : D ⊓ innerAut K = ⊥)
    {W : Subgroup (MulAut K)} (hWC : W ≤ H ⊓ Subgroup.centralizer (D : Set (MulAut K)))
    (hWn : ∀ c ∈ H ⊓ Subgroup.centralizer (D : Set (MulAut K)), ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hWp : ¬ p ∣ Nat.card ↥W) :
    W = ⊥ ∨ (p = 3 ∧ catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27))) := by
  haveI : Finite (MulAut K) := finite_mulAut K
  by_cases hWb : W = ⊥
  · exact Or.inl hWb
  right
  obtain ⟨r, hrC, hr1, hrp⟩ := hF1 K hK hch D hDel hD1 hDI
  have hrI : r ∈ innerAut K := (Subgroup.mem_inf.1 hrC).1
  have hrD : r ∈ Subgroup.centralizer (D : Set (MulAut K)) := (Subgroup.mem_inf.1 hrC).2
  have hLQ := hLQall hH
  have hDp : IsPGroup p ↥D := fun g => ⟨1, Subtype.ext (by simpa using hDel.2 g.1 g.2)⟩
  have hDH : ∀ d ∈ D, ∀ h ∈ H, d * h * d⁻¹ ∈ H := fun d hd h hh =>
    (Subgroup.mem_normalizer_iff.1 (hDN hd) h).1 hh
  have hfixr : ∀ e ∈ D, ∀ z ∈ Subgroup.zpowers r, e * z * e⁻¹ = z := by
    intro e he z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have her : Commute e r := (Subgroup.mem_centralizer_iff.1 hrD) e he
    have hek : Commute e (r ^ k) := her.zpow_right k
    rw [mul_inv_eq_iff_eq_mul]
    exact hek.eq
  have hzpowC : Subgroup.zpowers r ≤ innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K)) :=
    Subgroup.zpowers_le.2 hrC
  have hQ_bot : Subgroup.zpowers r ⊓ Subgroup.centralizer (W : Set (MulAut K)) = ⊥ := by
    by_contra hQne
    apply hWb
    refine h196_core hLQ hDp hDH hWC hWn hWp (Q := Subgroup.zpowers r ⊓ Subgroup.centralizer (W : Set (MulAut K)))
      ?_ hQne ?_ ?_ ?_
    · intro z hz
      exact (Subgroup.mem_inf.1 (hzpowC hz.1)).1
    · exact IsPGroup.to_le (isPGroup_zpowers p hrp) inf_le_left
    · intro d hd y
      constructor
      · intro hy
        rw [hfixr d hd y hy.1]
        exact hy
      · intro hy
        have h2 := hfixr d⁻¹ (D.inv_mem hd) (d * y * d⁻¹) hy.1
        rw [inv_inv] at h2
        have h3 : y = d * y * d⁻¹ := by
          calc y = d⁻¹ * (d * y * d⁻¹) * d := by group
            _ = d * y * d⁻¹ := h2
        refine ⟨?_, ?_⟩
        · rw [h3]
          exact hy.1
        · rw [h3]
          exact hy.2
    · intro w hw q hq
      exact (Subgroup.mem_centralizer_iff.1 hq.2) w hw
  obtain ⟨w, hw, hrw⟩ : ∃ w ∈ W, r * w ≠ w * r := by
    by_contra hall
    push Not at hall
    have hrQ : r ∈ Subgroup.zpowers r ⊓ Subgroup.centralizer (W : Set (MulAut K)) :=
      ⟨Subgroup.mem_zpowers r, Subgroup.mem_centralizer_iff.2 (fun w hw => (hall w hw).symm)⟩
    rw [hQ_bot, Subgroup.mem_bot] at hrQ
    exact hr1 hrQ
  have hrHC : r ∈ H ⊓ Subgroup.centralizer (D : Set (MulAut K)) :=
    Subgroup.mem_inf.2 ⟨hH hrI, hrD⟩
  have hcW : r⁻¹ * w⁻¹ * r * w ∈ W := by
    have h1 := hWn r⁻¹ ((H ⊓ Subgroup.centralizer (D : Set (MulAut K))).inv_mem hrHC) w⁻¹
      (W.inv_mem hw)
    rw [inv_inv] at h1
    exact W.mul_mem h1 hw
  have hcC : r⁻¹ * w⁻¹ * r * w ∈ innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K)) := by
    have e : r⁻¹ * w⁻¹ * r * w = r⁻¹ * (w⁻¹ * r * w) := by group
    rw [e]
    refine (innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))).mul_mem
      ((innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))).inv_mem (Subgroup.mem_inf.2 ⟨hrI, hrD⟩)) ?_
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := (innerAut_normal K).conj_mem r hrI w⁻¹
      simpa using h1
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hdw : Commute d w :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hWC hw)).2) d hd
      have hdr : Commute d r := (Subgroup.mem_centralizer_iff.1 hrD) d hd
      calc d * (w⁻¹ * r * w) = (d * w⁻¹) * r * w := by group
        _ = (w⁻¹ * d) * r * w := by rw [hdw.inv_right.eq]
        _ = w⁻¹ * (d * r) * w := by group
        _ = w⁻¹ * (r * d) * w := by rw [hdr.eq]
        _ = (w⁻¹ * r) * (d * w) := by group
        _ = (w⁻¹ * r) * (w * d) := by rw [hdw.eq]
        _ = (w⁻¹ * r * w) * d := by group
  have hcne : r⁻¹ * w⁻¹ * r * w ≠ 1 := by
    intro h1
    apply hrw
    have hc : ⁅r⁻¹, w⁻¹⁆ = 1 := by
      rw [commutatorElement_def, inv_inv, inv_inv]
      exact h1
    have hc2 := commutatorElement_eq_one_iff_mul_comm.1 hc
    have hinv := congrArg (fun z => z⁻¹) hc2
    exact (by simpa [mul_inv_rev] using hinv : w * r = r * w).symm
  have hV : W ⊓ (innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))) ≤
      GLAPPrimeCoreOf p (innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))) := by
    apply le_GLAPPrimeCoreOf p inf_le_right
    · intro c hc v hv
      have hcHC : c ∈ H ⊓ Subgroup.centralizer (D : Set (MulAut K)) :=
        Subgroup.mem_inf.2 ⟨hH (Subgroup.mem_inf.1 hc).1, (Subgroup.mem_inf.1 hc).2⟩
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact hWn c hcHC v (Subgroup.mem_inf.1 hv).1
      · exact (innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))).mul_mem
          ((innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))).mul_mem hc
            (Subgroup.mem_inf.1 hv).2)
          ((innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))).inv_mem hc)
    · intro hdvd
      exact hWp (dvd_trans hdvd (Subgroup.card_dvd_of_le inf_le_left))
  have hcmem := hV (Subgroup.mem_inf.2 ⟨hcW, hcC⟩)
  rcases hF2 hp2 K hK hch D hDel hD1 hDI with h | h
  · exfalso
    rw [h, Subgroup.mem_bot] at hcmem
    exact hcne hcmem
  · exact h

theorem h196_outer {p : ℕ} [hp : Fact p.Prime]
    (hLQall : ∀ {H : Subgroup (MulAut K)}, innerAut K ≤ H → H196LQ p H (innerAut K))
    (hp2 : p ≠ 2) (hK : CFSG.Open.IsQuasisimple K) (hch : IsChevSimple p (K ⧸ Subgroup.center K))
    (hF1 : I196OuterFix p) (hF2 : I196OuterCore p)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H)
    {D : Subgroup (MulAut K)} (hDel : IsElemAbelian p D)
    (hDN : D ≤ Subgroup.normalizer (H : Set (MulAut K)))
    (hD1 : D ≠ ⊥) (hDI : D ⊓ innerAut K = ⊥) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer (D : Set (MulAut K))) = ⊥ ∨
      (p = 3 ∧ catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27))) := by
  haveI : Finite (MulAut K) := finite_mulAut K
  exact h196_outer_aux hLQall hp2 hK hch hF1 hF2 hH hDel hDN hD1 hDI (GLAPPrimeCoreOf_le p _)
    (fun c hc w hw => GLAPPrimeCoreOf_conj p _ hc hw) (not_dvd_card_GLAPPrimeCoreOf p _)

theorem h196_main {p : ℕ} [hp : Fact p.Prime]
    (hLQall : ∀ {H : Subgroup (MulAut K)}, innerAut K ≤ H → H196LQ p H (innerAut K))
    (hp2 : p ≠ 2) (hK : CFSG.Open.IsQuasisimple K) (hch : IsChevSimple p (K ⧸ Subgroup.center K))
    (hF1 : I196OuterFix p) (hF2 : I196OuterCore p) (hC2 : I196ChevCard p)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H)
    {D : Subgroup (MulAut K)} (hDel : IsElemAbelian p D)
    (hDN : D ≤ Subgroup.normalizer (H : Set (MulAut K))) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer (D : Set (MulAut K))) = ⊥ ∨
      (D ≠ ⊥ ∧ D ⊓ innerAut K = ⊥ ∧ p = 3 ∧
        catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27))) := by
  haveI : Finite (MulAut K) := finite_mulAut K
  by_cases hDI : D ⊓ innerAut K = ⊥
  · by_cases hD1 : D = ⊥
    · left
      subst hD1
      have hHC : H ⊓ Subgroup.centralizer ((⊥ : Subgroup (MulAut K)) : Set (MulAut K)) = H := by
        ext h
        simp [Subgroup.mem_centralizer_iff]
      rw [hHC]
      exact GLAPPrimeCoreOf_eq_bot_of_innerAut hK hch hC2 hH
    · rcases h196_outer hLQall hp2 hK hch hF1 hF2 hH hDel hDN hD1 hDI with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hD1, hDI, h.1, h.2⟩
  · left
    have hne : ∃ x ∈ D ⊓ innerAut K, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hDI (eq_bot_iff.2 (fun x hx => Subgroup.mem_bot.2 (hcon x hx)))
    obtain ⟨x, hx, hx1⟩ := hne
    exact h196_inner hLQall hH hDel hDN (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hx).2 hx1

end CFSG.LocalAnalysis.GLTheoremA
