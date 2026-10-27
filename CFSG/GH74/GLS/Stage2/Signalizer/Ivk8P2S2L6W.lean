module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6Aux
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Comp

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg
open CFSG.LocalAnalysis.ComponentInitial (isComponent_le_centralizer_of_isPGroup)
open CFSG.GH74.GLS.Stage2.Final.L26 (WBar_normal WBar_two_pow WBar_le_generalizedFitting
  WBar_eq_map_O22Res)

section ThreeFacts

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem three_basic {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ 3 L₁ L₂) :
    WBar z ≤ L₂ ∧ zBar z ∈ L₂ ∧
      (∀ x ∈ L₂, ∀ y ∈ L₂, orderOf x = 2 → orderOf y = 2 → x = y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hr₁, hr₂, hgt₁, hprod, m₁, m₂, -, h3, -, -, -, -⟩ := hsh
  obtain ⟨-, hF⟩ := h3 rfl
  have hq₁ : IsQuasisimple ↥L₁ := (sl2_model_facts hr₁ (by omega) m₁).1
  have hK₁ : IsComponent L₁ := ⟨hq₁, isSubnormal_of_commute (LBar_normal z) hprod.1 hprod.2.1⟩
  have hFL : generalizedFitting (CentralizerBar z) ≤ LBar z := by
    rw [hF]
    exact Subgroup.map_subtype_le _
  have hWp : IsPGroup 2 ↥(WBar z) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := WBar_two_pow z w hw
    exact ⟨a, Subtype.ext ha⟩
  have hc₁ := isComponent_le_centralizer_of_isPGroup hK₁ (WBar_normal z) hWp
  have hZ₁ := (sl2_model_center_inv hr₁ m₁).1
  have hinv₂ := (sl2_model_center_inv hr₂ m₂).2
  refine ⟨?_, ?_, hinv₂⟩
  · intro w hw
    have hwL : w ∈ L₁ ⊔ L₂ := by
      rw [hprod.1]
      exact hFL (WBar_le_generalizedFitting z hw)
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hprod.2.1 hwL
    have hca : ∀ c ∈ L₁, c * a = a * c := by
      intro c hc
      have h1 : a * b * c = c * (a * b) := mem_centralizer_iff.1 (hc₁ hc) (a * b) hw
      have h2 : c * a * b = a * c * b := by
        calc c * a * b = c * (a * b) := by rw [mul_assoc]
          _ = a * b * c := h1.symm
          _ = a * (b * c) := by rw [mul_assoc]
          _ = a * (c * b) := by rw [hprod.2.1 c hc b hb]
          _ = a * c * b := by rw [mul_assoc]
      exact mul_right_cancel h2
    exact mul_mem (central_mem_of_card_inf hprod.2.1 hZ₁ hprod.2.2 ha hca) hb
  · have hzL : zBar z ∈ L₁ ⊔ L₂ := by
      rw [hprod.1]
      exact hFL (zBar_mem_generalizedFitting z)
    exact (central_le_inf hr₁ hr₂ m₁ m₂ hprod.2.1 hprod.2.2 hzL
      (fun y _ => zBar_central z y)).2

end ThreeFacts

section Claim1

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

omit [Finite G] in
theorem card_quat_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem orderOf_zBar (hz : orderOf z = 2) : orderOf (zBar z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : (zElt z) ^ 2 = 1 := Subtype.ext (by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact this)
  have h2 : (zBar z) ^ 2 = 1 := by
    have : toBar z (zElt z ^ 2) = 1 := by rw [hE, map_one]
    rwa [map_pow] at this
  exact orderOf_eq_prime h2 (zBar_ne_one hz)

omit [Finite G] in
theorem WBar_card_pow_four {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ 3 L₁ L₂) :
    Nat.card ↥(WBar z) = 8 ∧ ∀ w ∈ WBar z, w ^ 4 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h3, -, -, -, -⟩ := hsh
  obtain ⟨⟨e⟩, -⟩ := h3 rfl
  refine ⟨by rw [Nat.card_congr e.toEquiv, card_quat_two], fun w hw => ?_⟩
  have hq4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have : (⟨w, hw⟩ : ↥(WBar z)) ^ 4 = 1 := e.injective (by rw [map_pow, map_one]; exact hq4 _)
  simpa using congrArg Subtype.val this

theorem zBar_mem_WBar_three {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ 3 L₁ L₂) (hz : orderOf z = 2) : zBar z ∈ WBar z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWL, hzL, hinv⟩ := three_basic hsh
  have hdvd : 2 ∣ Nat.card ↥(WBar z) := by rw [(WBar_card_pow_four hsh).1]; norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(WBar z)) 2 hdvd
  have huo : orderOf (u : CentralizerBar z) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have := hinv _ (hWL u.2) _ hzL huo (orderOf_zBar hz)
  rw [← this]
  exact u.2

theorem normal_between {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ 3 L₁ L₂) (hz : orderOf z = 2) {Nb : Subgroup (CentralizerBar z)}
    (hNn : Nb.Normal) (hzN : zBar z ∈ Nb) (hNW : Nb ≤ WBar z) :
    Nb ≤ zpowers (zBar z) ∨ WBar z ≤ Nb := by
  obtain ⟨hWL, hzL, hinv⟩ := three_basic hsh
  have hm₂ : HasSL2Model ↥L₂ (fun q => q = 3) := hsh.2.2.2.2.2.1
  have h4 := (WBar_card_pow_four hsh).2
  have hzo := orderOf_zBar hz
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨x, hxN, hxz⟩ : ∃ x ∈ Nb, x ∉ zpowers (zBar z) := by
    by_contra hh
    push Not at hh
    exact h1 fun x hx => hh x hx
  obtain ⟨w, hwW, hwN⟩ : ∃ w ∈ WBar z, w ∉ Nb := by
    by_contra hh
    push Not at hh
    exact h2 fun w hw => hh w hw
  have hwz : w ∉ zpowers (zBar z) := fun h => hwN (zpowers_le.2 hzN h)
  have hsq : ∀ u ∈ WBar z, u ∉ zpowers (zBar z) → u ^ 2 ≠ 1 := by
    intro u hu huz hu2
    apply huz
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    · have : orderOf u = 2 := orderOf_eq_prime hu2 hu1
      rw [hinv u (hWL hu) (zBar z) hzL this hzo]
      exact mem_zpowers _
  obtain ⟨g, -, hg⟩ := sl2_three_conj4 hm₂ x (hWL (hNW hxN)) w (hWL hwW)
    ⟨h4 x (hNW hxN), hsq x (hNW hxN) hxz⟩ ⟨h4 w hwW, hsq w hwW hwz⟩
  apply hwN
  rw [hg]
  exact hNn.conj_mem x hxN g

end Claim1

section XLevel

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem eq_of_toBar_eq {Q : Subgroup ↥(Cen z)} (hQ : IsPGroup 2 ↥Q) {q q' : ↥(Cen z)}
    (hq : q ∈ Q) (hq' : q' ∈ Q) (h : toBar z q = toBar z q') : q = q' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : q⁻¹ * q' ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 h
  obtain ⟨k, hk⟩ := hQ ⟨q⁻¹ * q', mul_mem (inv_mem hq) hq'⟩
  have hk' : (q⁻¹ * q') ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  exact inv_mul_eq_one.1 (eq_one_of_mem_pPrimeCore_of_two_pow hd hk')

theorem exists_lift (Q : Sylow 2 ↥(Cen z)) {w : ↥(Cen z)} (hw : w ∈ O22Res ↥(Cen z)) :
    ∃ q ∈ (Q : Subgroup ↥(Cen z)), q ∈ O22Res ↥(Cen z) ∧ toBar z q = toBar z w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 ↥(WBar z) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := WBar_two_pow z w hw
    exact ⟨a, Subtype.ext ha⟩
  have := WBar_normal z
  have hle : WBar z ≤ ((Sylow.mapSurjective (toBar_surjective z) Q : Sylow 2 (CentralizerBar z)) :
      Subgroup (CentralizerBar z)) := hWp.le_sylow_of_normal _
  have hwb : toBar z w ∈ WBar z := by
    rw [WBar_eq_map_O22Res]
    exact mem_map_of_mem _ hw
  obtain ⟨q, hqQ, hq⟩ := hle hwb
  refine ⟨q, hqQ, ?_, hq⟩
  have hA : w⁻¹ * q ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 hq.symm
  have hqw : q = w * (w⁻¹ * q) := by group
  rw [hqw]
  exact mul_mem hw (pPrimeCore_le_O22Res hA)

theorem O22Res_eq_sup (Q : Sylow 2 ↥(Cen z)) :
    O22Res ↥(Cen z) =
      pPrimeCore 2 ↥(Cen z) ⊔ ((Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨q, hqQ, hqW, hq⟩ := exists_lift Q hw
    have hA : q⁻¹ * w ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 hq
    have hwq : w = q * (q⁻¹ * w) := by group
    rw [hwq]
    exact mul_mem (mem_sup_right ⟨hqQ, hqW⟩) (mem_sup_left hA)
  · exact sup_le pPrimeCore_le_O22Res inf_le_right

theorem nonempty_equiv_quat (Q : Sylow 2 ↥(Cen z))
    (hWq : Nonempty (↥(WBar z) ≃* QuaternionGroup 2)) :
    Nonempty (↥((Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z)) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := hWq
  let f : ↥((Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z)) →* ↥(WBar z) :=
    ((toBar z).comp ((Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z)).subtype).codRestrict (WBar z)
      (fun q => by
        rw [WBar_eq_map_O22Res]
        exact mem_map_of_mem _ q.2.2)
  have hinj : Function.Injective f := by
    intro q q' h
    apply Subtype.ext
    exact eq_of_toBar_eq Q.isPGroup' q.2.1 q'.2.1 (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    rintro ⟨b, hb⟩
    rw [WBar_eq_map_O22Res] at hb
    obtain ⟨w, hw, rfl⟩ := hb
    obtain ⟨q, hqQ, hqW, hq⟩ := exists_lift Q hw
    exact ⟨⟨q, hqQ, hqW⟩, Subtype.ext hq⟩
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).trans e⟩

omit [Finite G] in
theorem normal_zpowers_zElt (z : G) : (zpowers (zElt z)).Normal := ⟨fun n hn g => by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
  have hc : Commute g (zElt z) := Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  exact zpow_mem_zpowers _ k⟩

theorem zElt_mem_O22Res {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ 3 L₁ L₂) (hz : orderOf z = 2) : zElt z ∈ O22Res ↥(Cen z) := by
  have hb : zBar z ∈ WBar z := zBar_mem_WBar_three hsh hz
  rw [WBar_eq_map_O22Res] at hb
  obtain ⟨w, hw, hwz⟩ := hb
  have hA : w⁻¹ * zElt z ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 hwz
  have hzw : zElt z = w * (w⁻¹ * zElt z) := by group
  rw [hzw]
  exact mul_mem hw (pPrimeCore_le_O22Res hA)

end XLevel

section CentralizerPart

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem inf_centralizer_eq {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ 3 L₁ L₂) (hz : orderOf z = 2) (Q : Sylow 2 ↥(Cen z))
    (hno : ¬ ∀ s ∈ (Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z), ∀ a ∈ pPrimeCore 2 ↥(Cen z),
      s * a = a * s) :
    (Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z) ⊓ centralizer (pPrimeCore 2 ↥(Cen z) : Set ↥(Cen z)) =
      zpowers (zElt z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  have hzW : zElt z ∈ O22Res ↥(Cen z) := zElt_mem_O22Res hsh hz
  have hzc : ∀ a : ↥(Cen z), zElt z * a = a * zElt z := fun a =>
    (Subtype.ext (mem_centralizer_singleton_iff.1 a.2)).symm
  have hzp : IsPGroup 2 ↥(zpowers (zElt z)) := by
    have hord : orderOf (zElt z) = 2 := by
      rw [← hz, ← Subgroup.orderOf_coe]
      rfl
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have := normal_zpowers_zElt z
  have hzQ : zElt z ∈ (Q : Subgroup ↥(Cen z)) := hzp.le_sylow_of_normal Q (mem_zpowers _)
  have hzN : zElt z ∈ O22Res ↥(Cen z) ⊓ centralizer (pPrimeCore 2 ↥(Cen z) : Set ↥(Cen z)) :=
    ⟨hzW, mem_centralizer_iff.2 fun a _ => (hzc a).symm⟩
  apply le_antisymm
  · rintro s ⟨⟨hsQ, hsW⟩, hsC⟩
    have : (O22Res ↥(Cen z)).Normal := O22Res_normal
    have : (centralizer (pPrimeCore 2 ↥(Cen z) : Set ↥(Cen z))).Normal :=
      normal_centralizer_of_normal _
    set N : Subgroup ↥(Cen z) :=
      O22Res ↥(Cen z) ⊓ centralizer (pPrimeCore 2 ↥(Cen z) : Set ↥(Cen z)) with hN
    have hNb : (N.map (toBar z)).Normal :=
      Subgroup.Normal.map inferInstance (toBar z) (toBar_surjective z)
    have hzNb : zBar z ∈ N.map (toBar z) := ⟨zElt z, hzN, rfl⟩
    have hNW : N.map (toBar z) ≤ WBar z := by
      rw [WBar_eq_map_O22Res]
      exact Subgroup.map_mono inf_le_left
    rcases normal_between hsh hz hNb hzNb hNW with h1 | h2
    · have hb : toBar z s ∈ barOf z (zpowers z) :=
        zpowers_le.2 (zBar_mem_barOf z) (h1 ⟨s, ⟨hsW, hsC⟩, rfl⟩)
      obtain ⟨k, hk⟩ := Q.isPGroup' ⟨s, hsQ⟩
      have hs2 : ∃ k : ℕ, (s : G) ^ (2 ^ k) = 1 := ⟨k, congrArg (fun x : ↥(Q : Subgroup ↥(Cen z)) =>
        ((x : ↥(Cen z)) : G)) hk⟩
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (mem_zpowers_of_toBar_mem hz s.2 hs2 hb)
      exact ⟨n, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn)⟩
    · exfalso
      apply hno
      intro s' hs' a ha
      have hs'W : toBar z s' ∈ WBar z := by
        rw [WBar_eq_map_O22Res]
        exact mem_map_of_mem _ hs'.2
      obtain ⟨n, hnN, hn⟩ := h2 hs'W
      have hna : n⁻¹ * s' ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 hn
      obtain ⟨k, hk⟩ := Q.isPGroup' ⟨s', hs'.1⟩
      exact centralizes_of_mul_eq hodd ⟨k, congrArg Subtype.val hk⟩
        (fun x hx => (mem_centralizer_iff.1 hnN.2 x hx).symm) hna
        (mul_inv_cancel_left n s').symm a ha
  · rw [zpowers_le]
    exact ⟨⟨hzQ, hzW⟩, mem_centralizer_iff.2 fun a _ => (hzc a).symm⟩

end CentralizerPart

section Final

theorem lemma17_6W_thm : Lemma17_6W := by
  intro G _ _ z k S M hF hMC hE hLE hG3
  subst hMC
  have ctx : Stage2Ctx G z k S := hF.ctx.ctx
  have hz : orderOf z = 2 := ctx.central.1
  obtain ⟨r₁, L₁, L₂, hsh⟩ := hG3
  have hWq : Nonempty (↥(WBar z) ≃* QuaternionGroup 2) := (hsh.2.2.2.2.2.2.2.1 rfl).1
  obtain ⟨Q, hQ⟩ := ctx.sylow
  have hno : ¬ ∀ s ∈ (Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z), ∀ a ∈ pPrimeCore 2 ↥(Cen z),
      s * a = a * s := by
    intro h
    apply hF.fail
    refine ⟨hLE, fun h' => absurd h' (lt_irrefl _), fun _ => ?_⟩
    refine isInternalDirectProduct_of_sylow_of_centralizes ⟨Q, hQ⟩ ?_
    rintro s ⟨hsS, w, hw, rfl⟩ f ⟨f', hf', rfl⟩
    obtain ⟨q, hqQ, hqw⟩ := (hQ ▸ hsS : _ ∈ (Q : Subgroup ↥(Cen z)).map (Cen z).subtype)
    have hqw' : q = w := Subtype.ext hqw
    subst hqw'
    have := h q ⟨hqQ, hw⟩ f' hf'.2
    exact congrArg Subtype.val this
  have h3 := inf_centralizer_eq hsh hz Q hno
  have hW : O22Of (O2Of (Cen z)) = (O22Res ↥(Cen z)).map (Cen z).subtype := O22Of_O2Of_eq _
  have hD : pPrimeCoreOf 2 (O22Of (O2Of (Cen z))) =
      (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype := by
    rw [hW, pPrimeCoreOf_map_subtype, pPrimeCoreOf_eq_inf O22Res_normal.isSubnormal,
      inf_eq_right.2 pPrimeCore_le_O22Res]
  have hSW : S ⊓ O22Of (O2Of (Cen z)) =
      ((Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z)).map (Cen z).subtype := by
    rw [hW, ← hQ, Subgroup.map_inf _ _ _ (Cen z).subtype_injective]
  refine ⟨?_, ?_, ?_⟩
  · rw [hSW, hD]
    conv_lhs => rw [hW]
    rw [← Subgroup.map_sup, ← O22Res_eq_sup Q]
  · rw [hSW]
    obtain ⟨e⟩ := nonempty_equiv_quat Q hWq
    exact ⟨(Subgroup.equivMapOfInjective _ _ (Cen z).subtype_injective).symm.trans e⟩
  · ext s
    constructor
    · rintro ⟨hsSW, hsC⟩
      rw [hSW] at hsSW
      obtain ⟨q, hq, rfl⟩ := hsSW
      have hqC : q ∈ centralizer (pPrimeCore 2 ↥(Cen z) : Set ↥(Cen z)) := by
        rw [mem_centralizer_iff]
        intro a ha
        have h1 : ((a : ↥(Cen z)) : G) ∈ pPrimeCoreOf 2 (O22Of (O2Of (Cen z))) := by
          rw [hD]
          exact ⟨a, ha, rfl⟩
        exact Subtype.ext (mem_centralizer_iff.1 hsC _ h1)
      have hmem : q ∈ zpowers (zElt z) := by
        rw [← h3]
        exact ⟨hq, hqC⟩
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
      exact ⟨n, by rw [← hn, map_zpow]; rfl⟩
    · intro hs
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hs
      have hmem : zElt z ^ n ∈ (Q : Subgroup ↥(Cen z)) ⊓ O22Res ↥(Cen z) ⊓
          centralizer (pPrimeCore 2 ↥(Cen z) : Set ↥(Cen z)) := by
        rw [h3]
        exact zpow_mem_zpowers _ n
      refine ⟨?_, ?_⟩
      · rw [hSW]
        exact ⟨zElt z ^ n, hmem.1, by rw [map_zpow]; rfl⟩
      · refine Subgroup.mem_centralizer_iff.2 ?_
        intro d hd
        rw [hD] at hd
        obtain ⟨a, ha, rfl⟩ := hd
        have h4 := congrArg Subtype.val (mem_centralizer_iff.1 hmem.2 a ha)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow] at h4
        exact h4

end Final

theorem lemma17_6_thm (h171 : Prop17_1) : Lemma17_6 := lemma17_6_of h171 lemma17_6W_thm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
