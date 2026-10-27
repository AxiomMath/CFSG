module

public import CFSG.CGT.PushingUpLit.SolKNA.Lemma18
public import CFSG.CGT.PushingUpLit.SolKNA.Prop18Sz

public section

open scoped IsMulCommutative

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender
open CFSG.RankThree.GF2n (conjSubgroup_mul card_conjSubgroup isTI_conjSubgroup
  conjSubgroup_eq_self_iff)
open CFSG.RankThree.GF2n.Tim77 (mem_normalizer_of_commute_of_isTI conjSubgroup_eq_of_inf_ne_bot)
open scoped MatrixGroups

section Transport

variable {G : Type} [Group G]

theorem conjSubgroup_subgroupOf {Y : Subgroup G} (y : Y) (T : Subgroup G) :
    conjSubgroup y (T.subgroupOf Y) = (conjSubgroup (y : G) T).subgroupOf Y := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSubgroup]
  rfl

@[expose] def IsTIIn (Z R : Subgroup G) : Prop :=
  ∀ z ∈ Z, R ⊓ conjSubgroup z R = ⊥ ∨ R ⊓ conjSubgroup z R = R

theorem isTIIn_of_isTI {Z R : Subgroup G} (h : IsTI R) : IsTIIn Z R := fun z _ => h z

theorem conjSubgroup_eq_of_isTIIn [Finite G] {Z R : Subgroup G} (h : IsTIIn Z R) {z : G}
    (hz : z ∈ Z) (hne : R ⊓ conjSubgroup z R ≠ ⊥) : conjSubgroup z R = R := by
  rcases h z hz with h' | h'
  · exact absurd h' hne
  · have hle : R ≤ conjSubgroup z R := calc
      R = R ⊓ conjSubgroup z R := h'.symm
      _ ≤ conjSubgroup z R := inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [CFSG.RankThree.GF2n.card_conjSubgroup])).symm

theorem isTIIn_conj {Z R : Subgroup G} (h : IsTIIn Z R) {g : G} (hg : g ∈ Z) :
    IsTIIn Z (conjSubgroup g R) := by
  intro k hk
  have e : conjSubgroup k (conjSubgroup g R) =
      conjSubgroup g (conjSubgroup (g⁻¹ * k * g) R) := by
    rw [← conjSubgroup_mul, ← conjSubgroup_mul]
    congr 1
    group
  have hk' : g⁻¹ * k * g ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem hg) hk) hg
  rw [e, ← CFSG.RankThree.GF2n.conjSubgroup_inf]
  rcases h _ hk' with hk | hk
  · left
    rw [hk]
    exact Subgroup.map_bot _
  · right
    rw [hk]

theorem mem_normalizer_of_commute_of_isTIIn [Finite G] {Z R : Subgroup G} (h : IsTIIn Z R)
    {c x : G} (hc : c ∈ Z) (hx : x ∈ R) (hx1 : x ≠ 1) (hcx : c * x = x * c) :
    c ∈ Subgroup.normalizer (R : Set G) := by
  rw [← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_isTIIn h hc fun hbot => hx1 ?_
  have hmem : x ∈ R ⊓ conjSubgroup c R := by
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup, show c⁻¹ * x * c = x by rw [mul_assoc, ← hcx]; group]
    exact hx
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem conjSubgroup_eq_of_inf_ne_botIn [Finite G] {Z R : Subgroup G} (h : IsTIIn Z R) {a b : G}
    (ha : a ∈ Z) (hb : b ∈ Z) (hne : conjSubgroup a R ⊓ conjSubgroup b R ≠ ⊥) :
    conjSubgroup a R = conjSubgroup b R := by
  have hTI := isTIIn_conj h hb
  have e : conjSubgroup a R = conjSubgroup (a * b⁻¹) (conjSubgroup b R) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  rw [e] at hne ⊢
  exact conjSubgroup_eq_of_isTIIn hTI (Z.mul_mem ha (Z.inv_mem hb)) (by rwa [inf_comm] at hne)

theorem isTI_subgroupOf_of_isTIIn {T Z : Subgroup G} (Y : Subgroup G) (hYZ : Y ≤ Z)
    (hT : IsTIIn Z T) [Finite G] : IsTI (T.subgroupOf Y) := by
  intro y
  rw [conjSubgroup_subgroupOf]
  rcases hT (y : G) (hYZ y.2) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have : (x : G) ∈ T ⊓ conjSubgroup (y : G) T :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_subgroupOf.mp h2⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · right
    ext x
    constructor
    · exact fun hx => (Subgroup.mem_inf.mp hx).1
    · intro hx
      refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_subgroupOf.mpr ?_⟩
      have h1 : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
      have : (x : G) ∈ T ⊓ conjSubgroup (y : G) T := by
        rw [h]
        exact h1
      exact (Subgroup.mem_inf.mp this).2

theorem card_subgroupOf_of_le {A Y : Subgroup G} (h : A ≤ Y) :
    Nat.card (A.subgroupOf Y) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

end Transport

variable {G : Type} [Group G] [Finite G]

theorem prop18Setup_of_ambient {R : Subgroup G} {g : G} {Z : Subgroup G} (hgZ : g ∈ Z) (hRZ : R ≤ Z)
    (hR2 : IsPGroup 2 R) (hTI : IsTIIn Z R)
    {T C N : Subgroup G}
    (hT : T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hinf : R ⊓ conjSubgroup g R = ⊥)
    (hC : C = R ⊓ Subgroup.centralizer (T : Set G))
    (hΦ₁ : ∀ x ∈ R, x * x ∈ C) (hΦ₂ : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C)
    (hCZ : ∀ c ∈ C, ∀ x ∈ R, c * x = x * c)
    (hCT : Nonempty (↥C ≃* ↥T)) (hT2 : ∀ x ∈ T, x * x = 1) (hCR : C ≠ R)
    (hN : N = C ⊔ T) (hNnorm : R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G))
    (hΦb₁ : ∀ x ∈ conjSubgroup g R, x * x ∈ T)
    (hΦb₂ : ∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T)
    (hTZ : ∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) :
    Prop18Setup (R.subgroupOf (R ⊔ conjSubgroup g R))
      ((conjSubgroup g R).subgroupOf (R ⊔ conjSubgroup g R))
      (C.subgroupOf (R ⊔ conjSubgroup g R)) (T.subgroupOf (R ⊔ conjSubgroup g R))
      (N.subgroupOf (R ⊔ conjSubgroup g R)) := by
  classical
  set Rb := conjSubgroup g R with hRb
  set Y := R ⊔ Rb with hY
  have hRY : R ≤ Y := le_sup_left
  have hRbY : Rb ≤ Y := le_sup_right
  have hRb2 : IsPGroup 2 Rb := hR2.map (MulAut.conj g).toMonoidHom
  have hRbZ : Rb ≤ Z := by
    rintro x ⟨r, hr, rfl⟩
    exact Z.mul_mem (Z.mul_mem hgZ (hRZ hr)) (Z.inv_mem hgZ)
  have hYZ : Y ≤ Z := sup_le hRZ hRbZ
  have hTIb : IsTIIn Z Rb := isTIIn_conj hTI hgZ
  have hTRb : T ≤ Rb := hT ▸ inf_le_left
  have hTNR : ∀ t ∈ T, t ∈ Subgroup.normalizer (R : Set G) := fun t ht =>
    (Subgroup.mem_inf.mp (hT ▸ ht)).2
  have hCR' : C ≤ R := hC ▸ inf_le_left
  obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t ∈ T, t ≠ 1 := by
    obtain ⟨⟨t, ht⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT0
    exact ⟨t, ht, fun h => h1 (Subtype.ext h)⟩
  have hCL : C = R ⊓ Subgroup.normalizer (Rb : Set G) := by
    refine le_antisymm (fun c hc => ?_) (fun c hc => ?_)
    · have hc' := hC ▸ hc
      obtain ⟨hcR, hcZ⟩ := Subgroup.mem_inf.mp hc'
      have hct : c * t₀ = t₀ * c :=
        (Subgroup.mem_centralizer_iff.mp hcZ t₀ ht₀).symm
      exact Subgroup.mem_inf.mpr ⟨hcR, mem_normalizer_of_commute_of_isTIIn hTIb (hRZ hcR)
        (hTRb ht₀) ht₀1 hct⟩
    · obtain ⟨hcR, hcN⟩ := Subgroup.mem_inf.mp hc
      rw [hC]
      refine Subgroup.mem_inf.mpr ⟨hcR, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have h1 : c * t * c⁻¹ * t⁻¹ ∈ Rb := by
        have := (Subgroup.mem_normalizer_iff.mp hcN t).mp (hTRb ht)
        exact Rb.mul_mem this (Rb.inv_mem (hTRb ht))
      have h2 : c * t * c⁻¹ * t⁻¹ ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp (hTNR t ht) c⁻¹).mp (R.inv_mem hcR)
        rw [show c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) by group]
        exact R.mul_mem hcR this
      have h3 : c * t * c⁻¹ * t⁻¹ ∈ R ⊓ Rb := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hinf, Subgroup.mem_bot] at h3
      calc t * c = c * t * c⁻¹ * t⁻¹ * (t * c) := by rw [h3, one_mul]
        _ = c * t := by group
  obtain ⟨e⟩ := hCT
  have hC2 : ∀ x ∈ C, x * x = 1 := fun x hx => by
    have h1 : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := Subtype.ext (hT2 _ (e ⟨x, hx⟩).2)
    have h2 : e (⟨x, hx⟩ * ⟨x, hx⟩) = e 1 := by rw [map_mul, h1, map_one]
    have := congrArg Subtype.val (e.injective h2)
    simpa using this
  have hCT' : ∀ c ∈ C, ∀ t ∈ T, c * t = t * c := fun c hc t ht => by
    have := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hC ▸ hc)).2 t ht)
    exact this.symm
  have hNY : N ≤ Y := hN ▸ sup_le (hCR'.trans hRY) (hTRb.trans hRbY)
  have hCY : C ≤ Y := hCR'.trans hRY
  have hTY : T ≤ Y := hTRb.trans hRbY
  have hN2 : ∀ x ∈ N, x * x = 1 := by
    intro x hx
    rw [hN] at hx
    obtain ⟨c, hc, t, ht, rfl⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup
      (CFSG.RankThree.GF2n.le_normalizer_of_comm (X := T) (N := C)
        fun t ht c hc => (hCT' c hc t ht).symm) hx
    have h1 := hC2 c hc
    have h2 := hT2 t ht
    calc c * t * (c * t) = c * (t * c) * t := by group
      _ = c * (c * t) * t := by rw [(hCT' c hc t ht).symm]
      _ = (c * c) * (t * t) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  refine
    { gen := ?_, two := ?_, twob := ?_, ti := ?_, tib := ?_, mixed := ?_, card_RRb := ?_,
      hL := ?_, hLb := ?_, hN := ?_, normal := ?_, sq_N := ?_, L_cent := ?_, Lb_cent := ?_,
      sq_R := ?_, comm_R := ?_, sq_Rb := ?_, comm_Rb := ?_, card_eq := ?_, ne_bot := ?_,
      ne := ?_ }
  · rw [← Subgroup.subgroupOf_sup hRY hRbY, hY, Subgroup.subgroupOf_self]
  · exact hR2.comap_of_injective Y.subtype Subtype.coe_injective
  · exact hRb2.comap_of_injective Y.subtype Subtype.coe_injective
  · exact isTI_subgroupOf_of_isTIIn Y hYZ hTI
  · exact isTI_subgroupOf_of_isTIIn Y hYZ hTIb
  · intro x y hne
    rw [conjSubgroup_subgroupOf, conjSubgroup_subgroupOf] at hne ⊢
    have hne' : conjSubgroup (x : G) R ⊓ conjSubgroup (y : G) Rb ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hu
      have : (u : G) ∈ conjSubgroup (x : G) R ⊓ conjSubgroup (y : G) Rb :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_subgroupOf.mp h2⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    have hyb : conjSubgroup (y : G) Rb = conjSubgroup ((y : G) * g) R := by
      rw [hRb, conjSubgroup_mul]
    rw [hyb] at hne'
    have := conjSubgroup_eq_of_inf_ne_botIn hTI (hYZ x.2) (Z.mul_mem (hYZ y.2) hgZ) hne'
    rw [hyb, this]
  · rw [card_subgroupOf_of_le hRbY, card_subgroupOf_of_le hRY, hRb,
      CFSG.RankThree.GF2n.card_conjSubgroup]
  · rw [hCL]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      ← Subgroup.subgroupOf_normalizer_eq hRbY, Subgroup.mem_subgroupOf]
  · rw [hT]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      ← Subgroup.subgroupOf_normalizer_eq hRY, Subgroup.mem_subgroupOf]
  · rw [hN, Subgroup.subgroupOf_sup hCY hTY]
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hNnorm
  · intro x hx
    exact Subtype.ext (hN2 _ (Subgroup.mem_subgroupOf.mp hx))
  · intro l hl x hx
    exact Subtype.ext (hCZ _ (Subgroup.mem_subgroupOf.mp hl) _ (Subgroup.mem_subgroupOf.mp hx))
  · intro l hl x hx
    exact Subtype.ext (hTZ _ (Subgroup.mem_subgroupOf.mp hl) _ (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hΦ₁ _ (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx y hy
    exact Subgroup.mem_subgroupOf.mpr
      (hΦ₂ _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hΦb₁ _ (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx y hy
    exact Subgroup.mem_subgroupOf.mpr
      (hΦb₂ _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  · rw [card_subgroupOf_of_le hTY, card_subgroupOf_of_le hCY]
    exact (Nat.card_congr e.toEquiv).symm
  · intro hbot
    apply hT0
    have hC1 : ∀ x ∈ C, x = 1 := fun x hx => by
      have : (⟨x, hCY hx⟩ : Y) ∈ C.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hCbot : C = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hC1
    have h1 : Nat.card C = 1 := by rw [hCbot]; exact Subgroup.card_bot
    have h2 : Nat.card T = 1 := by rw [← Nat.card_congr e.toEquiv]; exact h1
    exact Subgroup.eq_bot_of_card_eq T h2
  · intro h
    apply hCR
    refine le_antisymm hCR' fun x hx => ?_
    have : (⟨x, hRY hx⟩ : Y) ∈ C.subgroupOf Y := h ▸ Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp this

def Lemma18SzAbelian : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R Rb L Lb N : Subgroup X), Prop18Setup R Rb L Lb N →
    ∀ [N.Normal], (∃ a : ℕ, 1 ≤ a ∧ L.relIndex R = 2 ^ (2 * a + 1) ∧
      Nonempty (X ⧸ N ≃* Sz a)) → ∀ a ∈ R, ∀ b ∈ R, a * b = b * a

theorem lemma18_abelian
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) (hSz : Lemma18SzAbelian)
    {R : Subgroup G} {g : G} {Z : Subgroup G} (hgZ : g ∈ Z) (hRZ : R ≤ Z)
    (hR2 : IsPGroup 2 R) (hTI : IsTIIn Z R)
    {T C N : Subgroup G}
    (hT : T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hinf : R ⊓ conjSubgroup g R = ⊥)
    (hC : C = R ⊓ Subgroup.centralizer (T : Set G))
    (hΦ₁ : ∀ x ∈ R, x * x ∈ C) (hΦ₂ : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C)
    (hCZ : ∀ c ∈ C, ∀ x ∈ R, c * x = x * c)
    (hCT : Nonempty (↥C ≃* ↥T)) (hT2 : ∀ x ∈ T, x * x = 1) (hCR : C ≠ R)
    (hN : N = C ⊔ T) (hNnorm : R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G))
    (hΦb₁ : ∀ x ∈ conjSubgroup g R, x * x ∈ T)
    (hΦb₂ : ∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T)
    (hTZ : ∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have S := prop18Setup_of_ambient hgZ hRZ hR2 hTI hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR hN
    hNnorm hΦb₁
    hΦb₂ hTZ
  have := S.normal
  intro a ha b hb
  have := S.abelian_of_models hCen hU
    (fun hsz => hSz _ _ _ _ _ _ S hsz) ⟨a, Subgroup.mem_sup_left ha⟩ ha
    ⟨b, Subgroup.mem_sup_left hb⟩ hb
  exact congrArg Subtype.val this

omit [Finite G] in
theorem relIndex_subgroupOf_of_le {A B Y : Subgroup G} (hA : A ≤ B) (hB : B ≤ Y) [Finite G] :
    (A.subgroupOf Y).relIndex (B.subgroupOf Y) = A.relIndex B := by
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf Y) (K := B.subgroupOf Y)
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  have hle : A.subgroupOf Y ≤ B.subgroupOf Y := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hA (Subgroup.mem_subgroupOf.mp hx))
  rw [inf_of_le_left hle, card_subgroupOf_of_le (hA.trans hB)] at h1
  rw [inf_of_le_left hA] at h2
  rw [card_subgroupOf_of_le hB] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem lemma18_abelian_eq
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {R : Subgroup G} {g : G} {Z : Subgroup G} (hgZ : g ∈ Z) (hRZ : R ≤ Z)
    (hR2 : IsPGroup 2 R) (hTI : IsTIIn Z R)
    {T C N : Subgroup G}
    (hT : T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hinf : R ⊓ conjSubgroup g R = ⊥)
    (hC : C = R ⊓ Subgroup.centralizer (T : Set G))
    (hΦ₁ : ∀ x ∈ R, x * x ∈ C) (hΦ₂ : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C)
    (hCZ : ∀ c ∈ C, ∀ x ∈ R, c * x = x * c)
    (hCT : Nonempty (↥C ≃* ↥T)) (hT2 : ∀ x ∈ T, x * x = 1) (hCR : C ≠ R)
    (he : C.relIndex R = Nat.card T)
    (hN : N = C ⊔ T) (hNnorm : R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G))
    (hΦb₁ : ∀ x ∈ conjSubgroup g R, x * x ∈ T)
    (hΦb₂ : ∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T)
    (hTZ : ∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have S := prop18Setup_of_ambient hgZ hRZ hR2 hTI hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR hN
    hNnorm hΦb₁
    hΦb₂ hTZ
  have := S.normal
  have hCR' : C ≤ R := hC ▸ inf_le_left
  have hTRb : T ≤ conjSubgroup g R := hT ▸ inf_le_left
  have hrel : (C.subgroupOf (R ⊔ conjSubgroup g R)).relIndex (R.subgroupOf (R ⊔ conjSubgroup g R))
      = Nat.card (T.subgroupOf (R ⊔ conjSubgroup g R)) := by
    rw [relIndex_subgroupOf_of_le hCR' le_sup_left, card_subgroupOf_of_le (hTRb.trans le_sup_right)]
    exact he
  intro a ha b hb
  have := S.abelian_of_models hCen hU
    (fun ⟨a', ha', h2, ⟨e⟩⟩ => (S.false_of_sz ha' e (by rw [← hrel]; exact h2)).elim)
    ⟨a, Subgroup.mem_sup_left ha⟩ ha ⟨b, Subgroup.mem_sup_left hb⟩ hb
  exact congrArg Subtype.val this

end CFSG.CGT.PushingUpLit.SolKNA
