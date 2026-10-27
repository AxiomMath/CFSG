module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveAlpha

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj_iff {Q : Subgroup G} {h y : G} :
    y ∈ Q.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * y * h ∈ Q := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hq
  · intro hy
    exact ⟨h⁻¹ * y * h, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem isSylowOf_of_sylow_le {M : Subgroup G} (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M) :
    IsSylowOf 2 S M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsSylowOf 2 (S : Subgroup G) ⊤ :=
    isSylowOf_of_card le_top (by rw [card_top]; exact S.card_eq_multiplicity)
  exact h1.of_le hSM le_top

theorem exists_conj_sylow_of_isConj (S : Sylow 2 G) {z : G}
    (hzS : ∀ y ∈ (S : Subgroup G), z * y = y * z) {x : G} (hzx : IsConj z x) :
    ∃ k : G, k * z * k⁻¹ = x ∧
      ∀ y ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G), k⁻¹ * y * k ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcx⟩ := isConj_iff.mp hzx
  have hS'C : (S : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ centralizer ({x} : Set G) := by
    intro y hy
    rw [mem_map_conj_iff] at hy
    rw [mem_centralizer_singleton_iff, ← hcx]
    have e := hzS _ hy
    calc y * (c * z * c⁻¹) = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [e]
      _ = c * z * c⁻¹ * y := by group
  have hS'syl : IsSylowOf 2 ((S : Subgroup G).map (MulAut.conj c).toMonoidHom)
      (centralizer ({x} : Set G)) :=
    isSylowOf_of_sylow_le (c • S) (by rw [Sylow.coe_subgroup_smul]; exact hS'C)
  obtain ⟨T₀, hT₀, hCT₀⟩ := exists_isSylowOf_le
    (inf_le_right : (S : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ _)
    (S.isPGroup'.to_le inf_le_left)
  obtain ⟨d, hd, hT₀d⟩ := Lemma22.exists_conj_eq_of_isSylowOf hS'syl hT₀
  obtain ⟨k, hk⟩ : ∃ k : G, d * c = k := ⟨_, rfl⟩
  have hmemT : ∀ y, y ∈ T₀ ↔ k⁻¹ * y * k ∈ (S : Subgroup G) := by
    intro y
    rw [hT₀d]
    change y ∈ ((S : Subgroup G).map (MulAut.conj c).toMonoidHom).map
      (MulAut.conj d).toMonoidHom ↔ _
    rw [mem_map_conj_iff, mem_map_conj_iff, ← hk]
    rw [show c⁻¹ * (d⁻¹ * y * d) * c = (d * c)⁻¹ * y * (d * c) by group]
  have hxk : k * z * k⁻¹ = x := by
    rw [mem_centralizer_singleton_iff] at hd
    rw [← hk]
    calc d * c * z * (d * c)⁻¹ = d * (c * z * c⁻¹) * d⁻¹ := by group
      _ = d * x * d⁻¹ := by rw [hcx]
      _ = x := by rw [hd]; group
  exact ⟨k, hxk, fun y hy => (hmemT y).mp (hCT₀ hy)⟩

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem mem_V₀_of_isConj (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1)
    {t : G} (ht : t ∈ P) (ht2 : t * t = 1) (hzt : IsConj z t) : t ∈ V₀ := by
  obtain ⟨S, hPS⟩ := hP.isPGroup.exists_le_sylow
  obtain ⟨-, -, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hPS' : P < S := lt_of_le_of_ne hPS (h.P_not_sylow hP hPC hGold hGs hIIa hP64 hVP S).symm
  obtain ⟨s₀, hs₀, hs₀P⟩ := IsConcreteLE.exists_of_lt hPS'
  obtain ⟨hVs, hV's⟩ := hswap s₀ hs₀ hs₀P
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  by_cases htV : t ∈ R ⊔ T
  · by_contra ht0
    exact h.not_isConj_of_mem_V₀ hz hz1 htV ht0 hzt
  · exfalso
    have htV' := hV'inv t ht ht2 htV
    have h1 : s₀ * t * s₀⁻¹ ∈ R ⊔ T := by
      rw [← hVs] at htV'
      exact (mem_rightConjugate_iff _ _ _).mp htV'
    have h2 : s₀ * t * s₀⁻¹ ∉ V₀ := by
      intro h0
      apply htV
      rw [← hV's, mem_rightConjugate_iff]
      exact hV₀V' h0
    exact h.not_isConj_of_mem_V₀ hz hz1 h1 h2 (hzt.trans (isConj_iff.mpr ⟨s₀, rfl⟩))

theorem exists_conj_inf_of_tau (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    (hτ : ∀ s ∈ (S : Subgroup G), ∀ w ∈ V₀, s * w = w * s)
    {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) {x : G} (hxS : x ∈ (S : Subgroup G)) {k : G}
    (hCk : ∀ y ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G), k⁻¹ * y * k ∈ (S : Subgroup G)) :
    ∃ v ∈ V₀, v ≠ 1 ∧ k⁻¹ * v * k ∈ V₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPz : ∀ t ∈ P, t * t = 1 → IsConj z t → t ∈ V₀ := fun t ht ht2 hzt =>
    h.mem_V₀_of_isConj hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv hz hz1
      ht ht2 hzt
  obtain ⟨-, hS128, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε
    hV'P hV'e hV'16 hinf hsup hV'inv S hPS
  have hrelPS : P.relIndex S = 2 := by
    have h1 := Subgroup.relIndex_mul_card P S
    rw [inf_eq_left.mpr hPS, hS128, hP64] at h1
    omega
  set T₀ := (S : Subgroup G).map (MulAut.conj k).toMonoidHom with hT₀def
  have hmemT : ∀ y, y ∈ T₀ ↔ k⁻¹ * y * k ∈ (S : Subgroup G) := fun y => mem_map_conj_iff
  have hCT₀ : (S : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ T₀ := fun y hy =>
    (hmemT y).mpr (hCk y hy)
  have hrelk : (P.map (MulAut.conj k).toMonoidHom).relIndex T₀ = 2 := by
    rw [hT₀def, relIndex_map_map_of_injective _ _ (MulAut.conj k).injective, hrelPS]
  have hΩk : ∀ y ∈ P.map (MulAut.conj k).toMonoidHom, y * y = 1 → IsConj z y →
      k⁻¹ * y * k ∈ V₀ := by
    intro y hy hy2 hzy
    rw [mem_map_conj_iff] at hy
    refine hPz _ hy ?_ (hzy.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩))
    calc k⁻¹ * y * k * (k⁻¹ * y * k) = k⁻¹ * (y * y) * k := by group
      _ = 1 := by rw [hy2]; group
  have hNA := h.normalizer_le_sup_of_eps_one hP hε
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hcls : ∀ y : G, y ^ 2 = 1 → y ≠ 1 → IsConj z y ∨ IsConj r₀ y := fun y hy2 hy1 =>
    h.isConj_or_isConj hIIa hP hPC hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv hz hz1
      hr₀ hr₀1 hy2 hy1
  set W := V₀.map (MulAut.conj k).toMonoidHom with hW
  have hV₀S : V₀ ≤ (S : Subgroup G) := (h.V₀_le.trans hVP).trans hPS
  have hV₀T : V₀ ≤ T₀ := fun w hw => hCT₀ (mem_inf.mpr ⟨hV₀S hw,
    mem_centralizer_singleton_iff.mpr (hτ x hxS w hw).symm⟩)
  have hWcomm : ∀ w ∈ W, ∀ y ∈ T₀, w * y = y * w := by
    intro w hw y hy
    rw [mem_map_conj_iff] at hw
    have e := hτ _ ((hmemT y).mp hy) _ hw
    calc w * y = k * ((k⁻¹ * w * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * (k⁻¹ * w * k)) * k⁻¹ := by rw [e]
      _ = y * w := by group
  have hWN : V₀ ≤ normalizer (W : Set G) := fun v hv =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => hWcomm w hw v (hV₀T hv))
  have hcard := card_sup_mul_card_inf_of_le hWN
  rw [card_map_of_injective (MulAut.conj k).injective, h.card_V₀] at hcard
  have hET : V₀ ⊔ W ≤ T₀ :=
    sup_le hV₀T fun w hw => (hmemT w).mpr (hV₀S ((mem_map_conj_iff).mp hw))
  have hEP : P.map (MulAut.conj k).toMonoidHom ⊓ (V₀ ⊔ W) ≤ W := by
    intro e he
    obtain ⟨heP, heE⟩ := mem_inf.mp he
    have he' : e ∈ ((V₀ ⊔ W : Subgroup G) : Set G) := heE
    rw [coe_mul_of_left_le_normalizer_right _ _ hWN] at he'
    obtain ⟨v, hv, w, hw, hew⟩ := he'
    have hew' : v * w = e := hew
    subst hew'
    have hvw : v * w = w * v :=
      (hWcomm w hw v (hV₀T hv)).symm
    have hw' := (mem_map_conj_iff).mp hw
    have hv2 : v * v = 1 := h.mul_self (h.V₀_le hv)
    have hw2 : w * w = 1 := by
      have := h.mul_self (h.V₀_le hw')
      calc w * w = k * ((k⁻¹ * w * k) * (k⁻¹ * w * k)) * k⁻¹ := by group
        _ = 1 := by rw [this]; group
    by_cases hvw1 : v * w = 1
    · rw [hvw1]; exact one_mem _
    rw [mem_map_conj_iff]
    apply hΩk _ heP
    · calc v * w * (v * w) = v * (w * v) * w := by group
        _ = v * (v * w) * w := by rw [hvw]
        _ = (v * v) * (w * w) := by group
        _ = 1 := by rw [hv2, hw2, one_mul]
    · by_cases hv1 : v = 1
      · rw [hv1, one_mul]
        have hw1 : w ≠ 1 := fun he => hvw1 (by rw [hv1, he, one_mul])
        have hw'1 : k⁻¹ * w * k ≠ 1 := fun he => hw1 (by
          calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
            _ = 1 := by rw [he]; group)
        exact (h.isConj_of_mem_V₀ hz hz1 hw' hw'1).trans (isConj_iff.mpr ⟨k, by group⟩)
      by_cases hw1 : w = 1
      · rw [hw1, mul_one]
        exact h.isConj_of_mem_V₀ hz hz1 hv hv1
      have hw'1 : k⁻¹ * w * k ≠ 1 := fun he => hw1 (by
        calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
          _ = 1 := by rw [he]; group)
      have hzv := h.isConj_of_mem_V₀ hz hz1 hv hv1
      have hzw : IsConj z w := (h.isConj_of_mem_V₀ hz hz1 hw' hw'1).trans
        (isConj_iff.mpr ⟨k, by group⟩)
      have hne : v ≠ w := fun he => hvw1 (by rw [he, hw2])
      exact h.isConj_mul_of_commute hNA hz hz1 hr₀ hcls hzv hzw hvw hne
  have hEcard : Nat.card (V₀ ⊔ W : Subgroup G) ≤ 8 := by
    have h1 := Subgroup.relIndex_mul_card (P.map (MulAut.conj k).toMonoidHom) (V₀ ⊔ W)
    have h2 : (P.map (MulAut.conj k).toMonoidHom).relIndex (V₀ ⊔ W) ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := P.map (MulAut.conj k).toMonoidHom) hET
        (by rw [hrelk]; norm_num)
      rwa [hrelk] at this
    have h3 := Subgroup.card_le_of_le hEP
    rw [card_map_of_injective (MulAut.conj k).injective, h.card_V₀] at h3
    calc Nat.card (V₀ ⊔ W : Subgroup G) =
        (P.map (MulAut.conj k).toMonoidHom).relIndex (V₀ ⊔ W) *
          Nat.card (P.map (MulAut.conj k).toMonoidHom ⊓ (V₀ ⊔ W) : Subgroup G) := h1.symm
      _ ≤ 2 * 4 := Nat.mul_le_mul h2 h3
  have hinf1 : V₀ ⊓ W ≠ ⊥ := by
    intro h0
    rw [h0, card_bot, mul_one] at hcard
    omega
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf1
  obtain ⟨hvV₀, hvW⟩ := mem_inf.mp v.2
  exact ⟨v, hvV₀, fun he => hv1 (Subtype.ext he), (mem_map_conj_iff).mp hvW⟩


theorem conj_mem_V₀_of_not_tau (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    (hτ : ∃ s ∈ (S : Subgroup G), ∃ w ∈ V₀, s * w ≠ w * s)
    {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) (hzS : ∀ y ∈ (S : Subgroup G), z * y = y * z)
    {x : G} (hxS : x ∈ (S : Subgroup G)) (hxP : x ∉ P) (hx2 : x * x = 1) {k : G}
    (hCk : ∀ y ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G), k⁻¹ * y * k ∈ (S : Subgroup G)) :
    k⁻¹ * z * k ∈ V₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPz : ∀ t ∈ P, t * t = 1 → IsConj z t → t ∈ V₀ := fun t ht ht2 hzt =>
    h.mem_V₀_of_isConj hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv hz hz1
      ht ht2 hzt
  obtain ⟨-, hS128, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε
    hV'P hV'e hV'16 hinf hsup hV'inv S hPS
  have hrelPS : P.relIndex S = 2 := by
    have h1 := Subgroup.relIndex_mul_card P S
    rw [inf_eq_left.mpr hPS, hS128, hP64] at h1
    omega
  set T₀ := (S : Subgroup G).map (MulAut.conj k).toMonoidHom with hT₀def
  have hmemT : ∀ y, y ∈ T₀ ↔ k⁻¹ * y * k ∈ (S : Subgroup G) := fun y => mem_map_conj_iff
  have hCT₀ : (S : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ T₀ := fun y hy =>
    (hmemT y).mpr (hCk y hy)
  have hrelk : (P.map (MulAut.conj k).toMonoidHom).relIndex T₀ = 2 := by
    rw [hT₀def, relIndex_map_map_of_injective _ _ (MulAut.conj k).injective, hrelPS]
  have hΩk : ∀ y ∈ P.map (MulAut.conj k).toMonoidHom, y * y = 1 → IsConj z y →
      k⁻¹ * y * k ∈ V₀ := by
    intro y hy hy2 hzy
    rw [mem_map_conj_iff] at hy
    refine hPz _ hy ?_ (hzy.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩))
    calc k⁻¹ * y * k * (k⁻¹ * y * k) = k⁻¹ * (y * y) * k := by group
      _ = 1 := by rw [hy2]; group
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hz2 : z * z = 1 := h.mul_self (h.V₀_le hz)
  obtain ⟨s, hs, w₀, hw₀, hsw₀⟩ := hτ
  have hsP : s ∉ P := fun hsP => hsw₀ (P_comm_V₀ hP hw₀ hsP)
  have hxs : x⁻¹ * s ∈ P :=
    CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hrelPS hxS hs hxP hsP
  have hxinv : x⁻¹ = x := by
    calc x⁻¹ = x⁻¹ * (x * x) := by rw [hx2, mul_one]
      _ = x := by group
  have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  obtain ⟨hVx, hV'x⟩ := hswap x hxS hxP
  have hxV : ∀ y ∈ R ⊔ T, x * y * x⁻¹ ∈ V' := fun y hy => by
    rw [← hV'x] at hy
    exact (mem_rightConjugate_iff _ _ _).mp hy
  have hxV' : ∀ y ∈ V', x * y * x⁻¹ ∈ R ⊔ T := fun y hy => by
    rw [← hVx] at hy
    exact (mem_rightConjugate_iff _ _ _).mp hy
  have hxV₀ : ∀ w ∈ V₀, x * w * x⁻¹ ∈ V₀ := fun w hw =>
    hinf ▸ mem_inf.mpr ⟨hxV' w (hV₀V' hw), hxV w (h.V₀_le hw)⟩
  have hxw₀ : x * w₀ * x⁻¹ ≠ w₀ := by
    intro he
    apply hsw₀
    have hp := P_comm_V₀ hP hw₀ hxs
    calc s * w₀ = x * ((x⁻¹ * s) * w₀) := by group
      _ = x * (w₀ * (x⁻¹ * s)) := by rw [hp]
      _ = (x * w₀ * x⁻¹) * s := by group
      _ = w₀ * s := by rw [he]
  have hzfix : x * z * x⁻¹ = z := by rw [← hzS x hxS]; group
  have hfix : ∀ w ∈ V₀, w ≠ 1 → x * w * x⁻¹ = w → w = z := by
    intro w hw hw1 hwx
    by_contra hwz
    apply hxw₀
    rcases mem_four h.card_V₀ hV₀2 hz hw hz1 hw1 (Ne.symm hwz) hw₀ with e | e | e | e
    · rw [e]; group
    · rw [e, hzfix]
    · rw [e, hwx]
    · rw [e, show x * (z * w) * x⁻¹ = (x * z * x⁻¹) * (x * w * x⁻¹) by group, hzfix, hwx]
  have hmove : ∀ w ∈ V₀, w ≠ 1 → w ≠ z → x * w * x⁻¹ = z * w := by
    intro w hw hw1 hwz
    have hxw1 : x * w * x⁻¹ ≠ 1 := fun he => hw1 (by
      calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
        _ = 1 := by rw [he]; group)
    rcases mem_four h.card_V₀ hV₀2 hz hw hz1 hw1 (Ne.symm hwz) (hxV₀ w hw) with e | e | e | e
    · exact absurd e hxw1
    · exfalso
      apply hwz
      calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
        _ = x⁻¹ * z * x := by rw [e]
        _ = z := by rw [show x⁻¹ * z * x = x * z * x⁻¹ by rw [hxinv]]; exact hzfix
    · exact absurd (hfix w hw hw1 e) hwz
    · exact e
  have hr₀V : r₀ ∈ R ⊔ T := mem_sup_left hr₀
  have hr₀V₀ : r₀ ∉ V₀ := fun h0 => hr₀1 (by
    have h1 : r₀ ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr₀, h0⟩
    rwa [h.inf_R_V₀, mem_bot] at h1)
  obtain ⟨v', hv'⟩ : ∃ v' : G, x * r₀ * x⁻¹ = v' := ⟨_, rfl⟩
  have hv'V' : v' ∈ V' := hv' ▸ hxV r₀ hr₀V
  have hv'P : v' ∈ P := hV'P hv'V'
  have hv'V : v' ∉ R ⊔ T := by
    intro hv'V
    apply hr₀V₀
    have h1 : v' ∈ V₀ := hinf ▸ mem_inf.mpr ⟨hv'V, hv'V'⟩
    have h2 := hxV₀ v' h1
    rwa [← hv', show x * (x * r₀ * x⁻¹) * x⁻¹ = (x * x) * r₀ * (x * x)⁻¹ by group, hx2,
      one_mul, inv_one, mul_one] at h2
  have hxv' : x * v' * x⁻¹ = r₀ := by
    rw [← hv', show x * (x * r₀ * x⁻¹) * x⁻¹ = (x * x) * r₀ * (x * x)⁻¹ by group, hx2,
      one_mul, inv_one, mul_one]
  obtain ⟨c, hc⟩ : ∃ c : G, v'⁻¹ * r₀⁻¹ * v' * r₀ = c := ⟨_, rfl⟩
  have hc0 : c ∈ V₀ := by
    have := h.P_comm_mem_V₀ hP hPC hIIa (inv_mem hv'P) (inv_mem (hVP hr₀V))
    rwa [inv_inv, inv_inv, hc] at this
  have hc1 : c ≠ 1 := by
    intro he
    apply hr₀V₀
    refine h.P_fixed hP hPC hv'P hv'V hr₀V ?_
    have e1 : v'⁻¹ * r₀⁻¹ * v' * r₀ = 1 := hc.trans he
    have e2 : v' * r₀ = r₀ * v' := by
      calc v' * r₀ = r₀ * v' * (v'⁻¹ * r₀⁻¹ * v' * r₀) := by group
        _ = r₀ * v' := by rw [e1, mul_one]
    rw [e2]
    group
  have hcc : c * c = 1 := hV₀2 c hc0
  have hcfix : x * c * x⁻¹ = c := by
    calc x * c * x⁻¹ = x * (v'⁻¹ * r₀⁻¹ * v' * r₀) * x⁻¹ := by rw [hc]
      _ = (x * v' * x⁻¹)⁻¹ * (x * r₀ * x⁻¹)⁻¹ * (x * v' * x⁻¹) * (x * r₀ * x⁻¹) := by group
      _ = r₀⁻¹ * v'⁻¹ * r₀ * v' := by rw [hxv', hv']
      _ = (v'⁻¹ * r₀⁻¹ * v' * r₀)⁻¹ := by group
      _ = c⁻¹ := by rw [hc]
      _ = c := inv_eq_of_mul_eq_one_right hcc
  have hcz : c = z := hfix c hc0 hc1 hcfix
  obtain ⟨w, hw, hw1, hwz⟩ := exists_ne_one_ne h.card_V₀ hV₀2 hz
  have hxw := hmove w hw hw1 hwz
  obtain ⟨u, hu⟩ : ∃ u : G, r₀ * v' * w = u := ⟨_, rfl⟩
  have huP : u ∈ P := hu ▸ mul_mem (mul_mem (hVP hr₀V) hv'P) (hVP (h.V₀_le hw))
  have hzw : z * w = w * z := h.comm (h.V₀_le hz) (h.V₀_le hw)
  have hv'r : v' * r₀ = r₀ * v' * c := by rw [← hc]; group
  have hux : x * u * x⁻¹ = u := by
    rw [← hu]
    calc x * (r₀ * v' * w) * x⁻¹ = (x * r₀ * x⁻¹) * (x * v' * x⁻¹) * (x * w * x⁻¹) := by
          group
      _ = v' * r₀ * (z * w) := by rw [hv', hxv', hxw]
      _ = r₀ * v' * c * (z * w) := by rw [hv'r]
      _ = r₀ * v' * (z * (z * w)) := by rw [hcz]; group
      _ = r₀ * v' * w := by rw [← mul_assoc z z w, hz2, one_mul]
  have huV : u ∉ R ⊔ T := by
    intro huV
    apply hv'V
    have := mul_mem (mul_mem (inv_mem hr₀V) huV) (inv_mem (h.V₀_le hw))
    rwa [← hu, show r₀⁻¹ * (r₀ * v' * w) * w⁻¹ = v' by group] at this
  have hu2 : u * u ≠ 1 := by
    intro hu2
    have huV' := hV'inv u huP hu2 huV
    apply hr₀V₀
    have h1 : r₀ ∈ V' := by
      have := mul_mem (mul_mem huV' (inv_mem (hV₀V' hw))) (inv_mem hv'V')
      rwa [← hu, show r₀ * v' * w * w⁻¹ * v'⁻¹ = r₀ by group] at this
    exact hinf ▸ mem_inf.mpr ⟨hr₀V, h1⟩
  have huz : u * u = z := by
    refine hfix _ (h.P_sq_mem_V₀ hP hPC huP huV) hu2 ?_
    calc x * (u * u) * x⁻¹ = (x * u * x⁻¹) * (x * u * x⁻¹) := by group
      _ = u * u := by rw [hux]
  have huT : u ∈ T₀ := hCT₀ (mem_inf.mpr ⟨hPS huP, by
    rw [mem_centralizer_singleton_iff]
    calc u * x = x * u * x⁻¹ * x := by rw [hux]
      _ = x * u := by group⟩)
  have hzPk : z ∈ P.map (MulAut.conj k).toMonoidHom := by
    rw [← huz]
    by_cases huPk : u ∈ P.map (MulAut.conj k).toMonoidHom
    · exact mul_mem huPk huPk
    · have hu'Pk : u⁻¹ ∉ P.map (MulAut.conj k).toMonoidHom := fun h' => huPk (by
        simpa using inv_mem h')
      have := CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hrelk (inv_mem huT) huT hu'Pk huPk
      rwa [inv_inv] at this
  exact hΩk z hzPk hz2 (IsConj.refl z)

theorem hconn_of_eps_one (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) (hzS : ∀ y ∈ (S : Subgroup G), z * y = y * z) :
    ∀ x ∈ (S : Subgroup G), x ∉ P → x * x = 1 → IsConj z x →
      Relation.EqvGen (CoA A) x z := by
  intro x hxS hxP hx2 hzx
  have hz2 : z * z = 1 := h.mul_self (h.V₀_le hz)
  have hzA : z ∈ A := h.V₀_le_A hz
  have hx1 : x ≠ 1 := fun he => hxP (he ▸ one_mem P)
  obtain ⟨k, hxk, hCk⟩ := exists_conj_sylow_of_isConj S hzS hzx
  have hAk : ∀ y, k⁻¹ * y * k ∈ A → y ∈ rightConjugate A k⁻¹ := fun y hy => by
    rw [mem_rightConjugate_iff, inv_inv]
    exact hy
  have hxA : x ∈ rightConjugate A k⁻¹ :=
    hAk x (by rw [← hxk, show k⁻¹ * (k * z * k⁻¹) * k = z by group]; exact hzA)
  by_cases hτ : ∀ s ∈ (S : Subgroup G), ∀ w ∈ V₀, s * w = w * s
  ·
    obtain ⟨v, hvV₀, hv1, hvk⟩ := h.exists_conj_inf_of_tau hP hPC hIIa hGold hGs hP64 hVP hε
      hV'P hV'e hV'16 hinf hsup hV'inv S hPS hτ hz hz1 hxS hCk
    have hvA : v ∈ rightConjugate A k⁻¹ := hAk _ (h.V₀_le_A hvk)
    have hv2 : v * v = 1 := h.mul_self (h.V₀_le hvV₀)
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _
      ⟨hx2, hx1, hv2, hv1, k⁻¹, hxA, hvA⟩) (Relation.EqvGen.rel _ _
      ⟨hv2, hv1, hz2, hz1, 1, by rw [rightConjugate_one]; exact h.V₀_le_A hvV₀,
        by rw [rightConjugate_one]; exact hzA⟩)
  · push Not at hτ
    have hzk := h.conj_mem_V₀_of_not_tau hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf
      hsup hV'inv S hPS hτ hz hz1 hzS hxS hxP hx2 hCk
    exact Relation.EqvGen.rel _ _ ⟨hx2, hx1, hz2, hz1, k⁻¹, hxA, hAk z (h.V₀_le_A hzk)⟩

theorem oddCoreIn_centralizer_eq_bot_of_eps_one
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) (hzS : ∀ y ∈ (S : Subgroup G), z * y = y * z) :
    oddCoreIn (centralizer ({z} : Set G)) = ⊥ :=
  h.oddCoreIn_centralizer_eq_bot hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup
    hV'inv S hPS hz hz1 hzS
    (h.hconn_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv S hPS
      hz hz1 hzS)

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive

