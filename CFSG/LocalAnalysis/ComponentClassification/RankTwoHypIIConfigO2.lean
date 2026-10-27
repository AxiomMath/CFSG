module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIClassicalConfig
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

namespace CFSG.ComponentClassification.RankTwoHypIIClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.le_oddCore_of_normal
  EvenCatalog.odd_card_oddCore EvenCatalog.oddCore_eq_bot_of_mulEquiv)
open scoped commutatorElement

variable {W : Type*} [Group W]

theorem oddCore_eq_bot_of_normal' {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (h : CFSG.oddCore G = ⊥) : CFSG.oddCore N = ⊥ := by
  have hinv : ∀ φ : MulAut N, (CFSG.oddCore N).map φ.toMonoidHom ≤ CFSG.oddCore N := by
    intro φ
    refine EvenCatalog.le_oddCore_of_normal ?_ ?_
    · exact (CFSG.oddCore_normal (G := N)).map _ φ.surjective
    · rw [card_map_of_injective φ.injective]
      exact EvenCatalog.odd_card_oddCore
  have hn : ((CFSG.oddCore N).map N.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy' : MulAut.conjNormal g y ∈ CFSG.oddCore N :=
      hinv (MulAut.conjNormal g) (Subgroup.mem_map_of_mem _ hy)
    exact Subgroup.mem_map.2 ⟨_, hy', by simp [MulAut.conjNormal_apply]⟩
  have hle := EvenCatalog.le_oddCore_of_normal hn (by
    rw [card_map_of_injective N.subtype_injective]
    exact EvenCatalog.odd_card_oddCore)
  rw [h, le_bot_iff, map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
  exact hle

theorem oUpperTwo_conj_mem {X : Subgroup W} {c : W} (hc : c ∈ X) {y : W}
    (hy : y ∈ oUpperTwo X) : c * y * c⁻¹ ∈ oUpperTwo X := by
  induction hy using closure_induction with
  | mem y hy =>
    refine subset_closure ⟨mul_mem (mul_mem hc hy.1) (inv_mem hc), ?_⟩
    have hsc : SemiconjBy c y (c * y * c⁻¹) := by rw [SemiconjBy, inv_mul_cancel_right]
    rw [← hsc.orderOf_eq]
    exact hy.2
  | one => simp
  | mul a b _ _ ha hb =>
    have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem oUpperTwo_le (X : Subgroup W) : oUpperTwo X ≤ X :=
  (closure_le _).2 fun _ hy => hy.1

theorem map_oUpperTwo_equiv (φ : W ≃* W) (X : Subgroup W) :
    (oUpperTwo X).map φ.toMonoidHom = oUpperTwo (X.map φ.toMonoidHom) := by
  rw [oUpperTwo, oUpperTwo, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] using hodd⟩
  · rintro ⟨⟨x, hx, rfl⟩, hodd⟩
    exact ⟨x, ⟨hx, by simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] using hodd⟩, rfl⟩

section Lift

variable {H : Type*} [Group H]

theorem exists_mem_centralizer_of_odd_orderOf {B : Subgroup H} {t b : H}
    (ht : t ∈ normalizer (B : Set H)) (ht2 : t ^ 2 = 1) (hb : b ∈ B)
    (hz : t * b * t⁻¹ * b⁻¹ ∈ centralizer (B : Set H))
    (hord : Odd (orderOf (t * b * t⁻¹ * b⁻¹))) :
    ∃ b' ∈ B, b' * t = t * b' ∧ b' * b⁻¹ ∈ centralizer (B : Set H) := by
  set z := t * b * t⁻¹ * b⁻¹ with hzdef
  have htb : t * b * t⁻¹ ∈ B := (mem_normalizer_iff.mp ht b).mp hb
  have hzB : z ∈ B := B.mul_mem htb (B.inv_mem hb)
  obtain ⟨j, hj⟩ := hord
  have hinv : t * z * t⁻¹ = z⁻¹ := by
    have htt : t * t = 1 := by rw [← sq, ht2]
    have hzb : t * b * t⁻¹ = z * b := by rw [hzdef]; group
    have : t * (t * b * t⁻¹) * t⁻¹ = b := by
      calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t * t)⁻¹ := by group
        _ = b := by rw [htt]; group
    rw [hzb] at this
    have h3 : t * z * t⁻¹ * (t * b * t⁻¹) = b := by
      calc t * z * t⁻¹ * (t * b * t⁻¹) = t * (z * b) * t⁻¹ := by group
        _ = b := this
    rw [hzb] at h3
    calc t * z * t⁻¹ = t * z * t⁻¹ * (z * b) * b⁻¹ * z⁻¹ := by group
      _ = z⁻¹ := by rw [h3]; group
  refine ⟨z ^ (j + 1) * b, B.mul_mem (B.pow_mem hzB _) hb, ?_, ?_⟩
  · have hpow : t * z ^ (j + 1) * t⁻¹ = (z⁻¹) ^ (j + 1) := by
      rw [← hinv, conj_pow]
    have hzr : z ^ (2 * j + 1) = 1 := by rw [← hj, pow_orderOf_eq_one]
    have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])
    calc z ^ (j + 1) * b * t = t * (t⁻¹ * z ^ (j + 1) * t) * (t⁻¹ * b * t) := by group
      _ = t * (t * z ^ (j + 1) * t⁻¹) * (t * b * t⁻¹) := by rw [htt]
      _ = t * (z⁻¹) ^ (j + 1) * (z * b) := by rw [hpow, show t * b * t⁻¹ = z * b by
            rw [hzdef]; group]
      _ = t * (z ^ (j + 1) * b) := by
          rw [inv_pow]
          have : (z ^ (j + 1))⁻¹ * z = z ^ (j + 1) := by
            rw [inv_mul_eq_iff_eq_mul, ← pow_add, show j + 1 + (j + 1) = 2 * j + 1 + 1 by ring,
              pow_succ, hzr, one_mul]
          calc t * (z ^ (j + 1))⁻¹ * (z * b) = t * ((z ^ (j + 1))⁻¹ * z) * b := by group
            _ = t * (z ^ (j + 1) * b) := by rw [this, mul_assoc]
  · rw [mul_inv_cancel_right]
    exact (centralizer (B : Set H)).pow_mem hz _

theorem commutatorElement_pow_of_central {B : Subgroup H} {t b : H} (hb : b ∈ B)
    (hz : t * b * t⁻¹ * b⁻¹ ∈ centralizer (B : Set H)) (n : ℕ) :
    t * b ^ n * t⁻¹ * (b ^ n)⁻¹ = (t * b * t⁻¹ * b⁻¹) ^ n := by
  set z := t * b * t⁻¹ * b⁻¹ with hzdef
  have hzb : z * b = b * z := (mem_centralizer_iff.mp hz b hb).symm
  induction n with
  | zero => simp
  | succ n ih =>
    have htb : t * b * t⁻¹ = z * b := by rw [hzdef]; group
    have hzbn : z ^ n * b = b * z ^ n := (Commute.pow_left hzb n).eq
    calc t * b ^ (n + 1) * t⁻¹ * (b ^ (n + 1))⁻¹
        = (t * b ^ n * t⁻¹ * (b ^ n)⁻¹) * (b ^ n * (t * b * t⁻¹) * b⁻¹ * (b ^ n)⁻¹) := by group
      _ = z ^ n * (b ^ n * (z * b) * b⁻¹ * (b ^ n)⁻¹) := by rw [ih, htb]
      _ = z ^ (n + 1) := by
          rw [pow_succ]
          have : b ^ n * (z * b) * b⁻¹ * (b ^ n)⁻¹ = z := by
            have hzbn' : z * b ^ n = b ^ n * z := (Commute.pow_right hzb n).eq
            calc b ^ n * (z * b) * b⁻¹ * (b ^ n)⁻¹ = b ^ n * z * (b ^ n)⁻¹ := by group
              _ = z := by rw [← hzbn', mul_inv_cancel_right]
          rw [this]

theorem exists_odd_orderOf_lift {G' : Type*} [Group G'] [Finite H] (ψ : H →* G') (b : H)
    (hodd : Odd (orderOf (ψ b))) : ∃ k : ℕ, Odd (orderOf (b ^ k)) ∧ ψ (b ^ k) = ψ b := by
  have hN : orderOf b ≠ 0 := (orderOf_pos b).ne'
  obtain ⟨e, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd hN
  have hcop : Nat.Coprime (2 ^ e) (orderOf (ψ b)) := Nat.Coprime.pow_left e
    (Nat.coprime_two_left.mpr hodd)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 0 1
  refine ⟨k, ?_, ?_⟩
  ·
    have hdvd : 2 ^ e ∣ k := (Nat.modEq_zero_iff_dvd.mp hk1)
    obtain ⟨l, rfl⟩ := hdvd
    have h1 : (b ^ (2 ^ e * l)) ^ m = 1 := by
      rw [← pow_mul, show 2 ^ e * l * m = 2 ^ e * m * l by ring, pow_mul, ← hNm,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  · rw [map_pow]
    have h1 : (ψ b) ^ k = (ψ b) ^ 1 := (pow_eq_pow_iff_modEq).mpr hk2
    rw [h1, pow_one]

theorem commutatorElement_mul_central {G : Type*} [Group G] {z₁ z₂ b₁ b₂ : G}
    (h11 : Commute z₁ b₁) (h12 : Commute z₁ b₂) (h1z : Commute z₁ z₂) (h21 : Commute z₂ b₁)
    (h22 : Commute z₂ b₂) : ⁅z₁ * b₁, z₂ * b₂⁆ = ⁅b₁, b₂⁆ := by
  have hz1 : Commute z₁ (b₁ * (z₂ * b₂) * b₁⁻¹) :=
    (h11.mul_right (h1z.mul_right h12)).mul_right h11.inv_right
  have hz2 : Commute z₂ (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) :=
    ((h21.mul_right h22).mul_right h21.inv_right).mul_right h22.inv_right
  have hb : b₁ * z₂ = z₂ * b₁ := h21.eq.symm
  rw [commutatorElement_def, commutatorElement_def]
  calc z₁ * b₁ * (z₂ * b₂) * (z₁ * b₁)⁻¹ * (z₂ * b₂)⁻¹
      = z₁ * (b₁ * (z₂ * b₂) * b₁⁻¹) * z₁⁻¹ * (z₂ * b₂)⁻¹ := by group
    _ = (b₁ * (z₂ * b₂) * b₁⁻¹) * (z₂ * b₂)⁻¹ := by rw [hz1.eq, mul_inv_cancel_right]
    _ = (b₁ * z₂) * b₂ * b₁⁻¹ * b₂⁻¹ * z₂⁻¹ := by group
    _ = z₂ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * z₂⁻¹ := by rw [hb]; group
    _ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ := by rw [hz2.eq, mul_inv_cancel_right]

theorem commutatorElement_commute_of_central {B : Subgroup H} {t b₁ b₂ : H}
    (ht : t ∈ normalizer (B : Set H)) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hz₁ : t * b₁ * t⁻¹ * b₁⁻¹ ∈ centralizer (B : Set H))
    (hz₂ : t * b₂ * t⁻¹ * b₂⁻¹ ∈ centralizer (B : Set H)) :
    ⁅b₁, b₂⁆ * t = t * ⁅b₁, b₂⁆ := by
  set z₁ := t * b₁ * t⁻¹ * b₁⁻¹ with hz₁def
  set z₂ := t * b₂ * t⁻¹ * b₂⁻¹ with hz₂def
  have h1 : t * b₁ * t⁻¹ = z₁ * b₁ := by rw [hz₁def]; group
  have h2 : t * b₂ * t⁻¹ = z₂ * b₂ := by rw [hz₂def]; group
  have hz₂B : z₂ ∈ B := B.mul_mem ((mem_normalizer_iff.mp ht b₂).mp hb₂) (B.inv_mem hb₂)
  have key : t * ⁅b₁, b₂⁆ * t⁻¹ = ⁅b₁, b₂⁆ := by
    calc t * ⁅b₁, b₂⁆ * t⁻¹ = ⁅t * b₁ * t⁻¹, t * b₂ * t⁻¹⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅z₁ * b₁, z₂ * b₂⁆ := by rw [h1, h2]
      _ = ⁅b₁, b₂⁆ := commutatorElement_mul_central
          (mem_centralizer_iff.mp hz₁ b₁ hb₁).symm (mem_centralizer_iff.mp hz₁ b₂ hb₂).symm
          (mem_centralizer_iff.mp hz₁ z₂ hz₂B).symm (mem_centralizer_iff.mp hz₂ b₁ hb₁).symm
          (mem_centralizer_iff.mp hz₂ b₂ hb₂).symm
  calc ⁅b₁, b₂⁆ * t = (t * ⁅b₁, b₂⁆ * t⁻¹) * t := by rw [key]
    _ = t * ⁅b₁, b₂⁆ := by group

end Lift

structure HypIIConfigO2 (X E M : Subgroup W) : Prop where
  elemAbelian : IsElemAbelian 2 E
  four_le_card : 4 ≤ Nat.card E
  not_le : ¬ E ≤ X
  sylow : IsSylowOf 2 E M
  twoNilpotent : IsTwoNilpotent M
  le_sup : M ≤ X ⊔ E
  centDer_le : ∀ x ∈ E, x ≠ 1 → centDer X x ≤ normalizer (M : Set W)
  oTwo_le : ∀ x ∈ E, x ≠ 1 →
    oUpperTwo (X ⊓ centralizer ({x} : Set W)) ≤ normalizer (M : Set W)

section Criterion

theorem hypII_of_forall_not_configO2 {X₀ : Type*} [Group X₀] [Finite W] {X : Subgroup W}
    (hW : AutModel X₀ W X) (hc : ∀ E M : Subgroup W, ¬ HypIIConfigO2 X E M)
    {A : Type*} [Group A] (hA : commutator A = ⊤) (e : A ⧸ center A ≃* X₀) : HypII A := by
  intro H _ _ B T ⟨f⟩ hT hXh
  obtain ⟨hTab, hT4, hTN, hTC⟩ := hT
  obtain ⟨Xh, hXle, hTsyl, hnil, htight⟩ := hXh
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : commutator ↥B = ⊤ := by
    have hAp : Group.IsPerfect A := (Group.isPerfect_def).2 hA
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective)
  let eB : ↥B ⧸ center ↥B ≃* X₀ :=
    (QuotientGroup.congr (center ↥B) (center A) f (map_center_eq f)).trans e
  obtain ⟨ψ, hψ⟩ := exists_isActionHom hW hB eB
  have hTX : T ≤ Xh := hTsyl.le
  have hXN : Xh ≤ normalizer (B : Set H) := hXle.trans (sup_le hTN le_normalizer)
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ B, c * t = t * c → c ∈ normalizer (Xh : Set H) := by
    intro t ht ht1 c hc hct
    have hn := mem_normalizer_of_commute_of_tightlyEmbedded htight
      (t := ⟨t, le_sup_left (a := T) (b := B) ht⟩) (c := ⟨c, le_sup_right (a := T) hc⟩)
      (hTX ht) (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext (hTab.2 t ht))
      (Subtype.ext hct)
    rw [mem_normalizer_iff]
    intro x
    by_cases hx : x ∈ T ⊔ B
    · have := (mem_normalizer_iff.mp hn) ⟨x, hx⟩
      simpa [mem_subgroupOf] using this
    · have hcx : c * x * c⁻¹ ∉ T ⊔ B := by
        intro h
        apply hx
        have := (T ⊔ B).mul_mem ((T ⊔ B).mul_mem ((T ⊔ B).inv_mem
          (le_sup_right (a := T) hc)) h) (le_sup_right (a := T) hc)
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd (hXle h) hx, fun h => absurd (hXle h) hcx⟩
  set E := (T.subgroupOf (normalizer (B : Set H))).map ψ with hE
  set M := (Xh.subgroupOf (normalizer (B : Set H))).map ψ with hM
  have hNM : ∀ t ∈ T, t ≠ 1 → ∀ (b' : H) (hb' : b' ∈ B), b' * t = t * b' →
      ψ ⟨b', le_normalizer hb'⟩ ∈ normalizer (M : Set W) := by
    intro t ht ht1 b' hb' hb't
    have hnorm : (⟨b', le_normalizer hb'⟩ : normalizer (B : Set H)) ∈
        normalizer ((Xh.subgroupOf (normalizer (B : Set H)) :
          Subgroup (normalizer (B : Set H))) : Set (normalizer (B : Set H))) := by
      rw [mem_normalizer_iff]
      intro y
      have := mem_normalizer_iff.mp (hQ t ht ht1 b' hb' hb't) (y : H)
      simpa [mem_subgroupOf] using this
    exact le_normalizer_map ψ ⟨_, hnorm, rfl⟩
  have hcen : ∀ (t : normalizer (B : Set H)) (b : H) (hb : b ∈ B),
      ψ ⟨b, le_normalizer hb⟩ * ψ t = ψ t * ψ ⟨b, le_normalizer hb⟩ →
        (t : H) * b * (t : H)⁻¹ * b⁻¹ ∈ centralizer (B : Set H) := by
    intro t b hb hcomm
    have h1 : ψ (t * ⟨b, le_normalizer hb⟩ * t⁻¹ *
        (⟨b, le_normalizer hb⟩ : normalizer (B : Set H))⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    simpa using (hψ.eq_one_iff _).mp h1
  refine hc E M ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [coe_mul]
      exact congrArg Subtype.val (hTab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab.2 _ hx)
      rw [this, map_one]
  ·
    rw [card_map_eq_of_inf_centralizer hψ hTC,
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv]
    exact hT4
  ·
    intro hle
    apply hnot
    intro t ht
    obtain ⟨b, hb, hbt⟩ := hψ.exists_eq _ (hle ⟨⟨t, hTN ht⟩, ht, rfl⟩)
    have h1 : ψ ((⟨b, le_normalizer hb⟩ : normalizer (B : Set H))⁻¹ * ⟨t, hTN ht⟩) = 1 := by
      rw [map_mul, map_inv, hbt, inv_mul_cancel]
    have hC := (hψ.eq_one_iff _).mp h1
    simp only [coe_mul, coe_inv] at hC
    rw [show t = b * (b⁻¹ * t) by group]
    exact mul_mem_sup hb hC
  ·
    have hT' : IsSylowOf 2 (T.subgroupOf (normalizer (B : Set H)))
        (Xh.subgroupOf (normalizer (B : Set H))) := by
      rw [← isSylowOf_map_subtype_iff, subgroupOf_map_subtype, subgroupOf_map_subtype,
        inf_eq_left.mpr hTN, inf_eq_left.mpr hXN]
      exact hTsyl
    exact IsSylowOf.map hT' ψ
  ·
    exact (hnil.subgroupOf hXN).map ψ
  ·
    have hle : Xh.subgroupOf (normalizer (B : Set H)) ≤
        T.subgroupOf (normalizer (B : Set H)) ⊔ B.subgroupOf (normalizer (B : Set H)) := by
      rw [← subgroupOf_sup hTN le_normalizer]
      exact fun x hx => hXle hx
    refine (map_mono hle).trans ?_
    rw [Subgroup.map_sup, sup_comm]
    refine sup_le_sup ?_ le_rfl
    rintro _ ⟨b, hb, rfl⟩
    exact hψ.map_mem (b : H) hb
  ·
    rintro _ ⟨t, ht, rfl⟩ hx1
    have ht1 : (t : H) ≠ 1 := fun h => hx1 (by rw [show t = 1 from Subtype.ext h, map_one])
    rw [centDer, commutator_le]
    intro c₁ hc₁ c₂ hc₂
    obtain ⟨b₁, hb₁, rfl⟩ := hψ.exists_eq c₁ hc₁.1
    obtain ⟨b₂, hb₂, rfl⟩ := hψ.exists_eq c₂ hc₂.1
    have hz₁ := hcen t b₁ hb₁ (mem_centralizer_iff.mp hc₁.2 (ψ t) rfl).symm
    have hz₂ := hcen t b₂ hb₂ (mem_centralizer_iff.mp hc₂.2 (ψ t) rfl).symm
    have hcomm := commutatorElement_commute_of_central t.2 hb₁ hb₂ hz₁ hz₂
    have hmem : ⁅b₁, b₂⁆ ∈ B := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hb₁ hb₂) (inv_mem hb₁)) (inv_mem hb₂)
    have h1 := hNM t ht ht1 _ hmem hcomm
    have e : (⟨⁅b₁, b₂⁆, le_normalizer hmem⟩ : normalizer (B : Set H)) =
        ⁅(⟨b₁, le_normalizer hb₁⟩ : normalizer (B : Set H)), ⟨b₂, le_normalizer hb₂⟩⁆ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, map_commutatorElement] at h1
    exact h1
  ·
    rintro _ ⟨t, ht, rfl⟩ hx1
    have ht1 : (t : H) ≠ 1 := fun h => hx1 (by rw [show t = 1 from Subtype.ext h, map_one])
    have ht2 : (t : H) ^ 2 = 1 := hTab.2 _ ht
    refine (closure_le _).2 fun c hc => ?_
    obtain ⟨⟨hcX, hcx⟩, hcodd⟩ := hc
    obtain ⟨b, hb, rfl⟩ := hψ.exists_eq c hcX
    obtain ⟨k, hkodd, hk⟩ := exists_odd_orderOf_lift ψ ⟨b, le_normalizer hb⟩ hcodd
    have hb₀ : b ^ k ∈ B := pow_mem hb k
    have e₀ : (⟨b, le_normalizer hb⟩ : normalizer (B : Set H)) ^ k =
        ⟨b ^ k, le_normalizer hb₀⟩ := Subtype.ext (by simp)
    rw [e₀] at hkodd hk
    have hkodd' : Odd (orderOf (b ^ k)) := by
      rwa [← Subgroup.orderOf_mk (b ^ k) (le_normalizer hb₀)]
    have hcomm₀ : ψ ⟨b ^ k, le_normalizer hb₀⟩ * ψ t = ψ t * ψ ⟨b ^ k, le_normalizer hb₀⟩ := by
      rw [hk]
      exact (mem_centralizer_iff.mp hcx (ψ t) rfl).symm
    have hz₀ := hcen t _ hb₀ hcomm₀
    have hzodd : Odd (orderOf ((t : H) * b ^ k * (t : H)⁻¹ * (b ^ k)⁻¹)) := by
      have h1 := commutatorElement_pow_of_central hb₀ hz₀ (orderOf (b ^ k))
      simp only [pow_orderOf_eq_one, mul_one, mul_inv_cancel, inv_one] at h1
      exact Odd.of_dvd_nat hkodd' (orderOf_dvd_of_pow_eq_one h1.symm)
    obtain ⟨b', hb', hb't, hb'b⟩ :=
      exists_mem_centralizer_of_odd_orderOf t.2 ht2 hb₀ hz₀ hzodd
    have hψb : ψ ⟨b', le_normalizer hb'⟩ = ψ ⟨b ^ k, le_normalizer hb₀⟩ := by
      have h1 : ψ (⟨b', le_normalizer hb'⟩ *
          (⟨b ^ k, le_normalizer hb₀⟩ : normalizer (B : Set H))⁻¹) = 1 :=
        (hψ.eq_one_iff _).mpr (by simpa using hb'b)
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    rw [← hk, ← hψb]
    exact hNM t ht ht1 b' hb' hb't

end Criterion

section Consequences

variable {X E M : Subgroup W}

theorem map_inf_centralizer_equiv (φ : W ≃* W) (hφX : X.map φ.toMonoidHom = X) (x : W) :
    (X ⊓ centralizer ({x} : Set W)).map φ.toMonoidHom = X ⊓ centralizer ({φ x} : Set W) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzX, hzx⟩, rfl⟩
    have hzx' : z * x = x * z := mem_centralizer_singleton_iff.1 hzx
    refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
    · rw [← hφX]
      exact ⟨z, hzX, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hzx']
  · rintro ⟨hyX, hyx⟩
    have hyx' : y * φ x = φ x * y := mem_centralizer_singleton_iff.1 hyx
    refine ⟨φ.symm y, ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩, by simp⟩
    · have hyX' : y ∈ X.map φ.toMonoidHom := by rw [hφX]; exact hyX
      obtain ⟨z, hz, rfl⟩ := hyX'
      simpa using hz
    · apply φ.injective
      simpa using hyx'

namespace HypIIConfigO2

theorem commute (h : HypIIConfigO2 X E M) {x y : W} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x :=
  congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem le_centralizer (h : HypIIConfigO2 X E M) {x : W} (hx : x ∈ E) :
    E ≤ centralizer ({x} : Set W) := fun _ hy =>
  mem_centralizer_singleton_iff.mpr (h.commute hy hx)

theorem gammaE_le (h : HypIIConfigO2 X E M) : gammaE X E ≤ normalizer (M : Set W) :=
  iSup₂_le fun x hx => iSup_le fun hx1 => h.centDer_le x hx hx1

theorem nE_le (h : HypIIConfigO2 X E M) : nE X E ≤ M := by
  rw [nE, commutator_le]
  intro e he g hg
  have hgN := h.gammaE_le hg
  have he' : e ∈ M := h.sylow.le he
  have h1 : g * e⁻¹ * g⁻¹ ∈ M := (mem_normalizer_iff.mp hgN _).mp (M.inv_mem he')
  rw [commutatorElement_def]
  have := M.mul_mem he' h1
  simpa [mul_assoc] using this

theorem isTwoNilpotent_nE [Finite W] (h : HypIIConfigO2 X E M) : IsTwoNilpotent (nE X E) :=
  h.twoNilpotent.mono h.nE_le

theorem not_rigidInvolution [Finite W] (h : HypIIConfigO2 X E M) {t : W} (htE : t ∈ E)
    (ht1 : t ≠ 1) : ¬ RigidInvolution X t := fun ht =>
  false_of_rigidInvolution h.elemAbelian h.four_le_card h.isTwoNilpotent_nE htE ht1 ht

theorem map_equiv [Finite W] (h : HypIIConfigO2 X E M) (φ : W ≃* W)
    (hφX : X.map φ.toMonoidHom = X) :
    HypIIConfigO2 X (E.map φ.toMonoidHom) (M.map φ.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, ?_, ?_, IsSylowOf.map h.sylow _, h.twoNilpotent.map _, ?_, ?_, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    simp only [coe_mul, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h.commute hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h.elemAbelian.2 x hx, map_one]
  · rw [card_map_of_injective φ.injective]
    exact h.four_le_card
  · intro hle
    apply h.not_le
    intro x hx
    have := hle ⟨x, hx, rfl⟩
    rw [← hφX] at this
    obtain ⟨y, hy, hyx⟩ := this
    rwa [φ.injective hyx] at hy
  · rw [← hφX, ← Subgroup.map_sup]
    exact map_mono h.le_sup
  · rintro _ ⟨x, hx, rfl⟩ hx1
    have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    have e : centDer X (φ x) = (centDer X x).map φ.toMonoidHom := by
      rw [centDer, centDer, Subgroup.map_commutator, map_inf_centralizer_equiv φ hφX x]
    rw [show φ.toMonoidHom x = φ x from rfl, e]
    exact (map_mono (h.centDer_le x hx hx1')).trans (le_normalizer_map _)
  · rintro _ ⟨x, hx, rfl⟩ hx1
    have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    have e : oUpperTwo (X ⊓ centralizer ({φ x} : Set W)) =
        (oUpperTwo (X ⊓ centralizer ({x} : Set W))).map φ.toMonoidHom := by
      rw [map_oUpperTwo_equiv, map_inf_centralizer_equiv φ hφX x]
    rw [show φ.toMonoidHom x = φ x from rfl, e]
    exact (map_mono (h.oTwo_le x hx hx1')).trans (le_normalizer_map _)

theorem conj [Finite W] (h : HypIIConfigO2 X E M) (hX : X.Normal) (w : W) :
    HypIIConfigO2 X (E.map (MulAut.conj w).toMonoidHom) (M.map (MulAut.conj w).toMonoidHom) :=
  h.map_equiv _ (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hX.conj_mem x hx w
    · intro x hx
      refine ⟨w⁻¹ * x * w, ?_, ?_⟩
      · simpa using hX.conj_mem x hx w⁻¹
      · simp [MulAut.conj_apply, mul_assoc])

variable [Finite W]

theorem oddPart (h : HypIIConfigO2 X E M) (hX : X.Normal) :
    ∃ N : Subgroup W, N ≤ M ∧ N ≤ X ∧ Odd (Nat.card N) ∧
      normalizer (M : Set W) ≤ normalizer (N : Set W) ∧
      ∃ k : ℕ, ∀ m ∈ M, m ^ (2 ^ k) ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNM, hNn, hNo, k, hk⟩ := h.twoNilpotent
  have hpow : ∀ m ∈ M, m ^ (2 ^ k) ∈ N := by
    intro m hm
    have hcard : Nat.card (↥M ⧸ N.subgroupOf M) = 2 ^ k := hk
    have h1 : (QuotientGroup.mk (⟨m, hm⟩ : ↥M) : ↥M ⧸ N.subgroupOf M) ^ (2 ^ k) = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  refine ⟨N, hNM, ?_, hNo, normalizer_le_normalizer_of_complement hNM hNn hNo hk, k, hpow⟩
  intro x hx
  have hodd : Odd (orderOf x) := by
    have : orderOf (⟨x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hNo this
  have hxM : x ∈ ((X ⊔ E : Subgroup W) : Set W) := h.le_sup (hNM hx)
  have := hX
  rw [normal_mul] at hxM
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hxM
  have hb2 : b ^ 2 = 1 := h.elemAbelian.2 b hb
  have hq : (QuotientGroup.mk (a * b) : W ⧸ X) = QuotientGroup.mk b := by
    rw [QuotientGroup.eq, mul_inv_rev]
    simpa [mul_assoc] using hX.conj_mem a⁻¹ (X.inv_mem ha) b⁻¹
  have h1 : (QuotientGroup.mk b : W ⧸ X) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hb2, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk b : W ⧸ X) ^ orderOf (a * b) = 1 := by
    rw [← hq, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk b : W ⧸ X) ∣ Nat.gcd 2 (orderOf (a * b)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [(Nat.coprime_two_left).mpr hodd, Nat.dvd_one, orderOf_eq_one_iff,
    QuotientGroup.eq_one_iff] at h3
  exact X.mul_mem ha h3

theorem oTwo_le_normalizer (h : HypIIConfigO2 X E M) (hX : X.Normal) {x : W} (hxE : x ∈ E)
    (hx1 : x ≠ 1) (hO : CFSG.oddCore ↥(X ⊓ centralizer ({x} : Set W)) = ⊥) :
    oUpperTwo (X ⊓ centralizer ({x} : Set W)) ≤ normalizer (E : Set W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNM, hNX, hNo, hMN, k, hpow⟩ := h.oddPart hX
  set C := X ⊓ centralizer ({x} : Set W) with hC
  set C₂ := oUpperTwo C with hC₂
  have hC₂C : C₂ ≤ C := oUpperTwo_le C
  have hCM : C₂ ≤ normalizer (M : Set W) := h.oTwo_le x hxE hx1
  have hO₂ : CFSG.oddCore ↥C₂ = ⊥ := by
    have : (C₂.subgroupOf C).Normal :=
      ⟨fun n hn g => mem_subgroupOf.2 (oUpperTwo_conj_mem g.2 (mem_subgroupOf.1 hn))⟩
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (subgroupOfEquivOfLe hC₂C)
      (oddCore_eq_bot_of_normal' (G := ↥C) (N := C₂.subgroupOf C) hO)
  have hCN : N ⊓ centralizer ({x} : Set W) = ⊥ := by
    have hle : N ⊓ centralizer ({x} : Set W) ≤ C₂ := by
      intro y hy
      refine subset_closure ⟨⟨hNX hy.1, hy.2⟩, ?_⟩
      have : orderOf (⟨y, hy.1⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hNo this
    have hnorm : ((N ⊓ centralizer ({x} : Set W)).subgroupOf C₂).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc => ?_
      rw [mem_normalizer_iff]
      intro y
      have hcN := hMN (hCM hc)
      have hcC : c ∈ centralizer ({x} : Set W) := (hC₂C hc).2
      constructor
      · intro hy
        obtain ⟨hyN, hyx⟩ := mem_inf.mp hy
        exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hcN y).mp hyN,
          mul_mem (mul_mem hcC hyx) (inv_mem hcC)⟩
      · intro hy
        obtain ⟨hyN, hyx⟩ := mem_inf.mp hy
        refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hcN y).mpr hyN, ?_⟩
        have := mul_mem (mul_mem (inv_mem hcC) hyx) hcC
        simpa [mul_assoc] using this
    have hodd : Odd (Nat.card ((N ⊓ centralizer ({x} : Set W)).subgroupOf C₂)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
      exact Odd.of_dvd_nat hNo (card_dvd_of_le inf_le_left)
    have h1 : (N ⊓ centralizer ({x} : Set W)).subgroupOf C₂ ≤ CFSG.oddCore ↥C₂ :=
      le_sSup ⟨hnorm, hodd⟩
    rw [hO₂, le_bot_iff] at h1
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hle hy⟩ : C₂) ∈ (N ⊓ centralizer ({x} : Set W)).subgroupOf C₂ := hy
    rw [h1, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  have hE : M ⊓ centralizer ({x} : Set W) = E := by
    refine h.sylow.eq_of_le (le_inf h.sylow.le (h.le_centralizer hxE)) inf_le_left ?_
    intro y
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (y : W) ^ (2 ^ k) ∈ N ⊓ centralizer ({x} : Set W) :=
      ⟨hpow _ y.2.1, pow_mem y.2.2 _⟩
    rw [hCN, mem_bot] at h1
    simpa using h1
  intro c hc
  have hcM := hCM hc
  have hcC : c ∈ centralizer ({x} : Set W) := (hC₂C hc).2
  have key : ∀ d : W, d ∈ normalizer (M : Set W) → d ∈ centralizer ({x} : Set W) →
      ∀ y ∈ E, d * y * d⁻¹ ∈ E := by
    intro d hd hdx y hy
    rw [← hE] at hy ⊢
    obtain ⟨hyM, hyx⟩ := mem_inf.mp hy
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hd y).mp hyM,
      mul_mem (mul_mem hdx hyx) (inv_mem hdx)⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key c hcM hcC y, fun hy => ?_⟩
  have := key c⁻¹ (inv_mem hcM) (inv_mem hcC) _ hy
  simpa [mul_assoc] using this

end HypIIConfigO2

end Consequences

end CFSG.ComponentClassification.RankTwoHypIIClassical
