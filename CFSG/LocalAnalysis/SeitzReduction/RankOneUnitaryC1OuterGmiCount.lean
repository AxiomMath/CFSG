module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiLayer
public import CFSG.Monster.B.Recog.GenericGoldschmidtArithOmega
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups

theorem gmi_three_dvd (f : ℕ) : 3 ∣ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  refine Dvd.dvd.mul_left ?_ _
  have h := Nat.sub_dvd_pow_sub_pow 4 1 f
  rw [one_pow, show (4 : ℕ) - 1 = 3 by norm_num] at h
  rwa [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]

theorem gmi_five_dvd : 5 ∣ 2 ^ 2 * ((2 ^ 2) ^ 2 - 1) := by norm_num

namespace GmiLayerHyp

variable {X : Type} [Group X] [Finite X] {f : ℕ} {Q : Sylow 2 X} {J F A₁ K₀ Dv : Subgroup X}
  {v e : X} {τ : MulAut X} (h : GmiLayerHyp X f Q J F A₁ K₀ Dv v e τ)
include h

theorem not_sz (hC4 : GmiCatFourInput) {K : Subgroup X}
    (hK : CFSG.IsComponent K) (n : ℕ) : IsEmpty ((K ⧸ Subgroup.center K) ≃* Sz n) := by
  refine ⟨fun e' => ?_⟩
  have h3 := CFSG.Monster.B.Recog.GoldschmidtArithOmega.sz_not_three_dvd e'
  apply h3
  exact (h.card_K₀ ▸ gmi_three_dvd f).trans (h.card_K₀_dvd hC4 hK)

theorem not_ree (hC4 : GmiCatFourInput) {K : Subgroup X} (hK : CFSG.IsComponent K) (m : ℕ) :
    Nat.card (K ⧸ Subgroup.center K) ≠ ordRee (3 ^ (2 * m + 1)) := by
  intro hcard
  have hdvd := h.card_K₀_dvd hC4 hK
  rw [h.card_K₀] at hdvd
  obtain ⟨k, hk⟩ := h.even
  rcases Nat.lt_or_ge f 3 with hf | hf
  ·
    have hf2 : f = 2 := by have := h.two_le; omega
    subst hf2
    apply CFSG.ProperTwoGeneratedCore.Lemma37.not_five_dvd_ordRee m
    rw [← hcard]
    exact gmi_five_dvd.trans hdvd
  ·
    have hf4 : 4 ≤ f := by omega
    have h16 : 2 ^ 4 ∣ Nat.card (K ⧸ Subgroup.center K) :=
      ((pow_dvd_pow 2 hf4).trans (Dvd.intro _ rfl)).trans hdvd
    have hv := CFSG.Monster.B.Recog.GoldschmidtArithOmega.ree_factorization hcard
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h16
    omega

theorem exists_ne_one_A₁ : ∃ a ∈ A₁, a ≠ 1 := by
  refine (Subgroup.bot_or_exists_ne_one A₁).resolve_left fun hbot => ?_
  have hc := h.card_A₁
  rw [hbot, Subgroup.card_bot] at hc
  have : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := h.two_le; omega) 2
  omega

theorem false_of_sl2 (hC4 : GmiCatFourInput) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hu : ∀ T : Subgroup X, IsSylowOf 2 T K → ∃ u ∈ K, (∀ x ∈ T, u * x * u⁻¹ ∈ T) ∧
      ∀ k ∈ T, (∃ y ∈ K, k * y ≠ y * k) → k * (u * k * u⁻¹) ≠ u * k * u⁻¹ * k) : False := by
  obtain ⟨u, huK, huT, hu'⟩ := hu _ (h.isSylowOf_inf hK)
  obtain ⟨a, haA, ha1⟩ := h.exists_ne_one_A₁
  have haK₀ := h.A₁_le_K₀ haA
  have haF := h.A₁_le_F haA
  have haQ : a ∈ (Q : Subgroup X) := h.J_le_Q (h.F_le haF)
  obtain ⟨k, hk, c, hc, hkc⟩ := h.exists_mul_of_mem_Q hK haQ
  have hkK : k ∈ K := (mem_inf.mp hk).2
  have hcC : c ∈ centralizer (K : Set X) := (mem_inf.mp hc).2
  have hcK : ∀ y ∈ K, y * c = c * y := mem_centralizer_iff.mp hcC
  have hkZ : ∃ y ∈ K, k * y ≠ y * k := by
    by_contra hno
    push Not at hno
    have hkC : k ∈ centralizer (K : Set X) :=
      mem_centralizer_iff.mpr fun y hy => (hno y hy).symm
    have hmem : a ∈ K₀ ⊓ centralizer (K : Set X) :=
      mem_inf.mpr ⟨haK₀, hkc ▸ mul_mem hkC hcC⟩
    rw [h.K₀_inf_centralizer hC4 hK] at hmem
    exact ha1 (Subgroup.mem_bot.mp hmem)
  have hne := hu' k hk hkZ
  have hk'T := huT k hk
  have hk'K : u * k * u⁻¹ ∈ K := (mem_inf.mp hk'T).2
  have hua : u * a * u⁻¹ = u * k * u⁻¹ * c := by
    rw [← hkc]
    have h1 := hcK u⁻¹ (inv_mem huK)
    calc u * (k * c) * u⁻¹ = u * k * (c * u⁻¹) := by group
      _ = u * k * (u⁻¹ * c) := by rw [h1]
      _ = u * k * u⁻¹ * c := by group
  have ha'Q : u * a * u⁻¹ ∈ (Q : Subgroup X) := by
    rw [hua]
    exact mul_mem (mem_inf.mp hk'T).1 (mem_inf.mp hc).1
  have ha'E : u * a * u⁻¹ ∈ CFSG.layer X := h.layer_normal.conj_mem a (h.F_le_layer haF) u
  have ha'2 : (u * a * u⁻¹) ^ 2 = 1 := by
    rw [sq, show u * a * u⁻¹ * (u * a * u⁻¹) = u * (a * a) * u⁻¹ by group, ← sq, h.F_sq a haF]
    group
  have ha'Ω := h.mem_omega ha'Q ha'E ha'2
  have haΩ := h.F_le_omega haF
  have hcomm := h.J_comm a (h.omega_le_J haΩ) _ (h.omega_le_J ha'Ω)
  rw [hua, ← hkc] at hcomm
  apply hne
  have e1 : k * c * (u * k * u⁻¹ * c) = k * (u * k * u⁻¹) * (c * c) := by
    rw [show k * c * (u * k * u⁻¹ * c) = k * (c * (u * k * u⁻¹)) * c by group,
      ← hcK _ hk'K]
    group
  have e2 : u * k * u⁻¹ * c * (k * c) = u * k * u⁻¹ * k * (c * c) := by
    rw [show u * k * u⁻¹ * c * (k * c) = u * k * u⁻¹ * (c * k) * c by group, ← hcK k hkK]
    group
  rw [e1, e2] at hcomm
  exact mul_right_cancel hcomm

theorem center_eq_bot (hC4 : GmiCatFourInput)
    (hSchur : GmiCatSchurInput) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    Subgroup.center K = ⊥ := by
  by_contra hZ
  obtain ⟨hL2, hU3, hJ1, hSL2⟩ := hSchur X K hK.1 (h.center_isPGroup hK) hZ
  have hty := h.type K ((CFSG.isComponent_iff_open K).mp hK)
  rcases hty with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ |
      ⟨p, n, hp, hpodd, hn0, -, h8, ⟨e'⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e'⟩⟩
  · exact (hL2 n hn).false e'
  · exact (h.not_sz hC4 hK n).false e'
  · exact (hU3 n hn).false e'
  · exact h.false_of_sl2 hC4 hK (hSL2 p n hpodd hn0 h8 ⟨e'⟩)
  · exact h.not_ree hC4 hK m hcard
  · exact hJ1.false e'

theorem inf_centralizer_eq_bot {K : Subgroup X} (hZ : Subgroup.center K = ⊥) :
    K ⊓ centralizer (K : Set X) = ⊥ := by
  rw [CFSG.GroupTheory.inf_centralizer_eq_map_center, hZ, Subgroup.map_bot]

theorem v_not_mem_layer (hcen : ∀ K : Subgroup X, CFSG.IsComponent K → Subgroup.center K = ⊥) :
    v ∉ CFSG.layer X := by
  intro hvE
  have hc := (CFSG.LocalCores.layer_center (G := X)).1
  have hbot : ⨆ K : CFSG.LocalCores.ComponentIndex X,
      (Subgroup.center K.1).map K.1.subtype = ⊥ := by
    refine iSup_eq_bot.mpr fun K => ?_
    rw [hcen K.1 K.2, Subgroup.map_bot]
  rw [hbot] at hc
  have hmem : (⟨v, hvE⟩ : CFSG.layer X) ∈ Subgroup.center (CFSG.layer X) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h.v_comm g).symm
  have hv : v ∈ (Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype := ⟨_, hmem, rfl⟩
  rw [hc, Subgroup.mem_bot] at hv
  exact h.v_not_mem (hv ▸ one_mem F)

theorem zpowers_v_normal : (zpowers v).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
  rw [← (Commute.zpow_left (h.v_comm g) k).eq, mul_inv_cancel_right]
  exact hn

theorem card_le_of_le_omega (hcen : ∀ K : Subgroup X, CFSG.IsComponent K → Subgroup.center K = ⊥)
    {Y : Subgroup X} (hY : Y ≤ gmiOmega Q) : Nat.card Y ≤ 2 * (2 ^ f) ^ 2 := by
  have hvE := h.v_not_mem_layer hcen
  have hAJ : F ⊔ zpowers v ≤ J := sup_le h.F_le (zpowers_le.mpr h.v_mem)
  have hYc : ∀ y ∈ Y, ∀ a ∈ F ⊔ zpowers v, y * a = a * y := fun y hy a ha =>
    h.J_comm y (h.omega_le_J (hY hy)) a (hAJ ha)
  have h1 := h.L4 Y (hY.trans h.omega_le_Q) hYc
  have hle : Y ⊓ (F ⊔ zpowers v) ≤ F := by
    intro x hx
    obtain ⟨hxY, hxA⟩ := mem_inf.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := ncyc_exists_mul_of_mem_sup
      (fun a _ => gmi_top_le_normalizer h.zpowers_v_normal (mem_top a)) hxA
    rcases mem_zpowers_involution_eq_one_or_eq h.v_sq hb with hb1 | hbv
    · rwa [hb1, mul_one]
    · exfalso
      apply hvE
      rw [hbv] at hxY
      rw [show v = a⁻¹ * (a * v) by group]
      exact mul_mem (inv_mem (h.F_le_layer ha)) (h.omega_le_layer (hY hxY))
  have h2 := Subgroup.card_le_of_le hle
  rw [h.card_F] at h2
  omega

theorem card_omega_inf_ge (hC4 : GmiCatFourInput) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hZ : Subgroup.center K = ⊥) : 2 ^ f ≤ Nat.card (gmiOmega Q ⊓ K : Subgroup X) := by
  have hKC := h.inf_centralizer_eq_bot hZ
  have hdec : ∀ a : A₁, ∃ k ∈ (Q : Subgroup X) ⊓ K,
      ∃ c ∈ (Q : Subgroup X) ⊓ centralizer (K : Set X), k * c = a :=
    fun a => h.exists_mul_of_mem_Q hK (h.J_le_Q (h.F_le (h.A₁_le_F a.2)))
  choose k hk c hc hkc using hdec
  have hk2 : ∀ a : A₁, (k a) ^ 2 = 1 := by
    intro a
    have hcK : ∀ y ∈ K, y * c a = c a * y := mem_centralizer_iff.mp (mem_inf.mp (hc a)).2
    have ha2 : ((a : X)) ^ 2 = 1 := h.F_sq _ (h.A₁_le_F a.2)
    rw [← hkc a] at ha2
    have hcomm : Commute (k a) (c a) := hcK (k a) (mem_inf.mp (hk a)).2
    rw [hcomm.mul_pow] at ha2
    have hmem : (k a) ^ 2 ∈ K ⊓ centralizer (K : Set X) := by
      refine mem_inf.mpr ⟨pow_mem (mem_inf.mp (hk a)).2 2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left ha2]
      exact inv_mem (pow_mem (mem_inf.mp (hc a)).2 2)
    rw [hKC] at hmem
    exact Subgroup.mem_bot.mp hmem
  let φ : A₁ → (gmiOmega Q ⊓ K : Subgroup X) := fun a =>
    ⟨k a, mem_inf.mpr ⟨h.mem_omega (mem_inf.mp (hk a)).1
      (CFSG.LocalCores.component_le_layer hK (mem_inf.mp (hk a)).2) (hk2 a),
      (mem_inf.mp (hk a)).2⟩⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have hkab : k a = k b := congrArg Subtype.val hab
    have hmem : (a : X)⁻¹ * b ∈ K₀ ⊓ centralizer (K : Set X) := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (h.A₁_le_K₀ a.2)) (h.A₁_le_K₀ b.2), ?_⟩
      rw [← hkc a, ← hkc b, hkab, show (k b * c a)⁻¹ * (k b * c b) = (c a)⁻¹ * c b by group]
      exact mul_mem (inv_mem (mem_inf.mp (hc a)).2) (mem_inf.mp (hc b)).2
    rw [h.K₀_inf_centralizer hC4 hK, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem
  have hle := Nat.card_le_card_of_injective φ hφ
  rwa [h.card_A₁] at hle

theorem le_centralizer_of_ne {K L : Subgroup X} (hK : CFSG.IsComponent K)
    (hL : CFSG.IsComponent L) (hne : L ≠ K) : L ≤ centralizer (K : Set X) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((CFSG.LocalCores.distinct_components_commute hL hK).resolve_left hne)

theorem mem_normalizer_of_le_omega {A : Subgroup X} (hA : A ≤ gmiOmega Q) {b : X}
    (hb : b ∈ gmiOmega Q) : b ∈ normalizer (A : Set X) := by
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [h.J_comm b (h.omega_le_J hb) a (h.omega_le_J (hA ha)), mul_inv_cancel_right]
    exact ha
  · intro ha
    have hc := h.J_comm b (h.omega_le_J hb) _ (h.omega_le_J (hA ha))
    have e : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * ((b * a * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [← hc]
        _ = b * a * b⁻¹ := by group
    rw [e]
    exact ha

theorem card_sup_of_le_omega {A B : Subgroup X} (hA : A ≤ gmiOmega Q) (hB : B ≤ gmiOmega Q)
    (hAB : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  have hc := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer (A := A)
    (B := B) (fun b hb => h.mem_normalizer_of_le_omega hA (hB hb))
  rwa [hAB, Subgroup.card_bot, mul_one] at hc

theorem not_three_components (hC4 : GmiCatFourInput)
    (hSchur : GmiCatSchurInput) {K₁ K₂ K₃ : Subgroup X} (h₁ : CFSG.IsComponent K₁)
    (h₂ : CFSG.IsComponent K₂) (h₃ : CFSG.IsComponent K₃) (h12 : K₂ ≠ K₁) (h13 : K₃ ≠ K₁)
    (h23 : K₃ ≠ K₂) : False := by
  have hcen := fun K (hK : CFSG.IsComponent K) => h.center_eq_bot hC4 hSchur hK
  set W₁ := gmiOmega Q ⊓ K₁ with hW₁
  set W₂ := gmiOmega Q ⊓ K₂ with hW₂
  set W₃ := gmiOmega Q ⊓ K₃ with hW₃
  have c21 := h.le_centralizer_of_ne h₁ h₂ h12
  have c13 := h.le_centralizer_of_ne h₃ h₁ h13.symm
  have c23 := h.le_centralizer_of_ne h₃ h₂ h23.symm
  have hW12 : W₁ ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff, ← h.inf_centralizer_eq_bot (hcen K₁ h₁)]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans (inf_le_right.trans c21))
  have hW123 : (W₁ ⊔ W₂) ⊓ W₃ = ⊥ := by
    rw [eq_bot_iff, ← h.inf_centralizer_eq_bot (hcen K₃ h₃)]
    refine le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans ?_)
    exact sup_le (inf_le_right.trans c13) (inf_le_right.trans c23)
  have hc12 := h.card_sup_of_le_omega inf_le_left inf_le_left hW12
  have hc123 := h.card_sup_of_le_omega (sup_le inf_le_left inf_le_left) inf_le_left hW123
  rw [hc12] at hc123
  have hle := h.card_le_of_le_omega hcen
    (sup_le (sup_le inf_le_left inf_le_left) inf_le_left : W₁ ⊔ W₂ ⊔ W₃ ≤ gmiOmega Q)
  rw [hc123] at hle
  have g1 := h.card_omega_inf_ge hC4 h₁ (hcen K₁ h₁)
  have g2 := h.card_omega_inf_ge hC4 h₂ (hcen K₂ h₂)
  have g3 := h.card_omega_inf_ge hC4 h₃ (hcen K₃ h₃)
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hprod : q * q * q ≤ Nat.card W₁ * Nat.card W₂ * Nat.card W₃ :=
    Nat.mul_le_mul (Nat.mul_le_mul g1 g2) g3
  have h3 : q * q * q ≤ q * q * 2 := by nlinarith
  have h4 := Nat.le_of_mul_le_mul_left h3 (by positivity)
  omega

end GmiLayerHyp

end CFSG.SeitzReduction.RankOne
