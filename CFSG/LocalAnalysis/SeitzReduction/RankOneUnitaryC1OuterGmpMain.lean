module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmpCore
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmhMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmcChar
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmfClosure

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

section GmpComm

variable {G : Type*} [Group G]

theorem gmp_comm_mul_left (x₁ x₂ t : G) :
    ⁅x₁ * x₂, t⁆ = x₁ * ⁅x₂, t⁆ * x₁⁻¹ * ⁅x₁, t⁆ := by
  simp only [commutatorElement_def]
  group

theorem gmp_comm_mul_right (y x₁ x₂ : G) :
    ⁅y, x₁ * x₂⁆ = ⁅y, x₁⁆ * (x₁ * ⁅y, x₂⁆ * x₁⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem gmp_comm_mul_comm (y₁ y₂ v : G) :
    ⁅y₁ * y₂, v⁆ = ⁅y₁, ⁅y₂, v⁆⁆ * ⁅y₂, v⁆ * ⁅y₁, v⁆ := by
  simp only [commutatorElement_def]
  group

theorem gmp_comm_conj {g v : G} (hgv : g * v = v * g) (y : G) :
    ⁅g * y * g⁻¹, v⁆ = g * ⁅y, v⁆ * g⁻¹ := by
  have h1 : v = g * v * g⁻¹ := by rw [hgv, mul_inv_cancel_right]
  simp only [commutatorElement_def]
  conv_lhs => rw [h1]
  group

theorem gmp_comm_conj_conj (g a b : G) :
    ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

end GmpComm

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmp_exists_comm_eq {a : G} (ha : a ∈ U₁ ⊓ centralizer ({t * w} : Set G)) :
    ∃ u ∈ U₁, ⁅u, t * w⁆ = a := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W', hW'T₁, hAW', hW'card, -, -, -, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hvv : (t * w) * (t * w) = 1 := by rw [← sq]; exact hW.tw_sq
  have hvinv : (t * w)⁻¹ = t * w := inv_eq_of_mul_eq_one_right hvv
  have hvN : ∀ u ∈ U₁, (t * w) * u * (t * w)⁻¹ ∈ U₁ := fun u hu =>
    (mem_normalizer_iff.mp (hL.T_le hW.tw_mem) u).mp hu
  have hXW : ∀ c ∈ U₁, (t * w) * c * (t * w)⁻¹ = c⁻¹ → c ∈ W' ⊔ V := by
    intro c hcU hinv
    refine hL.gms_mem_sup_of_comm_mem_szA₁ hS hW.tw_mem (fun r hr => hW.tw_inv hr) hW'iff hcU ?_
    have e : c * (t * w) * c⁻¹ * (t * w)⁻¹ = c * ((t * w) * c * (t * w)⁻¹)⁻¹ := by group
    rw [e, hinv, inv_inv, ← sq]
    exact hL.muOne_sq_mem_szA₁ hS hc hW.mu hK hμ hcU
  have hW'V : Nat.card (W' ⊔ V : Subgroup G) ≤ (2 ^ f) ^ 3 := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := V) (B := W') (fun y hy => hL.muOne_T₁_le_normalizer hS (hW'T₁ hy))
    have hinf : 2 ^ f ≤ Nat.card (V ⊓ W' : Subgroup G) := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le (le_inf hS.conf.le hAW')
    rw [hS.conf.card, hW'card, sup_comm] at h1
    have h2 : Nat.card (W' ⊔ V : Subgroup G) * 2 ^ f ≤ (2 ^ f) ^ 3 * 2 ^ f := by
      calc Nat.card (W' ⊔ V : Subgroup G) * 2 ^ f ≤
            Nat.card (W' ⊔ V : Subgroup G) * Nat.card (V ⊓ W' : Subgroup G) :=
            Nat.mul_le_mul_left _ hinf
        _ = (2 ^ f) ^ 3 * 2 ^ f := by rw [h1]; ring
    exact Nat.le_of_mul_le_mul_right h2 hq0
  have hφ : ∀ u ∈ U₁, u * (t * w) * u⁻¹ * (t * w)⁻¹ ∈ W' ⊔ V := by
    intro u hu
    refine hXW _ ?_ ?_
    · rw [show u * (t * w) * u⁻¹ * (t * w)⁻¹ = u * ((t * w) * u⁻¹ * (t * w)⁻¹) by group]
      exact mul_mem hu (hvN _ (inv_mem hu))
    · have e1 : (t * w) * (u * (t * w) * u⁻¹ * (t * w)⁻¹) * (t * w)⁻¹ =
          (t * w) * u * (t * w) * u⁻¹ * ((t * w)⁻¹ * (t * w)⁻¹) := by group
      have e2 : (u * (t * w) * u⁻¹ * (t * w)⁻¹)⁻¹ = (t * w) * u * (t * w)⁻¹ * u⁻¹ := by group
      rw [e1, e2, hvinv, hvv, mul_one]
  have hcard : Nat.card ((centralizer ({t * w} : Set G)).subgroupOf U₁) *
      Nat.card (W' ⊔ V : Subgroup G) ≤ Nat.card U₁ := by
    have h1 : Nat.card ((centralizer ({t * w} : Set G)).subgroupOf U₁) = (2 ^ f) ^ 2 := by
      rw [← hW.card_F, ← card_map_of_injective U₁.subtype_injective, subgroupOf_map_subtype,
        inf_comm]
    rw [h1, hL.muOne_card_U₁ hS]
    calc (2 ^ f) ^ 2 * Nat.card (W' ⊔ V : Subgroup G) ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 3 :=
          Nat.mul_le_mul_left _ hW'V
      _ = (2 ^ f) ^ 5 := by ring
  obtain ⟨u, hu, hu'⟩ := gmc_exists_comm_eq_of_card_le hφ hcard (hW.F_le hW'iff ha)
  exact ⟨u, hu, hu'⟩

theorem gmp_comm_mem_F {u : G} (hu : u ∈ U₁ ⊓ normalizer
      (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) : Set G)) :
    ⁅u, t * w⁆ ∈ U₁ ⊓ centralizer ({t * w} : Set G) := by
  obtain ⟨hAmem, -, -⟩ := hW.gmh_A_facts
  obtain ⟨huU, huN⟩ := mem_inf.mp hu
  have h1 : u * (t * w) * u⁻¹ ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) :=
    (mem_normalizer_iff.mp huN (t * w)).mp (mem_sup_right (mem_zpowers _))
  obtain ⟨b, hb, h2 | h2⟩ := hAmem _ h1
  · exfalso
    apply hW.gmh_tw_not_mem_U₁
    rw [show t * w = u⁻¹ * (u * (t * w) * u⁻¹) * u by group, h2]
    exact mul_mem (mul_mem (inv_mem huU) (mem_inf.mp hb).1) huU
  · rw [commutatorElement_def, h2, mul_inv_cancel_right]
    exact hb

theorem gmp_mem_of_comm_mem_F {u : G} (hu : u ∈ U₁)
    (huF : ⁅u, t * w⁆ ∈ U₁ ⊓ centralizer ({t * w} : Set G)) :
    u ∈ U₁ ⊓ normalizer
      (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) : Set G) := by
  have hS := hW.step
  have hL := hW.level
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨hAmem, -, -⟩ := hW.gmh_A_facts
  have hcomm := hL.muOne_comm_mem_szA₁ hS hc hW.mu hK hμ
  have hA₁F := hW.gmh_szA₁_le_F
  have hconjF : ∀ b ∈ U₁ ⊓ centralizer ({t * w} : Set G),
      u * b * u⁻¹ ∈ U₁ ⊓ centralizer ({t * w} : Set G) := by
    intro b hb
    rw [show u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b by group]
    exact mul_mem (hA₁F (hcomm u hu b (mem_inf.mp hb).1)) hb
  refine mem_inf.mpr ⟨hu, gmh_mem_normalizer_of_conj_mem fun x hx => ?_⟩
  obtain ⟨b, hb, h1 | h1⟩ := hAmem x hx <;> rw [h1]
  · exact mem_sup_left (hconjF b hb)
  · rw [show u * (b * (t * w)) * u⁻¹ =
      (u * b * u⁻¹) * (u * (t * w) * u⁻¹ * (t * w)⁻¹) * (t * w) by group]
    exact mul_mem (mul_mem (mem_sup_left (hconjF b hb)) (mem_sup_left huF))
      (mem_sup_right (mem_zpowers _))

theorem gmp_comm_comm_eq_one :
    ∀ y ∈ U₁ ⊓ normalizer
        (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) : Set G),
      ∀ y' ∈ U₁ ⊓ normalizer
          (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) : Set G),
        ⁅y, ⁅y', t * w⁆⁆ = 1 := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨W', hW'T₁, -, -, hW'ab, -, -, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  obtain ⟨-, hvA, hCv, -⟩ := h.outer_facts_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hF
  set Z := U₁ ⊓ normalizer ((F ⊔ zpowers (t * w) : Subgroup G) : Set G) with hZ
  set A₁ := szA₁ (szT₁ L T) with hA₁
  have hcommA : ∀ x ∈ U₁, ∀ y ∈ U₁, ⁅x, y⁆ ∈ A₁ := hL.muOne_comm_mem_szA₁ hS hc hW.mu hK hμ
  have hcent : ∀ x ∈ U₁, ∀ a ∈ A₁, x * a = a * x := by
    intro x hx a ha
    have e := hL.muOne_conj_szA₁ hS hx ha
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [e]
  have hA₁U : ∀ {a : G}, a ∈ A₁ → a ∈ U₁ := fun ha => hW.T₁_le_U₁ (szA₁_le _ ha)
  have hFE : F ≤ W' ⊔ V := hW.F_le hW'iff
  have hEab := hW.sup_V_comm hW'T₁ hW'ab
  have hFTV : F ≤ szT₁ L T ⊔ V := hFE.trans (sup_le_sup_right hW'T₁ V)
  have hZU : ∀ {y : G}, y ∈ Z → y ∈ U₁ := fun hy => (mem_inf.mp hy).1
  have hZF : ∀ y ∈ Z, ⁅y, t * w⁆ ∈ F := fun y hy => hW.gmp_comm_mem_F hy
  have hFU : ∀ {x : G}, x ∈ F → x ∈ U₁ := fun hx => (mem_inf.mp hx).1
  have htA : ∀ a ∈ A₁, a * t = t * a := fun a ha =>
    mem_centralizer_iff.mp h.mem_centralizer_szT₁ a (szA₁_le _ ha)
  have hψA : ∀ x ∈ F, ⁅x, t⁆ ∈ A₁ := fun x hx => hL.muOne_comm_t_mem_szA₁_of_mem_sup hS (hFTV hx)
  have hπA : ∀ y ∈ Z, ⁅⁅y, t * w⁆, t⁆ ∈ A₁ := fun y hy => hψA _ (hZF y hy)
  have hker : ∀ y ∈ Z, ⁅⁅y, t * w⁆, t⁆ = 1 → ⁅y, t * w⁆ ∈ A₁ := by
    intro y hy h1
    have hp := hZF y hy
    have hpT : ⁅y, t * w⁆ ∈ szT₁ L T :=
      hW.gmh_mem_T₁_of_commute (hFU hp) (commutatorElement_eq_one_iff_mul_comm.mp h1)
    exact hCv _ hpT (mem_centralizer_singleton_iff.mp (mem_inf.mp hp).2).symm
  have hπmul : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z,
      ⁅⁅y₁ * y₂, t * w⁆, t⁆ = ⁅⁅y₁, t * w⁆, t⁆ * ⁅⁅y₂, t * w⁆, t⁆ := by
    intro y₁ hy₁ y₂ hy₂
    have hc₁ := hZF y₁ hy₁
    have hc₂ := hZF y₂ hy₂
    have hκ : ⁅y₁, ⁅y₂, t * w⁆⁆ ∈ A₁ := hcommA _ (hZU hy₁) _ (hFU hc₂)
    rw [gmp_comm_mul_comm y₁ y₂ (t * w), mul_assoc ⁅y₁, ⁅y₂, t * w⁆⁆,
      gmp_comm_mul_left ⁅y₁, ⁅y₂, t * w⁆⁆ (⁅y₂, t * w⁆ * ⁅y₁, t * w⁆) t,
      commutatorElement_eq_one_iff_mul_comm.mpr (htA _ hκ), mul_one,
      hL.muOne_conj_szA₁ hS (hA₁U hκ) (hψA _ (mul_mem hc₂ hc₁)),
      gmp_comm_mul_left ⁅y₂, t * w⁆ ⁅y₁, t * w⁆ t,
      hL.muOne_conj_szA₁ hS (hFU hc₂) (hψA _ hc₁)]
  have hBA : ∀ y ∈ Z, ∀ y' ∈ Z, ⁅y, ⁅y', t * w⁆⁆ ∈ A₁ := fun y hy y' hy' =>
    hcommA _ (hZU hy) _ (hFU (hZF y' hy'))
  have hBl : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, ∀ y' ∈ Z,
      ⁅y₁ * y₂, ⁅y', t * w⁆⁆ = ⁅y₁, ⁅y', t * w⁆⁆ * ⁅y₂, ⁅y', t * w⁆⁆ := by
    intro y₁ hy₁ y₂ hy₂ y' hy'
    have hc := hFU (hZF y' hy')
    rw [gmp_comm_mul_left y₁ y₂, hL.muOne_conj_szA₁ hS (hZU hy₁) (hcommA _ (hZU hy₂) _ hc)]
    exact hcent _ (hA₁U (hcommA _ (hZU hy₂) _ hc)) _ (hcommA _ (hZU hy₁) _ hc)
  have hBr : ∀ y ∈ Z, ∀ y₁ ∈ Z, ∀ y₂ ∈ Z,
      ⁅y, ⁅y₁ * y₂, t * w⁆⁆ = ⁅y, ⁅y₁, t * w⁆⁆ * ⁅y, ⁅y₂, t * w⁆⁆ := by
    intro y hy y₁ hy₁ y₂ hy₂
    have hc₁ := hFU (hZF y₁ hy₁)
    have hc₂ := hFU (hZF y₂ hy₂)
    have hκ : ⁅y₁, ⁅y₂, t * w⁆⁆ ∈ A₁ := hcommA _ (hZU hy₁) _ hc₂
    rw [gmp_comm_mul_comm y₁ y₂ (t * w),
      gmp_comm_mul_right y (⁅y₁, ⁅y₂, t * w⁆⁆ * ⁅y₂, t * w⁆) ⁅y₁, t * w⁆,
      gmp_comm_mul_right y ⁅y₁, ⁅y₂, t * w⁆⁆ ⁅y₂, t * w⁆,
      commutatorElement_eq_one_iff_mul_comm.mpr (hcent _ (hZU hy) _ hκ), one_mul,
      hL.muOne_conj_szA₁ hS (hA₁U hκ) (hcommA _ (hZU hy) _ hc₂),
      hL.muOne_conj_szA₁ hS (mul_mem (hA₁U hκ) hc₂) (hcommA _ (hZU hy) _ hc₁)]
    exact hcent _ (hA₁U (hcommA _ (hZU hy) _ hc₂)) _ (hcommA _ (hZU hy) _ hc₁)
  have hB0l : ∀ y ∈ Z, ⁅⁅y, t * w⁆, t⁆ = 1 → ∀ y' ∈ Z, ⁅y, ⁅y', t * w⁆⁆ = 1 := by
    intro y hy h1 y' hy'
    have hyE : y ∈ W' ⊔ V := hL.gms_mem_sup_of_comm_mem_szA₁ hS hW.tw_mem
      (fun r hr => hW.tw_inv hr) hW'iff (hZU hy) (hker y hy h1)
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hEab _ hyE _ (hFE (hZF y' hy')))
  have hB0r : ∀ y ∈ Z, ⁅⁅y, t * w⁆, t⁆ = 1 → ∀ y' ∈ Z, ⁅y', ⁅y, t * w⁆⁆ = 1 :=
    fun y hy h1 y' hy' =>
      commutatorElement_eq_one_iff_mul_comm.mpr (hcent _ (hZU hy') _ (hker y hy h1))
  have hBd : ∀ y ∈ Z, ⁅y, ⁅y, t * w⁆⁆ = 1 := by
    intro y hy
    have hp2 : ⁅y, t * w⁆ ^ 2 = 1 := hW.F_sq (hZF y hy)
    have hsv : y * y * (t * w) = (t * w) * (y * y) := by
      rw [← sq]
      exact (hvA _ (hL.muOne_sq_mem_szA₁ hS hc hW.mu hK hμ (hZU hy))).symm
    have hinv : y * ⁅y, t * w⁆ * y⁻¹ = ⁅y, t * w⁆⁻¹ := by
      simp only [commutatorElement_def]
      calc y * (y * (t * w) * y⁻¹ * (t * w)⁻¹) * y⁻¹
          = y * y * (t * w) * y⁻¹ * (t * w)⁻¹ * y⁻¹ := by group
        _ = (t * w) * (y * y) * y⁻¹ * (t * w)⁻¹ * y⁻¹ := by rw [hsv]
        _ = (y * (t * w) * y⁻¹ * (t * w)⁻¹)⁻¹ := by group
    rw [commutatorElement_def y ⁅y, t * w⁆, hinv, ← mul_inv_rev, ← sq, hp2, inv_one]
  obtain ⟨c, hc₁, hcD⟩ := hW.gmh_exists_normalizes
  have hW' := hW.gmh_conj hc₁
  obtain ⟨e, heD, hev, hetr⟩ := hW'.gmh_exists_torus hcD
  have heU : e⁻¹ ∈ normalizer (U₁ : Set G) := inv_mem (hW'.level.D_le heD)
  have het : e * t = t * e := mem_centralizer_iff.mp h.mem e (hW'.step.cartan.le heD)
  have hgv : e⁻¹ * (t * w) = (t * w) * e⁻¹ := (show Commute e (t * w) from hev).inv_left.eq
  have hgt : e⁻¹ * t = t * e⁻¹ := (show Commute e t from het).inv_left.eq
  have hgA := hW.gmh_mem_normalizer_A heU hgv
  have hgN : e⁻¹ ^ Nat.card (D.map (MulAut.conj c⁻¹).toMonoidHom) = 1 := by
    have h1 := pow_card_eq_one' (G := D.map (MulAut.conj c⁻¹).toMonoidHom)
      (x := ⟨e⁻¹, inv_mem heD⟩)
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    exact h2
  have hgZ : ∀ y ∈ Z, e⁻¹ * y * e⁻¹⁻¹ ∈ Z := by
    intro y hy
    obtain ⟨hyU, hyN⟩ := mem_inf.mp hy
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp heU y).mp hyU,
      mul_mem (mul_mem hgA hyN) (inv_mem hgA)⟩
  have hπg : ∀ y ∈ Z, ⁅⁅e⁻¹ * y * e⁻¹⁻¹, t * w⁆, t⁆ = e⁻¹ * ⁅⁅y, t * w⁆, t⁆ * e⁻¹⁻¹ :=
    fun y _ => by rw [gmp_comm_conj hgv y, gmp_comm_conj hgt]
  have hBg : ∀ y ∈ Z, ∀ y' ∈ Z, ⁅e⁻¹ * y * e⁻¹⁻¹, ⁅e⁻¹ * y' * e⁻¹⁻¹, t * w⁆⁆ =
      e⁻¹ * ⁅y, ⁅y', t * w⁆⁆ * e⁻¹⁻¹ :=
    fun y _ y' _ => by rw [gmp_comm_conj hgv y', gmp_comm_conj_conj]
  have htr : ∀ a ∈ A₁, ∀ b ∈ A₁, a ≠ 1 → b ≠ 1 → ∃ n : ℕ, e⁻¹ ^ n * a * (e⁻¹ ^ n)⁻¹ = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨n, hn⟩ := hetr a ha b hb ha1 hb1
    exact ⟨n, by rw [inv_pow, inv_inv]; exact hn⟩
  exact gmp_pairing_eq_one (A := A₁) (Z := Z) (π := fun y => ⁅⁅y, t * w⁆, t⁆)
    (B := fun y y' => ⁅y, ⁅y', t * w⁆⁆) (g := e⁻¹) hW'.step.cartan.odd hgN hπA hπmul hBA hBl
    hBr hB0l hB0r hBd hgZ hπg hBg htr

theorem gmp_commute_of_comm_mem_F {u : G} (hu : u ∈ U₁)
    (huF : ⁅u, t * w⁆ ∈ U₁ ⊓ centralizer ({t * w} : Set G)) {x : G}
    (hx : x ∈ U₁ ⊓ centralizer ({t * w} : Set G)) : u * x = x * u := by
  obtain ⟨u', hu', hu'x⟩ := hW.gmp_exists_comm_eq hx
  have h1 := hW.gmp_comm_comm_eq_one u (hW.gmp_mem_of_comm_mem_F hu huF) u'
    (hW.gmp_mem_of_comm_mem_F hu' (hu'x ▸ hx))
  rw [hu'x] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end U3C1OuterSwapHigh

theorem u3C1GmhTransInput_holds : U3C1GmhTransInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW a ha
  obtain ⟨u, hu, hua⟩ := hW.gmp_exists_comm_eq ha
  refine ⟨u, hu, fun x hx => (hW.gmp_commute_of_comm_mem_F hu (hua ▸ ha) hx).symm, ?_⟩
  rw [← hua, commutatorElement_def]
  group

theorem u3C1GmhNArgInput_holds : U3C1GmhNArgInput :=
  u3C1GmhNArgInput_of_trans u3C1GmhTransInput_holds

theorem u3C1OuterSwapHighInput_of_gmp (hC : U3C1GmsCharInput)
    (hc : U3C1GmsFusionInput) (hf : U3C1GmsClosureInput) (hg : U3C1GmsLayerInput) :
    U3C1OuterSwapHighInput :=
  u3C1OuterSwapHighInput_of_gmh hC hc hf hg u3C1GmhNArgInput_holds

theorem u3C1OuterSwapHighInput_of_gmp_fusion_layer
    (hc : U3C1GmsFusionInput) (hg : U3C1GmsLayerInput) : U3C1OuterSwapHighInput :=
  u3C1OuterSwapHighInput_of_gmp u3C1GmsCharInput_holds hc u3C1GmsClosureInput_holds hg

end CFSG.SeitzReduction.RankOne
