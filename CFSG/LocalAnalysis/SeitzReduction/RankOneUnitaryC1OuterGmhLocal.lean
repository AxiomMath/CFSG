module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmhCore
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsF
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmh_szA₁_le_F : szA₁ (szT₁ L T) ≤ U₁ ⊓ centralizer ({t * w} : Set G) := by
  intro a ha
  obtain ⟨-, hvA, -, -⟩ := hW.step.start.outer_facts_of_card_sylow hW.step.card_sylow hW.tw_mem
    hW.tw_sq hW.tw_not_mem
  exact mem_inf.mpr ⟨hW.T₁_le_U₁ (szA₁_le _ ha), mem_centralizer_singleton_iff.mpr (hvA a ha).symm⟩

theorem gmh_tw_not_mem_U₁ : t * w ∉ U₁ := fun h =>
  hW.tw_not_mem (mem_sup_left (hW.level.muOne_mem_T₁_of_mem_T hW.step h hW.tw_mem))

theorem gmh_mem_T₁_of_commute {u : G} (hu : u ∈ U₁) (hut : u * t = t * u) : u ∈ szT₁ L T := by
  have hS := hW.step
  have hL := hW.level
  have hu' : u ∈ U ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨hL.U₁_le hu, mem_centralizer_singleton_iff.mpr hut⟩
  rw [hL.inf_centralizer] at hu'
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers hS.start.mem_centralizer_szT₁ hu'
  rcases mem_zpowers_involution_eq_one_or_eq hS.start.sq_eq_one hz with h1 | h1
  · rw [← hyz, h1, mul_one]
    exact hy
  · exfalso
    apply hL.t_not_mem
    rw [h1] at hyz
    rw [show t = y⁻¹ * u by rw [← hyz]; group]
    exact mul_mem (inv_mem (hW.T₁_le_U₁ hy)) hu

theorem gmh_not_forall_commute_t :
    ¬ ∀ a ∈ U₁ ⊓ centralizer ({t * w} : Set G), t * a = a * t := by
  intro hall
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, hCw, -⟩ := h.outer_facts_of_card_sylow hS2 hW.w_mem hW.w_sq hW.w_not_mem
  have hle : U₁ ⊓ centralizer ({t * w} : Set G) ≤ szA₁ (szT₁ L T) := by
    intro a ha
    have haT₁ := hW.gmh_mem_T₁_of_commute (mem_inf.mp ha).1 (hall a ha).symm
    refine hCw a haT₁ ?_
    have h1 : a * (t * w) = (t * w) * a := mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2
    have h2 : t * a = a * t := hall a ha
    calc w * a = t⁻¹ * ((t * w) * a) := by group
      _ = t⁻¹ * (a * (t * w)) := by rw [h1]
      _ = t⁻¹ * (a * t) * w := by group
      _ = t⁻¹ * (t * a) * w := by rw [h2]
      _ = a * w := by group
  have hc := Subgroup.card_le_of_le hle
  rw [hW.card_F, hA₁card] at hc
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.two_le)
  nlinarith

theorem gmh_mem_of_mem_centralizer {x : G} (hx : x ∈ U ⊔ T)
    (hxC : x ∈ centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) :
      Subgroup G) : Set G)) :
    x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hF
  have hFA : F ≤ F ⊔ zpowers (t * w) := le_sup_left
  have hvA : t * w ∈ F ⊔ zpowers (t * w) := mem_sup_right (mem_zpowers _)
  have hxF : ∀ a ∈ F, a * x = x * a := fun a ha => mem_centralizer_iff.mp hxC a (hFA ha)
  have hxv : (t * w) * x = x * (t * w) := mem_centralizer_iff.mp hxC _ hvA
  have hA₁F := hW.gmh_szA₁_le_F
  have hTU₁ : ∀ τ ∈ T, ∀ u ∈ U₁, τ * u * τ⁻¹ ∈ U₁ := fun τ hτ u hu =>
    (mem_normalizer_iff.mp (hL.T_le hτ) u).mp hu
  have hkey : ∀ u' ∈ U₁, ∀ z : G, z * (t * w) = (t * w) * z →
      ((∀ a ∈ F, z * a = a * z) → False) → x = u' * z → False := by
    intro u' hu' z hzv hzc hxz
    have hu'v : u' * (t * w) = (t * w) * u' := by
      have e1 : u' = x * z⁻¹ := by rw [hxz]; group
      have hzv' : z⁻¹ * (t * w) = (t * w) * z⁻¹ := by
        calc z⁻¹ * (t * w) = z⁻¹ * ((t * w) * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * (t * w)) * z⁻¹ := by rw [hzv]
          _ = (t * w) * z⁻¹ := by group
      rw [e1]
      calc x * z⁻¹ * (t * w) = x * (t * w) * z⁻¹ := by rw [mul_assoc, hzv', ← mul_assoc]
        _ = (t * w) * (x * z⁻¹) := by rw [← hxv, mul_assoc]
    have hu'F : u' ∈ F := mem_inf.mpr ⟨hu', mem_centralizer_singleton_iff.mpr hu'v⟩
    apply hzc
    intro a ha
    have e1 : z = u'⁻¹ * x := by rw [hxz]; group
    have hau : a * u' = u' * a := hW.F_comm ha hu'F
    rw [e1]
    calc u'⁻¹ * x * a = u'⁻¹ * (a * x) := by rw [mul_assoc, hxF a ha]
      _ = a * (u'⁻¹ * x) := by
          rw [← mul_assoc, ← mul_assoc, (show Commute a u' from hau).inv_right.eq]
  have htv : t * (t * w) = (t * w) * t := by rw [mul_assoc t w t, hW.wt_comm]
  have hwv : w * (t * w) = (t * w) * w := by rw [← mul_assoc, hW.wt_comm]
  have htc : (∀ a ∈ F, t * a = a * t) → False := hW.gmh_not_forall_commute_t
  have hwc : (∀ a ∈ F, w * a = a * w) → False := by
    intro hwF
    apply hW.gmh_not_forall_commute_t
    intro a ha
    have hav : a * (t * w) = (t * w) * a := mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2
    have haw : w⁻¹ * a = a * w⁻¹ := by
      calc w⁻¹ * a = w⁻¹ * (a * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * a) * w⁻¹ := by rw [hwF a ha]
        _ = a * w⁻¹ := by group
    calc t * a = (t * w) * (w⁻¹ * a) := by group
      _ = ((t * w) * a) * w⁻¹ := by rw [haw]; group
      _ = (a * (t * w)) * w⁻¹ := by rw [← hav]
      _ = a * t := by group
  rw [hL.muOne_sup_eq hS] at hx
  obtain ⟨τ, hτ, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hx
  have hτA : ∀ a ∈ szA₁ (szT₁ L T), τ * a = a * τ := by
    intro a ha
    have h1 := hxF a (hA₁F ha)
    have h2 : u * a * u⁻¹ = a := hL.conj_szA₁ u (hL.U₁_le hu) a ha
    have h2' : u⁻¹ * a = a * u⁻¹ := by
      calc u⁻¹ * a = u⁻¹ * (u * a * u⁻¹) := by rw [h2]
        _ = a * u⁻¹ := by group
    calc τ * a = (τ * u) * (u⁻¹ * a) := by group
      _ = ((τ * u) * a) * u⁻¹ := by rw [h2']; group
      _ = (a * (τ * u)) * u⁻¹ := by rw [h1]
      _ = a * τ := by group
  have hτ2 := h.pushUp_sq_mem_of_conj_szA₁ hS2 hτ hτA
  by_cases hτS : τ ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hτS
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with h1 | h1
    · have hτU : τ ∈ U₁ := by rw [← hyz, h1, mul_one]; exact hW.T₁_le_U₁ hy
      exact hFA (mem_inf.mpr ⟨mul_mem hτU hu, mem_centralizer_singleton_iff.mpr hxv.symm⟩)
    · rw [h1] at hyz
      exact (hkey (y * (t * u * t⁻¹)) (mul_mem (hW.T₁_le_U₁ hy) (hTU₁ t hW.t_mem u hu)) t
        htv htc (by rw [← hyz]; group)).elim
  · have hM := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hτ hW.tw_mem hτ2
      (by rw [hW.tw_sq]; exact one_mem _) hτS hW.tw_not_mem
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hM
    have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with h1 | h1
    · have hτe : τ = y * (t * w) := by
        rw [h1, mul_one] at hyz
        calc τ = τ * (t * w)⁻¹ * (t * w) := by group
          _ = y * (t * w) := by rw [← hyz]
      have hu' : y * ((t * w) * u * (t * w)⁻¹) ∈ U₁ :=
        mul_mem (hW.T₁_le_U₁ hy) (hTU₁ _ hW.tw_mem u hu)
      have hxe : τ * u = (y * ((t * w) * u * (t * w)⁻¹)) * (t * w) := by rw [hτe]; group
      have hu'v : (y * ((t * w) * u * (t * w)⁻¹)) * (t * w) =
          (t * w) * (y * ((t * w) * u * (t * w)⁻¹)) := by
        have e1 : y * ((t * w) * u * (t * w)⁻¹) = (τ * u) * (t * w)⁻¹ := by rw [hxe]; group
        rw [e1]
        calc τ * u * (t * w)⁻¹ * (t * w) = τ * u := by group
          _ = (t * w) * (τ * u) * (t * w)⁻¹ := by rw [hxv]; group
          _ = (t * w) * (τ * u * (t * w)⁻¹) := by group
      rw [hxe]
      exact mul_mem (hFA (mem_inf.mpr ⟨hu', mem_centralizer_singleton_iff.mpr hu'v⟩)) hvA
    · rw [h1] at hyz
      have hτe : τ = y * w := by
        calc τ = τ * (t * w)⁻¹ * (t * w) := by group
          _ = y * t * (t * w) := by rw [← hyz]
          _ = y * (t * t) * w := by group
          _ = y * w := by rw [htt, mul_one]
      exact (hkey (y * (w * u * w⁻¹)) (mul_mem (hW.T₁_le_U₁ hy) (hTU₁ w hW.w_mem u hu)) w
        hwv hwc (by rw [hτe]; group)).elim


theorem gmh_card_centralizer_le :
    Nat.card (swapS₂ P U T ⊓ centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔
      zpowers (t * w) : Subgroup G) : Set G) : Subgroup G) ≤
      2 * Nat.card ((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) := by
  set A := (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) with hA
  set X := swapS₂ P U T ⊓ centralizer (A : Set G) with hX
  have h1 := relIndex_mul_card (H := U ⊔ T) (K := X)
  have hle : (U ⊔ T) ⊓ X ≤ A := fun x hx =>
    hW.gmh_mem_of_mem_centralizer (mem_inf.mp hx).1 (mem_inf.mp (mem_inf.mp hx).2).2
  have h2 : (U ⊔ T).relIndex X ≤ 2 := by
    rw [← hW.relIndex_SU_S₂]
    exact relIndex_le_of_le_right inf_le_left (by rw [hW.relIndex_SU_S₂]; norm_num)
  have h3 := Subgroup.card_le_of_le hle
  calc Nat.card X = (U ⊔ T).relIndex X * Nat.card ((U ⊔ T) ⊓ X : Subgroup G) := h1.symm
    _ ≤ 2 * Nat.card A := Nat.mul_le_mul h2 h3

theorem gmh_A_facts :
    (∀ x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w),
      ∃ a ∈ U₁ ⊓ centralizer ({t * w} : Set G), x = a ∨ x = a * (t * w)) ∧
      (∀ x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w),
        ∀ y ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w), x * y = y * x) ∧
      ∀ x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w), x ^ 2 = 1 :=
  gmh_sup_zpowers_facts (fun _ ha _ hb => hW.F_comm ha hb) (fun _ ha => hW.F_sq ha)
    (fun _ ha => (mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2).symm) hW.tw_sq

theorem gmh_mem_normalizer_A {g : G} (hgU : g ∈ normalizer (U₁ : Set G))
    (hgv : g * (t * w) = (t * w) * g) :
    g ∈ normalizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
      Set G) := by
  obtain ⟨hAmem, -, -⟩ := hW.gmh_A_facts
  have hgF : ∀ a ∈ U₁ ⊓ centralizer ({t * w} : Set G),
      g * a * g⁻¹ ∈ U₁ ⊓ centralizer ({t * w} : Set G) := by
    intro a ha
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hgU a).mp (mem_inf.mp ha).1,
      mem_centralizer_singleton_iff.mpr ?_⟩
    have hav : a * (t * w) = (t * w) * a := mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2
    have hgv' : g⁻¹ * (t * w) = (t * w) * g⁻¹ := by
      calc g⁻¹ * (t * w) = g⁻¹ * ((t * w) * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * (t * w)) * g⁻¹ := by rw [hgv]
        _ = (t * w) * g⁻¹ := by group
    calc g * a * g⁻¹ * (t * w) = g * (a * (t * w)) * g⁻¹ := by rw [mul_assoc (g * a), hgv']; group
      _ = (t * w) * (g * a * g⁻¹) := by rw [hav, ← mul_assoc, hgv]; group
  have hgvv : g * (t * w) * g⁻¹ = t * w := by rw [hgv, mul_inv_cancel_right]
  apply gmh_mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨a, ha, h1 | h1⟩ := hAmem x hx <;> rw [h1]
  · exact mem_sup_left (hgF a ha)
  · rw [show g * (a * (t * w)) * g⁻¹ = (g * a * g⁻¹) * (g * (t * w) * g⁻¹) by group, hgvv]
    exact mul_mem (mem_sup_left (hgF a ha)) (mem_sup_right (mem_zpowers _))

theorem gmh_isSylowOf_centralizer
    (he : IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
      (centralizer ({t * w} : Set G))) :
    IsSylowOf 2 ((swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
      centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
        Set G))
      (centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
        Set G)) := by
  set A := (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) with hA
  set I := centralizer ({t * w} : Set G) with hI
  have hvA : t * w ∈ A := mem_sup_right (mem_zpowers _)
  have hS₀N : swapS₂ P U T ⊓ I ≤ I ⊓ normalizer (A : Set G) := by
    intro g hg
    obtain ⟨hgS, hgI⟩ := mem_inf.mp hg
    refine mem_inf.mpr ⟨hgI, hW.gmh_mem_normalizer_A ?_ (mem_centralizer_singleton_iff.mp hgI)⟩
    exact gmh_mem_normalizer_of_conj_mem fun u hu => hW.conj_U₁ hgS hu
  have hCA : centralizer (A : Set G) ≤ I ⊓ normalizer (A : Set G) := fun c hc =>
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc _ hvA).symm,
      centralizer_le_normalizer _ hc⟩
  have hnorm : I ⊓ normalizer (A : Set G) ≤ normalizer (centralizer (A : Set G) : Set G) :=
    fun g hg => gmh_mem_normalizer_centralizer (mem_inf.mp hg).2
  exact (he.of_le hS₀N inf_le_left).inf_of_le_normalizer hCA hnorm


theorem gmh_conj_mem_F {g : G} (hgU : g ∈ normalizer (U₁ : Set G))
    (hgv : g * (t * w) = (t * w) * g) {a : G} (ha : a ∈ U₁ ⊓ centralizer ({t * w} : Set G)) :
    g * a * g⁻¹ ∈ U₁ ⊓ centralizer ({t * w} : Set G) := by
  refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hgU a).mp (mem_inf.mp ha).1,
    mem_centralizer_singleton_iff.mpr ?_⟩
  have hav : a * (t * w) = (t * w) * a := mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2
  have hgv' : g⁻¹ * (t * w) = (t * w) * g⁻¹ := by
    calc g⁻¹ * (t * w) = g⁻¹ * ((t * w) * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * (t * w)) * g⁻¹ := by rw [hgv]
      _ = (t * w) * g⁻¹ := by group
  calc g * a * g⁻¹ * (t * w) = g * (a * (t * w)) * g⁻¹ := by rw [mul_assoc (g * a), hgv']; group
    _ = (t * w) * (g * a * g⁻¹) := by rw [hav, ← mul_assoc, hgv]; group

theorem gmh_exists_comm_sq_ne {e : G} (heT : e ∈ normalizer (szT₁ L T : Set G))
    (hev : e * (t * w) = (t * w) * e)
    (hefix : ∀ a ∈ szA₁ (szT₁ L T), e * a * e⁻¹ = a → a = 1) :
    ∃ y ∈ U₁, y ∈ centralizer ((U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) : Set G) ∧
      y ∈ normalizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
        Set G) ∧ (y * e * y⁻¹ * e⁻¹) ^ 2 ≠ 1 := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W', hW'T₁, -, -, hW'ab, hW'inv, hW'sq, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  obtain ⟨hAmem, -, -⟩ := hW.gmh_A_facts
  have h2 : 2 < Nat.card (szA₁ (szT₁ L T)) := by
    rw [hA₁card]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  obtain ⟨a, ha, -, -, ha1, -, -⟩ := exists_two_ne_one h2
  obtain ⟨y, hyW, hyy⟩ := hW'sq a ha
  have hyT₁ : y ∈ szT₁ L T := hW'T₁ hyW
  have hWVN : W' ≤ normalizer (V : Set G) := fun z hz => hL.muOne_T₁_le_normalizer hS (hW'T₁ hz)
  have hyF : y ∈ centralizer ((U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hWVN (hW.F_le hW'iff hx)
    have c1 : a₁ * y = y * a₁ := hW'ab a₁ ha₁ y hyW
    have c2 : a₂ * y = y * a₂ := (hL.muOne_T₁_comm hS hyT₁ ha₂).symm
    calc a₁ * a₂ * y = a₁ * (y * a₂) := by rw [mul_assoc, c2]
      _ = y * (a₁ * a₂) := by rw [← mul_assoc, c1, mul_assoc]
  have hyv : y * (t * w) * y⁻¹ = (y * y) * (t * w) := by
    have h1 := hW'inv y hyW
    calc y * (t * w) * y⁻¹ = y * ((t * w) * y * (t * w)⁻¹)⁻¹ * (t * w) := by group
      _ = (y * y) * (t * w) := by rw [h1, inv_inv]
  have hA₁F := hW.gmh_szA₁_le_F
  have hyN : y ∈ normalizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) :
      Subgroup G) : Set G) := by
    apply gmh_mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨b, hb, h1 | h1⟩ := hAmem x hx <;> rw [h1]
    · rw [← mem_centralizer_iff.mp hyF b hb, mul_inv_cancel_right]
      exact mem_sup_left hb
    · rw [show y * (b * (t * w)) * y⁻¹ = (y * b * y⁻¹) * (y * (t * w) * y⁻¹) by group, hyv,
        ← mem_centralizer_iff.mp hyF b hb, mul_inv_cancel_right]
      exact mul_mem (mem_sup_left hb) (mul_mem (mem_sup_left (hA₁F (by rw [hyy]; exact ha)))
        (mem_sup_right (mem_zpowers _)))
  have heA₁ : ∀ z ∈ szA₁ (szT₁ L T), e * z * e⁻¹ ∈ szA₁ (szT₁ L T) := fun z hz =>
    U3RootCoords.conj_mem_szA₁_of_mem_normalizer heT hz
  have heW : ∀ z ∈ W', e * z * e⁻¹ ∈ W' := by
    intro z hz
    have hzT := hW'T₁ hz
    have hezT : e * z * e⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp heT z).mp hzT
    refine (hW'iff _ hezT).mp ?_
    have h1 : e⁻¹ * (t * w) * e = t * w := by rw [mul_assoc, ← hev, inv_mul_cancel_left]
    have h2 : e⁻¹ * (t * w)⁻¹ = (t * w)⁻¹ * e⁻¹ := by
      calc e⁻¹ * (t * w)⁻¹ = ((t * w) * e)⁻¹ := by group
        _ = (e * (t * w))⁻¹ := by rw [hev]
        _ = (t * w)⁻¹ * e⁻¹ := by group
    rw [show (e * z * e⁻¹)⁻¹ * ((t * w) * (e * z * e⁻¹) * (t * w)⁻¹) =
      e * z⁻¹ * (e⁻¹ * (t * w) * e) * z * (e⁻¹ * (t * w)⁻¹) by group, h1, h2,
      show e * z⁻¹ * (t * w) * z * ((t * w)⁻¹ * e⁻¹) =
        e * (z⁻¹ * ((t * w) * z * (t * w)⁻¹)) * e⁻¹ by group]
    exact heA₁ _ ((hW'iff z hzT).mpr hz)
  refine ⟨y, hW.T₁_le_U₁ hyT₁, hyF, hyN, fun hsq => ha1 (hefix a ha ?_)⟩
  have hz : e * y⁻¹ * e⁻¹ ∈ W' := heW _ (inv_mem hyW)
  have hcomm : Commute y (e * y⁻¹ * e⁻¹) := hW'ab y hyW _ hz
  have hy2 : y ^ 2 = a := by rw [sq, hyy]
  have hz2 : (e * y⁻¹ * e⁻¹) ^ 2 = e * a⁻¹ * e⁻¹ := by rw [conj_pow, inv_pow, hy2]
  rw [show y * e * y⁻¹ * e⁻¹ = y * (e * y⁻¹ * e⁻¹) by group, hcomm.mul_pow, hy2, hz2] at hsq
  have h3 : e * a⁻¹ * e⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_right hsq
  calc e * a * e⁻¹ = (e * a⁻¹ * e⁻¹)⁻¹ := by group
    _ = a := by rw [h3, inv_inv]

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
