module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterSwapTPos

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapTwo

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapTwo G L f t T R₂ D d V U U₁ w s P)
include hW

theorem inf_le_of_not_mem {x : G} (hxS₂ : x ∈ swapS₂ P U T) (hxS : x ∉ U ⊔ T) {h : G}
    (hhS : h ∈ U ⊔ T) (hhx : h * x = x * h) : h ∈ U₁ ⊔ zpowers (t * w) := by
  obtain ⟨hxtw, hxwt⟩ := hW.conj_of_not_mem hxS₂ hxS
  have hconj : x * h * x⁻¹ = h := by rw [← hhx]; group
  have hxu : ∀ u ∈ U₁, x * u * x⁻¹ ∈ U₁ := fun u hu => hW.conj_U₁ hxS₂ hu
  have htw : t * w⁻¹ ∉ U₁ := hW.not_mem_U₁_of_mem_T (mul_mem hW.t_mem (inv_mem hW.w_mem))
    hW.t_mul_w_inv_not_mem_T₁
  rcases hW.mem_U₁_cases hhS with h1 | h1 | h1 | h1
  · exact mem_sup_left h1
  · exfalso
    have h2 : h * w⁻¹ ∈ U₁ := by
      have e : x * (h * t⁻¹) * x⁻¹ * (x * t * x⁻¹ * w⁻¹) = h * w⁻¹ := by
        rw [show x * (h * t⁻¹) * x⁻¹ * (x * t * x⁻¹ * w⁻¹) = (x * h * x⁻¹) * w⁻¹ by group,
          hconj]
      rw [← e]
      exact mul_mem (hxu _ h1) hxtw
    apply htw
    rw [show t * w⁻¹ = (h * t⁻¹)⁻¹ * (h * w⁻¹) by group]
    exact mul_mem (inv_mem h1) h2
  · exfalso
    have h2 : h * t⁻¹ ∈ U₁ := by
      have e : x * (h * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * t⁻¹) = h * t⁻¹ := by
        rw [show x * (h * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * t⁻¹) = (x * h * x⁻¹) * t⁻¹ by group,
          hconj]
      rw [← e]
      exact mul_mem (hxu _ h1) hxwt
    apply htw
    rw [show t * w⁻¹ = (h * t⁻¹)⁻¹ * (h * w⁻¹) by group]
    exact mul_mem (inv_mem h2) h1
  · rw [show h = (h * (t * w)⁻¹) * (t * w) by group]
    exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers _))

theorem card_inf_ge_of_not_mem {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T)
    (hxS : c * t * c⁻¹ ∉ U ⊔ T) :
    (2 ^ f) ^ 3 ≤ Nat.card (U₁ ⊓ T.map (MulAut.conj c).toMonoidHom : Subgroup G) := by
  have hL := hW.level
  set H := T.map (MulAut.conj c).toMonoidHom with hHdef
  have hHS := hW.map_le hcT
  have hxH : c * t * c⁻¹ ∈ H := ⟨t, hW.t_mem, by simp⟩
  have hstep1 : (U ⊔ T) ⊓ H ≤ U₁ ⊔ zpowers (t * w) := fun h hh =>
    hW.inf_le_of_not_mem (hHS hxH) hxS (mem_inf.mp hh).1
      (hW.commute_of_mem_map (mem_inf.mp hh).2)
  have e1 := relIndex_mul_card (H := U ⊔ T) (K := H)
  rw [hW.card_map c] at e1
  have r1 := Subgroup.relIndex_le_of_le_right hHS (by rw [hW.relIndex_SU_S₂]; norm_num)
  rw [hW.relIndex_SU_S₂] at r1
  have e2 := relIndex_mul_card (H := U₁) (K := (U ⊔ T) ⊓ H)
  have htwT : t * w ∈ T := mul_mem hW.t_mem hW.w_mem
  have htwN : t * w ∈ normalizer (U₁ : Set G) := hL.T_le htwT
  have htwU : t * w ∉ U₁ := hW.not_mem_U₁_of_mem_T htwT hW.tw_not_mem_T₁
  have htw2 : t * w * (t * w) = 1 := by
    rw [← sq, Commute.mul_pow hW.wt_comm.symm 2, hW.step.start.sq_eq_one, hW.w_sq, one_mul]
  have r2' := RankOne.Endings.relIndex_sup_zpowers_eq_two htwU htwN htw2
  have r2 := Subgroup.relIndex_le_of_le_right hstep1 (by rw [r2']; norm_num)
  rw [r2'] at r2
  have hsub : U₁ ⊓ ((U ⊔ T) ⊓ H) ≤ U₁ ⊓ H := inf_le_inf_left _ inf_le_right
  have c3 := Subgroup.card_le_of_le hsub
  have h4 : 4 * (2 ^ f) ^ 3 ≤ 4 * Nat.card (U₁ ⊓ H : Subgroup G) := by
    calc 4 * (2 ^ f) ^ 3 = (U ⊔ T).relIndex H * Nat.card ((U ⊔ T) ⊓ H : Subgroup G) := e1.symm
      _ ≤ 2 * Nat.card ((U ⊔ T) ⊓ H : Subgroup G) := Nat.mul_le_mul_right _ r1
      _ = 2 * (U₁.relIndex ((U ⊔ T) ⊓ H) * Nat.card (U₁ ⊓ ((U ⊔ T) ⊓ H) : Subgroup G)) := by
          rw [e2]
      _ ≤ 2 * (2 * Nat.card (U₁ ⊓ H : Subgroup G)) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul r2 c3)
      _ = 4 * Nat.card (U₁ ⊓ H : Subgroup G) := by ring
  omega

theorem false_of_conj_not_mem {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T)
    (hxS : c * t * c⁻¹ ∉ U ⊔ T) : False := by
  have hS := hW.step
  have hL := hW.level
  obtain ⟨hT₁card, hA₁card, -, -, -, hA₁2, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  set x := c * t * c⁻¹ with hxdef
  set H := T.map (MulAut.conj c).toMonoidHom with hHdef
  have hHS := hW.map_le hcT
  have hxH : x ∈ H := ⟨t, hW.t_mem, by simp [hxdef]⟩
  have hxS₂ : x ∈ swapS₂ P U T := hHS hxH
  have htt : t * t = 1 := by rw [← sq, hS.start.sq_eq_one]
  have hxx : x * x = 1 := by
    rw [hxdef, show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  have hVU₁ : V ≤ U₁ := le_sup_right.trans hL.sup_le_U₁
  have hxU₁ : x ∉ U₁ := fun h' => hxS (mem_sup_left (hL.U₁_le h'))
  have hN := hW.card_inf_ge_of_not_mem hcT hxS
  obtain ⟨c₁, hc₁T, hc₁⟩ := hL.norm_exists_conj hS hW.mu hW.w_mem hW.w_sq hW.w_not_mem
    hW.w_cent hW.isPGroup hW.le (mem_swapS₂.mp hxS₂).2 (mem_swapS₂.mp hxS₂).1 hxS
  have hxt : x * t * x⁻¹ = c₁⁻¹ * w * c₁ := by rw [← hc₁]; group
  have hT₁C : ∀ y ∈ szT₁ L T, y * x = x * y → y ∈ szA₁ (szT₁ L T) := by
    intro y hy hyx
    have hyt : y * t = t * y :=
      mem_centralizer_singleton_iff.mp (hS.start.le (szT₁_le_left L T hy))
    have hyx' : y * x⁻¹ = x⁻¹ * y := (Commute.inv_right (show Commute y x from hyx)).eq
    have h1 : y * (x * t * x⁻¹) = (x * t * x⁻¹) * y := by
      calc y * (x * t * x⁻¹) = (y * x) * t * x⁻¹ := by group
        _ = x * (y * t) * x⁻¹ := by rw [hyx]; group
        _ = x * t * (y * x⁻¹) := by rw [hyt]; group
        _ = (x * t * x⁻¹) * y := by rw [hyx']; group
    have hcy : c₁ * y * c₁⁻¹ ∈ szT₁ L T := mul_mem (mul_mem hc₁T hy) (inv_mem hc₁T)
    have h2 : w * (c₁ * y * c₁⁻¹) = (c₁ * y * c₁⁻¹) * w := by
      rw [← hc₁]
      calc c₁ * (x * t * x⁻¹) * c₁⁻¹ * (c₁ * y * c₁⁻¹) =
            c₁ * ((x * t * x⁻¹) * y) * c₁⁻¹ := by group
        _ = c₁ * (y * (x * t * x⁻¹)) * c₁⁻¹ := by rw [h1]
        _ = c₁ * y * c₁⁻¹ * (c₁ * (x * t * x⁻¹) * c₁⁻¹) := by group
    have h3 := (hS.start.outer_facts_of_card_sylow hS.card_sylow hW.w_mem hW.w_sq
      hW.w_not_mem).2.2.1 _ hcy h2
    have h4 := U3RootCoords.conj_mem_szA₁_of_mem_normalizer
      (Subgroup.le_normalizer (inv_mem hc₁T)) h3
    rwa [show c₁⁻¹ * (c₁ * y * c₁⁻¹) * c₁⁻¹⁻¹ = y by group] at h4
  have hA₁x : ∀ a ∈ szA₁ (szT₁ L T), a * x = x * a := by
    set N' := U₁ ⊓ H with hN'def
    have e1 := relIndex_mul_card (H := szT₁ L T) (K := N')
    have e2 := relIndex_mul_card (H := szT₁ L T) (K := U₁)
    rw [inf_of_le_left hW.T₁_le_U₁, hT₁card, hL.muOne_card_U₁ hS] at e2
    have hq2 : (szT₁ L T).relIndex U₁ = (2 ^ f) ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hq0 3)
      rw [e2]
      ring
    have r := Subgroup.relIndex_le_of_le_right (inf_le_left : N' ≤ U₁)
      (by rw [hq2]; positivity)
    rw [hq2] at r
    have hle : szT₁ L T ⊓ N' ≤ szA₁ (szT₁ L T) := fun y hy =>
      hT₁C y (mem_inf.mp hy).1 (hW.commute_of_mem_map (mem_inf.mp (mem_inf.mp hy).2).2)
    have hge : 2 ^ f ≤ Nat.card (szT₁ L T ⊓ N' : Subgroup G) := by
      by_contra hlt
      push Not at hlt
      have h5 : Nat.card N' < (2 ^ f) ^ 2 * 2 ^ f := by
        rw [← e1]
        calc (szT₁ L T).relIndex N' * Nat.card (szT₁ L T ⊓ N' : Subgroup G) ≤
              (2 ^ f) ^ 2 * Nat.card (szT₁ L T ⊓ N' : Subgroup G) := Nat.mul_le_mul_right _ r
          _ < (2 ^ f) ^ 2 * 2 ^ f := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
      have h6 : (2 ^ f) ^ 2 * 2 ^ f = (2 ^ f) ^ 3 := by ring
      omega
    have heq : szT₁ L T ⊓ N' = szA₁ (szT₁ L T) :=
      eq_of_le_of_card_ge hle (by rw [hA₁card]; exact hge)
    intro a ha
    rw [← heq] at ha
    exact hW.commute_of_mem_map (mem_inf.mp (mem_inf.mp ha).2).2
  have hw'V : ∀ r ∈ V, (x * t * x⁻¹) * r = r * (x * t * x⁻¹) := by
    intro r hr
    have hc₁r : Commute c₁ r := hL.muOne_T₁_comm hS hc₁T hr
    have hwr : w * r = r * w := by
      have e := hW.w_cent r hr
      calc w * r = w * r * w⁻¹ * w := by group
        _ = r * w := by rw [e]
    rw [hxt]
    calc c₁⁻¹ * w * c₁ * r = c₁⁻¹ * w * (c₁ * r) := by group
      _ = c₁⁻¹ * (w * r) * c₁ := by rw [hc₁r.eq]; group
      _ = (c₁⁻¹ * r) * w * c₁ := by rw [hwr]; group
      _ = r * (c₁⁻¹ * w * c₁) := by rw [hc₁r.inv_left.eq]; group
  have et : x * (x * t * x⁻¹) * x⁻¹ = t := by
    rw [show x * (x * t * x⁻¹) * x⁻¹ = (x * x) * t * (x * x)⁻¹ by group, hxx]
    group
  have hxV : ∀ r ∈ V, x * r * x⁻¹ ∈ szT₁ L T := by
    intro r hr
    have h1 : x * r * x⁻¹ ∈ U₁ := hW.conj_U₁ hxS₂ (hVU₁ hr)
    have h2 : x * r * x⁻¹ * t = t * (x * r * x⁻¹) := by
      calc x * r * x⁻¹ * t = x * r * x⁻¹ * (x * (x * t * x⁻¹) * x⁻¹) := by rw [et]
        _ = x * (r * (x * t * x⁻¹)) * x⁻¹ := by group
        _ = x * ((x * t * x⁻¹) * r) * x⁻¹ := by rw [hw'V r hr]
        _ = (x * (x * t * x⁻¹) * x⁻¹) * (x * r * x⁻¹) := by group
        _ = t * (x * r * x⁻¹) := by rw [et]
    have h3 : x * r * x⁻¹ ∈ U ⊓ centralizer ({t} : Set G) :=
      mem_inf.mpr ⟨hL.U₁_le h1, mem_centralizer_singleton_iff.mpr h2⟩
    rw [hL.inf_centralizer] at h3
    exact hL.muOne_mem_T₁_of_mem_T hS h1
      ((sup_le (szT₁_le_left L T) (zpowers_le.mpr hW.t_mem)) h3)
  have key : ∀ a ∈ V, ∀ b ∈ V,
      a * b * (x * (a * b) * x⁻¹) = a * (x * a * x⁻¹) * (b * (x * b * x⁻¹)) := by
    intro a ha b hb
    have hab : (x * a * x⁻¹) * b = b * (x * a * x⁻¹) := hL.muOne_T₁_comm hS (hxV a ha) hb
    calc a * b * (x * (a * b) * x⁻¹) = a * (b * (x * a * x⁻¹)) * (x * b * x⁻¹) := by group
      _ = a * ((x * a * x⁻¹) * b) * (x * b * x⁻¹) := by rw [hab]
      _ = a * (x * a * x⁻¹) * (b * (x * b * x⁻¹)) := by group
  let φ : V →* G := MonoidHom.mk' (fun r => (r : G) * (x * r * x⁻¹)) (fun a b => by
    simp only [Subgroup.coe_mul]
    exact key a a.2 b b.2)
  have hφ : ∀ r : V, φ r = (r : G) * (x * r * x⁻¹) := fun r => rfl
  have hφU : ∀ r : V, φ r ∈ U₁ := fun r => by
    rw [hφ]
    exact mul_mem (hVU₁ r.2) (hW.T₁_le_U₁ (hxV r r.2))
  have hφx : ∀ r : V, φ r * x = x * φ r := by
    intro r
    have hcomm : (x * r * x⁻¹) * (r : G) = r * (x * r * x⁻¹) := hL.muOne_T₁_comm hS (hxV r r.2) r.2
    have e1 : x * φ r * x⁻¹ = φ r := by
      rw [hφ, show x * ((r : G) * (x * r * x⁻¹)) * x⁻¹ =
        (x * r * x⁻¹) * ((x * x) * r * (x * x)⁻¹) by group, hxx]
      rw [show (1 : G) * r * 1⁻¹ = r by group]
      exact hcomm
    calc φ r * x = (x * φ r * x⁻¹) * x := by rw [e1]
      _ = x * φ r := by group
  have hφ2 : ∀ r : V, φ r ^ 2 = 1 := by
    intro r
    rw [hφ]
    have hcomm : Commute (r : G) (x * r * x⁻¹) :=
      (hL.muOne_T₁_comm hS (hxV r r.2) r.2).symm
    rw [hcomm.mul_pow]
    have hr2 : (r : G) ^ 2 ∈ szA₁ (szT₁ L T) := hL.muOne_sq_mem_szA₁_of_mem_V hS r.2
    have e : (x * r * x⁻¹) ^ 2 = (r : G) ^ 2 := by
      rw [conj_pow]
      have h1 := hA₁x _ hr2
      calc x * (r : G) ^ 2 * x⁻¹ = ((r : G) ^ 2 * x) * x⁻¹ := by rw [h1]
        _ = (r : G) ^ 2 := by group
    rw [e, ← pow_add]
    have h4 : (r : G) ^ 4 = 1 := by simpa using hS.conf.pow r r.2
    exact h4
  have hker : ∀ r : V, φ r = 1 → (r : G) ∈ szA₁ (szT₁ L T) := by
    intro r hr1
    rw [hφ] at hr1
    have e : x * r * x⁻¹ = (r : G)⁻¹ := by
      calc x * r * x⁻¹ = (r : G)⁻¹ * (r * (x * r * x⁻¹)) := by group
        _ = (r : G)⁻¹ := by rw [hr1, mul_one]
    have hrT : (r : G) ∈ szT₁ L T := by
      have h1 := hxV r r.2
      rw [e] at h1
      simpa using inv_mem h1
    exact mem_szA₁.mpr ⟨hrT, hS.conf.le_centralizer r.2⟩
  have hkercard : Nat.card φ.ker ≤ 2 ^ f := by
    rw [← hA₁card]
    refine Nat.card_le_card_of_injective (fun k : φ.ker =>
      (⟨((k : V) : G), hker k (MonoidHom.mem_ker.mp k.2)⟩ : szA₁ (szT₁ L T))) ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  set R := φ.range with hRdef
  have hRcard : 2 ^ f ≤ Nat.card R := by
    have h7 := card_mul_index φ.ker
    rw [Subgroup.index_ker, hS.conf.card] at h7
    by_contra hlt
    push Not at hlt
    have h8 : Nat.card φ.ker * Nat.card φ.range < 2 ^ f * 2 ^ f :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hkercard) (Nat.mul_lt_mul_of_pos_left hlt hq0)
    rw [h7, show 2 ^ f * 2 ^ f = (2 ^ f) ^ (1 + 1) by ring] at h8
    exact lt_irrefl _ h8
  have hRA : R ⊓ szA₁ (szT₁ L T) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨r, rfl⟩, he⟩
    rw [mem_bot]
    change φ r ∈ szA₁ (szT₁ L T) at he
    rw [hφ] at he ⊢
    have hrT : (r : G) ∈ szT₁ L T := by
      rw [show (r : G) = ((r : G) * (x * r * x⁻¹)) * (x * r * x⁻¹)⁻¹ by group]
      exact mul_mem (szA₁_le _ he) (inv_mem (hxV r r.2))
    have hrA : (r : G) ∈ szA₁ (szT₁ L T) := mem_szA₁.mpr ⟨hrT, hS.conf.le_centralizer r.2⟩
    have e1 : x * r * x⁻¹ = (r : G) := by
      have h1 := hA₁x _ hrA
      calc x * r * x⁻¹ = ((r : G) * x) * x⁻¹ := by rw [h1]
        _ = r := by group
    rw [e1, ← sq]
    exact hA₁2 _ hrA
  have hRU : R ≤ U₁ := by
    rintro _ ⟨r, rfl⟩
    exact hφU r
  have hAR : ∀ a ∈ szA₁ (szT₁ L T), ∀ e ∈ R, a * e = e * a := by
    intro a ha e he
    have h1 := hL.conj_szA₁ e (hL.U₁_le (hRU he)) a ha
    calc a * e = (e * a * e⁻¹) * e := by rw [h1]
      _ = e * a := by group
  have hAN : szA₁ (szT₁ L T) ≤ normalizer (R : Set G) := fun a ha =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun e he => by
      rw [show a⁻¹ * e * a = e by
        calc a⁻¹ * e * a = a⁻¹ * (e * a) := by group
          _ = a⁻¹ * (a * e) := by rw [hAR a ha e he]
          _ = e := by group]
      exact he
  set E := szA₁ (szT₁ L T) ⊔ R with hEdef
  have hEcard : (2 ^ f) ^ 2 ≤ Nat.card E := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := R) (B := szA₁ (szT₁ L T)) hAN
    rw [hRA, card_bot, mul_one, sup_comm, hA₁card] at h1
    rw [h1, sq]
    exact Nat.mul_le_mul_right _ hRcard
  have hEmem : ∀ e ∈ E, e ∈ U₁ ∧ e ^ 2 = 1 ∧ e * x = x * e := by
    intro e he
    obtain ⟨a, ha, ρ, hρ, rfl⟩ := ncyc_exists_mul_of_mem_sup hAN he
    obtain ⟨r, rfl⟩ := hρ
    have haρ : Commute a (φ r) := hAR a ha (φ r) ⟨r, rfl⟩
    refine ⟨mul_mem (hW.T₁_le_U₁ (szA₁_le _ ha)) (hφU r), ?_, ?_⟩
    · rw [haρ.mul_pow, hA₁2 a ha, hφ2 r, one_mul]
    · calc a * φ r * x = a * (φ r * x) := by group
        _ = a * (x * φ r) := by rw [hφx r]
        _ = (a * x) * φ r := by group
        _ = (x * a) * φ r := by rw [hA₁x a ha]
        _ = x * (a * φ r) := by group
  have hxE : x ∉ E := fun h' => hxU₁ (hEmem x h').1
  have hxN : x ∈ normalizer (E : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun e he => by
      have hex := (hEmem e he).2.2
      rw [show x⁻¹ * e * x = e by
        calc x⁻¹ * e * x = x⁻¹ * (e * x) := by group
          _ = x⁻¹ * (x * e) := by rw [hex]
          _ = e := by group]
      exact he
  have hB2 := RankOne.Endings.relIndex_sup_zpowers_eq_two hxE hxN hxx
  have hBcard := relIndex_mul_card (H := E) (K := E ⊔ zpowers x)
  rw [hB2, inf_of_le_left le_sup_left] at hBcard
  set B := zpowers x ⊔ E with hBdef
  have hBeq : E ⊔ zpowers x = B := sup_comm _ _
  rw [hBeq] at hBcard
  have hx2' : x ^ 2 = 1 := by rw [sq]; exact hxx
  have hBsq : ∀ b ∈ B, b ^ 2 = 1 := by
    intro b hb
    obtain ⟨a, ha, e, he, rfl⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr hxN) hb
    have hae : a * e = e * a := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (Commute.symm (hEmem e he).2.2) k).eq
    rw [Commute.mul_pow hae 2, (hEmem e he).2.1, mul_one]
    rcases mem_zpowers_involution_eq_one_or_eq hx2' ha with h1 | h1
    · rw [h1]; exact one_pow 2
    · rw [h1]; exact hx2'
  have hBC : B ≤ centralizer ({x} : Set G) := sup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    (fun e he => mem_centralizer_singleton_iff.mpr (hEmem e he).2.2)
  set B' : Subgroup G := B.map (MulAut.conj c⁻¹).toMonoidHom with hB'def
  have hB'card : Nat.card B' = Nat.card B := card_map_of_injective (MulAut.conj c⁻¹).injective
  have hB'C : B' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hbx := mem_centralizer_singleton_iff.mp (hBC hb)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * b * c * t = c⁻¹ * (b * x) * c := by rw [hxdef]; group
      _ = c⁻¹ * (x * b) * c := by rw [hbx]
      _ = t * (c⁻¹ * b * c) := by rw [hxdef]; group
  have hB'2 : ∀ y ∈ B', y ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show (c⁻¹ * b * c) ^ 2 = c⁻¹ * b ^ 2 * c by rw [sq, sq]; group, hBsq b hb]
    group
  have hlt := hS.start.card_lt_of_sq_eq_one_of_card_sylow hS.card_sylow hB'C hB'2
  rw [hB'card, ← hBcard] at hlt
  omega

theorem conj_mem_cases {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T) :
    c * t * c⁻¹ * t⁻¹ ∈ U₁ ∨ c * t * c⁻¹ * w⁻¹ ∈ U₁ := by
  by_cases hxS : c * t * c⁻¹ ∈ U ⊔ T
  · rcases hW.mem_U₁_cases hxS with h1 | h1 | h1 | h1
    · exact (hW.false_of_conj_mem_U₁ hcT h1).elim
    · exact Or.inl h1
    · exact Or.inr h1
    · exact (hW.false_of_conj_mem_tw hcT h1).elim
  · exact (hW.false_of_conj_not_mem hcT hxS).elim

end U3C1OuterSwapTwo

end CFSG.SeitzReduction.RankOne
