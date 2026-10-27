module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem sup_V_comm {W : Subgroup G} (hWT₁ : W ≤ szT₁ L T)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : ∀ a ∈ W ⊔ V, ∀ b ∈ W ⊔ V, a * b = b * a := by
  have hS := hW.step
  have hL := hW.level
  have hWVN : W ≤ normalizer (V : Set G) := fun y hy => hL.muOne_T₁_le_normalizer hS (hWT₁ hy)
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hWVN ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hWVN hb
  have c1 : a₁ * b₂ = b₂ * a₁ := hL.muOne_T₁_comm hS (hWT₁ ha₁) hb₂
  have c2 : a₂ * b₁ = b₁ * a₂ := (hL.muOne_T₁_comm hS (hWT₁ hb₁) ha₂).symm
  have c3 : a₁ * b₁ = b₁ * a₁ := hWab a₁ ha₁ b₁ hb₁
  have c4 : a₂ * b₂ = b₂ * a₂ := hS.conf.comm a₂ ha₂ b₂ hb₂
  calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
    _ = a₁ * (b₁ * a₂) * b₂ := by rw [c2]
    _ = (a₁ * b₁) * (a₂ * b₂) := by group
    _ = (b₁ * a₁) * (b₂ * a₂) := by rw [c3, c4]
    _ = b₁ * (a₁ * b₂) * a₂ := by group
    _ = b₁ * (b₂ * a₁) * a₂ := by rw [c1]
    _ = b₁ * b₂ * (a₁ * a₂) := by group

theorem F_le {W' : Subgroup G}
    (hW'iff : ∀ y ∈ szT₁ L T,
      (y⁻¹ * ((t * w) * y * (t * w)⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W')) :
    U₁ ⊓ centralizer ({t * w} : Set G) ≤ W' ⊔ V := by
  intro c hc
  obtain ⟨hcU, hcC⟩ := mem_inf.mp hc
  obtain ⟨K, _, _, _, v, μ, hK, hcK, hμ⟩ := hW.step.exists_coords
  exact hW.level.muOne_mem_sup_of_commute_inv hW.step hcK hW.mu hK hμ hW.tw_mem
    (fun r hr => hW.tw_inv hr) hW'iff (x := t * w) (by rw [mul_inv_cancel]; exact one_mem _) hcU
    (mem_centralizer_singleton_iff.mp hcC)

theorem F_sq {c : G} (hc : c ∈ U₁ ⊓ centralizer ({t * w} : Set G)) : c ^ 2 = 1 := by
  have h := hW.step.start
  obtain ⟨W', hW'T₁, -, -, hW'ab, hW'inv, -, hW'iff⟩ :=
    h.exists_W_of_card_sylow hW.step.card_sylow hW.tw_mem hW.tw_sq hW.tw_not_mem
  have hcE := hW.F_le hW'iff hc
  have hWVN : W' ≤ normalizer (V : Set G) := fun y hy =>
    hW.level.muOne_T₁_le_normalizer hW.step (hW'T₁ hy)
  obtain ⟨a₁, ha₁, a₂, ha₂, hae⟩ := ncyc_exists_mul_of_mem_sup hWVN hcE
  have hab := hW.sup_V_comm hW'T₁ hW'ab
  have hinv : (t * w) * c * (t * w)⁻¹ = c⁻¹ := by
    rw [← hae, show (t * w) * (a₁ * a₂) * (t * w)⁻¹ =
      ((t * w) * a₁ * (t * w)⁻¹) * ((t * w) * a₂ * (t * w)⁻¹) by group, hW'inv a₁ ha₁,
      hW.tw_inv ha₂, ← mul_inv_rev]
    congr 1
    exact (hab _ (mem_sup_right ha₂) _ (mem_sup_left ha₁))
  have hcomm : c * (t * w) = (t * w) * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
  have hcc : c = c⁻¹ := by
    rw [← hinv, ← hcomm, mul_inv_cancel_right]
  calc c ^ 2 = c * c := sq c
    _ = c * c⁻¹ := by nth_rewrite 2 [hcc]; rfl
    _ = 1 := mul_inv_cancel c

theorem F_comm {a b : G} (ha : a ∈ U₁ ⊓ centralizer ({t * w} : Set G))
    (hb : b ∈ U₁ ⊓ centralizer ({t * w} : Set G)) : a * b = b * a := by
  obtain ⟨W', hW'T₁, -, -, hW'ab, -, -, hW'iff⟩ :=
    hW.step.start.exists_W_of_card_sylow hW.step.card_sylow hW.tw_mem hW.tw_sq hW.tw_not_mem
  exact hW.sup_V_comm hW'T₁ hW'ab a (hW.F_le hW'iff ha) b (hW.F_le hW'iff hb)

theorem card_F : Nat.card (U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) = (2 ^ f) ^ 2 := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨-, hA₁card, -, hsqT₁, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W', hW'T₁, hAW', hW'card, hW'ab, hW'inv, hW'sq, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  set E := W' ⊔ V with hEdef
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hFdef
  have hab := hW.sup_V_comm hW'T₁ hW'ab
  have hWVN : W' ≤ normalizer (V : Set G) := fun y hy => hL.muOne_T₁_le_normalizer hS (hW'T₁ hy)
  have hVU₁ : V ≤ U₁ := le_sup_right.trans hL.sup_le_U₁
  have hEU₁ : E ≤ U₁ := sup_le (hW'T₁.trans hW.T₁_le_U₁) hVU₁
  have hFE : F ≤ E := hW.F_le hW'iff
  have hEcard : Nat.card E = (2 ^ f) ^ 3 := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := V) (B := W') hWVN
    have hinf : V ⊓ W' = szA₁ (szT₁ L T) := le_antisymm
      (fun z hz => mem_szA₁.mpr ⟨hW'T₁ (mem_inf.mp hz).2,
        hS.conf.le_centralizer (mem_inf.mp hz).1⟩)
      (le_inf hS.conf.le hAW')
    rw [hinf, hA₁card, hS.conf.card, hW'card, sup_comm] at h1
    apply Nat.eq_of_mul_eq_mul_right hq0
    rw [h1]
    ring
  have hinvE : ∀ c ∈ E, (t * w) * c * (t * w)⁻¹ = c⁻¹ := by
    intro c hc
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hWVN hc
    rw [show (t * w) * (a₁ * a₂) * (t * w)⁻¹ =
      ((t * w) * a₁ * (t * w)⁻¹) * ((t * w) * a₂ * (t * w)⁻¹) by group, hW'inv a₁ ha₁,
      hW.tw_inv ha₂, ← mul_inv_rev]
    congr 1
    exact hab _ (mem_sup_right ha₂) _ (mem_sup_left ha₁)
  let φ : E →* E := MonoidHom.mk' (fun x => x ^ 2) (fun a b => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
    exact (show Commute (a : G) (b : G) from hab a a.2 b b.2).mul_pow 2)
  have hφ : ∀ x : E, ((φ x : E) : G) = (x : G) ^ 2 := fun x => by
    simp [φ]
  have hker : φ.ker = F.subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hx
      have hx2 : (x : G) ^ 2 = 1 := by
        rw [← hφ x, hx]
        rfl
      have hxx : (x : G)⁻¹ = x := by
        rw [inv_eq_iff_mul_eq_one, ← sq, hx2]
      refine mem_inf.mpr ⟨hEU₁ x.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have e := hinvE x x.2
      rw [hxx] at e
      calc (x : G) * (t * w) = (t * w) * x * (t * w)⁻¹ * (t * w) := by rw [e]
        _ = (t * w) * x := by group
    · intro hx
      exact Subtype.ext ((hφ x).trans (hW.F_sq hx))
  have hrange : Nat.card φ.range = 2 ^ f := by
    have hmap : φ.range.map E.subtype = szA₁ (szT₁ L T) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        change ((φ x : E) : G) ∈ _
        rw [hφ]
        obtain ⟨a₁, ha₁, a₂, ha₂, hae⟩ := ncyc_exists_mul_of_mem_sup hWVN x.2
        rw [← hae, (show Commute a₁ a₂ from hab _ (mem_sup_left ha₁) _ (mem_sup_right ha₂)).mul_pow]
        exact mul_mem (hsqT₁ a₁ (hW'T₁ ha₁)) (hL.muOne_sq_mem_szA₁_of_mem_V hS ha₂)
      · intro hz
        obtain ⟨y, hyW, hyy⟩ := hW'sq z hz
        refine ⟨φ ⟨y, mem_sup_left hyW⟩, ⟨_, rfl⟩, ?_⟩
        change ((φ ⟨y, mem_sup_left hyW⟩ : E) : G) = z
        rw [hφ, sq]
        exact hyy
    rw [← hA₁card, ← hmap, card_map_of_injective E.subtype_injective]
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, hEcard, hker,
    Nat.card_congr (subgroupOfEquivOfLe hFE).toEquiv] at hcard
  apply Nat.eq_of_mul_eq_mul_right hq0
  rw [hcard]
  ring

theorem not_conj_mem_F_sup (g : G) :
    g * t * g⁻¹ ∉ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) := by
  intro hx
  have hS := hW.step
  have h := hS.start
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hFdef
  set x := g * t * g⁻¹ with hxdef
  have htw2 : (t * w) * (t * w) = 1 := by rw [← sq]; exact hW.tw_sq
  have htwF : t * w ∉ F := fun h' => hW.tw_not_mem (mem_sup_left
    (hW.level.muOne_mem_T₁_of_mem_T hS (mem_inf.mp h').1 hW.tw_mem))
  have htwN : t * w ∈ normalizer (F : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun e he => by
      have hec := mem_centralizer_singleton_iff.mp (mem_inf.mp he).2
      rw [show (t * w)⁻¹ * e * (t * w) = e by
        calc (t * w)⁻¹ * e * (t * w) = (t * w)⁻¹ * (e * (t * w)) := by group
          _ = (t * w)⁻¹ * ((t * w) * e) := by rw [hec]
          _ = e := by group]
      exact he
  set B := F ⊔ zpowers (t * w) with hBdef
  have hBmem : ∀ b ∈ B, ∃ e ∈ zpowers (t * w), ∃ c ∈ F, e * c = b := fun b hb => by
    rw [hBdef, sup_comm] at hb
    exact ncyc_exists_mul_of_mem_sup (zpowers_le.mpr htwN) hb
  have hcommF : ∀ e ∈ zpowers (t * w), ∀ c ∈ F, e * c = c * e := fun e he c hc =>
    (commute_of_mem_zpowers he (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2)).symm
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨e₁, he₁, c₁, hc₁, rfl⟩ := hBmem a ha
    obtain ⟨e₂, he₂, c₂, hc₂, rfl⟩ := hBmem b hb
    have h1 : e₁ * e₂ = e₂ * e₁ := by
      obtain ⟨k₁, rfl⟩ := mem_zpowers_iff.mp he₁
      obtain ⟨k₂, rfl⟩ := mem_zpowers_iff.mp he₂
      rw [← zpow_add, ← zpow_add, add_comm]
    calc e₁ * c₁ * (e₂ * c₂) = e₁ * (c₁ * e₂) * c₂ := by group
      _ = e₁ * (e₂ * c₁) * c₂ := by rw [hcommF e₂ he₂ c₁ hc₁]
      _ = (e₁ * e₂) * (c₁ * c₂) := by group
      _ = (e₂ * e₁) * (c₂ * c₁) := by rw [h1, hW.F_comm hc₁ hc₂]
      _ = e₂ * (e₁ * c₂) * c₁ := by group
      _ = e₂ * (c₂ * e₁) * c₁ := by rw [hcommF e₁ he₁ c₂ hc₂]
      _ = e₂ * c₂ * (e₁ * c₁) := by group
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    intro b hb
    obtain ⟨e, he, c, hc, rfl⟩ := hBmem b hb
    rw [(show Commute e c from hcommF e he c hc).mul_pow, hW.F_sq hc, mul_one]
    rcases mem_zpowers_involution_eq_one_or_eq hW.tw_sq he with h1 | h1
    · rw [h1, one_pow]
    · rw [h1, hW.tw_sq]
  have hBcard : Nat.card B = 2 * (2 ^ f) ^ 2 := by
    have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two htwF htwN htw2
    have h3 := relIndex_mul_card (H := F) (K := B)
    rw [h2, inf_of_le_left le_sup_left, hW.card_F] at h3
    exact h3.symm
  set B' : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'def
  have hB'card : Nat.card B' = Nat.card B := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB'C : B' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hbx := hBab b hb x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * b * g * t = g⁻¹ * (b * x) * g := by rw [hxdef]; group
      _ = g⁻¹ * (x * b) * g := by rw [hbx]
      _ = t * (g⁻¹ * b * g) := by rw [hxdef]; group
  have hB'2 : ∀ y ∈ B', y ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show (g⁻¹ * b * g) ^ 2 = g⁻¹ * b ^ 2 * g by rw [sq, sq]; group, hB2 b hb]
    group
  have hlt := h.card_lt_of_sq_eq_one_of_card_sylow hS.card_sylow hB'C hB'2
  rw [hB'card, hBcard] at hlt
  exact lt_irrefl _ hlt

theorem conj_t_mem_of_commute_tw (g : G) (hxS : g * t * g⁻¹ ∈ U ⊔ T)
    (hxv : g * t * g⁻¹ * (t * w) = (t * w) * (g * t * g⁻¹)) :
    g * t * g⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) ∨ g * t * g⁻¹ * w⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  set x := g * t * g⁻¹ with hxdef
  have hx2 : x ^ 2 = 1 := by
    rw [hxdef, show (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ by rw [sq, sq]; group, h.sq_eq_one]
    group
  have hcF : ∀ u ∈ U₁, u * (t * w) = (t * w) * u → u ∈ U₁ ⊓ centralizer ({t * w} : Set G) :=
    fun u hu hcomm => mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr hcomm⟩
  have hwt := hW.wt_comm
  have htv : t * (t * w) = (t * w) * t := by rw [mul_assoc t w t, hwt]
  have hwv : w * (t * w) = (t * w) * w := by rw [← mul_assoc, hwt]
  rcases hW.mem_cases hxS with h1 | h1 | h1 | ⟨n, h1⟩
  · exact (hW.not_conj_mem_F_sup g (mem_sup_left (hcF x h1 hxv))).elim
  · left
    have hu2 : (x * t⁻¹ * t) ^ 2 = 1 := by rw [inv_mul_cancel_right]; exact hx2
    have huV : x * t⁻¹ ∈ V := hL.muOne_mem_V_of_sq_eq_one hS hc hW.mu hK hμ h1 hu2
    have hucomm : x * t⁻¹ * (t * w) = (t * w) * (x * t⁻¹) := by
      have htv' : t⁻¹ * (t * w) = (t * w) * t⁻¹ := (Commute.inv_left htv).eq
      calc x * t⁻¹ * (t * w) = x * (t⁻¹ * (t * w)) := by group
        _ = x * ((t * w) * t⁻¹) := by rw [htv']
        _ = (x * (t * w)) * t⁻¹ := by group
        _ = (t * w) * x * t⁻¹ := by rw [hxv]
        _ = (t * w) * (x * t⁻¹) := by group
    have hinv := hW.tw_inv huV
    have huu : (x * t⁻¹)⁻¹ = x * t⁻¹ := by
      rw [← hinv, ← hucomm, mul_inv_cancel_right]
    refine hS.conf.omega _ huV ?_
    rw [sq]
    nth_rewrite 2 [← huu]
    exact mul_inv_cancel _
  · right
    have hucomm : x * w⁻¹ * (t * w) = (t * w) * (x * w⁻¹) := by
      have hwv' : w⁻¹ * (t * w) = (t * w) * w⁻¹ := (Commute.inv_left hwv).eq
      calc x * w⁻¹ * (t * w) = x * (w⁻¹ * (t * w)) := by group
        _ = x * ((t * w) * w⁻¹) := by rw [hwv']
        _ = (x * (t * w)) * w⁻¹ := by group
        _ = (t * w) * x * w⁻¹ := by rw [hxv]
        _ = (t * w) * (x * w⁻¹) := by group
    have huF := hcF _ h1 hucomm
    have hu2 := hW.F_sq huF
    have hww : w * w = 1 := by rw [← sq, hW.w_sq]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have huw : (x * w⁻¹) * w = w * (x * w⁻¹) := by
      have huu : (x * w⁻¹)⁻¹ = x * w⁻¹ := by
        rw [inv_eq_iff_mul_eq_one, ← sq, hu2]
      have hxx : x * x = 1 := by rw [← sq, hx2]
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      calc (x * w⁻¹) * w = x := by group
        _ = w * (w⁻¹ * x) := by group
        _ = w * (x * w⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, hxinv, hwinv]
        _ = w * (x * w⁻¹) := by rw [huu]
    have hut : (x * w⁻¹) * t = t * (x * w⁻¹) := by
      have e1 : t = (t * w) * w⁻¹ := by group
      have huw' : (x * w⁻¹) * w⁻¹ = w⁻¹ * (x * w⁻¹) := (Commute.inv_right huw).eq
      calc (x * w⁻¹) * t = (x * w⁻¹) * ((t * w) * w⁻¹) := by rw [← e1]
        _ = ((x * w⁻¹) * (t * w)) * w⁻¹ := by group
        _ = (t * w) * ((x * w⁻¹) * w⁻¹) := by rw [hucomm]; group
        _ = (t * w) * (w⁻¹ * (x * w⁻¹)) := by rw [huw']
        _ = t * (x * w⁻¹) := by group
    have hU := (mem_inf.mp huF).1
    have huT₁t : x * w⁻¹ ∈ U ⊓ centralizer ({t} : Set G) :=
      mem_inf.mpr ⟨hL.U₁_le hU, mem_centralizer_singleton_iff.mpr hut⟩
    rw [hL.inf_centralizer] at huT₁t
    have huT₁ : x * w⁻¹ ∈ szT₁ L T := hL.muOne_mem_T₁_of_mem_T hS hU
      ((sup_le (szT₁_le_left L T) (zpowers_le.mpr hW.t_mem)) huT₁t)
    exact (h.outer_facts_of_card_sylow hS.card_sylow hW.tw_mem hW.tw_sq hW.tw_not_mem).2.2.1 _
      huT₁ hucomm.symm
  · exfalso
    have hxv' : x * (t * w)⁻¹ ∈ U₁ := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exfalso
        rw [← two_mul, pow_mul, hx2, one_pow, one_mul] at h1
        have h1' : t * w ∈ U₁ := by simpa using inv_mem h1
        exact hW.tw_not_mem (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS h1' hW.tw_mem))
      · rwa [pow_succ, pow_mul, hx2, one_pow, one_mul] at h1
    have hucomm : x * (t * w)⁻¹ * (t * w) = (t * w) * (x * (t * w)⁻¹) := by
      calc x * (t * w)⁻¹ * (t * w) = x := by group
        _ = (t * w) * x * (t * w)⁻¹ := by rw [← hxv]; group
        _ = (t * w) * (x * (t * w)⁻¹) := by group
    have huF := hcF _ hxv' hucomm
    apply hW.not_conj_mem_F_sup g
    rw [show g * t * g⁻¹ = x * (t * w)⁻¹ * (t * w) by rw [hxdef]; group]
    exact mul_mem (mem_sup_left huF) (mem_sup_right (mem_zpowers _))

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
