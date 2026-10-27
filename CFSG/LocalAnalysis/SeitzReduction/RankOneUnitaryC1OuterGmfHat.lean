module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmfLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

section Hat

variable {W' : Subgroup G} (hW'T₁ : W' ≤ szT₁ L T) (hW'ab : ∀ x ∈ W', ∀ y ∈ W', x * y = y * x)
  (hW'inv : ∀ y ∈ W', (t * w) * y * (t * w)⁻¹ = y⁻¹)

include hW'T₁ hW'ab in
theorem gmf_E_comm : ∀ a ∈ W' ⊔ V, ∀ b ∈ W' ⊔ V, a * b = b * a :=
  hW.sup_V_comm hW'T₁ hW'ab

include hW'T₁ hW'ab hW'inv in
theorem gmf_E_inv {c : G} (hc : c ∈ W' ⊔ V) : (t * w) * c * (t * w)⁻¹ = c⁻¹ := by
  have hWVN : W' ≤ normalizer (V : Set G) := fun y hy =>
    hW.level.muOne_T₁_le_normalizer hW.step (hW'T₁ hy)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hWVN hc
  rw [show (t * w) * (a₁ * a₂) * (t * w)⁻¹ =
    ((t * w) * a₁ * (t * w)⁻¹) * ((t * w) * a₂ * (t * w)⁻¹) by group, hW'inv a₁ ha₁,
    hW.tw_inv ha₂, ← mul_inv_rev]
  congr 1
  exact hW.gmf_E_comm hW'T₁ hW'ab _ (mem_sup_right ha₂) _ (mem_sup_left ha₁)

include hW'T₁ hW'ab in
theorem gmf_E_sq {c : G} (hc : c ∈ W' ⊔ V) : c ^ 2 ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, -, -, hsqT₁, -, -, -⟩ := hW.step.start.facts_of_card_sylow hW.step.card_sylow
  have hWVN : W' ≤ normalizer (V : Set G) := fun y hy =>
    hW.level.muOne_T₁_le_normalizer hW.step (hW'T₁ hy)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ncyc_exists_mul_of_mem_sup hWVN hc
  rw [(show Commute a₁ a₂ from
    hW.gmf_E_comm hW'T₁ hW'ab _ (mem_sup_left ha₁) _ (mem_sup_right ha₂)).mul_pow]
  exact mul_mem (hsqT₁ a₁ (hW'T₁ ha₁)) (hW.level.muOne_sq_mem_szA₁_of_mem_V hW.step ha₂)

theorem gmf_E_le_U₁ (hW'T₁ : W' ≤ szT₁ L T) : W' ⊔ V ≤ U₁ :=
  sup_le (hW'T₁.trans hW.T₁_le_U₁) (le_sup_right.trans hW.level.sup_le_U₁)

include hW'T₁ hW'ab hW'inv in
theorem gmf_E_mem_F {c : G} (hc : c ∈ W' ⊔ V) (hc2 : c ^ 2 = 1) :
    c ∈ U₁ ⊓ centralizer ({t * w} : Set G) := by
  have hcc : c⁻¹ = c := by rw [inv_eq_iff_mul_eq_one, ← sq, hc2]
  refine mem_inf.mpr ⟨hW.gmf_E_le_U₁ hW'T₁ hc, mem_centralizer_singleton_iff.mpr ?_⟩
  have e := hW.gmf_E_inv hW'T₁ hW'ab hW'inv hc
  rw [hcc] at e
  calc c * (t * w) = (t * w) * c * (t * w)⁻¹ * (t * w) := by rw [e]
    _ = (t * w) * c := by group

include hW'T₁ in
theorem gmf_card_E (hAW' : szA₁ (szT₁ L T) ≤ W') (hW'card : Nat.card W' = (2 ^ f) ^ 2) :
    Nat.card (W' ⊔ V : Subgroup G) = (2 ^ f) ^ 3 := by
  have hS := hW.step
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hWVN : W' ≤ normalizer (V : Set G) := fun y hy =>
    hW.level.muOne_T₁_le_normalizer hS (hW'T₁ hy)
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

include hW'T₁ hW'ab hW'inv in
theorem gmf_conj_E
    (hW'iff : ∀ y ∈ szT₁ L T,
      (y⁻¹ * ((t * w) * y * (t * w)⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W'))
    {g : G} (hg : g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) {c : G} (hc : c ∈ W' ⊔ V) :
    g * c * g⁻¹ ∈ W' ⊔ V := by
  obtain ⟨hgS, hgC⟩ := mem_inf.mp hg
  have hgv := mem_centralizer_singleton_iff.mp hgC
  have hgv' : g⁻¹ * (t * w) * g = t * w := by
    calc g⁻¹ * (t * w) * g = g⁻¹ * (g * (t * w)) := by rw [mul_assoc, hgv]
      _ = t * w := by group
  have hgv'' : g⁻¹ * (t * w)⁻¹ * g = (t * w)⁻¹ := by
    rw [show g⁻¹ * (t * w)⁻¹ * g = (g⁻¹ * (t * w) * g)⁻¹ by group, hgv']
  have hcinv := hW.gmf_E_inv hW'T₁ hW'ab hW'inv (inv_mem hc)
  rw [inv_inv] at hcinv
  have h1 : c * (t * w) * c⁻¹ * (t * w)⁻¹ = c ^ 2 := by
    calc c * (t * w) * c⁻¹ * (t * w)⁻¹ = c * ((t * w) * c⁻¹ * (t * w)⁻¹) := by group
      _ = c * c := by rw [hcinv]
      _ = c ^ 2 := (sq c).symm
  have h2 : g * c * g⁻¹ * (t * w) * (g * c * g⁻¹)⁻¹ * (t * w)⁻¹ =
      g * (c * (t * w) * c⁻¹ * (t * w)⁻¹) * g⁻¹ := by
    calc g * c * g⁻¹ * (t * w) * (g * c * g⁻¹)⁻¹ * (t * w)⁻¹ =
        g * c * (g⁻¹ * (t * w) * g) * c⁻¹ * (g⁻¹ * (t * w)⁻¹ * g) * g⁻¹ := by group
      _ = g * (c * (t * w) * c⁻¹ * (t * w)⁻¹) * g⁻¹ := by rw [hgv', hgv'']; group
  refine hW.level.gms_mem_sup_of_comm_mem_szA₁ hW.step hW.tw_mem (fun r hr => hW.tw_inv hr)
    hW'iff (hW.conj_U₁ hgS (hW.gmf_E_le_U₁ hW'T₁ hc)) ?_
  rw [h2, h1]
  exact hW.conj_szA₁_of_mem hgS (hW.gmf_E_sq hW'T₁ hW'ab hc)

end Hat

theorem gmf_conj_t_mul_w_inv_mem {y : G} (hyS₂ : y ∈ swapS₂ P U T) (hyS : y ∉ U ⊔ T)
    (hyv : y * (t * w) = (t * w) * y) : y * t * y⁻¹ * w⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hL := hW.level
  have hxS : y * t * y⁻¹ ∈ U ⊔ T :=
    (mem_normalizer_iff.mp (mem_swapS₂.mp hyS₂).2 t).mp (mem_sup_right hW.t_mem)
  have hwt := hW.wt_comm
  have htv : t * (t * w) = (t * w) * t := by rw [mul_assoc t w t, hwt]
  have hyv' : y⁻¹ * (t * w) = (t * w) * y⁻¹ := (Commute.inv_left hyv).eq
  have hxv : y * t * y⁻¹ * (t * w) = (t * w) * (y * t * y⁻¹) := by
    calc y * t * y⁻¹ * (t * w) = y * t * (y⁻¹ * (t * w)) := by group
      _ = y * t * ((t * w) * y⁻¹) := by rw [hyv']
      _ = y * (t * (t * w)) * y⁻¹ := by group
      _ = y * ((t * w) * t) * y⁻¹ := by rw [htv]
      _ = (y * (t * w)) * t * y⁻¹ := by group
      _ = (t * w) * y * t * y⁻¹ := by rw [hyv]
      _ = (t * w) * (y * t * y⁻¹) := by group
  rcases hW.conj_t_mem_of_commute_tw y hxS hxv with h1 | h1
  · exfalso
    have h2 := (hW.conj_of_not_mem hyS₂ hyS).1
    have h3 : t * w⁻¹ ∈ U₁ := by
      have := mul_mem (inv_mem (hW.T₁_le_U₁ (szA₁_le _ h1))) h2
      rwa [show (y * t * y⁻¹ * t⁻¹)⁻¹ * (y * t * y⁻¹ * w⁻¹) = t * w⁻¹ by group] at this
    have hww : w * w = 1 := by rw [← sq, hW.w_sq]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rw [hwinv] at h3
    exact hW.tw_not_mem (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hW.step h3 hW.tw_mem))
  · exact h1

theorem gmf_mem_szA₁_of_mul_conj {y : G} (hyS₂ : y ∈ swapS₂ P U T) (hyS : y ∉ U ⊔ T)
    (hyv : y * (t * w) = (t * w) * y) {g : G} (hg : g ∈ szT₁ L T)
    (hgy : g * (y * g * y⁻¹) ∈ szA₁ (szT₁ L T)) : g ∈ szA₁ (szT₁ L T) := by
  have hS := hW.step
  have h := hS.start
  set z := y * g * y⁻¹ with hzdef
  have hzT₁ : z ∈ szT₁ L T := by
    rw [show z = g⁻¹ * (g * z) by group]
    exact mul_mem (inv_mem hg) (szA₁_le _ hgy)
  have htC := h.mem_centralizer_szT₁
  have hzt : z * t = t * z := mem_centralizer_iff.mp htC z hzT₁
  have hgt : g * t = t * g := mem_centralizer_iff.mp htC g hg
  have hzx : z * (y * t * y⁻¹) = (y * t * y⁻¹) * z := by
    calc z * (y * t * y⁻¹) = y * (g * t) * y⁻¹ := by rw [hzdef]; group
      _ = y * (t * g) * y⁻¹ := by rw [hgt]
      _ = (y * t * y⁻¹) * z := by rw [hzdef]; group
  have ha := hW.gmf_conj_t_mul_w_inv_mem hyS₂ hyS hyv
  set a := y * t * y⁻¹ * w⁻¹ with hadef
  have hza : z * a = a * z := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 z hzT₁
  have hzw : z * w = w * z := by
    have hw : w = a⁻¹ * (y * t * y⁻¹) := by rw [hadef]; group
    have hza' : z * a⁻¹ = a⁻¹ * z := (Commute.inv_right hza).eq
    rw [hw]
    calc z * (a⁻¹ * (y * t * y⁻¹)) = (z * a⁻¹) * (y * t * y⁻¹) := by group
      _ = (a⁻¹ * z) * (y * t * y⁻¹) := by rw [hza']
      _ = a⁻¹ * (z * (y * t * y⁻¹)) := by group
      _ = a⁻¹ * ((y * t * y⁻¹) * z) := by rw [hzx]
      _ = a⁻¹ * (y * t * y⁻¹) * z := by group
  have hzv : (t * w) * z = z * (t * w) := by
    calc (t * w) * z = t * (w * z) := by group
      _ = t * (z * w) := by rw [hzw]
      _ = (t * z) * w := by group
      _ = (z * t) * w := by rw [hzt]
      _ = z * (t * w) := by group
  have hzA := (h.outer_facts_of_card_sylow hS.card_sylow hW.tw_mem hW.tw_sq
    hW.tw_not_mem).2.2.1 z hzT₁ hzv
  have := hW.conj_szA₁_of_mem (inv_mem hyS₂) hzA
  rwa [inv_inv, hzdef, show y⁻¹ * (y * g * y⁻¹) * y = g by group] at this

theorem gmf_comm_F {y : G} (hyS₂ : y ∈ swapS₂ P U T) (hyv : y * (t * w) = (t * w) * y)
    (hyS : y ∉ U ⊔ T) (hy2 : y ^ 2 = 1) {M : Subgroup G}
    (hMA : M ≤ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w))
    (hMy : ∀ m ∈ M, y * m = m * y)
    (hcard : Nat.card ((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) ≤
      2 * Nat.card M) :
    ∀ e ∈ U₁ ⊓ centralizer ({t * w} : Set G), y * e = e * y := by
  have hS := hW.step
  have h := hS.start
  obtain ⟨-, hA₁card, -, -, -, hA₁2, -⟩ := h.facts_of_card_sylow hS.card_sylow
  obtain ⟨W', hW'T₁, hAW', hW'card, hW'ab, hW'inv, hW'sq, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS.card_sylow hW.tw_mem hW.tw_sq hW.tw_not_mem
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hFdef
  set A := F ⊔ zpowers (t * w) with hAdef
  set E := W' ⊔ V with hEdef
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hyS₀ : y ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) :=
    mem_inf.mpr ⟨hyS₂, mem_centralizer_singleton_iff.mpr hyv⟩
  have hEab := hW.gmf_E_comm hW'T₁ hW'ab
  have hyE : ∀ c ∈ E, y * c * y⁻¹ ∈ E := fun c hc =>
    hW.gmf_conj_E hW'T₁ hW'ab hW'inv hW'iff hyS₀ hc
  have hFE : F ≤ E := hW.F_le hW'iff
  have hW'E : W' ≤ E := le_sup_left
  have hyy : y * y = 1 := by rw [← sq, hy2]
  have hφE : ∀ c ∈ E, c * (y * c * y⁻¹) ∈ E := fun c hc => mul_mem hc (hyE c hc)
  have hφy : ∀ c ∈ E, y * (c * (y * c * y⁻¹)) * y⁻¹ = c * (y * c * y⁻¹) := by
    intro c hc
    calc y * (c * (y * c * y⁻¹)) * y⁻¹ = (y * c * y⁻¹) * (y * y * c * (y * y)⁻¹) := by group
      _ = (y * c * y⁻¹) * c := by rw [hyy]; group
      _ = c * (y * c * y⁻¹) := hEab _ (hyE c hc) _ hc
  have hφsq : ∀ c ∈ E, (c * (y * c * y⁻¹)) ^ 2 = c ^ 2 * (y * c ^ 2 * y⁻¹) := by
    intro c hc
    rw [(show Commute c (y * c * y⁻¹) from hEab _ hc _ (hyE c hc)).mul_pow]
    congr 1
    rw [sq, sq]
    group
  have hφmul : ∀ a ∈ E, ∀ b ∈ E, (a * b) * (y * (a * b) * y⁻¹) =
      (a * (y * a * y⁻¹)) * (b * (y * b * y⁻¹)) := by
    intro a ha b hb
    have hc : b * (y * a * y⁻¹) = (y * a * y⁻¹) * b := hEab _ hb _ (hyE a ha)
    calc (a * b) * (y * (a * b) * y⁻¹) = a * (b * (y * a * y⁻¹)) * (y * b * y⁻¹) := by group
      _ = a * ((y * a * y⁻¹) * b) * (y * b * y⁻¹) := by rw [hc]
      _ = (a * (y * a * y⁻¹)) * (b * (y * b * y⁻¹)) := by group
  have hkey : ∀ c ∈ W', c * (y * c * y⁻¹) ∈ szA₁ (szT₁ L T) → c ∈ szA₁ (szT₁ L T) :=
    fun c hcW hψA => hW.gmf_mem_szA₁_of_mul_conj hyS₂ hyS hyv (hW'T₁ hcW) hψA
  by_cases hyA₁ : ∀ a ∈ szA₁ (szT₁ L T), y * a = a * y
  ·
    let ψW : W' →* G := MonoidHom.mk' (fun c : W' => (c : G) * (y * c * y⁻¹))
      (fun a b => hφmul a (hW'E a.2) b (hW'E b.2))
    set R := ψW.range with hRdef
    have hRF : R ≤ F := by
      rintro _ ⟨c, rfl⟩
      have hc2 : (c : G) ^ 2 ∈ szA₁ (szT₁ L T) := hW.gmf_E_sq hW'T₁ hW'ab (hW'E c.2)
      refine hW.gmf_E_mem_F hW'T₁ hW'ab hW'inv (hφE _ (hW'E c.2)) ?_
      show ((c : G) * (y * c * y⁻¹)) ^ 2 = 1
      rw [hφsq _ (hW'E c.2), hyA₁ _ hc2, mul_inv_cancel_right, ← sq]
      exact hA₁2 _ hc2
    have hRy : ∀ r ∈ R, y * r = r * y := by
      rintro _ ⟨c, rfl⟩
      have h1 := hφy _ (hW'E c.2)
      show y * ((c : G) * (y * c * y⁻¹)) = ((c : G) * (y * c * y⁻¹)) * y
      calc y * ((c : G) * (y * c * y⁻¹)) = y * ((c : G) * (y * c * y⁻¹)) * y⁻¹ * y := by group
        _ = ((c : G) * (y * c * y⁻¹)) * y := by rw [h1]
    have hRA₁ : R ⊓ szA₁ (szT₁ L T) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨c, rfl⟩, hcA⟩
      have hcA₁ := hkey _ c.2 hcA
      rw [mem_bot]
      show (c : G) * (y * c * y⁻¹) = 1
      rw [hyA₁ _ hcA₁, mul_inv_cancel_right, ← sq, hA₁2 _ hcA₁]
    have hker : Nat.card ψW.ker ≤ 2 ^ f := by
      rw [← hA₁card]
      refine Nat.card_le_card_of_injective (fun k : ψW.ker =>
        (⟨((k : W') : G), hkey _ (k : W').2 (by
          have h1 : ψW (k : W') = 1 := MonoidHom.mem_ker.mp k.2
          rw [show ((k : W') : G) * (y * ((k : W') : G) * y⁻¹) = ψW (k : W') from rfl, h1]
          exact one_mem _)⟩ : szA₁ (szT₁ L T))) ?_
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    have hRcard : 2 ^ f ≤ Nat.card R := by
      have h1 := Subgroup.card_ker_mul_card_range ψW
      rw [hW'card] at h1
      by_contra hlt
      push Not at hlt
      have h2 : Nat.card ψW.ker * Nat.card ψW.range < 2 ^ f * 2 ^ f :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hker) (Nat.mul_lt_mul_of_pos_left hlt hq0)
      rw [h1, sq] at h2
      exact lt_irrefl _ h2
    have hA₁N : szA₁ (szT₁ L T) ≤ normalizer (R : Set G) := fun a ha =>
      mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => by
        have hc : a * x = x * a := hW.F_comm (hW.gmf_szA₁_le_F ha) (hRF hx)
        rw [show a⁻¹ * x * a = x by rw [mul_assoc, ← hc, inv_mul_cancel_left]]
        exact hx
    have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := R) (B := szA₁ (szT₁ L T)) hA₁N
    rw [hRA₁, Subgroup.card_bot, mul_one, hA₁card] at hprod
    have hKeq : R ⊔ szA₁ (szT₁ L T) = F := by
      refine eq_of_le_of_card_ge (sup_le hRF hW.gmf_szA₁_le_F) ?_
      rw [hW.card_F, hprod, sq]
      exact Nat.mul_le_mul_right _ hRcard
    have hKy : R ⊔ szA₁ (szT₁ L T) ≤ centralizer ({y} : Set G) := sup_le
      (fun r hr => mem_centralizer_singleton_iff.mpr (hRy r hr).symm)
      (fun a ha => mem_centralizer_singleton_iff.mpr (hyA₁ a ha).symm)
    intro e he
    rw [← hKeq] at he
    exact (mem_centralizer_singleton_iff.mp (hKy he)).symm
  ·
    exfalso
    push Not at hyA₁
    obtain ⟨a, haA₁, hya⟩ := hyA₁
    have haA : a ∈ A := mem_sup_left (hW.gmf_szA₁_le_F haA₁)
    have hMidx : (M.subgroupOf A).index = 2 := by
      have h1 := Subgroup.card_mul_index (M.subgroupOf A)
      rw [Nat.card_congr (subgroupOfEquivOfLe hMA).toEquiv] at h1
      have hpos : 0 < Nat.card M := Nat.card_pos
      have hne1 : (M.subgroupOf A).index ≠ 1 := by
        intro h1'
        rw [Subgroup.index_eq_one] at h1'
        have h2 : (⟨a, haA⟩ : A) ∈ M.subgroupOf A := by rw [h1']; exact mem_top _
        exact hya (hMy a (mem_subgroupOf.mp h2))
      have hne0 : (M.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hle2 : (M.subgroupOf A).index ≤ 2 := by
        have h3 : Nat.card M * (M.subgroupOf A).index ≤ Nat.card M * 2 := by
          rw [h1]; linarith
        exact Nat.le_of_mul_le_mul_left h3 hpos
      omega
    have hcomm : ∀ x ∈ F, y * x * y⁻¹ * x⁻¹ ∈ szA₁ (szT₁ L T) := by
      intro x hx
      have hxA : x ∈ A := mem_sup_left hx
      by_cases hxM : x ∈ M
      · rw [hMy x hxM, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _
      · have h1 := (Subgroup.mul_mem_iff_of_index_two hMidx (a := (⟨a, haA⟩ : A))
          (b := ⟨x, hxA⟩)).mpr (iff_of_false (fun h' => hya (hMy a (mem_subgroupOf.mp h')))
            (fun h' => hxM (mem_subgroupOf.mp h')))
        have hax : a * x ∈ M := mem_subgroupOf.mp h1
        have h3 : y * (a * x) * y⁻¹ = a * x := by rw [hMy _ hax, mul_inv_cancel_right]
        have e : y * x * y⁻¹ * x⁻¹ = (y * a⁻¹ * y⁻¹) * a := by
          calc y * x * y⁻¹ * x⁻¹ = (y * a⁻¹ * y⁻¹) * (y * (a * x) * y⁻¹) * x⁻¹ := by group
            _ = (y * a⁻¹ * y⁻¹) * (a * x) * x⁻¹ := by rw [h3]
            _ = (y * a⁻¹ * y⁻¹) * a := by group
        rw [e]
        exact mul_mem (hW.conj_szA₁_of_mem hyS₂ (inv_mem haA₁)) haA₁
    let ψ : E →* G := MonoidHom.mk' (fun c : E => (c : G) * (y * c * y⁻¹))
      (fun a b => hφmul a a.2 b b.2)
    set C := (szA₁ (szT₁ L T)).comap ψ with hCdef
    have hF'C : F.subgroupOf E ≤ C := by
      intro c hc
      have hcF : (c : G) ∈ F := mem_subgroupOf.mp hc
      have hz := hcomm _ hcF
      have hzF : y * (c : G) * y⁻¹ * (c : G)⁻¹ ∈ F := hW.gmf_szA₁_le_F hz
      have hcz : (c : G) * (y * (c : G) * y⁻¹ * (c : G)⁻¹) =
          (y * (c : G) * y⁻¹ * (c : G)⁻¹) * c := hW.F_comm hcF hzF
      show (c : G) * (y * c * y⁻¹) ∈ szA₁ (szT₁ L T)
      have e : (c : G) * (y * c * y⁻¹) = y * (c : G) * y⁻¹ * (c : G)⁻¹ := by
        calc (c : G) * (y * c * y⁻¹) =
            ((c : G) * (y * (c : G) * y⁻¹ * (c : G)⁻¹)) * c := by group
          _ = (y * (c : G) * y⁻¹ * (c : G)⁻¹) * c * c := by rw [hcz]
          _ = (y * (c : G) * y⁻¹ * (c : G)⁻¹) * (c : G) ^ 2 := by rw [sq]; group
          _ = y * (c : G) * y⁻¹ * (c : G)⁻¹ := by rw [hW.F_sq hcF, mul_one]
      rw [e]
      exact hz
    have hCW : C ⊓ W'.subgroupOf E ≤ (szA₁ (szT₁ L T)).subgroupOf E := by
      intro c hc
      obtain ⟨hcC, hcW⟩ := mem_inf.mp hc
      exact mem_subgroupOf.mpr (hkey (c : G) (mem_subgroupOf.mp hcW) hcC)
    have hCcard : Nat.card C ≤ (2 ^ f) ^ 2 := by
      have hN : W'.subgroupOf E ≤ normalizer (C : Set E) := fun x _ =>
        mem_normalizer_of_forall_inv_mul_mul_mem fun c hc => by
          have hxc : (x : G) * c = c * x := hEab _ x.2 _ c.2
          rw [show x⁻¹ * c * x = c from Subtype.ext (by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [mul_assoc, ← hxc, inv_mul_cancel_left])]
          exact hc
      have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
        (A := C) (B := W'.subgroupOf E) hN
      have h2 : Nat.card (C ⊔ W'.subgroupOf E : Subgroup E) ≤ (2 ^ f) ^ 3 := by
        rw [← hW.gmf_card_E hW'T₁ hAW' hW'card]
        exact Subgroup.card_le_card_group _
      have h3 : Nat.card (C ⊓ W'.subgroupOf E : Subgroup E) ≤ 2 ^ f := by
        calc _ ≤ Nat.card ((szA₁ (szT₁ L T)).subgroupOf E) := Subgroup.card_le_of_le hCW
          _ = 2 ^ f := by
            rw [Nat.card_congr (subgroupOfEquivOfLe (hAW'.trans hW'E)).toEquiv, hA₁card]
      have h4 : Nat.card (W'.subgroupOf E) = (2 ^ f) ^ 2 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hW'E).toEquiv, hW'card]
      rw [h4] at h1
      have h5 : Nat.card C * (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by
        calc Nat.card C * (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 3 * 2 ^ f := by
              rw [← h1]; exact Nat.mul_le_mul h2 h3
          _ = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right h5 (by positivity)
    have hCeq : F.subgroupOf E = C := by
      refine eq_of_le_of_card_ge hF'C ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hFE).toEquiv, hW.card_F]
      exact hCcard
    obtain ⟨g₀, hg₀W, hg₀a⟩ := hW'sq a haA₁
    have hpE := hφE g₀ (hW'E hg₀W)
    have hpy := hφy g₀ (hW'E hg₀W)
    have hpC : (⟨g₀ * (y * g₀ * y⁻¹), hpE⟩ : E) ∈ C := by
      show g₀ * (y * g₀ * y⁻¹) * (y * (g₀ * (y * g₀ * y⁻¹)) * y⁻¹) ∈ szA₁ (szT₁ L T)
      rw [hpy, ← sq]
      exact hW.gmf_E_sq hW'T₁ hW'ab hpE
    rw [← hCeq] at hpC
    have hp2 := hW.F_sq (mem_subgroupOf.mp hpC)
    rw [hφsq g₀ (hW'E hg₀W), sq g₀, hg₀a] at hp2
    have ha2 : a * a = 1 := by rw [← sq]; exact hA₁2 a haA₁
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have e : y * a * y⁻¹ = a := by rw [eq_inv_of_mul_eq_one_right hp2, hainv]
    apply hya
    calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [e]

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
