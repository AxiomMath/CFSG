module

public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeBound
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

section Inv

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1) {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K} (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include hS hL hc

theorem muOne_mem_sup_of_commute_inv (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {w : G}
    (hwT : w ∈ T) (hwV : ∀ r ∈ V, w * r * w⁻¹ = r⁻¹) {W : Subgroup G}
    (hWiff : ∀ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W)) {x : G}
    (hx : x * w⁻¹ ∈ U₁) {c : G} (hcU : c ∈ U₁) (hcx : c * x = x * c) : c ∈ W ⊔ V := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  have hcommA := hL.muOne_comm_mem_szA₁ hS hc hμV hK hμ
  have htC := hS.start.mem_centralizer_szT₁
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (hS.start.le hwT)
  set u := x * w⁻¹ with hudef
  have hxu : x = u * w := by rw [hudef]; group
  have hcw : c * w * c⁻¹ * w⁻¹ ∈ szA₁ (szT₁ L T) := by
    have hcx' : c * (u * w) * c⁻¹ = u * w := by rw [← hxu, hcx, mul_inv_cancel_right]
    have e : c * w * c⁻¹ * w⁻¹ = c * u⁻¹ * c⁻¹ * u⁻¹⁻¹ := by
      calc c * w * c⁻¹ * w⁻¹ = (c * u * c⁻¹)⁻¹ * (c * (u * w) * c⁻¹) * w⁻¹ := by group
        _ = (c * u * c⁻¹)⁻¹ * (u * w) * w⁻¹ := by rw [hcx']
        _ = c * u⁻¹ * c⁻¹ * u⁻¹⁻¹ := by group
    rw [e]
    exact hcommA c hcU u⁻¹ (inv_mem hx)
  have hlam := hL.lambda hS.start hS.card_sylow hS.conf
  have hV₁N : szT₁ L T ≤ normalizer (outerV₁ L T U₁ : Set G) := fun y hy =>
    mem_normalizer_outerV₁ (Subgroup.le_normalizer (hT₁U₁ hy)) (Subgroup.le_normalizer hy)
  have hA₁V₁ : szA₁ (szT₁ L T) ≤ outerV₁ L T U₁ := fun a ha =>
    mem_outerV₁.mpr ⟨hT₁U₁ (szA₁_le _ ha), (mem_szA₁.mp ha).2⟩
  rw [hlam] at hcU
  obtain ⟨y, hy, z, hz, rfl⟩ := ncyc_exists_mul_of_mem_sup hV₁N hcU
  obtain ⟨hzU, hzC⟩ := mem_outerV₁.mp hz
  set a := y * z * w * (y * z)⁻¹ * w⁻¹ with ha
  have haA : a ∈ szA₁ (szT₁ L T) := hcw
  have hwy : w * y * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
  have hwz : w * z * w⁻¹ ∈ outerV₁ L T U₁ :=
    (mem_normalizer_iff.mp (mem_normalizer_outerV₁ (hL.T_le hwT) (hTN₁ hwT)) z).mp hz
  have hay : y * a = a * y := mem_centralizer_iff.mp (mem_szA₁.mp haA).2 y hy
  have hc1 : y * a⁻¹ = a⁻¹ * y := (Commute.inv_right hay).eq
  have hrel : y⁻¹ * (w * y * w⁻¹) = a⁻¹ * (z * (w * z * w⁻¹)⁻¹) := by
    have e1 : w * y * w⁻¹ * (w * z * w⁻¹) = a⁻¹ * (y * z) := by rw [ha]; group
    calc y⁻¹ * (w * y * w⁻¹) =
          y⁻¹ * (w * y * w⁻¹ * (w * z * w⁻¹)) * (w * z * w⁻¹)⁻¹ := by group
      _ = y⁻¹ * (a⁻¹ * (y * z)) * (w * z * w⁻¹)⁻¹ := by rw [e1]
      _ = y⁻¹ * (a⁻¹ * y) * z * (w * z * w⁻¹)⁻¹ := by group
      _ = y⁻¹ * (y * a⁻¹) * z * (w * z * w⁻¹)⁻¹ := by rw [hc1]
      _ = a⁻¹ * (z * (w * z * w⁻¹)⁻¹) := by group
  have hRV : a⁻¹ * (z * (w * z * w⁻¹)⁻¹) ∈ outerV₁ L T U₁ :=
    mul_mem (hA₁V₁ (inv_mem haA)) (mul_mem hz (inv_mem hwz))
  have hA : y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨mul_mem (inv_mem hy) hwy, ?_⟩
    rw [hrel]
    exact (mem_outerV₁.mp hRV).2
  have hyW : y ∈ W := (hWiff y hy).mp hA
  have hb : w * z * w⁻¹ * z⁻¹ ∈ szA₁ (szT₁ L T) := by
    have e2 : z * (w * z * w⁻¹)⁻¹ = a * (y⁻¹ * (w * y * w⁻¹)) := by rw [hrel]; group
    have h1 : z * (w * z * w⁻¹)⁻¹ ∈ szA₁ (szT₁ L T) := by rw [e2]; exact mul_mem haA hA
    have h2 := inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  have hσz := hL.muOne_comm_t_mem hS (hL.U₁_le hzU)
  set b := w * z * w⁻¹ * z⁻¹ with hbdef
  have hbt : b * t = t * b := mem_centralizer_iff.mp htC b (szA₁_le _ hb)
  have htb : t * b⁻¹ * t⁻¹ = b⁻¹ := by
    rw [(Commute.inv_right (Commute.symm hbt)).eq, mul_inv_cancel_right]
  have hbσ : b * (z * t * z⁻¹ * t⁻¹) = (z * t * z⁻¹ * t⁻¹) * b :=
    hS.conf.comm _ (hS.conf.le hb) _ hσz
  have e3 : w * (z * t * z⁻¹ * t⁻¹) * w⁻¹ = z * t * z⁻¹ * t⁻¹ := by
    have hwz' : w * z * w⁻¹ = b * z := by rw [hbdef]; group
    have hwtw : w * t * w⁻¹ = t := by rw [hwt, mul_inv_cancel_right]
    calc w * (z * t * z⁻¹ * t⁻¹) * w⁻¹ =
          (w * z * w⁻¹) * (w * t * w⁻¹) * (w * z * w⁻¹)⁻¹ * (w * t * w⁻¹)⁻¹ := by group
      _ = (b * z) * t * (b * z)⁻¹ * t⁻¹ := by rw [hwz', hwtw]
      _ = b * (z * t * z⁻¹ * t⁻¹) * (t * b⁻¹ * t⁻¹) := by group
      _ = b * (z * t * z⁻¹ * t⁻¹) * b⁻¹ := by rw [htb]
      _ = z * t * z⁻¹ * t⁻¹ := by rw [hbσ, mul_inv_cancel_right]
  have e4 := hwV _ hσz
  rw [e3] at e4
  have hσ2 : (z * t * z⁻¹ * t⁻¹) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [e4]
    exact mul_inv_cancel _
  have hzTV := hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hzU (hS.conf.omega _ hσz hσ2)
  obtain ⟨y₁, hy₁, r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS) hzTV
  have hy₁A : y₁ ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy₁, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
    have hz₀ := mem_centralizer_iff.mp hzC y₀ hy₀
    have hr₀ := hL.muOne_T₁_comm hS hy₀ hr
    rw [show y₁ = z * r⁻¹ by rw [← hyr]; group]
    calc y₀ * (z * r⁻¹) = (y₀ * z) * r⁻¹ := by group
      _ = z * y₀ * r⁻¹ := by rw [hz₀]
      _ = z * (y₀ * r⁻¹) := by group
      _ = z * (r⁻¹ * y₀) := by rw [(Commute.inv_right hr₀).eq]
      _ = z * r⁻¹ * y₀ := by group
  have hzV : z ∈ V := by rw [← hyr]; exact mul_mem (hS.conf.le hy₁A) hr
  exact mul_mem (mem_sup_left hyW) (mem_sup_right hzV)

theorem muOne_false_of_conj_mem_inv (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {w : G}
    (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t)
    (hwV : ∀ r ∈ V, w * r * w⁻¹ = r⁻¹) {g : G} (hgT : ∀ s ∈ T, g * s * g⁻¹ ∈ U ⊔ T)
    (hx : g * t * g⁻¹ * w⁻¹ ∈ U₁) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT₁card, hA₁card, -, hsqT, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  obtain ⟨W, hWT₁, hAW, hWcard, hWab, -, -, hWiff⟩ :=
    hS.start.exists_W_of_card_sylow hS.card_sylow hwT hw2 hwS
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hVU₁ : V ≤ U₁ := le_sup_right.trans hL.sup_le_U₁
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  set x := g * t * g⁻¹ with hxdef
  set Kg : Subgroup G := T.map (MulAut.conj g).toMonoidHom with hKgdef
  have hKmem : ∀ k ∈ Kg, ∃ s ∈ T, k = g * s * g⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hSU : U ⊔ T = U₁ ⊔ T := by rw [hL.muOne_sup_eq hS, sup_comm]
  have hKS : Kg ≤ U₁ ⊔ T := fun k hk => by
    obtain ⟨s, hs, rfl⟩ := hKmem k hk
    rw [← hSU]
    exact hgT s hs
  have hKcard : Nat.card Kg = Nat.card T := card_map_of_injective (MulAut.conj g).injective
  have hKx : ∀ k ∈ Kg, k * x = x * k := by
    intro k hk
    obtain ⟨s, hs, rfl⟩ := hKmem k hk
    have hst := mem_centralizer_singleton_iff.mp (hS.start.le hs)
    calc g * s * g⁻¹ * x = g * (s * t) * g⁻¹ := by rw [hxdef]; group
      _ = g * (t * s) * g⁻¹ := by rw [hst]
      _ = x * (g * s * g⁻¹) := by rw [hxdef]; group
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := U₁) (B := T) hL.T_le
  have hU₁T : U₁ ⊓ T = szT₁ L T :=
    le_antisymm (fun z hz => hL.muOne_mem_T₁_of_mem_T hS (mem_inf.mp hz).1 (mem_inf.mp hz).2)
      (le_inf hT₁U₁ (szT₁_le_left L T))
  rw [hU₁T, hT₁card, hL.muOne_card_U₁ hS] at hprod
  have h1 := relIndex_mul_card (H := U₁) (K := Kg)
  have h2 := relIndex_mul_card (H := U₁) (K := U₁ ⊔ T)
  rw [inf_of_le_left le_sup_left, hL.muOne_card_U₁ hS] at h2
  rw [hKcard] at h1
  have hne : U₁.relIndex (U₁ ⊔ T) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := (U₁ ⊔ T : Subgroup G))).ne' h2.symm
  have h3 := Subgroup.relIndex_le_of_le_right hKS hne
  have e5 : U₁.relIndex (U₁ ⊔ T) * (2 ^ f) ^ 3 = Nat.card T := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq0 5)
    calc (2 ^ f) ^ 5 * (U₁.relIndex (U₁ ⊔ T) * (2 ^ f) ^ 3) =
          U₁.relIndex (U₁ ⊔ T) * (2 ^ f) ^ 5 * (2 ^ f) ^ 3 := by ring
      _ = (2 ^ f) ^ 5 * Nat.card T := by rw [h2, hprod]
  have hK3 : (2 ^ f) ^ 3 ≤ Nat.card (U₁ ⊓ Kg : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have hrK : 0 < U₁.relIndex Kg := by
      rcases Nat.eq_zero_or_pos (U₁.relIndex Kg) with h0 | h0
      · rw [h0, zero_mul] at h1
        exact absurd h1.symm (Nat.card_pos (α := T)).ne'
      · exact h0
    have h4 : U₁.relIndex Kg * Nat.card (U₁ ⊓ Kg : Subgroup G) <
        U₁.relIndex Kg * (2 ^ f) ^ 3 := Nat.mul_lt_mul_of_pos_left hlt hrK
    have h5 : U₁.relIndex Kg * (2 ^ f) ^ 3 ≤ U₁.relIndex (U₁ ⊔ T) * (2 ^ f) ^ 3 :=
      Nat.mul_le_mul_right _ h3
    omega
  set C := U₁ ⊓ centralizer ({x} : Set G) with hCdef
  have hCW : C ≤ W ⊔ V := fun c hc' =>
    hL.muOne_mem_sup_of_commute_inv hS hc hμV hK hμ hwT hwV hWiff hx (mem_inf.mp hc').1
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hc').2)
  have hKC : U₁ ⊓ Kg ≤ C := fun k hk => mem_inf.mpr ⟨(mem_inf.mp hk).1,
    mem_centralizer_singleton_iff.mpr (hKx k (mem_inf.mp hk).2)⟩
  have hWN : W ≤ normalizer (V : Set G) := hWT₁.trans (hL.muOne_T₁_le_normalizer hS)
  have hprod2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := V) (B := W) hWN
  rw [hS.conf.card, hWcard] at hprod2
  have hVW : 2 ^ f ≤ Nat.card (V ⊓ W : Subgroup G) := by
    rw [← hA₁card]
    exact Subgroup.card_le_of_le (le_inf hS.conf.le hAW)
  have hWVcard : Nat.card (W ⊔ V : Subgroup G) ≤ (2 ^ f) ^ 3 := by
    rw [sup_comm]
    by_contra hgt
    push Not at hgt
    have h6 : (2 ^ f) ^ 3 * 2 ^ f < Nat.card (V ⊔ W : Subgroup G) * Nat.card (V ⊓ W : Subgroup G) :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hgt hq0) (Nat.mul_le_mul_left _ hVW)
    rw [hprod2, show (2 ^ f) ^ (1 + 1) * (2 ^ f) ^ 2 = (2 ^ f) ^ 3 * 2 ^ f by ring] at h6
    exact lt_irrefl _ h6
  have hCcard : (2 ^ f) ^ 3 ≤ Nat.card C := hK3.trans (Subgroup.card_le_of_le hKC)
  have hCeq : C = W ⊔ V := eq_of_le_of_card_ge hCW (hWVcard.trans hCcard)
  have hMab : ∀ a ∈ W ⊔ V, ∀ b ∈ W ⊔ V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, hy, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup hWN ha
    obtain ⟨y', hy', r', hr', rfl⟩ := ncyc_exists_mul_of_mem_sup hWN hb
    have c1 := hL.muOne_T₁_comm hS (hWT₁ hy) hr'
    have c2 := hL.muOne_T₁_comm hS (hWT₁ hy') hr
    have c3 := hWab y hy y' hy'
    have c4 := hS.conf.comm r hr r' hr'
    calc y * r * (y' * r') = y * (r * y') * r' := by group
      _ = y * (y' * r) * r' := by rw [c2]
      _ = (y * y') * (r * r') := by group
      _ = (y' * y) * (r' * r) := by rw [c3, c4]
      _ = y' * (y * r') * r := by group
      _ = y' * (r' * y) * r := by rw [c1]
      _ = y' * r' * (y * r) := by group
  set M := W ⊔ V with hMdef
  let sqM : M →* M :=
    { toFun := fun m => m ^ 2
      map_one' := by simp
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul, SubmonoidClass.coe_pow]
        exact Commute.mul_pow (hMab a a.2 b b.2) 2) }
  have hsqA : ∀ m ∈ M, m ^ 2 ∈ szA₁ (szT₁ L T) := by
    intro m hm
    obtain ⟨y, hy, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup hWN hm
    rw [Commute.mul_pow (hL.muOne_T₁_comm hS (hWT₁ hy) hr) 2]
    exact mul_mem (hsqT y (hWT₁ hy)) (hL.muOne_sq_mem_szA₁_of_mem_V hS hr)
  have hrange : Nat.card sqM.range ≤ 2 ^ f := by
    rw [← hA₁card]
    refine Nat.card_le_card_of_injective
      (fun m : sqM.range => (⟨((m : M) : G), ?_⟩ : szA₁ (szT₁ L T))) ?_
    · obtain ⟨n, hn⟩ := m.2
      rw [← hn]
      exact hsqA (n : G) n.2
    · intro a b hab
      have h10 := congrArg Subtype.val hab
      simp only at h10
      exact Subtype.ext (Subtype.ext h10)
  have hMcard : (2 ^ f) ^ 3 ≤ Nat.card M := by rw [← hCeq]; exact hCcard
  have hkerE : (2 ^ f) ^ 2 ≤ Nat.card sqM.ker := by
    have h7 := card_mul_index sqM.ker
    rw [Subgroup.index_ker] at h7
    by_contra hlt
    push Not at hlt
    have h8 : Nat.card sqM.ker * Nat.card sqM.range < (2 ^ f) ^ 2 * 2 ^ f :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ hrange) (Nat.mul_lt_mul_of_pos_right hlt hq0)
    rw [h7, show (2 ^ f) ^ 2 * 2 ^ f = (2 ^ f) ^ 3 by ring] at h8
    omega
  set E : Subgroup G := sqM.ker.map M.subtype with hEdef
  have hEcard : Nat.card E = Nat.card sqM.ker := card_map_of_injective M.subtype_injective
  have hEmem : ∀ e ∈ E, e ∈ M ∧ e ^ 2 = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨m.2, ?_⟩
    have h9 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
    exact h9
  have hEC' : ∀ e ∈ E, e ∈ C := fun e he => by rw [hCeq]; exact (hEmem e he).1
  have hEC : E ≤ centralizer ({x} : Set G) := fun e he => (mem_inf.mp (hEC' e he)).2
  have hxE : x ∉ E := by
    intro hxE
    have hxU := (mem_inf.mp (hEC' x hxE)).1
    apply hwS
    have hwU : w ∈ U₁ := by
      rw [show w = (x * w⁻¹)⁻¹ * x by group]
      exact mul_mem (inv_mem hx) hxU
    exact mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS hwU hwT)
  have htt : t * t = 1 := by rw [← sq, hS.start.sq_eq_one]
  have hxx : x * x = 1 := by
    rw [hxdef, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  have hx2' : x ^ 2 = 1 := by rw [sq]; exact hxx
  have hxN : x ∈ normalizer (E : Set G) := mem_normalizer_of_forall_inv_mul_mul_mem fun e he => by
    have hex := mem_centralizer_singleton_iff.mp (hEC he)
    rw [show x⁻¹ * e * x = e by rw [mul_assoc, hex, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact he
  set B := E ⊔ zpowers x with hBdef
  have hB2 := RankOne.Endings.relIndex_sup_zpowers_eq_two hxE hxN hxx
  have hBcard := relIndex_mul_card (H := E) (K := B)
  rw [hB2, inf_of_le_left le_sup_left] at hBcard
  have hBC : B ≤ centralizer ({x} : Set G) :=
    sup_le hEC (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hBsq : ∀ b ∈ B, b ^ 2 = 1 := by
    intro b hb
    rw [hBdef, sup_comm] at hb
    obtain ⟨a, ha, e, he, rfl⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr hxN) hb
    have hex := mem_centralizer_singleton_iff.mp (hEC he)
    have hae : a * e = e * a := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (Commute.symm hex) k).eq
    rw [Commute.mul_pow hae 2, (hEmem e he).2, mul_one]
    rcases mem_zpowers_involution_eq_one_or_eq hx2' ha with rfl | rfl
    · exact one_pow 2
    · exact hx2'
  set B' : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'def
  have hB'card : Nat.card B' = Nat.card B := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB'C : B' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hbx := mem_centralizer_singleton_iff.mp (hBC hb)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * b * g * t = g⁻¹ * (b * x) * g := by rw [hxdef]; group
      _ = g⁻¹ * (x * b) * g := by rw [hbx]
      _ = t * (g⁻¹ * b * g) := by rw [hxdef]; group
  have hB'2 : ∀ y ∈ B', y ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show (g⁻¹ * b * g) ^ 2 = g⁻¹ * b ^ 2 * g by rw [sq, sq]; group, hBsq b hb]
    group
  have hlt := hS.start.card_lt_of_sq_eq_one_of_card_sylow hS.card_sylow hB'C hB'2
  rw [hB'card, ← hBcard, hEcard] at hlt
  omega

end Inv

end U3C1OuterLevelData

end CFSG.SeitzReduction.RankOne
