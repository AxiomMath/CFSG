module

public import CFSG.GH74.GLS.Stage2.Signalizer.L48StarStmt
public import CFSG.GH74.GLS.IVK.L2.GroupAux
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

@[expose] def StarAltStmt : Prop :=
  ∀ {K : Type} [Group K] [Finite K] {n : ℕ}, 8 ≤ n → n ≤ 11 → IsDoubleCoverOfAlt K n →
    ∀ (t : K), t * t = 1 → ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Subgroup K), IsPGroup p ↥Y →
      (∀ c : K, c * t = t * c → c ∈ normalizer (Y : Set K)) → ⁅Y, zpowers t⁆ = Y → Y = ⊥

@[expose] def StarSl2Stmt : Prop :=
  ∀ {A : Type} [Group A] [Finite A] (L₁ L₂ : Subgroup A) (r₁ r₂ : ℕ),
    IsCentralProd L₁ L₂ (L₁ ⊔ L₂) → HasSL2Model ↥L₁ (fun q => q = r₁) → HasSL2Model ↥L₂ (fun q => q = r₂) →
    Odd r₁ → Odd r₂ → ∀ (t : A), t ∈ L₁ ⊔ L₂ → t * t = 1 →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Subgroup A), IsPGroup p ↥Y → Y ≤ L₁ ⊔ L₂ →
      (∀ c ∈ L₁ ⊔ L₂, c * t = t * c → c ∈ normalizer (Y : Set A)) → ⁅Y, zpowers t⁆ = Y → Y = ⊥

theorem le_of_normal_of_commutator_eq {C : Type} [Group C] {L : Subgroup C} [L.Normal] {s : C} (hs : s ∈ L)
    {Y : Subgroup C} (h : ⁅Y, zpowers s⁆ = Y) : Y ≤ L := by
  rw [← h]
  refine Subgroup.commutator_le.mpr fun y _ w hw => ?_
  have hwL : w ∈ L := Subgroup.zpowers_le.mpr hs hw
  have : y * w * y⁻¹ ∈ L := Subgroup.Normal.conj_mem inferInstance w hwL y
  simpa [commutatorElement_def] using L.mul_mem this (L.inv_mem hwL)


section Dispatch

variable {G : Type} [Group G] [Finite G]

theorem toBar_mem_LBar {z : G} {S : Subgroup G} (base : Stage1Base G z S) {t : G} (ht : t ∈ Cen z)
    (hU4 : IVK.IsFourSubgroup (zpowers z ⊔ zpowers t)) (hUS : zpowers z ⊔ zpowers t ≤ S)
    (hUn : ∀ s ∈ S, ∀ u ∈ zpowers z ⊔ zpowers t, s * u * s⁻¹ ∈ zpowers z ⊔ zpowers t) :
    toBar z ⟨t, ht⟩ ∈ LBar z := by
  have h1 := base.four_le _ hUS hU4 hUn
  have htL : t ∈ LC z := h1 (Subgroup.mem_sup_right (mem_zpowers t))
  exact ⟨⟨t, ht⟩, htL, rfl⟩

theorem star_of_pair (hSl : StarSl2Stmt) {z : G} {L₁ L₂ : Subgroup (CentralizerBar z)} {r₁ r₂ : ℕ}
    (hprod : IsCentralProd L₁ L₂ (LBar z)) (h1 : HasSL2Model ↥L₁ (fun q => q = r₁))
    (h2 : HasSL2Model ↥L₂ (fun q => q = r₂)) (ho1 : Odd r₁) (ho2 : Odd r₂)
    {tb : CentralizerBar z} (htL : tb ∈ LBar z) (htb2 : tb * tb = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (CentralizerBar z)} (hY : IsPGroup p ↥Y)
    (hN : ∀ c : CentralizerBar z, c * tb = tb * c → c ∈ normalizer (Y : Set (CentralizerBar z)))
    (hcomm : ⁅Y, zpowers tb⁆ = Y) : Y = ⊥ := by
  have hsup : L₁ ⊔ L₂ = LBar z := hprod.1
  have hprod' : IsCentralProd L₁ L₂ (L₁ ⊔ L₂) := ⟨rfl, hprod.2.1, hprod.2.2⟩
  have := LBar_normal z
  have hYL : Y ≤ LBar z := le_of_normal_of_commutator_eq htL hcomm
  exact hSl L₁ L₂ r₁ r₂ hprod' h1 h2 ho1 ho2 tb (hsup ▸ htL) htb2 p hp hp2 Y hY (hsup ▸ hYL)
    (fun c _ hc => hN c hc) hcomm

theorem star_of_m12 {z : G} {S : Subgroup G} (h : Stage1M12 G z S) {t : G} (ht : t ∈ Cen z)
    (hU4 : IVK.IsFourSubgroup (zpowers z ⊔ zpowers t)) (hUS : zpowers z ⊔ zpowers t ≤ S)
    (hUn : ∀ s ∈ S, ∀ u ∈ zpowers z ⊔ zpowers t, s * u * s⁻¹ ∈ zpowers z ⊔ zpowers t)
    {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {Y : Subgroup (CentralizerBar z)} (hY : IsPGroup p ↥Y)
    (hcomm : ⁅Y, zpowers (toBar z ⟨t, ht⟩)⁆ = Y) : Y = ⊥ := by
  obtain ⟨U', -, -, -, -, hUW, huniq, -⟩ := h.four_group
  have hUU : zpowers z ⊔ zpowers t = U' := huniq _ hUS hU4 hUn
  have htW : t ∈ WC z := hUW (hUU ▸ Subgroup.mem_sup_right (mem_zpowers t))
  have htb : toBar z ⟨t, ht⟩ ∈ WBar z := ⟨⟨t, ht⟩, htW, rfl⟩
  obtain ⟨hWn, -⟩ := h.quot
  have hYW : Y ≤ WBar z := le_of_normal_of_commutator_eq htb hcomm
  obtain ⟨A, B, hAB, ⟨eA⟩, ⟨eB⟩, -⟩ := h.W_shape
  have hA2 : IsPGroup 2 ↥A := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr eA.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB2 : IsPGroup 2 ↥B := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr eB.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hW2 : IsPGroup 2 ↥(WBar z) := by
    rw [← hAB.1]
    exact IVK.isPGroup_sup_of_commute hA2 hB2 hAB.2.1
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha⟩ := hY ⟨y, hy⟩
  obtain ⟨b, hb⟩ := hW2 ⟨y, hYW hy⟩
  have ha' : y ^ (p ^ a) = 1 := congrArg Subtype.val ha
  have hb' : y ^ (2 ^ b) = 1 := congrArg Subtype.val hb
  have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have := pow_gcd_eq_one.mpr ⟨ha', hb'⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

theorem star48_of_parts (hAlt : StarAltStmt) (hSl : StarSl2Stmt) : Star48 := by
  intro G _ _ z k S ctx t ht p hp hp2 hU4 hUS hUn Y hY hN hcomm
  have htU : t ∈ zpowers z ⊔ zpowers t := Subgroup.mem_sup_right (mem_zpowers t)
  have ht2 : t * t = 1 := sq_eq_one_of_isFour hU4 htU
  have htb2 : toBar z ⟨t, ht⟩ * toBar z ⟨t, ht⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, ht⟩ * ⟨t, ht⟩ : ↥(Cen z)) = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hd := ctx.data
  cases hd with
  | g2 h =>
    obtain ⟨r₁, r₂, L₁, L₂, ho1, ho2, -, hprod, h1, h2, -⟩ := h.shape
    exact star_of_pair hSl hprod h1 h2 ho1 ho2 (toBar_mem_LBar h.base ht hU4 hUS hUn) htb2 hp hp2 hY hN hcomm
  | m12 h => exact star_of_m12 h ht hU4 hUS hUn hp2 hp hY hcomm
  | psp4 h =>
    obtain ⟨q, L₁, L₂, hh⟩ := h
    exact star_of_pair hSl hh.pair.prod hh.pair.sl₁ hh.pair.sl₂ hh.pair.odd hh.pair.odd
      (toBar_mem_LBar hh.pair.base ht hU4 hUS hUn) htb2 hp hp2 hY hN hcomm
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, hh⟩ := h
    exact star_of_pair hSl hh.pair.prod hh.pair.sl₁ hh.pair.sl₂ hh.pair.odd hh.pair.odd
      (toBar_mem_LBar hh.pair.base ht hU4 hUS hUn) htb2 hp hp2 hY hN hcomm
  | mcl h =>
    obtain ⟨n, hn, hs⟩ := h
    exact hAlt (by omega) (by omega) hs.cover _ htb2 p hp hp2 Y hY hN hcomm
  | ly h =>
    obtain ⟨n, hn, hs⟩ := h
    exact hAlt (by omega) (by omega) hs.cover _ htb2 p hp hp2 Y hY hN hcomm

end Dispatch

end CFSG.GH74.GLS.Stage2.Signalizer.L48
