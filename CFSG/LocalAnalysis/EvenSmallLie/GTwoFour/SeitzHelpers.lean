module

public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.AS81NXKernelCover
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWCentAux
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import CFSG.LocalAnalysis.EvenSmallLie.Setup

public section

namespace CFSG.EvenSmallLie.GTwoFour

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

theorem seitz_eq_of_orderOf_eq_two_of_cyclic_sylow {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (hS : IsCyclic (S : Subgroup H)) {t : H} (ht : t ∈ center H)
    (ht2 : orderOf t = 2) {x : H} (hx : orderOf x = 2) : x = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2x : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hxP⟩ := h2x.exists_le_sylow
  have htn : (zpowers t).Normal := by
    constructor
    intro a ha g
    rw [mem_center_iff.1 ((zpowers_le.2 ht) ha) g, mul_inv_cancel_right]
    exact ha
  have h2t : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  exact CFSG.ComponentClassification.M12Cover.CyclicKernel.eq_of_orderOf_eq_two_of_isCyclic
    ((Sylow.equiv S P).isCyclic.1 hS) (hxP (mem_zpowers x))
    (h2t.le_sylow_of_normal P (mem_zpowers t)) hx ht2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem seitz_center_facts (hL : standardComponentIsStandard L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : G} (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype) :
    t ∈ centralizer (L : Set G) ∧
      (∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = t) ∧
      centralizer ({t} : Set G) = normalizer (L : Set G) ∧
      L ≤ centralizer ({t} : Set G) ∧ centralizer (L : Set G) ≤ centralizer ({t} : Set G) := by
  obtain ⟨S, hS⟩ := hcyc
  obtain ⟨z, hzZ, rfl⟩ := htZ
  have ht' : orderOf (z : G) = 2 := ht
  have htC : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_of_mem_center hzZ
  have hcen : (⟨z, htC⟩ : centralizer (L : Set G)) ∈ center (centralizer (L : Set G)) := by
    rw [mem_center_iff]
    intro c
    exact Subtype.ext ((mem_centralizer_iff.1 c.2) z z.2).symm
  have huniq : ∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = z := fun x hx hx2 =>
    congrArg Subtype.val (seitz_eq_of_orderOf_eq_two_of_cyclic_sylow S hS hcen
      (by rwa [orderOf_mk]) (x := ⟨x, hx⟩) (by rwa [orderOf_mk]))
  have hNt : normalizer (L : Set G) ≤ centralizer ({(z : G)} : Set G) := by
    intro n hn
    have h1 : n * z * n⁻¹ = z := huniq _ (conj_mem_centralizer_of_mem_normalizer hn htC)
      (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht'])
    rw [mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h1]
  refine ⟨htC, huniq,
    le_antisymm (centralizer_le_normalizer_of_standard hL htC ht') hNt,
    fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl),
    fun c hc => mem_centralizer_singleton_iff.2 ?_⟩
  exact ((mem_centralizer_iff.1 hc) z z.2).symm

omit [Finite G] in
theorem seitz_commutator_sup_le_sup {K N : Subgroup G} (hKL : K ≤ centralizer (L : Set G))
    (hKK : ⁅K, K⁆ ≤ N) : ⁅L ⊔ K, L ⊔ K⁆ ≤ L ⊔ N := by
  have h := (CFSG.StandardType.GGL48TW.Cent.commutator_sup_le_of_le_normalizer (A := K) (N := L)
    (hKL.trans (Subgroup.centralizer_le_normalizer _))).trans (sup_le_sup hKK le_rfl)
  simpa only [sup_comm] using h

omit [Finite G] in
theorem seitz_mem_of_mem_sup_odd {N : Subgroup G} (hNL : N ≤ centralizer (L : Set G))
    (hN : Odd (Nat.card N)) (hLN : L ⊓ N = ⊥) {u : G} {m : ℕ} (hu : u ^ (2 ^ m) = 1)
    (huLN : u ∈ L ⊔ N) : u ∈ L := by
  have hcomm : ∀ a ∈ L, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (hNL hb) a ha
  obtain ⟨l, hl, n, hn, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm huLN
  have hc : Commute l n := hcomm l hl n hn
  have hn1 : n = 1 :=
    CFSG.ComponentClassification.AS81.NXKernel.eq_one_of_mul_pow hLN hN hl hn hc hu
  simpa [hn1] using hl

theorem seitz_commutator_le_pPrimeCore {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hS : IsCyclic (S : Subgroup H)) : commutator H ≤ CFSG.pPrimeCore 2 H := by
  obtain ⟨-, hmul, -, ⟨hnorm, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hS
  have hdec : ∀ x : H, ∃ n ∈ CFSG.pPrimeCore 2 H, ∃ s ∈ (S : Subgroup H), n * s = x := by
    intro x
    have hx : x ∈ ((CFSG.pPrimeCore 2 H : Set H) * (S : Set H)) := hmul ▸ Set.mem_univ x
    obtain ⟨n, hn, s, hs, h⟩ := hx
    exact ⟨n, hn, s, hs, h⟩
  have hSc : ∀ a ∈ (S : Subgroup H), ∀ b ∈ (S : Subgroup H), a * b = b * a := by
    intro a ha b hb
    have := hS.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  rw [_root_.commutator_def, commutator_le]
  intro a _ b _
  obtain ⟨n₁, hn₁, s₁, hs₁, rfl⟩ := hdec a
  obtain ⟨n₂, hn₂, s₂, hs₂, rfl⟩ := hdec b
  rw [← QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 H)]
  have e₁ : (QuotientGroup.mk (n₁ * s₁) : H ⧸ CFSG.pPrimeCore 2 H) = QuotientGroup.mk s₁ := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₁).2 hn₁, one_mul]
  have e₂ : (QuotientGroup.mk (n₂ * s₂) : H ⧸ CFSG.pPrimeCore 2 H) = QuotientGroup.mk s₂ := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₂).2 hn₂, one_mul]
  have hmk : ∀ x y : H, (QuotientGroup.mk ⁅x, y⁆ : H ⧸ CFSG.pPrimeCore 2 H) =
      ⁅(QuotientGroup.mk x : H ⧸ CFSG.pPrimeCore 2 H), QuotientGroup.mk y⁆ := fun x y =>
    map_commutatorElement (QuotientGroup.mk' (CFSG.pPrimeCore 2 H)) x y
  rw [hmk, e₁, e₂, ← hmk, commutatorElement_eq_one_iff_mul_comm.2 (hSc _ hs₁ _ hs₂),
    QuotientGroup.mk_one]

omit [Finite G] in
theorem seitz_commute_of_unique_involution {t c l r x : G}
    (htZ : ∀ m ∈ L, m * t = t * m)
    (huniq : ∀ k ∈ centralizer (L : Set G), k * k = 1 → k = 1 ∨ k = t)
    (hl : l ∈ L) (hr : r ∈ centralizer (L : Set G)) (hy : l * r = c * t * c⁻¹)
    (hrr : r * r = t) (ht₁L : c⁻¹ * t * c ∉ L)
    (hr₁L : ∀ m ∈ L, (c⁻¹ * r * c) * m * (c⁻¹ * r * c)⁻¹ ∈ L)
    (hx : x ∈ L) (hxt : x * (c⁻¹ * t * c) = (c⁻¹ * t * c) * x)
    (hxK : ∀ k ∈ centralizer (L : Set G),
      (c * x * c⁻¹) * k * (c * x * c⁻¹)⁻¹ ∈ centralizer (L : Set G)) :
    x * (c⁻¹ * r * c) = (c⁻¹ * r * c) * x := by
  set r₁ := c⁻¹ * r * c with hr₁
  set t₁ := c⁻¹ * t * c with ht₁
  set l₁ := c⁻¹ * l * c with hl₁
  set w := x * r₁ * x⁻¹ * r₁⁻¹ with hw
  have hwL : w ∈ L := by
    have h1 : r₁ * x⁻¹ * r₁⁻¹ ∈ L := hr₁L _ (inv_mem hx)
    have h2 : w = x * (r₁ * x⁻¹ * r₁⁻¹) := by rw [hw]; group
    rw [h2]
    exact mul_mem hx h1
  have hwK : c * w * c⁻¹ ∈ centralizer (L : Set G) := by
    have h1 := hxK r hr
    have h2 : c * w * c⁻¹ = (c * x * c⁻¹) * r * (c * x * c⁻¹)⁻¹ * r⁻¹ := by
      rw [hw, hr₁]; group
    rw [h2]
    exact mul_mem h1 (inv_mem hr)
  have hwt : Commute w t := htZ w hwL
  have hwl₁ : Commute w l₁ := by
    have h := (mem_centralizer_iff.1 hwK) l hl
    change w * l₁ = l₁ * w
    calc w * l₁ = c⁻¹ * ((c * w * c⁻¹) * l) * c := by rw [hl₁]; group
      _ = c⁻¹ * (l * (c * w * c⁻¹)) * c := by rw [← h]
      _ = l₁ * w := by rw [hl₁]; group
  have htlr : l₁ * r₁ = t := by
    rw [hl₁, hr₁]
    calc c⁻¹ * l * c * (c⁻¹ * r * c) = c⁻¹ * (l * r) * c := by group
      _ = t := by rw [hy]; group
  have hr₁eq : r₁ = l₁⁻¹ * t := by rw [← htlr]; group
  have hwr : Commute w r₁ := by
    rw [hr₁eq]
    exact hwl₁.inv_right.mul_right hwt
  have hr₁sq : r₁ * r₁ = t₁ := by
    rw [hr₁, ht₁]
    calc c⁻¹ * r * c * (c⁻¹ * r * c) = c⁻¹ * (r * r) * c := by group
      _ = c⁻¹ * t * c := by rw [hrr]
  have hww : w * w = 1 := by
    have e1 : x * r₁ * x⁻¹ = w * r₁ := by rw [hw]; group
    have e2 : (x * r₁ * x⁻¹) * (x * r₁ * x⁻¹) = t₁ := by
      calc (x * r₁ * x⁻¹) * (x * r₁ * x⁻¹) = x * (r₁ * r₁) * x⁻¹ := by group
        _ = x * t₁ * x⁻¹ := by rw [hr₁sq]
        _ = t₁ := by rw [hxt]; group
    have e3 : (w * r₁) * (w * r₁) = w * w * t₁ := by
      calc (w * r₁) * (w * r₁) = w * (r₁ * w) * r₁ := by group
        _ = w * (w * r₁) * r₁ := by rw [hwr.eq]
        _ = w * w * (r₁ * r₁) := by group
        _ = w * w * t₁ := by rw [hr₁sq]
    rw [e1, e3] at e2
    exact mul_eq_right.1 e2
  have hw1 : w = 1 := by
    have hsq : (c * w * c⁻¹) * (c * w * c⁻¹) = 1 := by
      calc (c * w * c⁻¹) * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
        _ = 1 := by rw [hww]; group
    rcases huniq _ hwK hsq with h | h
    · calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply ht₁L
      have h' : t₁ = w := by
        rw [ht₁]
        calc c⁻¹ * t * c = c⁻¹ * (c * w * c⁻¹) * c := by rw [h]
          _ = w := by group
      rw [h']
      exact hwL
  have h0 : x * r₁ * x⁻¹ * r₁⁻¹ = 1 := hw1
  calc x * r₁ = x * r₁ * x⁻¹ * r₁⁻¹ * (r₁ * x) := by group
    _ = r₁ * x := by rw [h0, one_mul]

namespace Setup

theorem congr_conj {A B : Type*} [Group A] [Group B] (ι : A ≃* B) (a : A) :
    MulAut.congr ι (MulAut.conj a) = MulAut.conj (ι a) := by
  ext b
  obtain ⟨a', rfl⟩ := ι.surjective b
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply, map_mul, map_inv]

end Setup

end CFSG.EvenSmallLie.GTwoFour
