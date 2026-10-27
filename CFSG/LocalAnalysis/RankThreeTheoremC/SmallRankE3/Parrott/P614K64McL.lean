module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64Types
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Holds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64

open CFSG.Open CFSG.HardMathSupport.Solomon Subgroup

variable {V : Type} [CommGroup V]

section Coset

variable {N : Subgroup (MulAut V)} {τ : MulAut V}

theorem inv_eq_of_mul_self (hτ2 : τ * τ = 1) : τ⁻¹ = τ :=
  (eq_inv_of_mul_eq_one_left hτ2).symm

theorem conj_inv_mem (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) {n : MulAut V}
    (hn : n ∈ N) : τ⁻¹ * n * τ ∈ N := by
  have h := hτN n hn
  rwa [inv_eq_of_mul_self hτ2] at h ⊢

theorem conj_inv_inv_mem (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) {n : MulAut V}
    (hn : n ∈ N) : τ⁻¹ * n * τ⁻¹ ∈ N := by
  have e : τ⁻¹ * n * τ⁻¹ = τ⁻¹ * n * τ := by rw [inv_eq_of_mul_self hτ2]
  rw [e]
  exact conj_inv_mem hτ2 hτN hn

@[expose] def cosetSub (N : Subgroup (MulAut V)) (τ : MulAut V) (hτ2 : τ * τ = 1)
    (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) : Subgroup (MulAut V) where
  carrier := {g | g ∈ N ∨ g * τ ∈ N}
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (N.mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact N.mul_mem ha hb)
    · refine Or.inr ?_
      have h1 : a * b * τ = (a * τ) * (τ⁻¹ * b * τ) := by group
      rw [h1]
      exact N.mul_mem ha (conj_inv_mem hτ2 hτN hb)
    · refine Or.inl ?_
      have h1 : a * b = (a * τ) * (τ⁻¹ * (b * τ) * τ⁻¹) := by group
      rw [h1]
      exact N.mul_mem ha (conj_inv_inv_mem hτ2 hτN hb)
  one_mem' := Or.inl N.one_mem
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (N.inv_mem ha)
    · refine Or.inr ?_
      have hinv := inv_eq_of_mul_self hτ2
      have h1 : a⁻¹ * τ = τ * (a * τ)⁻¹ * τ⁻¹ := by
        calc a⁻¹ * τ = a⁻¹ * τ⁻¹ := by rw [hinv]
          _ = τ * (a * τ)⁻¹ * τ⁻¹ := by group
      rw [h1]
      exact hτN _ (N.inv_mem ha)

theorem le_cosetSub (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) :
    N ≤ cosetSub N τ hτ2 hτN := fun _ h => Or.inl h

theorem tau_mem_cosetSub (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) :
    τ ∈ cosetSub N τ hτ2 hτN := Or.inr (by rw [hτ2]; exact N.one_mem)

theorem eq_mul_inv_of_mul (g : MulAut V) : g = (g * τ) * τ⁻¹ := by group

theorem conj_mem_of_mem_cosetSub (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    {g n : MulAut V} (hg : g ∈ cosetSub N τ hτ2 hτN) (hn : n ∈ N) : g * n * g⁻¹ ∈ N := by
  rcases hg with hg | hg
  · exact N.mul_mem (N.mul_mem hg hn) (N.inv_mem hg)
  · have h1 : g * n * g⁻¹ = (g * τ) * (τ⁻¹ * n * τ) * (g * τ)⁻¹ := by group
    rw [h1]
    exact N.mul_mem (N.mul_mem hg (conj_inv_mem hτ2 hτN hn)) (N.inv_mem hg)

theorem mul_self_mem_of_mem_cosetSub (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    {g : MulAut V} (hg : g ∈ cosetSub N τ hτ2 hτN) : g * g ∈ N := by
  rcases hg with hg | hg
  · exact N.mul_mem hg hg
  · have h1 : g * g = (g * τ) * (τ⁻¹ * (g * τ) * τ⁻¹) := by group
    rw [h1]
    exact N.mul_mem hg (conj_inv_inv_mem hτ2 hτN hg)

theorem cosetSub_le_of_mem (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) (hτ : τ ∈ N) :
    cosetSub N τ hτ2 hτN ≤ N := by
  intro g hg
  rcases hg with hg | hg
  · exact hg
  · rw [eq_mul_inv_of_mul (τ := τ) g]
    exact N.mul_mem hg (N.inv_mem hτ)

theorem card_cosetSub_of_not_mem (hτ2 : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    (hτ : τ ∉ N) : Nat.card (cosetSub N τ hτ2 hτN) = 2 * Nat.card N := by
  have h2 : N.relIndex (cosetSub N τ hτ2 hτN) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨τ, tau_mem_cosetSub hτ2 hτN, fun b hb => ?_⟩
    have e : τ = b⁻¹ * (b * τ) := by group
    rcases hb with hb | hb
    · refine Or.inr ⟨hb, fun h => hτ ?_⟩
      rw [e]
      exact N.mul_mem (N.inv_mem hb) h
    · refine Or.inl ⟨hb, fun h => hτ ?_⟩
      rw [e]
      exact N.mul_mem (N.inv_mem h) hb
  have h := relIndex_mul_card N (cosetSub N τ hτ2 hτN)
  rw [inf_of_le_left (le_cosetSub hτ2 hτN), h2] at h
  exact h.symm

end Coset

section Aux

variable {G : Type*} [Group G]

theorem le_normalizer_closure_of_conj {H : Subgroup G} {S : Set G}
    (h : ∀ g ∈ H, ∀ s ∈ S, g * s * g⁻¹ ∈ S) : H ≤ normalizer (closure S : Set G) := by
  have key : ∀ g ∈ H, ∀ x ∈ closure S, g * x * g⁻¹ ∈ closure S := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact subset_closure (h g hg s hs)
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact mul_mem ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ha
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using h1

theorem normal_inf_subgroupOf {N L : Subgroup G} (hNL : N ≤ normalizer (L : Set G)) :
    ((N ⊓ L).subgroupOf N).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  rw [mem_inf, mem_inf, (mem_normalizer_iff.mp (hNL hg) x)]
  constructor
  · rintro ⟨hx, hx'⟩
    exact ⟨N.mul_mem (N.mul_mem hg hx) (N.inv_mem hg), hx'⟩
  · rintro ⟨hx, hx'⟩
    refine ⟨?_, hx'⟩
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this]
    exact N.mul_mem (N.mul_mem (N.inv_mem hg) hx) hg

theorem inf_eq_bot_or_le {N L : Subgroup G} [IsSimpleGroup ↥N]
    (hNL : N ≤ normalizer (L : Set G)) : N ⊓ L = ⊥ ∨ N ≤ L := by
  haveI := normal_inf_subgroupOf hNL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ L).subgroupOf N) with h | h
  · left
    rw [subgroupOf_eq_bot] at h
    exact eq_bot_iff.mpr fun x hx => (Subgroup.disjoint_def.mp h) hx hx.1
  · right
    rw [subgroupOf_eq_top] at h
    exact h.trans inf_le_right

theorem comm_of_commutator_eq_one {a b : G} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

theorem comm_of_inv_commutator_eq_one {a b : G} (h : a⁻¹ * b⁻¹ * a * b = 1) : a * b = b * a := by
  calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
    _ = b * a := by rw [h, mul_one]

theorem center_eq_bot_of_l34 [Finite G] [IsSimpleGroup G] (hc : Nat.card G = 20160)
    (hi : ∀ t : G, orderOf t = 2 → Nat.card (centralizer ({t} : Set G)) = 64) :
    center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (by rw [hc]; norm_num)
    have h64 := hi t ht
    have htop : centralizer ({t} : Set G) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [mem_centralizer_singleton_iff]
      have : t ∈ center G := h ▸ mem_top t
      exact mem_center_iff.mp this g
    rw [htop, card_top, hc] at h64
    norm_num at h64

end Aux

section Main

variable [Finite V]

theorem pCoreOf_cosetSub_eq_bot {N : Subgroup (MulAut V)} [IsSimpleGroup ↥N]
    (hNc : Nat.card N = 20160) {τ : MulAut V} (hτ2 : τ * τ = 1)
    (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    (hout : ∀ n ∈ N, (∀ m ∈ N, n * τ * m = m * (n * τ)) → n * τ = 1) :
    pCoreOf 2 (cosetSub N τ hτ2 hτN) = ⊥ := by
  set P := cosetSub N τ hτ2 hτN
  set R := pCoreOf 2 P with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hRP : R ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPR : P ≤ normalizer (R : Set (MulAut V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hNP : N ≤ P := le_cosetSub hτ2 hτN
  have hRN : N ⊓ R = ⊥ := by
    rcases inf_eq_bot_or_le (L := R) (hNP.trans hPR) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR2.to_le h)
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hk, hNc]
        norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hcomm : ∀ r ∈ R, ∀ m ∈ N, r * m = m * r := by
    intro r hr m hm
    have hP := hRP hr
    have h1 : r * m * r⁻¹ * m⁻¹ ∈ N :=
      N.mul_mem (conj_mem_of_mem_cosetSub hτ2 hτN hP hm) (N.inv_mem hm)
    have h2 : r * m * r⁻¹ * m⁻¹ ∈ R := by
      have h3 : m * r⁻¹ * m⁻¹ ∈ R :=
        (mem_normalizer_iff.mp (hPR (hNP hm)) r⁻¹).mp (R.inv_mem hr)
      have : r * m * r⁻¹ * m⁻¹ = r * (m * r⁻¹ * m⁻¹) := by group
      rw [this]
      exact R.mul_mem hr h3
    have h4 : r * m * r⁻¹ * m⁻¹ ∈ N ⊓ R := ⟨h1, h2⟩
    rw [hRN, mem_bot] at h4
    calc r * m = r * m * r⁻¹ * m⁻¹ * (m * r) := by group
      _ = m * r := by rw [h4, one_mul]
  refine eq_bot_iff.mpr fun r hr => mem_bot.mpr ?_
  rcases hRP hr with hrN | hrN
  · have : r ∈ N ⊓ R := ⟨hrN, hr⟩
    rwa [hRN, mem_bot] at this
  · have hr' : r * τ * τ = r := by rw [mul_assoc, hτ2, mul_one]
    have h1 := hout (r * τ) hrN (fun m hm => by rw [hr']; exact hcomm r hr m hm)
    rwa [hr'] at h1

theorem hout_of_mem {N : Subgroup (MulAut V)} [IsSimpleGroup ↥N] (hNc : Nat.card N = 20160)
    (hNi : ∀ t : ↥N, orderOf t = 2 → Nat.card (centralizer ({t} : Set ↥N)) = 64)
    {τ : MulAut V} (hτ : τ ∈ N) :
    ∀ n ∈ N, (∀ m ∈ N, n * τ * m = m * (n * τ)) → n * τ = 1 := by
  intro n hn h
  have hz := center_eq_bot_of_l34 hNc hNi
  have hmem : (⟨n * τ, N.mul_mem hn hτ⟩ : ↥N) ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (h g g.2).symm
  rw [hz, mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem false_of_transvection (hV : ∀ v : V, v * v = 1) (N : Subgroup (MulAut V))
    [IsSimpleGroup ↥N] (hNc : Nat.card N = 20160)
    (hNi : ∀ t : ↥N, orderOf t = 2 → Nat.card (centralizer ({t} : Set ↥N)) = 64)
    (τ : MulAut V) (hτ : UniquenessMaximal.IsTransvection τ) (hτ2 : τ * τ = 1)
    (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) (hτc : ∃ n ∈ N, τ * n ≠ n * τ)
    (hout : ∀ n ∈ N, (∀ m ∈ N, n * τ * m = m * (n * τ)) → n * τ = 1) : False := by
  have hNP : N ≤ cosetSub N τ hτ2 hτN := le_cosetSub hτ2 hτN
  have hτP : τ ∈ cosetSub N τ hτ2 hτN := tau_mem_cosetSub hτ2 hτN
  have hR := pCoreOf_cosetSub_eq_bot hNc hτ2 hτN hout
  obtain ⟨r, W, hsup, hWP, hcomm, -, -, -, hτW, hmc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.input28_5_holds V hV _ hR τ hτP hτ
  obtain ⟨n₀, hn₀, hn₀c⟩ := hτc
  have hτT : τ ∈ closure {τ' | ∃ g ∈ cosetSub N τ hτ2 hτN, τ' = g⁻¹ * τ * g} :=
    subset_closure ⟨1, one_mem _, by group⟩
  have hPT' : cosetSub N τ hτ2 hτN ≤
      normalizer (closure {τ' | ∃ g ∈ cosetSub N τ hτ2 hτN, τ' = g⁻¹ * τ * g} :
        Set (MulAut V)) := by
    refine le_normalizer_closure_of_conj fun g hg s hs => ?_
    obtain ⟨h, hh, rfl⟩ := hs
    exact ⟨h * g⁻¹, (cosetSub N τ hτ2 hτN).mul_mem hh ((cosetSub N τ hτ2 hτN).inv_mem hg),
      by group⟩
  have hNT : N ≤ closure {τ' | ∃ g ∈ cosetSub N τ hτ2 hτN, τ' = g⁻¹ * τ * g} := by
    rcases inf_eq_bot_or_le (hNP.trans hPT') with h | h
    · exfalso
      apply hn₀c
      have h1 : τ⁻¹ * n₀⁻¹ * τ * n₀ ∈
          N ⊓ closure {τ' | ∃ g ∈ cosetSub N τ hτ2 hτN, τ' = g⁻¹ * τ * g} := by
        have e : τ⁻¹ * n₀⁻¹ * τ * n₀ = τ⁻¹ * (n₀⁻¹ * τ * n₀) := by group
        refine ⟨?_, ?_⟩
        · have e' : τ⁻¹ * n₀⁻¹ * τ * n₀ = (τ⁻¹ * n₀⁻¹ * τ) * n₀ := by group
          rw [e']
          exact N.mul_mem (conj_inv_mem hτ2 hτN (N.inv_mem hn₀)) hn₀
        · rw [e]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hτT)
            (Subgroup.subset_closure ⟨n₀, hNP hn₀, rfl⟩)
      rw [h, mem_bot] at h1
      exact comm_of_inv_commutator_eq_one h1
    · exact h
  have hPT : cosetSub N τ hτ2 hτN ≤ ⨆ i, W i := by
    rw [hsup]
    intro g hg
    rcases hg with hg | hg
    · exact hNT hg
    · rw [eq_mul_inv_of_mul (τ := τ) g]
      exact mul_mem (hNT hg) (inv_mem hτT)
  have hPN : cosetSub N τ hτ2 hτN ≤ normalizer (W 0 : Set (MulAut V)) := by
    refine hPT.trans (iSup_le fun i => ?_)
    by_cases hi : i = 0
    · subst hi
      exact le_normalizer
    · exact (hcomm i 0 hi).trans (centralizer_le_normalizer _)
  have hNW : N ≤ W 0 := by
    rcases inf_eq_bot_or_le (hNP.trans hPN) with h | h
    · exfalso
      apply hn₀c
      have h1 : τ * n₀ * τ⁻¹ * n₀⁻¹ ∈ N ⊓ W 0 := by
        refine ⟨N.mul_mem (hτN n₀ hn₀) (N.inv_mem hn₀), ?_⟩
        have h3 : n₀ * τ⁻¹ * n₀⁻¹ ∈ W 0 :=
          (mem_normalizer_iff.mp (hPN (hNP hn₀)) τ⁻¹).mp (inv_mem hτW)
        have e : τ * n₀ * τ⁻¹ * n₀⁻¹ = τ * (n₀ * τ⁻¹ * n₀⁻¹) := by group
        rw [e]
        exact mul_mem hτW h3
      rw [h, mem_bot] at h1
      exact comm_of_commutator_eq_one h1
    · exact h
  have hWP0 : W 0 = cosetSub N τ hτ2 hτN := by
    refine le_antisymm (hWP 0) fun g hg => ?_
    rcases hg with hg | hg
    · exact hNW hg
    · rw [eq_mul_inv_of_mul (τ := τ) g]
      exact mul_mem (hNW hg) (inv_mem hτW)
  have hcard : Nat.card ↥(W 0) = 20160 ∨ Nat.card ↥(W 0) = 40320 := by
    rw [hWP0]
    by_cases hτN' : τ ∈ N
    · left
      rw [le_antisymm (cosetSub_le_of_mem hτ2 hτN hτN') hNP, hNc]
    · right
      rw [card_cosetSub_of_not_mem hτ2 hτN hτN', hNc]
  obtain ⟨x, t₁, t₂, hx, h1, h2, hne, h12, hx1, hx2⟩ := mcl_hasThreeTwoTwo (hmc 0) hcard
  have hxP : (x : MulAut V) ∈ cosetSub N τ hτ2 hτN := hWP 0 x.2
  have ht₁P : (t₁ : MulAut V) ∈ cosetSub N τ hτ2 hτN := hWP 0 t₁.2
  have ht₂P : (t₂ : MulAut V) ∈ cosetSub N τ hτ2 hτN := hWP 0 t₂.2
  have hx3 : (x : MulAut V) ^ 3 = 1 := by
    rw [← hx, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have ht₁sq : (t₁ : MulAut V) * t₁ = 1 := by
    rw [← pow_two, ← h1, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have ht₂sq : (t₂ : MulAut V) * t₂ = 1 := by
    rw [← pow_two, ← h2, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have h12' : (t₁ : MulAut V) * t₂ = t₂ * t₁ := congrArg Subtype.val h12
  have hx1' : (x : MulAut V) * t₁ = t₁ * x := congrArg Subtype.val hx1
  have hx2' : (x : MulAut V) * t₂ = t₂ * x := congrArg Subtype.val hx2
  have hxN : (x : MulAut V) ∈ N := by
    have e : (x : MulAut V) = ((x : MulAut V) * x) * ((x : MulAut V) * x) := by
      calc (x : MulAut V) = (x : MulAut V) ^ 3 * x := by rw [hx3, one_mul]
        _ = _ := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    exact N.mul_mem (mul_self_mem_of_mem_cosetSub hτ2 hτN hxP)
      (mul_self_mem_of_mem_cosetSub hτ2 hτN hxP)
  obtain ⟨t, htN, ht2, htx⟩ : ∃ t ∈ N, orderOf t = 2 ∧ (x : MulAut V) * t = t * x := by
    by_cases h1N : (t₁ : MulAut V) ∈ N
    · exact ⟨t₁, h1N, by rwa [Subgroup.orderOf_coe], hx1'⟩
    by_cases h2N : (t₂ : MulAut V) ∈ N
    · exact ⟨t₂, h2N, by rwa [Subgroup.orderOf_coe], hx2'⟩
    have h1τ : (t₁ : MulAut V) * τ ∈ N := ht₁P.resolve_left h1N
    have h2τ : (t₂ : MulAut V) * τ ∈ N := ht₂P.resolve_left h2N
    have ht₂inv : (t₂ : MulAut V)⁻¹ = t₂ := inv_eq_of_mul_self ht₂sq
    refine ⟨t₁ * t₂, ?_, ?_, ?_⟩
    · have e : (t₁ : MulAut V) * t₂ = ((t₁ : MulAut V) * τ) * ((t₂ : MulAut V) * τ)⁻¹ := by
        calc (t₁ : MulAut V) * t₂ = (t₁ : MulAut V) * (t₂ : MulAut V)⁻¹ := by rw [ht₂inv]
          _ = _ := by group
      rw [e]
      exact N.mul_mem h1τ (N.inv_mem h2τ)
    · refine orderOf_eq_prime ?_ ?_
      · have e2 : ((t₁ : MulAut V) * t₂) ^ 2 = (t₁ : MulAut V) * (t₂ * t₁) * t₂ := by
          rw [pow_two]
          simp only [mul_assoc]
        calc ((t₁ : MulAut V) * t₂) ^ 2 = (t₁ : MulAut V) * (t₂ * t₁) * t₂ := e2
          _ = (t₁ : MulAut V) * (t₁ * t₂) * t₂ := by rw [h12']
          _ = ((t₁ : MulAut V) * t₁) * ((t₂ : MulAut V) * t₂) := by group
          _ = 1 := by rw [ht₁sq, ht₂sq, one_mul]
      · intro h
        apply hne
        apply Subtype.ext
        calc (t₁ : MulAut V) = (t₁ : MulAut V) * t₂ * (t₂ : MulAut V)⁻¹ := by group
          _ = (t₂ : MulAut V) := by rw [h, one_mul, ht₂inv]
    · calc (x : MulAut V) * (t₁ * t₂) = ((x : MulAut V) * t₁) * t₂ := by group
        _ = (t₁ : MulAut V) * ((x : MulAut V) * t₂) := by rw [hx1']; group
        _ = (t₁ : MulAut V) * t₂ * x := by rw [hx2']; group
  have hmem : (⟨x, hxN⟩ : ↥N) ∈ centralizer ({(⟨t, htN⟩ : ↥N)} : Set ↥N) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext htx
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hNi ⟨t, htN⟩ (by rwa [Subgroup.orderOf_mk]), Subgroup.orderOf_mk, Subgroup.orderOf_coe,
    hx] at hdvd
  norm_num at hdvd

theorem mul_self_eq_one_of_central {N : Subgroup (MulAut V)} {τ n : MulAut V} (hτ2 : τ * τ = 1)
    (hn : n ∈ N) (hz : center ↥N = ⊥) (hc : ∀ m ∈ N, n * τ * m = m * (n * τ)) :
    n * τ * (n * τ) = 1 := by
  have h1 : τ * n = n * τ := by
    have h2 : n * (τ * n) = n * (n * τ) := by rw [← mul_assoc, hc n hn]
    exact mul_left_cancel h2
  have hsq : n * τ * (n * τ) = n * n := by
    calc n * τ * (n * τ) = n * (τ * n) * τ := by group
      _ = n * (n * τ) * τ := by rw [h1]
      _ = n * n * (τ * τ) := by group
      _ = n * n := by rw [hτ2, mul_one]
  have hmem : (⟨n * n, N.mul_mem hn hn⟩ : ↥N) ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : MulAut V) * (n * n) = n * n * g
    rw [← hsq]
    have h3 := hc g g.2
    calc (g : MulAut V) * (n * τ * (n * τ)) = (g * (n * τ)) * (n * τ) := by group
      _ = (n * τ * g) * (n * τ) := by rw [← h3]
      _ = (n * τ) * (g * (n * τ)) := by group
      _ = (n * τ) * (n * τ * g) := by rw [← h3]
      _ = n * τ * (n * τ) * g := by group
  rw [hsq]
  rw [hz, mem_bot] at hmem
  exact congrArg Subtype.val hmem

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64
