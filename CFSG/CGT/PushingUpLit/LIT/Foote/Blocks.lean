module

public import CFSG.CGT.PushingUpLit.CGT6.EmbHyp
public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
open scoped commutatorElement

structure QBlock {G : Type} [Group G] [Finite G] (K : Subgroup G) : Prop where
  short : IsShortGroup ↥K
  quasisimple : CFSG.IsQuasisimple (↥K ⧸ pCore 2 ↥K)

namespace QBlock

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem perfect (h : QBlock K) : ⁅K, K⁆ = K :=
  CGT6.commutator_self_eq_of_isShortGroup h.short h.quasisimple

theorem blockU_stable (h : QBlock K) : ⁅blockU K, K⁆ = blockU K := by
  unfold blockU
  exact SixThree.commutator_commutator_eq
    (SubTwo.noTwoQuotient_of_oResidualTwo h.short.residual_eq) (SixThree.isPGroup_oTwoIn K)
    (SixThree.le_normalizer_oTwoIn K)

theorem isPGroup_blockU (_h : QBlock K) : IsPGroup 2 (blockU K) :=
  (SixThree.isPGroup_oTwoIn K).to_le (blockU_le_oTwoIn K)

theorem blockU_comm (h : QBlock K) : ∀ u ∈ blockU K, ∀ v ∈ blockU K, u * v = v * u :=
  fun u hu v hv => blockU_comm_of_short h.short u hu v (blockU_le_oTwoIn K hv)

omit [Finite G] in
theorem conj_mem_blockU' {g u : G} (hg : g ∈ K) (hu : u ∈ blockU K) : g * u * g⁻¹ ∈ blockU K :=
  conj_mem_blockU (Subgroup.le_normalizer hg) hu

theorem blockU_sq_mem_blockZ (h : QBlock K) : ∀ u ∈ blockU K, u * u ∈ blockZ K := by
  classical
  set S2 : Subgroup G := Subgroup.closure {x | ∃ u ∈ blockU K, x = u * u} with hS2
  have hS2U : S2 ≤ blockU K := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (blockU K).mul_mem hu hu
  have hnorm : ∀ g ∈ K, ∀ x ∈ S2, g * x * g⁻¹ ∈ S2 := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨g * u * g⁻¹, conj_mem_blockU' hg hu, ?_⟩
      group
    | one => simp
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact S2.mul_mem hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact S2.inv_mem hx
  have hKN : K ≤ Subgroup.normalizer (S2 : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm g hg x hx, fun hx => ?_⟩
    have := hnorm g⁻¹ (K.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hsq : ∀ x ∈ S2, ∃ u ∈ blockU K, x = u * u := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (blockU K).one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      refine ⟨u * v, (blockU K).mul_mem hu hv, ?_⟩
      have hc := h.blockU_comm u hu v hv
      calc u * u * (v * v) = u * (u * v) * v := by group
        _ = u * (v * u) * v := by rw [hc]
        _ = u * v * (u * v) := by group
    | inv x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨u⁻¹, (blockU K).inv_mem hu, by group⟩
  by_cases hcom : ⁅S2, K⁆ = ⊥
  · intro u hu
    have h1 : u * u ∈ S2 := Subgroup.subset_closure ⟨u, hu, rfl⟩
    have h2 : S2 ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcom
    exact Subgroup.mem_inf.2 ⟨(blockU K).mul_mem hu hu, h2 h1⟩
  · exfalso
    have hle : ⁅S2, K⁆ ≤ oTwoIn K :=
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hKN).trans
        (hS2U.trans (blockU_le_oTwoIn K))
    have hU := SixThree.commutator_eq_U h.short ((h.isPGroup_blockU).to_le hS2U) hKN hle hcom
    have hUS : blockU K ≤ S2 := by
      unfold blockU
      rw [← hU]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hKN
    have hsurj : Function.Surjective (fun u : ↥(blockU K) => u * u) := by
      intro y
      obtain ⟨u, hu, e⟩ := hsq y (hUS y.2)
      exact ⟨⟨u, hu⟩, Subtype.ext e.symm⟩
    have hinj : Function.Injective (fun u : ↥(blockU K) => u * u) :=
      Finite.injective_iff_surjective.2 hsurj
    have : Nontrivial ↥(blockU K) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 (blockU_ne_bot_of_short h.short)
    have hdvd : 2 ∣ Nat.card ↥(blockU K) := by
      rcases (h.isPGroup_blockU).card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_iff_card _ |>.2 h1) (blockU_ne_bot_of_short h.short)
      · exact h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hw2 : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rw [hw] at this
      simpa [pow_two] using this
    have hw1 : w = 1 := hinj (by simpa using hw2.trans (mul_one 1).symm)
    rw [hw1, orderOf_one] at hw
    omega

theorem blockU_sq_eq_one (h : QBlock K) : ∀ u ∈ blockU K, u * u = 1 := by
  have hgen : ∀ u ∈ blockU K, ∀ k ∈ K, ⁅u, k⁆ ∈ blockU K ∧ ⁅u, k⁆ * ⁅u, k⁆ = 1 := by
    intro u hu k hk
    have hw : k * u * k⁻¹ ∈ blockU K := conj_mem_blockU' hk hu
    have hc : ⁅u, k⁆ = u * (k * u * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    refine ⟨?_, ?_⟩
    · rw [hc]
      exact (blockU K).mul_mem hu ((blockU K).inv_mem hw)
    · have hz : u * u ∈ Subgroup.centralizer (K : Set G) :=
        (h.blockU_sq_mem_blockZ u hu).2
      have hkz : k * (u * u) = (u * u) * k := Subgroup.mem_centralizer_iff.1 hz k hk
      have hwz : (k * u * k⁻¹) * (k * u * k⁻¹) = u * u := by
        calc (k * u * k⁻¹) * (k * u * k⁻¹) = k * (u * u) * k⁻¹ := by group
          _ = (u * u) * k * k⁻¹ := by rw [hkz]
          _ = u * u := by group
      have hcomm : u * (k * u * k⁻¹)⁻¹ = (k * u * k⁻¹)⁻¹ * u :=
        h.blockU_comm u hu _ ((blockU K).inv_mem hw)
      rw [hc]
      calc u * (k * u * k⁻¹)⁻¹ * (u * (k * u * k⁻¹)⁻¹)
          = u * ((k * u * k⁻¹)⁻¹ * u) * (k * u * k⁻¹)⁻¹ := by group
        _ = u * (u * (k * u * k⁻¹)⁻¹) * (k * u * k⁻¹)⁻¹ := by rw [hcomm]
        _ = (u * u) * ((k * u * k⁻¹) * (k * u * k⁻¹))⁻¹ := by group
        _ = 1 := by rw [hwz]; group
  suffices H : ∀ x ∈ ⁅blockU K, K⁆, x ∈ blockU K ∧ x * x = 1 by
    intro u hu
    exact (H u (h.blockU_stable.symm ▸ hu)).2
  intro x hx
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, hu, k, hk, rfl⟩ := hx
    exact hgen u hu k hk
  | one => exact ⟨(blockU K).one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    refine ⟨(blockU K).mul_mem hx.1 hy.1, ?_⟩
    have hc := h.blockU_comm x hx.1 y hy.1
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx.2, hy.2]; simp
  | inv x _ hx =>
    refine ⟨(blockU K).inv_mem hx.1, ?_⟩
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hx.2]; simp

theorem eight_le_card_blockU (h : QBlock K) : 8 ≤ Nat.card ↥(blockU K) := by
  by_contra hlt
  push Not at hlt
  have hcard : Nat.card ↥(blockU K) ≤ 4 := by
    obtain ⟨n, hn⟩ := (h.isPGroup_blockU).exists_card_eq
    have : n < 3 := by
      by_contra hn3
      push Not at hn3
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      omega
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 h.perfect
  have hsolv : Group.IsSolvable (Equiv.Perm ↥(blockU K)) := Equiv.Perm.isSolvable hcard
  let ψ : ↥K →* Equiv.Perm ↥(blockU K) :=
    (MulAut.toPerm ↥(blockU K)).comp
      ((Subgroup.normalizerMonoidHom (blockU K)).comp
        (Subgroup.inclusion (le_normalizer_blockU K)))
  have htriv : ∀ k ∈ K, ∀ u ∈ blockU K, k * u * k⁻¹ = u := by
    intro k hk u hu
    have h1 := hom_eq_one_of_perfect_of_solvable ψ ⟨k, hk⟩
    have h2 := congrArg (fun σ : Equiv.Perm ↥(blockU K) => (σ ⟨u, hu⟩ : G)) h1
    have e : (ψ ⟨k, hk⟩ ⟨u, hu⟩ : G) = k * u * k⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe (blockU K) ⟨k, le_normalizer_blockU K hk⟩
        ⟨u, hu⟩
    have h3 : (ψ ⟨k, hk⟩ ⟨u, hu⟩ : G) = u := by
      have := h2
      simpa using this
    rw [← e, h3]
  have hcent : blockU K ≤ Subgroup.centralizer (K : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := htriv k hk u hu
    calc k * u = (k * u * k⁻¹) * k := by group
      _ = u * k := by rw [this]
  have hbot : ⁅blockU K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  exact blockU_ne_bot_of_short h.short (h.blockU_stable.symm.trans hbot)

end QBlock

end CFSG.CGT.PushingUpLit.LIT.Foote
