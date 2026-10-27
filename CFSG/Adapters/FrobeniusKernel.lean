module

public import CFSG.CharacterTheory.FrobeniusKernel

public section

open Pointwise

namespace CFSG.Adapters

theorem frobenius_kernel {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH1 : H ≠ ⊥) (hHG : H ≠ ⊤)
    (hfrob : ∀ g : G, g ∉ H → H ⊓ (MulAut.conj g • H) = ⊥) :
    ∃ K : Subgroup G,
      (K : Set G) = {1} ∪ (Set.univ \ ⋃ g : G, ((MulAut.conj g • H : Subgroup G) : Set G)) ∧
      K.Normal ∧ (∀ x : G, ∃ k ∈ K, ∃ h ∈ H, x = k * h) ∧ K ⊓ H = ⊥ ∧
      Nat.card K = H.index := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hconj : ∀ a g : G, g ∈ MulAut.conj a • H ↔ a⁻¹ * g * a ∈ H := by
    intro a g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  have hfix : ∀ a g : G, g • (a : G ⧸ H) = (a : G ⧸ H) ↔ a⁻¹ * g * a ∈ H := by
    intro a g
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, ← H.inv_mem_iff]
    simp [mul_assoc]
  have hcore : ∀ c : G, (∀ a : G, a⁻¹ * c * a ∈ H) → c = 1 := by
    intro c hc
    obtain ⟨b, hb⟩ : ∃ b : G, b ∉ H := by
      by_contra! h
      exact hHG ((Subgroup.eq_top_iff' H).2 h)
    have hmem : c ∈ H ⊓ (MulAut.conj b • H) :=
      ⟨by simpa using hc 1, (hconj b c).2 (hc b)⟩
    rw [hfrob b hb] at hmem
    exact (Subgroup.mem_bot).1 hmem
  have hfaith : FaithfulSMul G (G ⧸ H) := by
    refine ⟨fun {g₁ g₂} h => ?_⟩
    have : g₂⁻¹ * g₁ = 1 := by
      refine hcore _ fun a => (hfix a _).1 ?_
      rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
    exact (inv_mul_eq_one.1 this).symm
  have hn : Fintype.card (G ⧸ H) = H.index := by
    rw [Fintype.card_eq_nat_card]; rfl
  have hcard : 2 ≤ Fintype.card (G ⧸ H) := by
    rw [hn]; exact H.one_lt_index_of_ne_top hHG
  have htrans : ∀ x y : G ⧸ H, ∃ g : G, g • x = y := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨b * a⁻¹, by rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]⟩
  have hstab : ∀ x : G ⧸ H, MulAction.stabilizer G x ≠ ⊥ := by
    intro x hbot
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨⟨h, hh⟩, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH1
    have hmem : a * h * a⁻¹ ∈ MulAction.stabilizer G (a : G ⧸ H) := by
      rw [MulAction.mem_stabilizer_iff, hfix]
      simpa [mul_assoc] using hh
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left] at hmem
    exact hne (Subtype.ext hmem)
  have hfrob' : ∀ g : G, g ≠ 1 → ∀ x y : G ⧸ H, g • x = x → g • y = y → x = y := by
    intro g hg x y hx hy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hfix] at hx hy
    rw [QuotientGroup.eq]
    by_contra hab
    have hmem : a⁻¹ * g * a ∈ H ⊓ (MulAut.conj (a⁻¹ * b) • H) := by
      refine ⟨hx, (hconj _ _).2 ?_⟩
      simpa [mul_assoc] using hy
    rw [hfrob _ hab, Subgroup.mem_bot] at hmem
    exact hg (by simpa [mul_assoc] using congrArg (fun t => a * t * a⁻¹) hmem)
  obtain ⟨K, hKn, hKset⟩ :=
    CFSG.FrobeniusKernel.frobenius_kernel_isNormal G (G ⧸ H) hcard htrans hstab
      hfrob'
  have hK : ∀ g : G, g ∈ K ↔ g = 1 ∨ ∀ x : G ⧸ H, g • x ≠ x := by
    intro g
    rw [← SetLike.mem_coe, hKset]
    rfl
  have hset : {g : G | ∀ x : G ⧸ H, g • x ≠ x} =
      Set.univ \ ⋃ a : G, ((MulAut.conj a • H : Subgroup G) : Set G) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_iUnion,
      SetLike.mem_coe, hconj, not_exists]
    rw [QuotientGroup.mk_surjective.forall]
    simp only [ne_eq, hfix]
  have hKH : K ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgK, hgH⟩
    rw [Subgroup.mem_bot]
    rcases (hK g).1 hgK with h | h
    · exact h
    · exact absurd ((hfix 1 g).2 (by simpa using hgH)) (h _)
  let f : K → G ⧸ H := fun k => ((k : G) : G ⧸ H)
  have hf : Function.Injective f := by
    intro k₁ k₂ h
    have h' : (k₁ : G)⁻¹ * k₂ ∈ K ⊓ H :=
      ⟨K.mul_mem (K.inv_mem k₁.2) k₂.2, QuotientGroup.eq.1 h⟩
    rw [hKH, Subgroup.mem_bot, inv_mul_eq_one] at h'
    exact Subtype.ext h'
  have hle : Nat.card K ≤ H.index := Nat.card_le_card_of_injective f hf
  have hge : H.index ≤ Nat.card K := by
    set n := H.index
    set s := Nat.card (MulAction.stabilizer G ((1 : G) : G ⧸ H))
    have hs : ∀ x : G ⧸ H,
        (Finset.univ.filter (fun g : G => g • x = x)).card = s := by
      intro x
      have h1 : (Finset.univ.filter (fun g : G => g • x = x)).card =
          Nat.card (MulAction.stabilizer G x) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp [MulAction.mem_stabilizer_iff]
      rw [h1]
      have e1 := (MulAction.stabilizer G x).card_mul_index
      have e2 := (MulAction.stabilizer G ((1 : G) : G ⧸ H)).card_mul_index
      rw [MulAction.index_stabilizer_of_transitive] at e1 e2
      have hX : 0 < Nat.card (G ⧸ H) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hX (e1.trans e2.symm)
    have hGs : Nat.card G = s * n := by
      rw [← (MulAction.stabilizer G ((1 : G) : G ⧸ H)).card_mul_index,
        MulAction.index_stabilizer_of_transitive]
      rfl
    have hs1 : 1 ≤ s := Nat.card_pos
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset G)) (fun g => g ∈ K)
    have hKcard : (Finset.univ.filter (fun g : G => g ∈ K)).card = Nat.card K := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hsub : Finset.univ.filter (fun g : G => g ∉ K) ⊆
        Finset.univ.biUnion (fun x : G ⧸ H =>
          (Finset.univ.filter (fun g : G => g • x = x)).erase 1) := by
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hK, not_or, not_forall,
        not_not] at hg
      obtain ⟨hg1, x, hx⟩ := hg
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase,
        Finset.mem_filter]
      exact ⟨x, hg1, hx⟩
    have hout : (Finset.univ.filter (fun g : G => g ∉ K)).card ≤ n * (s - 1) := by
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      have : ∀ x : G ⧸ H,
          ((Finset.univ.filter (fun g : G => g • x = x)).erase 1).card = s - 1 := by
        intro x
        rw [Finset.card_erase_of_mem (by simp), hs]
      simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [← hn]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hKcard] at hsplit
    have hmul : n * (s - 1) = s * n - n := by
      rw [Nat.mul_sub_one, Nat.mul_comm]
    have hnle : n ≤ s * n := Nat.le_mul_of_pos_left n hs1
    omega
  have hKeq : Nat.card K = H.index := le_antisymm hle hge
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    rw [Fintype.card_eq_nat_card, hKeq, hn]
  refine ⟨K, ?_, hKn, ?_, hKH, hKeq⟩
  · rw [hKset, hset]
  · intro x
    obtain ⟨k, hk⟩ := hbij.2 (x : G ⧸ H)
    exact ⟨k, k.2, (k : G)⁻¹ * x, QuotientGroup.eq.1 hk, by group⟩

end CFSG.Adapters
