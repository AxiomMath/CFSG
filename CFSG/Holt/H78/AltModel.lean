module

public import CFSG.Holt.H78.Defs
import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction

section LongInvolutions

variable {Δ : Type*}

theorem mem_longInv_subgroup_perm_iff {M : Subgroup (Perm Δ)} {σ : M} :
    σ ∈ longInv M Δ ↔ (σ : Perm Δ) ∈ longInv (Perm Δ) Δ := by
  simp only [mem_longInv, Subgroup.smul_def, Subgroup.orderOf_coe]

theorem mem_longInvAt_subgroup_perm_iff {M : Subgroup (Perm Δ)} {σ : M} {α : Δ} :
    σ ∈ longInvAt M Δ α ↔ (σ : Perm Δ) ∈ longInvAt (Perm Δ) Δ α := by
  simp only [mem_longInvAt, mem_longInv_subgroup_perm_iff, Subgroup.smul_def]

theorem apply_eq_self_iff_of_mem_longInvAt_perm {σ : Perm Δ} {α x : Δ}
    (hσ : σ ∈ longInvAt (Perm Δ) Δ α) : σ x = x ↔ x = α := by
  obtain ⟨⟨-, ω, -, huniq⟩, hα⟩ := hσ
  exact ⟨fun hx => (huniq x hx).trans (huniq α hα).symm, fun hx => hx ▸ hα⟩

private theorem sq_eq_one_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ) :
    σ ^ 2 = 1 := by
  rw [← hσ.1]
  exact pow_orderOf_eq_one σ

private theorem apply_apply_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ)
    (x : Δ) : σ (σ x) = x := by
  rw [← Perm.mul_apply, ← sq, sq_eq_one_of_mem_longInv_perm hσ, Perm.one_apply]

variable [Fintype Δ] [DecidableEq Δ]

theorem support_eq_erase_of_mem_longInvAt_perm {σ : Perm Δ} {α : Δ}
    (hσ : σ ∈ longInvAt (Perm Δ) Δ α) : σ.support = Finset.univ.erase α := by
  ext x
  rw [Perm.mem_support, Finset.mem_erase, and_iff_left (Finset.mem_univ x), Ne,
    apply_eq_self_iff_of_mem_longInvAt_perm hσ]

theorem card_support_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ) :
    σ.support.card = Fintype.card Δ - 1 := by
  obtain ⟨α, hα, -⟩ := hσ.2
  rw [support_eq_erase_of_mem_longInvAt_perm ⟨hσ, hα⟩,
    Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ]

theorem odd_card_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ) :
    Odd (Fintype.card Δ) := by
  have h2 := two_dvd_card_support (sq_eq_one_of_mem_longInv_perm hσ)
  rw [card_support_of_mem_longInv_perm hσ] at h2
  obtain ⟨α, -⟩ := hσ.2
  have : 0 < Fintype.card Δ := Fintype.card_pos_iff.mpr ⟨α⟩
  rw [Nat.odd_iff]
  omega

theorem three_le_card_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ) :
    3 ≤ Fintype.card Δ := by
  have hne : σ ≠ 1 := by
    rintro rfl
    have h := hσ.1
    rw [orderOf_one] at h
    omega
  have h2 := two_le_card_support_of_ne_one hne
  rw [card_support_of_mem_longInv_perm hσ] at h2
  omega

theorem cycleType_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ) :
    σ.cycleType = Multiset.replicate ((Fintype.card Δ - 1) / 2) 2 := by
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k 2 :=
    ⟨_, cycleType_of_pow_prime_eq_one (sq_eq_one_of_mem_longInv_perm hσ)⟩
  have hsum := sum_cycleType σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul, card_support_of_mem_longInv_perm hσ] at hsum
  rw [hk]
  congr 1
  omega

theorem sign_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ) :
    sign σ = (-1) ^ ((Fintype.card Δ - 1) / 2) := by
  rw [sign_of_cycleType, cycleType_of_mem_longInv_perm hσ, Multiset.sum_replicate,
    Multiset.card_replicate, smul_eq_mul, pow_add, pow_mul', Int.units_sq, one_pow, one_mul]

theorem sign_eq_of_mem_longInv_perm {σ τ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ)
    (hτ : τ ∈ longInv (Perm Δ) Δ) : sign σ = sign τ := by
  rw [sign_of_mem_longInv_perm hσ, sign_of_mem_longInv_perm hτ]

theorem mem_alternatingGroup_iff_of_mem_longInv_perm {σ : Perm Δ}
    (hσ : σ ∈ longInv (Perm Δ) Δ) : σ ∈ alternatingGroup Δ ↔ Fintype.card Δ % 4 = 1 := by
  have hodd := odd_card_of_mem_longInv_perm hσ
  rw [Nat.odd_iff] at hodd
  rw [mem_alternatingGroup, sign_of_mem_longInv_perm hσ, neg_one_pow_eq_one_iff_even (by decide),
    Nat.even_iff]
  omega

theorem notMem_alternatingGroup_iff_of_mem_longInv_perm {σ : Perm Δ}
    (hσ : σ ∈ longInv (Perm Δ) Δ) : σ ∉ alternatingGroup Δ ↔ Fintype.card Δ % 4 = 3 := by
  have hodd := odd_card_of_mem_longInv_perm hσ
  rw [Nat.odd_iff] at hodd
  rw [mem_alternatingGroup_iff_of_mem_longInv_perm hσ]
  omega

theorem mem_alternatingGroup_iff_not_isOuterFactor {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ) :
    σ ∈ alternatingGroup Δ ↔ ¬ IsOuterFactor (alternatingGroup Δ) := by
  rw [IsOuterFactor, ← notMem_alternatingGroup_iff_of_mem_longInv_perm hσ]
  simp

end LongInvolutions

section Conjugacy

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

omit [Fintype Δ] [DecidableEq Δ] in
theorem conj_mem_longInvAt_perm {σ : Perm Δ} {α : Δ} (hσ : σ ∈ longInvAt (Perm Δ) Δ α)
    (g : Perm Δ) : g * σ * g⁻¹ ∈ longInvAt (Perm Δ) Δ (g α) := by
  have key : ∀ y, (g * σ * g⁻¹) y = y ↔ y = g α := fun y => by
    rw [Perm.mul_apply, Perm.mul_apply, ← Perm.eq_inv_iff_eq,
      apply_eq_self_iff_of_mem_longInvAt_perm hσ, Perm.inv_eq_iff_eq]
  refine ⟨⟨?_, g α, (key _).2 rfl, fun y hy => (key y).1 hy⟩, (key _).2 rfl⟩
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hσ.1.1]

theorem exists_mem_longInv_perm (hodd : Odd (Fintype.card Δ)) (h3 : 3 ≤ Fintype.card Δ) :
    ∃ σ : Perm Δ, σ ∈ longInv (Perm Δ) Δ := by
  rw [Nat.odd_iff] at hodd
  obtain ⟨σ, hσ⟩ := (exists_with_cycleType_iff Δ
    (m := Multiset.replicate ((Fintype.card Δ - 1) / 2) 2)).2
    ⟨by rw [Multiset.sum_replicate, smul_eq_mul]; omega,
      fun a ha => (Multiset.eq_of_mem_replicate ha).ge⟩
  have h2 : σ ^ 2 = 1 := pow_prime_eq_one_iff.2 fun c hc => by
    rw [hσ] at hc
    exact Multiset.eq_of_mem_replicate hc
  have hne : σ ≠ 1 := by
    rintro rfl
    have h := congrArg Multiset.card hσ
    rw [cycleType_one, Multiset.card_zero, Multiset.card_replicate] at h
    omega
  have hsupp : σ.support.card = Fintype.card Δ - 1 := by
    rw [← sum_cycleType, hσ, Multiset.sum_replicate, smul_eq_mul]
    omega
  obtain ⟨α, hα⟩ := Finset.card_eq_one.1 (show σ.supportᶜ.card = 1 by
    rw [Finset.card_compl, hsupp]
    omega)
  have hfix : ∀ y, σ y = y ↔ y = α := fun y => by
    rw [← notMem_support, ← Finset.mem_compl, hα, Finset.mem_singleton]
  exact ⟨σ, orderOf_eq_prime h2 hne, α, (hfix α).2 rfl, fun y hy => (hfix y).1 hy⟩

theorem exists_mem_longInvAt_perm (hodd : Odd (Fintype.card Δ)) (h3 : 3 ≤ Fintype.card Δ)
    (α : Δ) : ∃ σ : Perm Δ, σ ∈ longInvAt (Perm Δ) Δ α := by
  obtain ⟨σ, hσ⟩ := exists_mem_longInv_perm hodd h3
  obtain ⟨β, hβ, -⟩ := hσ.2
  have h := conj_mem_longInvAt_perm ⟨hσ, hβ⟩ (swap α β)
  rw [swap_apply_right] at h
  exact ⟨_, h⟩

omit [Fintype Δ] in
private theorem commute_swap_of_mem_longInv_perm {σ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ)
    (x : Δ) : Commute (swap x (σ x)) σ := by
  have h := swap_apply_apply σ x (σ x)
  rw [apply_apply_of_mem_longInv_perm hσ, swap_comm] at h
  show swap x (σ x) * σ = σ * swap x (σ x)
  conv_lhs => rw [h]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem exists_mem_alternatingGroup_conj_eq {σ τ : Perm Δ} (hσ : σ ∈ longInv (Perm Δ) Δ)
    (hτ : τ ∈ longInv (Perm Δ) Δ) : ∃ g ∈ alternatingGroup Δ, g * σ * g⁻¹ = τ := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2
    ((cycleType_of_mem_longInv_perm hσ).trans (cycleType_of_mem_longInv_perm hτ).symm))
  by_cases hgA : g ∈ alternatingGroup Δ
  · exact ⟨g, hgA, hg⟩
  obtain ⟨α, hα, -⟩ := hσ.2
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card (by
    have := three_le_card_of_mem_longInv_perm hσ
    omega) α
  have hσx : σ x ≠ x := by
    rw [Ne, apply_eq_self_iff_of_mem_longInvAt_perm ⟨hσ, hα⟩]
    exact hx
  refine ⟨g * swap x (σ x), ?_, ?_⟩
  · rw [mem_alternatingGroup] at hgA ⊢
    rw [Perm.sign_mul, Perm.sign_swap hσx.symm, (Int.units_eq_one_or _).resolve_left hgA,
      Int.units_mul_self]
  · calc g * swap x (σ x) * σ * (g * swap x (σ x))⁻¹
        = g * (swap x (σ x) * σ * (swap x (σ x))⁻¹) * g⁻¹ := by group
      _ = τ := by rw [(commute_swap_of_mem_longInv_perm hσ x).eq, mul_inv_cancel_right, hg]

theorem longInv_perm_subset_of_alternatingGroup_le {M : Subgroup (Perm Δ)}
    (hM : alternatingGroup Δ ≤ M) {s : Perm Δ} (hsM : s ∈ M) (hs : s ∈ longInv (Perm Δ) Δ) :
    longInv (Perm Δ) Δ ⊆ M := by
  intro τ hτ
  have hA : τ * s⁻¹ ∈ alternatingGroup Δ := by
    rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, sign_eq_of_mem_longInv_perm hτ hs,
      Int.units_mul_self]
  simpa using M.mul_mem (hM hA) hsM

end Conjugacy

section Natural

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

theorem centralizer_alternatingGroup_perm_eq_bot (h4 : 4 ≤ Fintype.card Δ) :
    Subgroup.centralizer (alternatingGroup Δ : Set (Perm Δ)) = ⊥ :=
  CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by rwa [Nat.card_eq_fintype_card])

theorem exists_mem_alternatingGroup_fix_apply_eq (h4 : 4 ≤ Fintype.card Δ) {α γ δ : Δ}
    (hγ : γ ≠ α) (hδ : δ ≠ α) : ∃ g ∈ alternatingGroup Δ, g α = α ∧ g γ = δ := by
  rcases eq_or_ne γ δ with rfl | hγδ
  · exact ⟨1, one_mem _, rfl, rfl⟩
  obtain ⟨ε, -, hε⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({α, γ, δ} : Finset Δ)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hε
  obtain ⟨hεα, hεγ, hεδ⟩ := hε
  refine ⟨swap γ δ * swap δ ε, ?_, ?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hγδ, Perm.sign_swap (Ne.symm hεδ),
      Int.units_mul_self]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hδ) (Ne.symm hεα),
      swap_apply_of_ne_of_ne (Ne.symm hγ) (Ne.symm hδ)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hγδ (Ne.symm hεγ), swap_apply_left]

theorem exists_mem_alternatingGroup_fix_two_apply_eq (h5 : 5 ≤ Fintype.card Δ) {α β γ δ : Δ}
    (hγα : γ ≠ α) (hγβ : γ ≠ β) (hδα : δ ≠ α) (hδβ : δ ≠ β) :
    ∃ g ∈ alternatingGroup Δ, g α = α ∧ g β = β ∧ g γ = δ := by
  rcases eq_or_ne γ δ with rfl | hγδ
  · exact ⟨1, one_mem _, rfl, rfl, rfl⟩
  obtain ⟨ε, -, hε⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({α, β, γ, δ} : Finset Δ)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_four.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hε
  obtain ⟨hεα, hεβ, hεγ, hεδ⟩ := hε
  refine ⟨swap γ δ * swap δ ε, ?_, ?_, ?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hγδ, Perm.sign_swap (Ne.symm hεδ),
      Int.units_mul_self]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hδα) (Ne.symm hεα),
      swap_apply_of_ne_of_ne (Ne.symm hγα) (Ne.symm hδα)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hδβ) (Ne.symm hεβ),
      swap_apply_of_ne_of_ne (Ne.symm hγβ) (Ne.symm hδβ)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hγδ (Ne.symm hεγ), swap_apply_left]

theorem relIndex_alternatingGroup_inf_stabilizer (h3 : 3 ≤ Fintype.card Δ) (α : Δ) :
    (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α).relIndex (alternatingGroup Δ) =
      Fintype.card Δ := by
  have hsub : (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α).subgroupOf (alternatingGroup Δ) =
      stabilizer (alternatingGroup Δ) α := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff,
      Subgroup.smul_def]
    exact and_iff_right g.2
  have := alternatingGroup.isPretransitive_of_three_le_card (α := Δ)
    (by rwa [Nat.card_eq_fintype_card])
  rw [Subgroup.relIndex, hsub, index_stabilizer, orbit_eq_univ, Set.ncard_univ,
    Nat.card_eq_fintype_card]

theorem orbit_alternatingGroup_inf_stabilizer (h4 : 4 ≤ Fintype.card Δ) {α β : Δ}
    (hβ : β ≠ α) :
    orbit (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α : Subgroup (Perm Δ)) β = {α}ᶜ := by
  ext γ
  rw [Set.mem_compl_singleton_iff, mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩ h
    have hgα : (g : Perm Δ) α = α := (Subgroup.mem_inf.1 g.2).2
    exact hβ ((g : Perm Δ).injective (h.trans hgα.symm))
  · intro hγ
    obtain ⟨g, hgA, hgα, hgβ⟩ := exists_mem_alternatingGroup_fix_apply_eq h4 hβ hγ
    exact ⟨⟨g, Subgroup.mem_inf.2 ⟨hgA, hgα⟩⟩, hgβ⟩

omit [Fintype Δ] in
theorem exists_mem_longInvAt_perm_apply_eq {s : Perm Δ} {α x y : Δ}
    (hs : s ∈ longInvAt (Perm Δ) Δ α) (hx : x ≠ α) (hy : y ≠ α) (hyx : y ≠ x) :
    ∃ t ∈ longInvAt (Perm Δ) Δ α, t x = y := by
  have hfix := fun z => apply_eq_self_iff_of_mem_longInvAt_perm (x := z) hs
  have hsx : s x ≠ x := fun h => hx ((hfix x).1 h)
  have hsxα : s x ≠ α := fun h => hx (by
    rw [← apply_apply_of_mem_longInv_perm hs.1 x, h, (hfix α).2 rfl])
  have hgα : swap (s x) y α = α := swap_apply_of_ne_of_ne (Ne.symm hsxα) (Ne.symm hy)
  have hgx : swap (s x) y x = x := swap_apply_of_ne_of_ne (Ne.symm hsx) (Ne.symm hyx)
  have ht := conj_mem_longInvAt_perm hs (swap (s x) y)
  rw [hgα] at ht
  refine ⟨_, ht, ?_⟩
  rw [swap_inv, Perm.mul_apply, Perm.mul_apply, hgx, swap_apply_left]

theorem holtDelta_eq_compl_of_longInv_subset {M : Subgroup (Perm Δ)}
    (hM : longInv (Perm Δ) Δ ⊆ M) (hodd : Odd (Fintype.card Δ)) {α β : Δ} (hαβ : α ≠ β) :
    holtDelta M Δ α β = {α, β}ᶜ := by
  ext γ
  simp only [mem_holtDelta, mem_longInvSwap, Subgroup.smul_def, Perm.smul_def,
    Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨t, ⟨ht, htα⟩, htγ⟩
    rw [mem_longInv_subgroup_perm_iff] at ht
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h] at htγ
      exact hαβ (htγ.symm.trans htα)
    · rw [h] at htγ
      exact hαβ (by rw [← apply_apply_of_mem_longInv_perm ht α, htα, htγ])
  · rintro ⟨hγα, hγβ⟩
    have h3 : 3 ≤ Fintype.card Δ := by
      have := Fintype.one_lt_card_iff.2 ⟨α, β, hαβ⟩
      rw [Nat.odd_iff] at hodd
      omega
    obtain ⟨s, hs⟩ := exists_mem_longInvAt_perm hodd h3 γ
    obtain ⟨t, ht, htα⟩ := exists_mem_longInvAt_perm_apply_eq hs (Ne.symm hγα) (Ne.symm hγβ)
      (Ne.symm hαβ)
    exact ⟨⟨t, hM ht.1⟩, ⟨mem_longInv_subgroup_perm_iff.2 ht.1, htα⟩, ht.2⟩

theorem holtDelta'_eq_compl_of_longInv_subset {M : Subgroup (Perm Δ)}
    (hM : longInv (Perm Δ) Δ ⊆ M) (hodd : Odd (Fintype.card Δ)) {α β : Δ} (hαβ : α ≠ β) :
    holtDelta' M Δ α β = {α, β}ᶜ := by
  ext γ
  simp only [mem_holtDelta', mem_longInvAt, Subgroup.smul_def, Perm.smul_def,
    Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨s, ⟨hs, hsα⟩, rfl⟩
    rw [mem_longInv_subgroup_perm_iff] at hs
    have hfix := fun z => apply_eq_self_iff_of_mem_longInvAt_perm (x := z) ⟨hs, hsα⟩
    refine ⟨fun h => hαβ ?_, fun h => hαβ ((hfix β).1 h).symm⟩
    rw [← apply_apply_of_mem_longInv_perm hs β, h, hsα]
  · rintro ⟨hγα, hγβ⟩
    have h3 : 3 ≤ Fintype.card Δ := by
      have := Fintype.one_lt_card_iff.2 ⟨α, β, hαβ⟩
      rw [Nat.odd_iff] at hodd
      omega
    obtain ⟨s, hs⟩ := exists_mem_longInvAt_perm hodd h3 α
    obtain ⟨t, ht, htβ⟩ := exists_mem_longInvAt_perm_apply_eq hs (Ne.symm hαβ) hγα hγβ
    exact ⟨⟨t, hM ht.1⟩, ⟨mem_longInv_subgroup_perm_iff.2 ht.1, ht.2⟩, htβ⟩

theorem holtDelta_eq_compl_of_alternatingGroup_le {M : Subgroup (Perm Δ)}
    (hM : alternatingGroup Δ ≤ M) {s : Perm Δ} (hsM : s ∈ M) (hs : s ∈ longInv (Perm Δ) Δ)
    {α β : Δ} (hαβ : α ≠ β) : holtDelta M Δ α β = {α, β}ᶜ :=
  holtDelta_eq_compl_of_longInv_subset (longInv_perm_subset_of_alternatingGroup_le hM hsM hs)
    (odd_card_of_mem_longInv_perm hs) hαβ

theorem holtDelta'_eq_compl_of_alternatingGroup_le {M : Subgroup (Perm Δ)}
    (hM : alternatingGroup Δ ≤ M) {s : Perm Δ} (hsM : s ∈ M) (hs : s ∈ longInv (Perm Δ) Δ)
    {α β : Δ} (hαβ : α ≠ β) : holtDelta' M Δ α β = {α, β}ᶜ :=
  holtDelta'_eq_compl_of_longInv_subset (longInv_perm_subset_of_alternatingGroup_le hM hsM hs)
    (odd_card_of_mem_longInv_perm hs) hαβ

end Natural

end CFSG.Holt.H78
