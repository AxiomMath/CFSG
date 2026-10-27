module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma33

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

@[expose] def Sol78Lemma65KP : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (H E H₁ : Subgroup G) (e : G), H ≠ ⊤ →
    E ≤ H → ∀ _hEN : (E.subgroupOf H).Normal, IsElemAbelian 2 E → Nat.card E = 2 ^ 12 →
    centralizer (E : Set G) ⊓ H = E → e ∈ E → orderOf e = 2 →
    Set.ncard {x : G | ∃ h ∈ H, x = h * e * h⁻¹} = 24 →
    centralizer ({e} : Set G) ⊓ H = H₁ ⊔ zpowers e → H₁ ≤ H → Disjoint H₁ (zpowers e) →
    ∀ _hN : (E.subgroupOf H₁).Normal, Nonempty (H₁ ⧸ E.subgroupOf H₁ ≃* Carrier .M23) →
      Nonempty (H ⧸ E.subgroupOf H ≃* Carrier .M24) ∧
      (∃ N₀ : Subgroup G, N₀ ≤ H ∧ (N₀.subgroupOf H).Normal ∧ N₀.relIndex H = 2 ∧ e ∉ N₀) ∧
      ∀ A : Subgroup G, A ≤ H → IsElemAbelian 2 A → Nat.card A = 2 ^ 12 → A = E

@[expose] def Sol78Lemma65Uniq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H E H₁ : Subgroup G) (e : G),
    E ≤ H → ∀ _hEN : (E.subgroupOf H).Normal, IsElemAbelian 2 E → Nat.card E = 2 ^ 12 →
    centralizer (E : Set G) ⊓ H = E → e ∈ E → orderOf e = 2 →
    Set.ncard {x : G | ∃ h ∈ H, x = h * e * h⁻¹} = 24 →
    centralizer ({e} : Set G) ⊓ H = H₁ ⊔ zpowers e → H₁ ≤ H → Disjoint H₁ (zpowers e) →
    ∀ _hN : (E.subgroupOf H₁).Normal, Nonempty (H₁ ⧸ E.subgroupOf H₁ ≃* Carrier .M23) →
      Nonempty (H ⧸ E.subgroupOf H ≃* Carrier .M24) →
      ∀ A : Subgroup G, A ≤ H → IsElemAbelian 2 A → Nat.card A = 2 ^ 12 → A = E

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

theorem normalizer_ne_top_of_card_eq (hN : FStarSimple N) {W : Subgroup H}
    (hWab : IsElemAbelian 2 W) (hW : Nat.card W = 2 ^ 12) : normalizer (W : Set H) ≠ ⊤ := by
  intro htop
  have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have := hN.isSimpleGroup
  have hNn : N.Normal := hN.normal
  obtain ⟨a, b, hab⟩ := hN.nonabelian
  have hWN : W ⊓ N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf N) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : ↥N) ∈ W.subgroupOf N := hx.1
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
    · have hNW : N ≤ W := Subgroup.subgroupOf_eq_top.1 h
      exact absurd (congrArg Subtype.val
        (hWab.1.is_comm.comm ⟨a, hNW a.2⟩ ⟨b, hNW b.2⟩)) (fun hc => hab (Subtype.ext hc))
  have hWle : W ≤ centralizer (N : Set H) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro n hn
    have h1 : w * n * w⁻¹ * n⁻¹ ∈ N := N.mul_mem (hNn.conj_mem n hn w) (N.inv_mem hn)
    have h2 : w * n * w⁻¹ * n⁻¹ ∈ W := by
      have := W.mul_mem hw (hWn.conj_mem w⁻¹ (W.inv_mem hw) n)
      simpa [mul_assoc] using this
    have h3 : w * n * w⁻¹ * n⁻¹ = 1 := by
      have : w * n * w⁻¹ * n⁻¹ ∈ W ⊓ N := ⟨h2, h1⟩
      rwa [hWN, Subgroup.mem_bot] at this
    have := mul_inv_eq_one.1 (by simpa [mul_assoc] using h3 : w * n * (n * w)⁻¹ = 1)
    exact this.symm
  rw [hN.centralizer_eq_bot, le_bot_iff] at hWle
  rw [hWle, Subgroup.card_bot] at hW
  norm_num at hW

end CFSG.EvenSporadicStandard.Induction.Balance
