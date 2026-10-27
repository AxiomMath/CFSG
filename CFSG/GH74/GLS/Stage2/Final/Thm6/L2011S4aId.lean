module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31g
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2

section Decomp

variable {K : Type} [Group K] [Finite K]

theorem decomp_eq_of_sl2 {z : K} {q : ℕ} (hq : 3 < q) (hz2 : orderOf z = 2) {E₁ E₂ I₁ I₂ : Subgroup K}
    (hE : E₁ ⊔ E₂ = I₁ ⊔ I₂) (hcE : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) (hiE : E₁ ⊓ E₂ = zpowers z)
    (hsE₁ : HasSL2Model ↥E₁ (fun r => r = q)) (hsE₂ : HasSL2Model ↥E₂ (fun r => r = q))
    (hcI : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a)
    (hsI₁ : HasSL2Model ↥I₁ (fun r => r = q)) (hsI₂ : HasSL2Model ↥I₂ (fun r => r = q)) :
    (I₁ = E₁ ∨ I₁ = E₂) ∧ (I₂ = E₁ ∨ I₂ = E₂) := by
  set E : Subgroup K := E₁ ⊔ E₂ with hEdef
  have hE₁E : E₁ ≤ E := le_sup_left
  have hE₂E : E₂ ≤ E := le_sup_right
  have hI₁E : I₁ ≤ E := hE ▸ le_sup_left
  have hI₂E : I₂ ≤ E := hE ▸ le_sup_right
  have hzE₁₂ : z ∈ E₁ ⊓ E₂ := by rw [hiE]; exact mem_zpowers z
  have hzE : z ∈ E := hE₁E hzE₁₂.1
  obtain ⟨F₁, i₁, f₁, hF₁q, ⟨e₁⟩⟩ := hsE₁
  obtain ⟨F₂, i₂, f₂, hF₂q, ⟨e₂⟩⟩ := hsE₂
  have hsE₁' : HasSL2Model ↥E₁ (fun r => r = q) := ⟨F₁, i₁, f₁, hF₁q, ⟨e₁⟩⟩
  have hsE₂' : HasSL2Model ↥E₂ (fun r => r = q) := ⟨F₂, i₂, f₂, hF₂q, ⟨e₂⟩⟩
  have hsup : E₁.subgroupOf E ⊔ E₂.subgroupOf E = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hE₁E hE₂E]
    exact Subgroup.subgroupOf_self E
  have hPr : IVK.ProdSL2 ↥E (E₁.subgroupOf E) (E₂.subgroupOf E) F₁ F₂ := by
    refine
      { comm := ?_
        iso₁ := ⟨(Subgroup.subgroupOfEquivOfLe hE₁E).trans e₁⟩
        iso₂ := ⟨(Subgroup.subgroupOfEquivOfLe hE₂E).trans e₂⟩
        card_inter := ?_
        fstar_normal := ?_
        fstar_centralizer := ?_ }
    · intro a ha b hb
      exact Subtype.ext (hcE a ha b hb)
    · have h : E₁.subgroupOf E ⊓ E₂.subgroupOf E = (zpowers z).subgroupOf E := by
        ext x
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf, ← hiE, Subgroup.mem_inf]
      rw [h]
      have hzC : zpowers z ≤ E := by rw [zpowers_le]; exact hzE
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzC).toEquiv, Nat.card_zpowers, hz2]
    · rw [hsup]; infer_instance
    · rw [hsup]; exact le_top
  have hF₁3 : 3 < Nat.card F₁ := by rw [hF₁q]; exact hq
  have hF₂3 : 3 < Nat.card F₂ := by rw [hF₂q]; exact hq
  set z' : ↥E := ⟨z, hzE⟩ with hz'
  have hz'mem : z' ∈ E₁.subgroupOf E ⊓ E₂.subgroupOf E := ⟨hzE₁₂.1, hzE₁₂.2⟩
  have hz'1 : z' ≠ 1 := by
    intro h
    have : z = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hz2
    omega
  obtain ⟨hint', hz'o⟩ := hPr.inter_eq hz'mem hz'1
  have hz'mem' : z' ∈ E₂.subgroupOf E ⊓ E₁.subgroupOf E := ⟨hz'mem.2, hz'mem.1⟩
  have hperf₁ := Lemma31g.commutator_eq hPr hF₁3
  have hperf₂ := Lemma31g.commutator_eq hPr.symm hF₂3
  have hn₁ := fun N hNK hN => Lemma31g.normal_sub_le_z hPr hF₁3 hz'mem hz'1 N hNK hN
  have hn₂ := fun N hNK hN => Lemma31g.normal_sub_le_z hPr.symm hF₂3 hz'mem' hz'1 N hNK hN
  have hK₁ := Lemma31g.not_le_zpowers hPr hF₁3 hz'o
  have hK₂ := Lemma31g.not_le_zpowers hPr.symm hF₂3 hz'o
  have hcardE₁ : Nat.card ↥E₁ = q * (q ^ 2 - 1) := card_of_hasSL2Model hsE₁'
  have hcardE₂ : Nat.card ↥E₂ = q * (q ^ 2 - 1) := card_of_hasSL2Model hsE₂'
  have hcardI₁ : Nat.card ↥I₁ = q * (q ^ 2 - 1) := card_of_hasSL2Model hsI₁
  have hcardI₂ : Nat.card ↥I₂ = q * (q ^ 2 - 1) := card_of_hasSL2Model hsI₂
  have core : ∀ {L N : Subgroup K}, L ≤ E → N ≤ E → (∀ l ∈ L, ∀ n ∈ N, l * n = n * l) →
      (∀ k ∈ E, ∀ n ∈ N, k * n * k⁻¹ ∈ N) → Nat.card ↥L = q * (q ^ 2 - 1) →
      Nat.card ↥N = q * (q ^ 2 - 1) → (L = E₁ ∨ L = E₂) := by
    intro L N hLE hNE hLN hNinv hcL hcN
    have key := ConjComponent.eq_or_eq_of_commute (z := z') hPr.comm hint' hperf₁ hperf₂ hn₁ hn₂ hK₁ hK₂
      (L := L.subgroupOf E) (N := N.subgroupOf E) (by rw [hsup]; exact le_top) (by rw [hsup]; exact le_top)
      (fun k _ n hn => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hNinv k k.2 n hn)
      (fun l hl n hn => Subtype.ext (hLN l hl n hn))
      (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNE).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂E).toEquiv, hcN, hcardE₂])
      (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLE).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁E).toEquiv, hcL, hcardE₁])
    rcases key with h | h
    · left
      have := (Subgroup.subgroupOf_inj).1 h
      rwa [inf_eq_left.2 hLE, inf_eq_left.2 hE₁E] at this
    · right
      have := (Subgroup.subgroupOf_inj).1 h
      rwa [inf_eq_left.2 hLE, inf_eq_left.2 hE₂E] at this
  have hcI' : ∀ a ∈ I₂, ∀ b ∈ I₁, a * b = b * a := fun a ha b hb => (hcI b hb a ha).symm
  refine ⟨core hI₁E hI₂E hcI ?_ hcardI₁ hcardI₂, core hI₂E hI₁E hcI' ?_ hcardI₂ hcardI₁⟩
  · intro k hk n hn
    exact ConjComponent.conj_mem_of_mem_sup hcI (hE ▸ hk) hn
  · intro k hk n hn
    have hk' : k ∈ I₂ ⊔ I₁ := by rw [sup_comm]; exact hE ▸ hk
    exact ConjComponent.conj_mem_of_mem_sup hcI' hk' hn

end Decomp

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
