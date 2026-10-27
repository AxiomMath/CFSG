module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SpecExtract
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.UpperBound

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3

theorem card_fixed_le {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (D : ModuleSpec X p) (P : Subgroup X) (tmats : List (List ℕ))
    (hP : ∀ A ∈ tmats, ∃ q ∈ P, ActsBy D q (toMatL p D.n A)) :
    Nat.card ↥(D.span ⊓ Subgroup.centralizer (P : Set X)) ≤
      Nat.card {c : Fin D.n → ZMod p // ∀ A ∈ tmats, (toMatL p D.n A).mulVec c = c} := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ι : ↥(D.span ⊓ Subgroup.centralizer (P : Set X)) →
      {c : Fin D.n → ZMod p // ∀ A ∈ tmats, (toMatL p D.n A).mulVec c = c} := fun a =>
    ⟨Classical.choose (D.exists_elt a.2.1), by
      intro A hA
      obtain ⟨q, hq, hqA⟩ := hP A hA
      have hc := Classical.choose_spec (D.exists_elt a.2.1)
      have h1 : q * (a : X) = (a : X) * q := Subgroup.mem_centralizer_iff.mp a.2.2 q hq
      apply D.elt_injective
      rw [← conj_elt D hqA, hc]
      rw [h1]
      group⟩
  refine Nat.card_le_card_of_injective ι fun a b hab => ?_
  have h := congrArg Subtype.val hab
  apply Subtype.ext
  rw [← Classical.choose_spec (D.exists_elt a.2.1), ← Classical.choose_spec (D.exists_elt b.2.1)]
  exact congrArg D.elt h

theorem pRank_le_of_sylowModuleData {X : Type} [Group X] [Finite X] {p n t z r : ℕ}
    (hp : p.Prime) {tmats : List (List ℕ)} (hdat : SylowModuleData X p n tmats)
    (hord : (Nat.card X).factorization p = n + t)
    (hfix : Nat.card {c : Fin n → ZMod p // ∀ A ∈ tmats, (toMatL p n A).mulVec c = c} ≤ p ^ z)
    (hnum : ∀ a j, a ≤ n → j ≤ t → (0 < j → a < n) → (j = t → a ≤ z) → a + j ≤ r) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ r := by
  have := Fact.mk hp
  obtain ⟨D, P, hn, -, -, hPcard, hspan, hnorm, hcen, htmats⟩ := hdat
  subst hn
  rw [hord] at hPcard
  have hAc : ∀ a ∈ D.span, ∀ b ∈ D.span, a * b = b * a := fun a ha b hb =>
    D.mul_comm_of_mem ha hb
  have hz := (card_fixed_le D P tmats htmats).trans hfix
  have hz' : Nat.card ↥(D.span ⊓ Subgroup.centralizer (P : Set X)) ≤ p ^ z := hz
  refine pRank_le_of_sylow hp P (by rw [hord]; exact hPcard) (k := r) fun E hEP hE => ?_
  obtain ⟨a, j, hcard, ha, hj, h1, h2⟩ := card_elemAbelian_le_of_setup hp D.span P hspan hnorm hAc
    hcen (D.card_span hp) hPcard hz' E hEP fun x hx y hy => by
      have := hE.1
      exact mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩ |> congrArg Subtype.val
  rw [hcard]
  exact Nat.pow_le_pow_right hp.pos (hnum a j ha hj h1 h2)

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
