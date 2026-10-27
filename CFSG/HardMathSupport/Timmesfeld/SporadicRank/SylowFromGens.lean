module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SpecExtract

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3

theorem sylowCover_of_gens {X : Type} [Group X] [Finite X] {p s : ℕ} (hp : p.Prime)
    (D : ModuleSpec X p) (hA : D.NoAlt) (hF : D.NoFun) (P : Subgroup X) (hspan : D.span ≤ P)
    (hnorm : P ≤ Subgroup.normalizer (D.span : Set X)) (As : List (List ℕ))
    (hgen : ∀ A ∈ As, ∃ q ∈ P, ActsBy D q (toMatL p D.n A))
    (hcodes : (wordsL p D.n As).Pairwise fun A B => codeL p A ≠ codeL p B)
    (hs : p ^ s ≤ (wordsL p D.n As).length * p ^ D.n) (hPcard : Nat.card P ≤ p ^ s)
    (hv : p ^ s ∣ Nat.card X ∧ ¬ p ^ (s + 1) ∣ Nat.card X) :
    SylowModuleCover X p D.n (wordsL p D.n As) := by
  have : Fact p.Prime := ⟨hp⟩
  set L : List (List ℕ) := wordsL p D.n As with hL
  have hall := exists_mem_wordsL D P As hgen
  have hex : ∀ a : Fin L.length, ∃ g ∈ P, ActsBy D g (toMatL p D.n (L.get a)) :=
    fun a => hall _ (List.get_mem L a)
  choose g hgP hgA using hex
  have hlen : ∀ a : Fin L.length, (L.get a).length = D.n * D.n ∧ ∀ x ∈ L.get a, x < p :=
    fun a => wordsL_spec p D.n hp.one_lt _ _ (List.get_mem L a)
  have hdiff : ∀ a b : Fin L.length, a.val < b.val →
      toMatL p D.n (L.get a) ≠ toMatL p D.n (L.get b) := by
    intro a b hab hM
    have hcode := List.pairwise_iff_getElem.1 hcodes a.val b.val a.2 b.2 hab
    apply hcode
    have := toMatL_inj p D.n (hlen a).1 (hlen b).1 (hlen a).2 (hlen b).2 hM
    show codeL p (L.get a) = codeL p (L.get b)
    rw [this]
  have hdist : ∀ a b : Fin L.length, a ≠ b →
      toMatL p D.n (L.get a) ≠ toMatL p D.n (L.get b) := by
    intro a b hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hdiff a b hlt
    · exact (hdiff b a hlt).symm
  have hlow : L.length * p ^ D.n ≤ Nat.card P := by
    have h := card_ge_of_actsBy D P hspan g (fun a => toMatL p D.n (L.get a)) hgP hgA hdist
    rw [D.card_span hp] at h
    exact h
  have hPeq : Nat.card P = p ^ s := le_antisymm hPcard (hs.trans hlow)
  have hPgrp : IsPGroup p P := IsPGroup.of_card hPeq
  have hs' : p ^ s ≤ L.length * p ^ D.n := hs
  have hcore := sylow_selfCentralizing D P hspan hPgrp rfl hv hs' g
    (fun a => toMatL p D.n (L.get a)) hgP hgA hdist
  refine ⟨D, P, rfl, hA, hF, hcore.1, hspan, hnorm, hcore.2.1, ?_, ?_, ?_⟩
  · rw [List.Nodup, List.pairwise_map, List.pairwise_iff_getElem]
    intro a b ha hb hab
    exact hdiff ⟨a, ha⟩ ⟨b, hb⟩ hab
  · intro A hA'
    obtain ⟨a, rfl⟩ := List.mem_iff_get.1 hA'
    exact ⟨g a, hgP a, hgA a⟩
  · intro x hx
    obtain ⟨a, α, hα, rfl⟩ := hcore.2.2 x hx
    exact ⟨L.get a, List.get_mem L a, actsBy_mul_span D (hgA a) hα⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
