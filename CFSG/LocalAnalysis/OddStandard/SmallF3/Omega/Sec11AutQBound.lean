module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ElemAbList
public import Certificates.Data.OmegaAutQ

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Certificates.OmegaAutQ

namespace AutQBound

theorem span1_eq (g : S81) (T : List S81) : span1 g T = adjoinL g T := by
  simp [span1, adjoinL, tabP_eq]

theorem leaf_spec {Q B T : List S81} (h : leaf Q B T = true) :
    ∃ g1 g2 : S81, g1 ∈ Q ∧ g2 ∈ Q ∧ (∀ y ∈ Q, y ∈ adjoinL g2 (adjoinL g1 T)) ∧
      (candsOf Q B T g1 g2).length ≤ 8 := by
  simp only [leaf, leafOf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, span1_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨_, _, h1, h2, h3, h4⟩

theorem chain_leaf (h : check () = true) {a b c : S81} (ha : a ∈ invsOf (qmList ()))
    (hb : b ∈ commL (invsOf (qmList ())) a) (hbT : b ∉ adjoinL a [1])
    (hc : c ∈ commL (commL (invsOf (qmList ())) a) b) (hcT : c ∉ adjoinL b (adjoinL a [1])) :
    leaf (qmList ()) ([a] ++ [b] ++ [c]) (adjoinL c (adjoinL b (adjoinL a [1]))) = true := by
  simp only [check, chainChk, List.all_eq_true] at h
  have h1 := h a ha
  simp only [level1, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, span1_eq] at h1
  rcases h1 b hb with h2 | h2
  · exact absurd h2 hbT
  simp only [level2, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, span1_eq] at h2
  rcases h2 c hc with h3 | h3
  · exact absurd h3 hcT
  simpa only [span1_eq] using h3

theorem card_le_length {α β : Type*} [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (l : List β) (h : ∀ x, f x ∈ l) : Nat.card α ≤ l.length := by
  calc Nat.card α ≤ Nat.card { x // x ∈ l.toFinset } :=
        Nat.card_le_card_of_injective (fun x => ⟨f x, by simpa using h x⟩)
          (fun x y hxy => hf (congrArg Subtype.val hxy))
    _ = l.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ l.length := List.toFinset_card_le l

variable {Qm Pm : Subgroup S81} {B T : List S81}

theorem img_mem (hQ : ∀ y, y ∈ Qm ↔ y ∈ qmList ()) (hPQ : Pm ≤ Qm)
    (hT : ∀ x, x ∈ T ↔ x ∈ Pm) (hB : ∀ q ∈ B, q ∈ Pm) {γ : MulAut ↥Qm}
    (hfix : ∀ p : ↥Qm, (p : S81) ∈ Pm → γ p = p) (g : ↥Qm) :
    ((γ g : ↥Qm) : S81) ∈ imgCand (qmList ()) B T g := by
  have hf : ∀ p : ↥Qm, (p : S81) ∈ Pm → ((γ p : ↥Qm) : S81) = p := fun p hp =>
    congrArg Subtype.val (hfix p hp)
  simp only [imgCand, imgAux, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, List.all_eq_true]
  refine ⟨(hQ _).1 (γ g).2, ?_, ?_⟩
  · by_cases hg : (g : S81) * g ∈ T
    · right
      have h1 := hf (g * g) ((hT _).1 hg)
      rw [map_mul] at h1
      exact h1
    · left
      exact hg
  · rintro ⟨q, c⟩ hqc
    simp only [conjPairs, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Prod.mk.injEq] at hqc
    obtain ⟨q', hq'B, c', ⟨hc'T, hcg⟩, rfl, rfl⟩ := hqc
    have hqP := hB _ hq'B
    have hcP := (hT _).1 hc'T
    have h1 : (⟨c', hPQ hcP⟩ : ↥Qm) * g = g * ⟨q', hPQ hqP⟩ := Subtype.ext hcg
    have h2 := congrArg (fun x : ↥Qm => ((γ x : ↥Qm) : S81)) h1
    simp only [map_mul, Subgroup.coe_mul] at h2
    rw [hf ⟨c', hPQ hcP⟩ hcP, hf ⟨q', hPQ hqP⟩ hqP] at h2
    exact h2.symm

theorem ev_mem (hQ : ∀ y, y ∈ Qm ↔ y ∈ qmList ()) (hPQ : Pm ≤ Qm)
    (hT : ∀ x, x ∈ T ↔ x ∈ Pm) (hB : ∀ q ∈ B, q ∈ Pm) {γ : MulAut ↥Qm}
    (hfix : ∀ p : ↥Qm, (p : S81) ∈ Pm → γ p = p) (g1 g2 : ↥Qm) :
    (((γ g1 : ↥Qm) : S81), ((γ g2 : ↥Qm) : S81)) ∈ candsOf (qmList ()) B T g1 g2 := by
  have hf : ∀ p : ↥Qm, (p : S81) ∈ Pm → ((γ p : ↥Qm) : S81) = p := fun p hp =>
    congrArg Subtype.val (hfix p hp)
  simp only [candsOf, List.mem_flatMap, List.mem_map, List.mem_filter, List.all_eq_true,
    decide_eq_true_eq, Prod.mk.injEq]
  refine ⟨_, img_mem hQ hPQ hT hB hfix g1, _, ⟨img_mem hQ hPQ hT hB hfix g2, ?_⟩, rfl, rfl⟩
  rintro e ⟨heT, hcomm⟩
  have heP := (hT _).1 heT
  have h1 : (⟨e, hPQ heP⟩ : ↥Qm) * (g2 * g1) = g1 * g2 := Subtype.ext hcomm
  have h2 := congrArg (fun x : ↥Qm => ((γ x : ↥Qm) : S81)) h1
  simp only [map_mul, Subgroup.coe_mul] at h2
  rw [hf ⟨e, hPQ heP⟩ heP] at h2
  exact h2.symm

theorem ev_inj (hQ : ∀ y, y ∈ Qm ↔ y ∈ qmList ()) (hPQ : Pm ≤ Qm)
    (hT : ∀ x, x ∈ T ↔ x ∈ Pm) {γ δ : MulAut ↥Qm}
    (hγ : ∀ p : ↥Qm, (p : S81) ∈ Pm → γ p = p) (hδ : ∀ p : ↥Qm, (p : S81) ∈ Pm → δ p = p)
    (g1 g2 : ↥Qm) (hcov : ∀ y ∈ qmList (), y ∈ adjoinL (g2 : S81) (adjoinL (g1 : S81) T))
    (h1 : γ g1 = δ g1) (h2 : γ g2 = δ g2) : γ = δ := by
  have hA : ∀ z : ↥Qm, (z : S81) ∈ adjoinL (g1 : S81) T → γ z = δ z := by
    intro z hz
    rcases mem_adjoinL.1 hz with hzT | ⟨t, htT, hzt⟩
    · rw [hγ z ((hT _).1 hzT), hδ z ((hT _).1 hzT)]
    · have htP := (hT t).1 htT
      have hz' : z = g1 * ⟨t, hPQ htP⟩ := Subtype.ext hzt
      rw [hz', map_mul, map_mul, h1, hγ ⟨t, hPQ htP⟩ htP, hδ ⟨t, hPQ htP⟩ htP]
  refine DFunLike.ext _ _ fun y => ?_
  rcases mem_adjoinL.1 (hcov y ((hQ _).1 y.2)) with hyA | ⟨z, hzA, hyz⟩
  · exact hA y hyA
  · have hzQ : z ∈ Qm := by
      rcases mem_adjoinL.1 hzA with hzT | ⟨t, htT, rfl⟩
      · exact hPQ ((hT _).1 hzT)
      · exact Qm.mul_mem g1.2 (hPQ ((hT _).1 htT))
    have hy' : y = g2 * ⟨z, hzQ⟩ := Subtype.ext hyz
    rw [hy', map_mul, map_mul, h2, hA ⟨z, hzQ⟩ hzA]

theorem aut_bound (h : check () = true) (hQ : ∀ y, y ∈ Qm ↔ y ∈ qmList ()) (hPQ : Pm ≤ Qm)
    (hcard : Nat.card Pm = 8) (hc : ∀ x ∈ Pm, ∀ y ∈ Pm, x * y = y * x)
    (hsq : ∀ x ∈ Pm, x * x = 1) (Φ : Subgroup (MulAut ↥Qm))
    (hfix : ∀ γ ∈ Φ, ∀ p : ↥Qm, (p : S81) ∈ Pm → γ p = p) : Nat.card ↥Φ ≤ 8 := by
  obtain ⟨a, b, c, ha, hb, hc', ha1, hbT, hcT, hspan⟩ := exists_basis_three Pm hcard hc hsq
  have hinv : ∀ x ∈ Pm, x ≠ 1 → x ∈ invsOf (qmList ()) := by
    intro x hx hx1
    simp only [invsOf, List.mem_filter, decide_eq_true_eq]
    exact ⟨(hQ x).1 (hPQ hx), hsq x hx, hx1⟩
  have hone : ∀ T : List S81, (1 : S81) ∈ T → ∀ x, x ∉ T → x ≠ 1 := fun T h1 x hx hx1 =>
    hx (hx1 ▸ h1)
  have h1T : (1 : S81) ∈ adjoinL a [1] := mem_adjoinL.2 (Or.inl (List.mem_singleton_self _))
  have h1T2 : (1 : S81) ∈ adjoinL b (adjoinL a [1]) := mem_adjoinL.2 (Or.inl h1T)
  have hbI : b ∈ commL (invsOf (qmList ())) a := by
    simp only [commL, List.mem_filter, decide_eq_true_eq]
    exact ⟨hinv b hb (hone _ h1T b hbT), hc b hb a ha⟩
  have hcI : c ∈ commL (commL (invsOf (qmList ())) a) b := by
    simp only [commL, List.mem_filter, decide_eq_true_eq]
    exact ⟨⟨hinv c hc' (hone _ h1T2 c hcT), hc c hc' a ha⟩, hc c hc' b hb⟩
  obtain ⟨g1, g2, hg1, hg2, hcov, hlen⟩ :=
    leaf_spec (chain_leaf h (hinv a ha ha1) hbI hbT hcI hcT)
  have hT : ∀ x, x ∈ adjoinL c (adjoinL b (adjoinL a [1])) ↔ x ∈ Pm := fun x => (hspan x).symm
  have hB : ∀ q ∈ [a] ++ [b] ++ [c], q ∈ Pm := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (rfl | rfl) | rfl <;> assumption
  let g1' : ↥Qm := ⟨g1, (hQ g1).2 hg1⟩
  let g2' : ↥Qm := ⟨g2, (hQ g2).2 hg2⟩
  let ev : ↥Φ → S81 × S81 := fun γ =>
    (((γ : MulAut ↥Qm) g1' : ↥Qm), ((γ : MulAut ↥Qm) g2' : ↥Qm))
  have hmem : ∀ γ, ev γ ∈ candsOf (qmList ()) ([a] ++ [b] ++ [c])
      (adjoinL c (adjoinL b (adjoinL a [1]))) g1 g2 := fun γ =>
    ev_mem hQ hPQ hT hB (hfix γ γ.2) g1' g2'
  have hinj : Function.Injective ev := by
    intro γ δ hev
    have e1 : (γ : MulAut ↥Qm) g1' = (δ : MulAut ↥Qm) g1' := Subtype.ext (congrArg Prod.fst hev)
    have e2 : (γ : MulAut ↥Qm) g2' = (δ : MulAut ↥Qm) g2' := Subtype.ext (congrArg Prod.snd hev)
    exact Subtype.ext (ev_inj hQ hPQ hT (hfix γ γ.2) (hfix δ δ.2) g1' g2' hcov e1 e2)
  exact (card_le_length ev hinj _ hmem).trans hlen

end AutQBound

end CFSG.OddStandard.SmallF3.Omega
