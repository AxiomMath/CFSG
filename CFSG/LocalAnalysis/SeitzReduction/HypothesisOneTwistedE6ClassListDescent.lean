module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassDescent

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem twistedE6Descent_check₁ :
    ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
      0 < height (TwistTag.E6.tag.rootCertificate.root k) →
        2 ≤ height (TwistTag.E6.tag.rootCertificate.root k) →
          ∃ a ∈ List.finRange TwistTag.E6.foldedTag.rank,
            (∃ j ∈ TwistTag.E6.orbitWord a, 0 < TwistTag.E6.tag.rootCertificate.root k j) ∧
            height (twistedE6RelAct [a] (TwistTag.E6.tag.rootCertificate.root k)) <
              height (TwistTag.E6.tag.rootCertificate.root k) := by
  decide +kernel

theorem twistedE6Descent_check₂ :
    ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
      0 < height (TwistTag.E6.tag.rootCertificate.root k) →
        2 ≤ height (TwistTag.E6.tag.rootCertificate.root k) →
          ∀ a ∈ List.finRange TwistTag.E6.foldedTag.rank,
            0 < height (twistedE6RelAct [a] (TwistTag.E6.tag.rootCertificate.root k)) := by
  decide +kernel

theorem twistedE6Descent_check₃ :
    ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
      ∀ a ∈ List.finRange TwistTag.E6.foldedTag.rank, ∀ l ∈ List.finRange TwistTag.E6.tag.rank,
        l ∉ TwistTag.E6.orbitWord a →
          twistedE6RelAct [a] (TwistTag.E6.tag.rootCertificate.root k) l =
            TwistTag.E6.tag.rootCertificate.root k l := by
  decide +kernel

theorem twistedE6Descent_check₄ :
    ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
      ∀ a ∈ List.finRange TwistTag.E6.foldedTag.rank,
        twistedE6RelAct [a] (twistedE6RelAct [a] (TwistTag.E6.tag.rootCertificate.root k)) =
          TwistTag.E6.tag.rootCertificate.root k := by
  decide +kernel

theorem twistedE6Descent_facts {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ) :
    (2 ≤ height γ → ∃ a : Fin TwistTag.E6.foldedTag.rank,
      (∃ j ∈ TwistTag.E6.orbitWord a, 0 < γ j) ∧ height (twistedE6RelAct [a] γ) < height γ) ∧
    ∀ a : Fin TwistTag.E6.foldedTag.rank,
      (2 ≤ height γ → 0 < height (twistedE6RelAct [a] γ)) ∧
      (∀ l, l ∉ TwistTag.E6.orbitWord a → twistedE6RelAct [a] γ l = γ l) ∧
      twistedE6RelAct [a] (twistedE6RelAct [a] γ) = γ := by
  rw [isRoot_iff_twistedE6TwoRootB] at hγ
  simp only [twistedE6TwoRootB, List.any_eq_true, List.mem_range, twistedE6TwoVecB_iff] at hγ
  obtain ⟨k, hk, rfl⟩ := hγ
  have hk' := List.mem_range.2 hk
  refine ⟨fun h => ?_, fun a => ⟨fun h => twistedE6Descent_check₂ k hk' hpos h a
    (List.mem_finRange a), fun l hl => twistedE6Descent_check₃ k hk' a (List.mem_finRange a) l
      (List.mem_finRange l) hl, twistedE6Descent_check₄ k hk' a (List.mem_finRange a)⟩⟩
  obtain ⟨a, -, ha⟩ := twistedE6Descent_check₁ k hk' hpos h
  exact ⟨a, ha⟩


theorem twistedE6_exists_relWeyl_word_list [CharP K 2] (J : Set (Fin TwistTag.E6.tag.rank))
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) (n : ℕ) :
    ∀ (L : List (Fin TwistTag.E6.tag.rank → ℤ)) (c : (Fin TwistTag.E6.tag.rank → ℤ) → K),
      L.Nodup → (∀ α ∈ L, α ∈ parabolicPosRoots TwistTag.E6.tag J ∧ c α ≠ 0) →
      (∃ α ∈ L, height α ≤ n) →
      ∃ ω : List (Fin TwistTag.E6.foldedTag.rank), (∀ a ∈ ω, ∀ j ∈ TwistTag.E6.orbitWord a, j ∈ J) ∧
        ∃ (L' : List (Fin TwistTag.E6.tag.rank → ℤ)) (c' : (Fin TwistTag.E6.tag.rank → ℤ) → K),
          L'.Nodup ∧ (∀ α ∈ L', α ∈ parabolicPosRoots TwistTag.E6.tag J ∧ c' α ≠ 0) ∧
          (∃ i ∈ J, Pi.single i 1 ∈ L') ∧
          twistedE6RelWeyl K ω * (L.map fun α => pinnedX TwistTag.E6.tag K α (c α)).prod *
              (twistedE6RelWeyl K ω)⁻¹ =
            (L'.map fun α => pinnedX TwistTag.E6.tag K α (c' α)).prod := by
  induction n with
  | zero =>
    rintro L c - hL ⟨α, hα, hle⟩
    have := (hL α hα).1.2.2
    push_cast at hle
    omega
  | succ n ih =>
    rintro L c hnd hL ⟨α₀, hα₀, hle⟩
    by_cases hlow : ∃ α ∈ L, height α ≤ n
    · exact ih L c hnd hL hlow
    push Not at hlow
    have hα₀h : height α₀ = n + 1 := by have := hlow α₀ hα₀; push_cast at hle ⊢; omega
    obtain ⟨⟨hα₀r, hα₀s⟩, -, hα₀p⟩ := (hL α₀ hα₀).1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      obtain ⟨i, hi⟩ := classDescent_eq_single_of_height_eq_one hα₀r (by simpa using hα₀h)
      have hiJ : i ∈ J := by
        by_contra hiJ
        have := hα₀s i hiJ
        rw [hi, Pi.single_eq_same] at this
        exact one_ne_zero this
      exact ⟨[], by simp, L, c, hnd, hL, ⟨i, hiJ, hi ▸ hα₀⟩, by simp [twistedE6RelWeyl]⟩
    ·
      have h2 : ∀ α ∈ L, 2 ≤ height α := fun α hα => by have := hlow α hα; omega
      obtain ⟨a, ⟨j, hj, hjpos⟩, hlt⟩ := (twistedE6Descent_facts hα₀r hα₀p).1 (h2 α₀ hα₀)
      have hjJ : j ∈ J := by
        by_contra hjJ
        have := hα₀s j hjJ
        omega
      have horb : ∀ l ∈ TwistTag.E6.orbitWord a, l = j ∨ l = TwistTag.E6.perm j := by
        have h : ∀ a : Fin TwistTag.E6.foldedTag.rank, ∀ j ∈ TwistTag.E6.orbitWord a,
            ∀ l ∈ TwistTag.E6.orbitWord a, l = j ∨ l = TwistTag.E6.perm j := by decide
        exact h a j hj
      have haJ : ∀ l ∈ TwistTag.E6.orbitWord a, l ∈ J := fun l hl => by
        rcases horb l hl with rfl | rfl
        · exact hjJ
        · exact hJ j hjJ
      set f := twistedE6RelAct [a] with hf
      have hfacts : ∀ α ∈ L, IsRoot TwistTag.E6.tag (f α) ∧ 0 < height (f α) ∧
          (∀ l, l ∉ TwistTag.E6.orbitWord a → f α l = α l) ∧ f (f α) = α := fun α hα => by
        obtain ⟨⟨hαr, -⟩, -, hαp⟩ := (hL α hα).1
        obtain ⟨-, H⟩ := twistedE6Descent_facts hαr hαp
        obtain ⟨H1, H2, H3⟩ := H a
        exact ⟨IsRoot.twistedE6RelAct hαr [a], H1 (h2 α hα), H2, H3⟩
      set c₂ : (Fin TwistTag.E6.tag.rank → ℤ) → K := fun β => c (f β) with hc₂
      have hL₂ : ∀ β ∈ L.map f, β ∈ parabolicPosRoots TwistTag.E6.tag J ∧ c₂ β ≠ 0 := by
        intro β hβ
        obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hβ
        obtain ⟨⟨-, hαs⟩, -, -⟩ := (hL α hα).1
        obtain ⟨hr, hp, hcoord, hinv⟩ := hfacts α hα
        refine ⟨⟨⟨hr, fun l hl => ?_⟩, hr, hp⟩, ?_⟩
        · rw [hcoord l (fun h => hl (haJ l h))]
          exact hαs l hl
        · simp only [hc₂, hinv]
          exact (hL α hα).2
      have hnd₂ : (L.map f).Nodup := hnd.map_on fun x hx y hy hxy => by
        rw [← (hfacts x hx).2.2.2, hxy, (hfacts y hy).2.2.2]
      have hlow₂ : ∃ β ∈ L.map f, height β ≤ (n : ℤ) :=
        ⟨f α₀, List.mem_map_of_mem hα₀, by omega⟩
      obtain ⟨ω, hωJ, L', c', hnd', hL', hsimple, hconj⟩ := ih _ c₂ hnd₂ hL₂ hlow₂
      refine ⟨ω ++ [a], fun a' ha' => ?_, L', c', hnd', hL', hsimple, ?_⟩
      · rcases List.mem_append.1 ha' with h | h
        · exact hωJ a' h
        · rw [List.mem_singleton.1 h]
          exact haJ
      · have htr := twistedE6RelWeyl_conj_list_prod (K := K) [a]
          (F := L) (fun α hα => (hL α hα).1.1.1) c
        have e : ((L.map f).map fun β => pinnedX TwistTag.E6.tag K β (c₂ β)) =
            L.map fun α => pinnedX TwistTag.E6.tag K (twistedE6RelAct [a] α) (c α) := by
          rw [List.map_map]
          refine List.map_congr_left fun α hα => ?_
          simp only [Function.comp_apply, hc₂, (hfacts α hα).2.2.2]
          rfl
        have hsplit : twistedE6RelWeyl K (ω ++ [a]) = twistedE6RelWeyl K ω * twistedE6RelWeyl K [a] := by
          simp only [twistedE6RelWeyl, List.flatMap_append, List.map_append, List.prod_append]
        rw [hsplit, ← hconj, e, ← htr]
        group

theorem exists_twistedE6RelWeyl_conj_not_mem_simpleRadical [CharP K 2]
    (J : Set (Fin TwistTag.E6.tag.rank)) (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {t : ModGL TwistTag.E6.tag K} (ht : t ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J))
    (ht1 : t ≠ 1) :
    ∃ ω : List (Fin TwistTag.E6.foldedTag.rank), (∀ a ∈ ω, ∀ j ∈ TwistTag.E6.orbitWord a, j ∈ J) ∧
      ∃ i ∈ J,
        twistedE6RelWeyl K ω * t * (twistedE6RelWeyl K ω)⁻¹ ∈
          rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) ∧
        twistedE6RelWeyl K ω * t * (twistedE6RelWeyl K ω)⁻¹ ∉
          rootSpan TwistTag.E6.tag K {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧
            α ≠ Pi.single i 1} := by
  obtain ⟨L, c, hnd, hL, rfl⟩ := classDescent_exists_list_of_mem ht
  obtain ⟨α, hα⟩ : ∃ α, α ∈ L := by
    cases L with
    | nil => exact absurd (by simp) ht1
    | cons α L => exact ⟨α, List.mem_cons_self⟩
  obtain ⟨ω, hωJ, L', c', hnd', hL', ⟨i, hiJ, hi⟩, hconj⟩ :=
    twistedE6_exists_relWeyl_word_list (K := K) J hJ (height α).toNat L c hnd hL
      ⟨α, hα, Int.self_le_toNat _⟩
  refine ⟨ω, hωJ, i, hiJ, ?_, ?_⟩
  · rw [hconj]
    exact classDescent_list_prod_mem_rootSpan L' (fun β hβ => (hL' β hβ).1) c'
  · rw [hconj]
    exact classDescent_list_prod_not_mem_rootSpan_ne_single hnd' (fun β hβ => (hL' β hβ).1.2) hi
      (hL' _ hi).2

end CFSG.SeitzReduction
