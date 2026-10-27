module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBTransData

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule


section Words

variable {τ : Tag}

theorem foldr_reflect_eq_of_fix {v : Fin τ.rank → ℤ} {l : List (Fin τ.rank)}
    (h : ∀ j ∈ l, reflect τ j v = v) : l.foldr (reflect τ) v = v := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]
    exact h j List.mem_cons_self

theorem exists_letter_moving {v : Fin τ.rank → ℤ} {l : List (Fin τ.rank)}
    (h : (coxeterSystem τ).wordProd l • v ≠ v) : ∃ j ∈ l, reflect τ j v ≠ v := by
  by_contra hcon
  push Not at hcon
  exact h (by rw [wordProd_smul_foldr]; exact foldr_reflect_eq_of_fix hcon)

end Words

section Main

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem card_le_finrank_of_words {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {v : Fin TwistTag.E6.foldedTag.rank → ℤ}
    (hv : ∀ j : Fin TwistTag.E6.foldedTag.rank, reflect TwistTag.E6.foldedTag j v ≠ v → j ∉ J)
    (L : List (List (Fin TwistTag.E6.foldedTag.rank)))
    (hL : (L.map fun w => w.foldr (reflect TwistTag.E6.foldedTag) v).Nodup) : L.length ≤ m := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (twistedCover_split hf hK σ hσ k)
  let w : Fin L.length → ↥(relWeylTwist TwistTag.E6) :=
    fun i => (relCs TwistTag.E6).wordProd (L.get i)
  have hfw : ∀ i, foldedWeylEquiv TwistTag.E6 (w i) • v = (L.get i).foldr (reflect TwistTag.E6.foldedTag) v :=
    fun i => by
      show foldedWeylEquiv TwistTag.E6 ((relCs TwistTag.E6).wordProd (L.get i)) • v = _
      rw [relCs_wordProd, wordProd_smul_foldr]
  have hinj : ∀ i j : Fin L.length, i ≠ j →
      foldedWeylEquiv TwistTag.E6 (w i) • v ≠ foldedWeylEquiv TwistTag.E6 (w j) • v := by
    intro i j hij h
    rw [hfw, hfw] at h
    refine hij (Fin.ext ?_)
    have := (List.Nodup.getElem_inj_iff hL (i := i.1) (j := j.1)
      (hi := by simp) (hj := by simp)).1 (by simpa [List.getElem_map] using h)
    exact this
  have key : L.length ≤ Module.finrank k (Fin m → k) := by
    refine CurtisExc.card_le_finrank hρ hμ w (fun i j hij ω hω hωe => ?_)
    have hne : (coxeterSystem TwistTag.E6.foldedTag).wordProd (ω : List (Fin TwistTag.E6.foldedTag.rank)) • v ≠ v := by
      intro h
      apply hinj i j hij
      rw [← relCs_wordProd, hωe, map_mul, map_inv, mul_smul] at h
      have := congrArg (fun z => foldedWeylEquiv TwistTag.E6 (w i) • z) h
      simpa [smul_smul] using this.symm
    obtain ⟨l, hl, hlv⟩ := exists_letter_moving hne
    have : Fintype (orbitField TwistTag.E6 K σ l)ˣ := Fintype.ofFinite _
    exact ⟨l, hl, IsCoverType.mu_eq_dScalar (twistedCover_hodd hf hK σ hσ) ht hμ (hv l hlv)⟩
  simpa using key

include hf hK hσ in
theorem twTransBound_holds : TwTransBound hf K hK σ hσ := by
  intro k _ _ _ _ m ρ y χ J hρ ht
  have h96 : ∀ a : Fin 4, (a.val = 1 ∨ a.val = 2) → 96 ≤ f4OrbitSize a := by decide
  constructor
  · rintro ⟨a, haJ, ha⟩
    have hv : ∀ j : Fin TwistTag.E6.foldedTag.rank,
        reflect TwistTag.E6.foldedTag j (f4Weight a) ≠ f4Weight a → j ∉ J := by
      intro j hj
      have hja : j = a := by
        by_contra hne
        exact hj (f4Weight_fixed a j hne)
      exact hja ▸ haJ
    have := card_le_finrank_of_words hf K hK σ hσ hρ ht hv (f4Words a) (f4Words_nodup a)
    exact (h96 a ha).trans ((f4Words_length a).symm.le.trans this)
  · rintro ⟨a, b, hab, haJ, hbJ⟩
    have hv : ∀ j : Fin TwistTag.E6.foldedTag.rank,
        reflect TwistTag.E6.foldedTag j (f4Weight a + f4Weight b) ≠ f4Weight a + f4Weight b →
          j ∉ J := by
      intro j hj
      by_cases hja : j = a
      · exact hja ▸ haJ
      by_cases hjb : j = b
      · exact hjb ▸ hbJ
      exact absurd (pairWeight_fixed a b j hja hjb) hj
    have := card_le_finrank_of_words hf K hK σ hσ hρ ht hv (pairWords a b)
      (pairWords_nodup a b hab)
    exact (pairWords_length a b hab).trans this

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
