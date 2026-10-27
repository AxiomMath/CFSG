module

public import CFSG.LieType.Chevalley.GraphFixedSimpleBruhat

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (t) in
theorem orbitLength_le
    (ω : List (Fin t.foldedTag.rank)) :
    t.orbitLength (ω.map t.orbitReflection).prod ≤ ω.length :=
  Nat.sInf_le ⟨ω, rfl, rfl⟩

theorem orbitLength_orbitReflection_mul_le
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (a : Fin t.foldedTag.rank) :
    t.orbitLength (t.orbitReflection a * w) ≤ t.orbitLength w + 1 := by
  rcases forall_height_pos_or_forall_height_neg (inv_mem hw) a with hp | hn
  · exact (length_orbitReflection_mul_of_pos t hw hp).1.le
  · have := (length_orbitReflection_mul_of_neg t hw hn).1
    omega

theorem canonicalRep_orbitReflection_mem_of_conj_le
    {A : Subgroup (ModGL t.tag K)}
    (hB : graphFixedRootBorel t K σ ≤ A) {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (hconj : ∀ b ∈ graphFixedRootBorel t K σ, canonicalRep (coxeterSystem t.tag) K w * b *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ A)
    {a : Fin t.foldedTag.rank}
    (hneg : ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A := by
  have hy : ∀ c : orbitField t K σ a, (orbitY t K σ a c : ModGL t.tag K) ∈ A := fun c => by
    have h := canonicalRep_inv_mul_mul_mem_graphFixedRootBorel (σ := σ) hw
      (S := (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a))
      (by rintro _ ⟨i, -, rfl⟩; exact isRoot_neg_single _ i)
      (by rintro _ ⟨i, hi, rfl⟩; rw [smul_neg, height_neg]; linarith [hneg i hi])
      (orbitYEquiv t σ a (Multiplicative.ofAdd c)).2
    rw [coe_orbitYEquiv] at h
    have e : (orbitY t K σ a c : ModGL t.tag K) = canonicalRep (coxeterSystem t.tag) K w *
        ((canonicalRep (coxeterSystem t.tag) K w)⁻¹ * (orbitY t K σ a c : ModGL t.tag K) *
          canonicalRep (coxeterSystem t.tag) K w) * (canonicalRep (coxeterSystem t.tag) K w)⁻¹ := by
      group
    rw [e]
    exact hconj _ h
  have hx : ∀ c : orbitField t K σ a, (orbitX t K σ a c : ModGL t.tag K) ∈ A := fun c =>
    hB (graphFixedPosUnipotent_le_graphFixedRootBorel (orbitX_mem_graphFixedPosUnipotent t σ a c))
  rw [canonicalRep_orbitReflection_eq_orbitN t σ a, orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem canonicalRep_orbitReflection_mem_of_reduced
    {A : Subgroup (ModGL t.tag K)}
    (hB : graphFixedRootBorel t K σ ≤ A) (ω : List (Fin t.foldedTag.rank)) :
    ∀ w ∈ relWeylTwist t,
      (∀ b ∈ graphFixedRootBorel t K σ, canonicalRep (coxeterSystem t.tag) K w * b *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ A) →
      (ω.map t.orbitReflection).prod = w → ω.length = t.orbitLength w →
        ∀ a ∈ ω, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A := by
  induction ω with
  | nil => intro _ _ _ _ _ a ha; exact absurd ha List.not_mem_nil
  | cons a ω ih =>
    intro w hw hconj hprod hlen
    set w' := (ω.map t.orbitReflection).prod with hw'def
    have hw' : w' ∈ relWeylTwist t := t.list_prod_orbitReflection_mem ω
    have hww' : w = t.orbitReflection a * w' := by
      rw [← hprod, List.map_cons, List.prod_cons]
    have hle : t.orbitLength w' ≤ ω.length := orbitLength_le t ω
    have hle' := orbitLength_orbitReflection_mul_le hw' a
    rw [← hww', ← hlen, List.length_cons] at hle'
    have hlen' : ω.length = t.orbitLength w' := by omega
    have hup : t.orbitLength (t.orbitReflection a * w') = t.orbitLength w' + 1 := by
      rw [← hww', ← hlen, List.length_cons, hlen']
    have hpos := forall_height_inv_smul_pos_of_orbitLength hw' hup
    have hneg : ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 := by
      intro i hi
      rw [hww', mul_inv_rev, t.orbitReflection_inv, mul_smul, t.orbitReflection_smul_single hi,
        smul_neg, height_neg]
      linarith [hpos i hi]
    have hNA := canonicalRep_orbitReflection_mem_of_conj_le hB hw hconj hneg
    obtain ⟨h, hh, hrep⟩ := exists_canonicalRep_mul_eq (K := K) (σ := σ) (t.orbitReflection_mem a)
      hw'
    rw [← hww'] at hrep
    have hconj' : ∀ b ∈ graphFixedRootBorel t K σ, canonicalRep (coxeterSystem t.tag) K w' * b *
        (canonicalRep (coxeterSystem t.tag) K w')⁻¹ ∈ A := by
      intro b hb
      have hhb : h * b * h⁻¹ ∈ graphFixedRootBorel t K σ :=
        mul_mem (mul_mem (graphFixedRootTorus_le_graphFixedRootBorel hh) hb)
          (inv_mem (graphFixedRootTorus_le_graphFixedRootBorel hh))
      have e : canonicalRep (coxeterSystem t.tag) K w' * b *
          (canonicalRep (coxeterSystem t.tag) K w')⁻¹ =
          (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ *
            (canonicalRep (coxeterSystem t.tag) K w * (h * b * h⁻¹) *
              (canonicalRep (coxeterSystem t.tag) K w)⁻¹) *
            canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) := by
        rw [eq_mul_inv_iff_mul_eq.2 hrep.symm]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hNA) (hconj _ hhb)) hNA
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact hNA
    · exact ih w' hw' hconj' rfl hlen' b hb'

theorem fixed_reduced_word_Borel_extraction
    (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    ∀ A : Subgroup (ModGL t.tag K), A ≤ graphFixedRootGroup t K σ →
      graphFixedRootBorel t K σ ≤ A → ∀ w ∈ relWeylTwist t,
        (∀ b ∈ graphFixedRootBorel t K σ, canonicalRep (coxeterSystem t.tag) K w * b *
          (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ A) →
        ∀ ω : List (Fin t.foldedTag.rank), (ω.map t.orbitReflection).prod = w →
          ω.length = t.orbitLength w →
            ∀ a ∈ ω, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A :=
  fun _ _ hB w hw hconj ω hprod hlen =>
    canonicalRep_orbitReflection_mem_of_reduced hB ω w hw hconj hprod hlen

end CFSG.LieType.Chevalley
