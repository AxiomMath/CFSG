module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888W1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem exists_delta_of_ctx (h514 : Asc82Lemma514) (h517 : Asc82Lemma517)
    (hpar : Asc82Lemma518Parity) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {U : Subgroup G}
    (hU : U ≤ normalizer (Qsub K₁ K₂ h : Set G))
    (hab : IsElemAbelianModSub
      (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) U)
    (hcard : 16 ≤ (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G))
      (Qsub K₁ K₂ h)).relIndex U) :
    ∃ e ∈ Delta5 z (Gamma5 K₁ K₂ h), e ∈ Qsub K₁ K₂ h ∧
      ∀ u ∈ U, ∃ r ∈ Qsub K₁ K₂ h, (u * r) * e * (u * r)⁻¹ = e := by
  classical
  have hq := sec5b517_quad h514 c
  have hQ : Qsub K₁ K₂ h = Sec5B517Q8 hq := by
    rw [sec5b517_Qsub_eq, hq.core_eq]
  have hNz := sec5b517_normalizer_le h514 c
  have hNz8 : normalizer (Sec5B517Q8 hq : Set G) ≤ centralizer ({z} : Set G) := by
    simpa only [hQ] using hNz
  have hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (Kfam5 K₁ K₂ h i) n = Kfam5 K₁ K₂ h j := by
    intro n hn i
    have hn' : n ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hn
    have hmem : CFSG.conjugate (Kfam5 K₁ K₂ h i) n ∈ Gamma5 K₁ K₂ h :=
      (h517 G t L S z r B A K₁ K₂ h c).1 n hn' (Kfam5 K₁ K₂ h i)
        (by rw [sec5b517_gamma_eq]; exact ⟨i, rfl⟩)
    rw [sec5b517_gamma_eq] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩
  have hparG : ∀ w ∈ normalizer (Sec5B517Q8 hq : Set G),
      (∀ i, CFSG.conjugate (Kfam5 K₁ K₂ h i) w = Kfam5 K₁ K₂ h i) →
      (∀ q ∈ Sec5B517Q8 hq, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ twoCoreIn (Kfam5 K₁ K₂ h i),
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}) := by
    intro w hw hwfix hww
    have hw' : w ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hw
    have hmod : w * w ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G))
        (Qsub K₁ K₂ h) := by
      refine ⟨mul_mem hw' hw', hNz (mul_mem hw' hw'), mul_mem hw' hw', ?_⟩
      intro q hqQ
      exact hww q (by simpa only [hQ] using hqQ)
    exact hpar G t L S z r B A K₁ K₂ h c w hw' hwfix hmod
  rw [hQ] at hU hab hcard ⊢
  obtain ⟨e, i, j, hij, heQ, hee, he1, hez, heK, hfix⟩ :=
    exists_delta_of_quad hq hNz8 hperm hparG hU hab hcard
  have heord : orderOf e = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hee
    · exact he1
  refine ⟨e, ⟨heord, hez, Kfam5 K₁ K₂ h i, ?_, Kfam5 K₁ K₂ h j, ?_, ?_, heK⟩, heQ, hfix⟩
  · rw [sec5b517_gamma_eq]; exact ⟨i, rfl⟩
  · rw [sec5b517_gamma_eq]; exact ⟨j, rfl⟩
  · exact Sec5B517Quad.ne hq hij

end CFSG.OddStandard.SmallF3.Omega
