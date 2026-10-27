module

import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExt
import CFSG.LocalAnalysis.AGLEmbeddingD2.SevenOnThree
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem mulAut_eq_one_of_pow_seven {T : Type*} [Group T] [Finite T] (hT : IsPGroup 3 T)
    (hrank : Open.pRank 3 (⊤ : Subgroup T) ≤ 3) {θ : MulAut T} (hθ : θ ^ 7 = 1) : θ = 1 := by
  let ι : T →* Equiv.Perm T := MulAction.toPermHom T T
  have hι : Function.Injective ι := fun a b h => by
    simpa [ι] using congrArg (fun f : Equiv.Perm T => f 1) h
  let T' : Subgroup (Equiv.Perm T) := ι.range
  have hT' : IsPGroup 3 T' := hT.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  have hrank' : Open.pRank 3 T' ≤ 3 := by
    rw [SectionRank.pRank_eq_pRank_top_subgroup (p := 3) T',
      ← SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MonoidHom.ofInjective hι)]
    exact hrank
  have hconj : ∀ (ϑ : MulAut T) (t : T),
      MulAut.toPerm T ϑ * ι t * (MulAut.toPerm T ϑ)⁻¹ = ι (ϑ t) := by
    intro ϑ t
    refine Equiv.ext fun s => ?_
    change ϑ (t * ϑ.symm s) = ϑ t * s
    rw [map_mul, MulEquiv.apply_symm_apply]
  let x : Equiv.Perm T := MulAut.toPerm T θ
  have hx : x ^ 7 = 1 := by
    rw [← map_pow, hθ, map_one]
  have hxN : x ∈ Subgroup.normalizer (T' : Set (Equiv.Perm T)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨θ t, (hconj θ t).symm⟩
    · rintro ⟨t, ht⟩
      refine ⟨θ⁻¹ t, ?_⟩
      have h1 : ι (θ⁻¹ t) = x⁻¹ * ι t * x := by
        have := hconj θ⁻¹ t
        rw [map_inv, inv_inv] at this
        exact this.symm
      rw [h1, ht]
      group
  have hcent := mem_centralizer_of_pow_seven hT' hrank' hx hxN
  refine MulEquiv.ext fun t => ?_
  have h1 := congrArg (fun f : Equiv.Perm T => f 1)
    (Subgroup.mem_centralizer_iff.1 hcent (ι t) ⟨t, rfl⟩)
  change t * θ 1 = θ (t * 1) at h1
  rw [map_one, mul_one] at h1
  exact h1.symm

theorem mulAut_eq_one_of_pow_seven_pow {T : Type*} [Group T] [Finite T] (hT : IsPGroup 3 T)
    (hrank : Open.pRank 3 (⊤ : Subgroup T) ≤ 3) (a : ℕ) {θ : MulAut T} (hθ : θ ^ 7 ^ a = 1) :
    θ = 1 := by
  induction a generalizing θ with
  | zero => simpa using hθ
  | succ a ih =>
    refine mulAut_eq_one_of_pow_seven hT hrank (ih ?_)
    rw [← pow_mul, ← pow_succ']
    exact hθ

theorem mem_centralizer_of_pow_seven_pow {Y : Type*} [Group Y] [Finite Y] {T : Subgroup Y}
    (hT : IsPGroup 3 T) (hrank : Open.pRank 3 T ≤ 3) {x : Y} {a : ℕ} (hx : x ^ 7 ^ a = 1)
    (hxT : x ∈ Subgroup.normalizer (T : Set Y)) : x ∈ Subgroup.centralizer (T : Set Y) := by
  let θ : MulAut T := T.normalizerMonoidHom ⟨x, hxT⟩
  have hθ : θ ^ 7 ^ a = 1 := by
    change (T.normalizerMonoidHom ⟨x, hxT⟩) ^ 7 ^ a = 1
    rw [← map_pow, show (⟨x, hxT⟩ : Subgroup.normalizer (T : Set Y)) ^ 7 ^ a = 1 from
      Subtype.ext hx, map_one]
  have hrank' : Open.pRank 3 (⊤ : Subgroup T) ≤ 3 :=
    (SectionRank.pRank_le_map (by norm_num) T.subtype T.subtype_injective ⊤).trans (by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hrank)
  have hθ1 := mulAut_eq_one_of_pow_seven_pow hT hrank' a hθ
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : x * y * x⁻¹ = y := congrArg (fun f : MulAut T => ((f ⟨y, hy⟩ : T) : Y)) hθ1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

namespace AltLargePrime

open Equiv in
theorem exists_pow_seven_eq_one {n : ℕ} (hn : 8 ≤ n) :
    ∃ σ : alternatingGroup (Fin n), σ ^ 7 = 1 ∧ σ ≠ 1 := by
  obtain ⟨f, hf⟩ := AltCentralExt.exists_injective_alt_eight hn
  have h8 : ∃ σ : alternatingGroup (Fin 8), σ ^ 7 = 1 ∧ σ ≠ 1 :=
    ⟨⟨c[0, 1, 2, 3, 4, 5, 6], Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      by decide +kernel, by decide +kernel⟩
  obtain ⟨σ, h7, h1⟩ := h8
  exact ⟨f σ, by rw [← map_pow, h7, map_one], fun h => h1 (hf (by rw [h, map_one]))⟩

variable {W : Type*} [Group W] [Finite W] {A : Type*} [Group A] [IsSimpleGroup A]

end AltLargePrime

end CFSG.AGLEmbeddingD2
