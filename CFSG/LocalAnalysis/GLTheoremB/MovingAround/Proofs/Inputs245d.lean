module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245cHolds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Model
public import Certificates.Certificate245401
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Push

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245d

open TauCeti CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.KFactProofs.ThreeWeak
  CFSG.LieType.Multipliers.U43 CFSG.SectionRank
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245c (CoverPointDatumA)

theorem coverPointDatumA_of_surjective {X Y : Type} [Group X] [Group Y] {p : ℕ} (φ : X →* Y)
    (hφ : Function.Surjective φ) (hker : ∀ x : X, φ x = 1 → x ^ p = 1 → x = 1)
    (h : CoverPointDatumA X p) : CoverPointDatumA Y p := by
  obtain ⟨D, k, b, l, h', e, hn, hA, hNF, hb, hconj, hgen⟩ := h
  let D' : ModuleSpec Y p :=
    { n := D.n
      m := D.m
      a := fun i => φ (D.a i)
      g := fun j => φ (D.g j)
      M := D.M
      comm := fun i j => by rw [← map_mul, ← map_mul, D.comm]
      pow := fun i => by rw [← map_pow, D.pow, map_one]
      indep := fun c hc => by
        refine D.indep c (hker _ ?_ ?_)
        · simpa [map_list_prod, List.map_map, Function.comp_def] using hc
        · refine moduleSpec_pow_eq_one_of_mem_span D (Subgroup.list_prod_mem _ fun x hx => ?_)
          obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
          exact Subgroup.pow_mem _ (show D.a k ∈ D.span from Subgroup.subset_closure ⟨k, rfl⟩) _
      act := fun j i => by
        rw [← map_inv, ← map_mul, ← map_mul, D.act, map_list_prod, List.map_map]
        simp only [Function.comp_def, map_pow] }
  have hspan : D'.span = D.span.map φ := by
    simp only [ModuleSpec.span, D', MonoidHom.map_closure, ← Set.range_comp, Function.comp_def]
  refine ⟨D', k, fun j => φ (b j), l, fun j i => φ (h' j i), e, hn, hA, hNF, ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rw [hspan]
      exact Subgroup.mem_map_of_mem φ (hb j).1
    · intro h1
      exact (hb j).2 (hker _ h1 (moduleSpec_pow_eq_one_of_mem_span D (hb j).1))
  · intro j i
    rw [← map_inv, ← map_mul, ← map_mul, hconj, map_pow]
  · have hmap : Subgroup.closure (Set.range D'.g ∪ ⋃ j, Set.range fun i => φ (h' j i)) =
        (Subgroup.closure (Set.range D.g ∪ ⋃ j, Set.range (h' j))).map φ := by
      rw [MonoidHom.map_closure, Set.image_union, Set.image_iUnion]
      simp only [D', ← Set.range_comp, Function.comp_def]
    rw [hmap, hgen, Subgroup.map_top, MonoidHom.range_eq_top.2 hφ]

theorem coverPointDatumA_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    (h : CoverPointDatumA X p) : CoverPointDatumA Y p :=
  coverPointDatumA_of_surjective e.toMonoidHom e.surjective
    (fun _ hx _ => e.injective (hx.trans (map_one e).symm)) h

section U43


theorem coverPointDatumA_X₀ : CoverPointDatumA X₀ 3 :=
  coverPointDatumA_of_surjective (p := 3) U43Seed.toX₀ U43Seed.toX₀_surjective
    (fun k hk hk3 => U43Seed.eq_one_of_toX₀_eq_one k hk hk3)
    (coverPointDatumA_of_mulEquiv U43Seed.seedEquiv
      (Inputs245c.coverPointDatumA_of_check (spec3 8) (D := cpSpec) Nat.prime_three
        (by show (3 : ℕ) ≠ 2; norm_num) Certificates.certificate245401.1
        Certificates.certificate245401.2 (by decide +kernel)))

theorem u43CoverX0_holds : Inputs245c.U43CoverX0 := by
  refine Inputs245c.u43CoverX0_of_coverPointDatumA fun q hv hq => ?_
  have hdvd : q.p ∣ 3 := by
    rw [← hq, PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  have hq1 : q.exponent = 1 := by
    have h : 3 ^ q.exponent = 3 ^ 1 := by
      rw [← hp3, ← PrimePower.card_def, hq, hp3, pow_one]
    exact Nat.pow_right_injective (by norm_num) h
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
    (G := (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (MulEquiv.refl _)
  rw [hp3, hq1] at hmod
  obtain ⟨e⟩ := nonempty_mulEquiv_X₀
    (X := (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (Or.inl ⟨by decide, hmod⟩)
  exact coverPointDatumA_of_mulEquiv e.symm coverPointDatumA_X₀

end U43

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245d
