module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.AGLEmbedding

theorem moduleSpec_span_comm {X : Type} [Group X] {p : ℕ} (D : ModuleSpec X p) {y z : X}
    (hy : y ∈ D.span) (hz : z ∈ D.span) : y * z = z * y := by
  have h1 : D.span ≤ Subgroup.centralizer (Set.range D.a) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    exact D.comm j i
  have h2 : y ∈ Subgroup.centralizer (Subgroup.centralizer (Set.range D.a) : Set X) :=
    Subgroup.closure_le_centralizer_centralizer _ hy
  exact ((Subgroup.mem_centralizer_iff.1 h2) z (h1 hz)).symm

theorem moduleSpec_pow_eq_one_of_mem_span {X : Type} [Group X] {p : ℕ} (D : ModuleSpec X p)
    {x : X} (hx : x ∈ D.span) : x ^ p = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact D.pow i
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (moduleSpec_span_comm D hx hy) p, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem coverPointDatum_of_surjective {X Y : Type} [Group X] [Group Y] {p : ℕ} (φ : X →* Y)
    (hφ : Function.Surjective φ) (hker : ∀ x : X, φ x = 1 → x ^ p = 1 → x = 1)
    (h : CoverPointDatum X p) : CoverPointDatum Y p := by
  obtain ⟨D, k, b, l, h', e, hn, hNF, hb, hconj, hgen⟩ := h
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
  refine ⟨D', k, fun j => φ (b j), l, fun j i => φ (h' j i), e, hn, hNF, ?_, ?_, ?_⟩
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

theorem coverPointDatum_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    (h : CoverPointDatum X p) : CoverPointDatum Y p :=
  coverPointDatum_of_surjective e.toMonoidHom e.surjective
    (fun _ hx _ => e.injective (hx.trans (map_one e).symm)) h

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
