module

public import CFSG.ClassicalInvolution.Phan.Phan3B3Alpha
public import CFSG.ClassicalInvolution.Phan.Phan3B3Sound

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.Asc77.B3C (SymplecticPhanPair)
open CFSG.ClassicalInvolution.PhanB3 (PhanFamilyB3)

@[expose] def sIdx : Fin 2 → Fin 4 := ![2, 3]

@[expose] def lIdx : Fin 2 → Fin 4 := ![0, 1]

@[expose] def wkSp (k : Fin 24) : List (Fin 4 × Bool) :=
  (decodeWord 2 (b3Su2Codes.getD k.val [])).map fun l => (sIdx l.1, l.2)

@[expose] def lWordSp (k : Fin 24) : List (Fin 4 × Bool) :=
  (decodeWord 2 (b3Su2Codes.getD k.val [])).map fun l => (lIdx l.1, l.2)

@[expose] def conjBy (c u : List (Fin 4 × Bool)) : List (Fin 4 × Bool) := c ++ u ++ invWord c

@[expose] def commWSp (a b : List (Fin 4 × Bool)) : List (Fin 4 × Bool) :=
  a ++ b ++ invWord a ++ invWord b

theorem h3_cases : ∀ k : Fin 24,
    (∃ i j : Fin 2, ∃ g : Fin 4,
      evalOrd spOrd spMats (commWSp [(lIdx i, true)] (conjBy (wkSp k) [(lIdx j, true)]) ++
        [(g, true)]) ≠
      evalOrd spOrd spMats ([(g, true)] ++
        commWSp [(lIdx i, true)] (conjBy (wkSp k) [(lIdx j, true)]))) ∨
    ((∀ j : Fin 2, ∃ u : Fin 24,
      evalOrd spOrd spMats (conjBy (wkSp k) [(lIdx j, true)]) =
        evalOrd spOrd spMats (conjBy wSp (lWordSp u))) ∧
     ∀ j : Fin 2, ∃ u : Fin 24,
      evalOrd spOrd spMats (conjBy wSp [(lIdx j, true)]) =
        evalOrd spOrd spMats (conjBy (wkSp k) (lWordSp u))) := by
  decide +kernel

section Reduction

variable {G : Type} [Group G] (E : PhanFamilyB3 b2Coord3 G)

theorem ι2_su2Elt (k : Fin 24) : E.ι 2 (su2Elt k) = E.ϑ (wordVal spGens (wkSp k)) := by
  have h1 : E.ι 2 (su2Elt k) = E.ϑ (b2Coord3.s (su2Elt k)) :=
    (DFunLike.congr_fun E.s_eq (su2Elt k)).symm
  rw [h1, wkSp, wordVal_reindex]
  have h2 : (fun i : Fin 2 => spGens (sIdx i)) = fun i => b2Coord3.s (gen2 i) := by
    funext i
    fin_cases i <;> rfl
  rw [h2, wordVal_map b2Coord3.s gen2, ← su2Words_getD k]
  rfl

theorem ι1_su2Elt (k : Fin 24) : E.ι 1 (su2Elt k) = E.ϑ (wordVal spGens (lWordSp k)) := by
  have h1 : E.ι 1 (su2Elt k) = E.ϑ (b2Coord3.ℓ (su2Elt k)) :=
    (DFunLike.congr_fun E.ℓ_eq (su2Elt k)).symm
  rw [h1, lWordSp, wordVal_reindex]
  have h2 : (fun i : Fin 2 => spGens (lIdx i)) = fun i => b2Coord3.ℓ (gen2 i) := by
    funext i
    fin_cases i <;> rfl
  rw [h2, wordVal_map b2Coord3.ℓ gen2, ← su2Words_getD k]
  rfl

theorem ϑ_conjBy (c u : List (Fin 4 × Bool)) :
    E.ϑ (wordVal spGens (conjBy c u)) =
      E.ϑ (wordVal spGens c) * E.ϑ (wordVal spGens u) * (E.ϑ (wordVal spGens c))⁻¹ := by
  simp only [conjBy, wordVal_append, wordVal_invWord, map_mul, map_inv]

theorem range_eq_closure_gen2 (φ : Su K9 3 1 2 →* G) :
    φ.range = Subgroup.closure {φ A2, φ B2} := by
  rw [MonoidHom.range_eq_map, ← closure_gen2, MonoidHom.map_closure]
  congr 1
  rw [gen2, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]
  simp [Set.image_insert_eq, Set.pair_comm]

theorem conjSub_le_of_mem_gens {n : G} {K L : Subgroup G} {S : Set G}
    (hK : K = Subgroup.closure S) (h : ∀ s ∈ S, n * s * n⁻¹ ∈ L) : conjSub n K ≤ L := by
  rw [conjSub, Subgroup.map_le_iff_le_comap, hK, Subgroup.closure_le]
  intro s hs
  exact h s hs

theorem conjSub_eq_b3W (hker : E.ϑ.ker ≤ Subgroup.center (StatedSp 2 F3F)) {w : G}
    (hw : w ∈ (E.ι 2).range)
    (hcomm : ∀ a ∈ (E.ι 1).range, ∀ b ∈ conjSub w (E.ι 1).range, a * b = b * a) :
    conjSub w (E.ι 1).range = conjSub (b3W E) (E.ι 1).range := by
  obtain ⟨A, rfl⟩ := hw
  obtain ⟨k, rfl⟩ := su2Elt_surjective A
  rw [ι2_su2Elt E k] at hcomm ⊢
  set g' : Fin 4 → G := fun i => E.ϑ (spGens i) with hg'
  have hwv : ∀ u : List (Fin 4 × Bool), wordVal g' u = E.ϑ (wordVal spGens u) := fun u =>
    wordVal_map E.ϑ spGens u
  have hmemU1 : ∀ u : Fin 24, E.ϑ (wordVal spGens (lWordSp u)) ∈ (E.ι 1).range := fun u =>
    ⟨su2Elt u, (ι1_su2Elt E u)⟩
  have hx : ∀ j : Fin 2, E.ϑ (spGens (lIdx j)) ∈ (E.ι 1).range := by
    intro j
    fin_cases j
    · exact ⟨A2, (DFunLike.congr_fun E.ℓ_eq A2).symm⟩
    · exact ⟨B2, (DFunLike.congr_fun E.ℓ_eq B2).symm⟩
  have hgen : ∀ j : Fin 2, E.ι 1 (gen2 j) = E.ϑ (spGens (lIdx j)) := by
    intro j
    fin_cases j
    · exact (DFunLike.congr_fun E.ℓ_eq A2).symm
    · exact (DFunLike.congr_fun E.ℓ_eq B2).symm
  have hcl : (E.ι 1).range = Subgroup.closure {E.ϑ (spGens (lIdx 0)), E.ϑ (spGens (lIdx 1))} := by
    rw [range_eq_closure_gen2 (E.ι 1)]
    have e0 : E.ι 1 A2 = E.ϑ (spGens (lIdx 0)) := hgen 0
    have e1 : E.ι 1 B2 = E.ϑ (spGens (lIdx 1)) := hgen 1
    rw [e0, e1]
  rcases h3_cases k with ⟨i, j, g, hg⟩ | ⟨h1, h2⟩
  ·
    exfalso
    have hval : E.ϑ (wordVal spGens (conjBy (wkSp k) [(lIdx j, true)])) =
        E.ϑ (wordVal spGens (wkSp k)) * E.ϑ (spGens (lIdx j)) *
          (E.ϑ (wordVal spGens (wkSp k)))⁻¹ := by
      rw [ϑ_conjBy]
      simp [wordVal, letterVal]
    have hmem : E.ϑ (wordVal spGens (conjBy (wkSp k) [(lIdx j, true)])) ∈
        conjSub (E.ϑ (wordVal spGens (wkSp k))) (E.ι 1).range := by
      rw [hval]
      exact ⟨_, hx j, rfl⟩
    have hc := hcomm _ (hx i) _ hmem
    have hone : E.ϑ (wordVal spGens (commWSp [(lIdx i, true)]
        (conjBy (wkSp k) [(lIdx j, true)]))) = 1 := by
      rw [← hwv]
      refine (wordVal_comm_iff g' [(lIdx i, true)] (conjBy (wkSp k) [(lIdx j, true)])).2 ?_
      rw [hwv, hwv]
      simpa [wordVal, letterVal, hg'] using hc
    have hcen := Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hone)) (spGens g)
    apply hg
    rw [← wordVal_spGens_eq_iff, wordVal_append, wordVal_append]
    simpa [wordVal, letterVal] using hcen.symm
  ·
    have hconj : ∀ (c : List (Fin 4 × Bool)) (u : Fin 24),
        E.ϑ (wordVal spGens (conjBy c (lWordSp u))) ∈
          conjSub (E.ϑ (wordVal spGens c)) (E.ι 1).range := by
      intro c u
      rw [ϑ_conjBy]
      exact ⟨_, hmemU1 u, rfl⟩
    refine le_antisymm ?_ ?_
    · refine conjSub_le_of_mem_gens hcl ?_
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · obtain ⟨u, hu⟩ := h1 0
        have := congrArg E.ϑ (wordVal_spGens_eq_iff.2 hu)
        rw [ϑ_conjBy, ϑ_conjBy, ϑ_wSp] at this
        have e : E.ϑ (wordVal spGens [(lIdx 0, true)]) = E.ϑ (spGens (lIdx 0)) := by
          simp [wordVal, letterVal]
        rw [e] at this
        rw [this]
        exact ⟨_, hmemU1 u, rfl⟩
      · obtain ⟨u, hu⟩ := h1 1
        have := congrArg E.ϑ (wordVal_spGens_eq_iff.2 hu)
        rw [ϑ_conjBy, ϑ_conjBy, ϑ_wSp] at this
        have e : E.ϑ (wordVal spGens [(lIdx 1, true)]) = E.ϑ (spGens (lIdx 1)) := by
          simp [wordVal, letterVal]
        rw [e] at this
        rw [this]
        exact ⟨_, hmemU1 u, rfl⟩
    · refine conjSub_le_of_mem_gens hcl ?_
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · obtain ⟨u, hu⟩ := h2 0
        have := congrArg E.ϑ (wordVal_spGens_eq_iff.2 hu)
        rw [ϑ_conjBy, ϑ_conjBy, ϑ_wSp] at this
        have e : E.ϑ (wordVal spGens [(lIdx 0, true)]) = E.ϑ (spGens (lIdx 0)) := by
          simp [wordVal, letterVal]
        rw [e] at this
        rw [this]
        exact ⟨_, hmemU1 u, rfl⟩
      · obtain ⟨u, hu⟩ := h2 1
        have := congrArg E.ϑ (wordVal_spGens_eq_iff.2 hu)
        rw [ϑ_conjBy, ϑ_conjBy, ϑ_wSp] at this
        have e : E.ϑ (wordVal spGens [(lIdx 1, true)]) = E.ϑ (spGens (lIdx 1)) := by
          simp [wordVal, letterVal]
        rw [e] at this
        rw [this]
        exact ⟨_, hmemU1 u, rfl⟩

end Reduction

section Closure

variable {G : Type} [Group G] (E : PhanFamilyB3 b2Coord3 G)

theorem ι_range_le_closure_b3Gens (k : Fin 3) :
    (E.ι k).range ≤ Subgroup.closure (Set.range (b3Gens E)) := by
  rw [range_eq_closure_gen2, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  fin_cases k
  · rcases hx with rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
  · rcases hx with rfl | rfl
    · exact Subgroup.subset_closure ⟨2, rfl⟩
    · exact Subgroup.subset_closure ⟨3, rfl⟩
  · rcases hx with rfl | rfl
    · exact Subgroup.subset_closure ⟨4, rfl⟩
    · exact Subgroup.subset_closure ⟨5, rfl⟩

theorem closure_b3Gens_eq_top {U : Fin 3 → Subgroup G} (hU : ∀ i, (E.ι i).range = U i)
    (hgen : ⨆ k, U k = ⊤) : Subgroup.closure (Set.range (b3Gens E)) = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact iSup_le fun k => (hU k) ▸ ι_range_le_closure_b3Gens E k

theorem closure_b3Gens6_eq : Subgroup.closure (Set.range (b3Gens6 E)) =
    (E.ι 0).range ⊔ (E.ι 1).range ⊔ conjSub (b3W E) (E.ι 1).range := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have h0 : (E.ι 0).range ≤ (E.ι 0).range ⊔ (E.ι 1).range ⊔ conjSub (b3W E) (E.ι 1).range :=
      le_sup_left.trans le_sup_left
    have h1 : (E.ι 1).range ≤ (E.ι 0).range ⊔ (E.ι 1).range ⊔ conjSub (b3W E) (E.ι 1).range :=
      le_sup_right.trans le_sup_left
    have hc : conjSub (b3W E) (E.ι 1).range ≤
        (E.ι 0).range ⊔ (E.ι 1).range ⊔ conjSub (b3W E) (E.ι 1).range := le_sup_right
    fin_cases i
    · exact h1 ⟨A2, rfl⟩
    · exact h1 ⟨B2, rfl⟩
    · exact h0 ⟨A2, rfl⟩
    · exact h0 ⟨B2, rfl⟩
    · exact hc ⟨E.ι 1 A2, ⟨A2, rfl⟩, rfl⟩
    · exact hc ⟨E.ι 1 B2, ⟨B2, rfl⟩, rfl⟩
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [range_eq_closure_gen2, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure ⟨2, rfl⟩
      · exact Subgroup.subset_closure ⟨3, rfl⟩
    · rw [range_eq_closure_gen2, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨1, rfl⟩
    · refine conjSub_le_of_mem_gens (range_eq_closure_gen2 (E.ι 1)) ?_
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact Subgroup.subset_closure ⟨4, rfl⟩
      · exact Subgroup.subset_closure ⟨5, rfl⟩

end Closure

theorem exists_surj_b3Hom
    (htw : ∀ p ∈ b3BadPairs, Subsingleton (CFSG.CosetTable.PG 6 (b3TwistRels p.1 p.2)))
    {G : Type} [Group G] {U : Fin 3 → Subgroup G} (hcomm : Commutes (U 0) (U 2))
    (h01 : ∃ W, UnitaryBlockStandardPair K9 3 1 W (U 0) (U 1))
    (h12 : ∃ W, SymplecticPhanPair F3F h2F W (U 1) (U 2)) (hgen : ⨆ k, U k = ⊤)
    (hH3 : ∃ w ∈ U 2, Commutes (U 1) (conjSub w (U 1)) ∧
      ¬ 3 ∣ Nat.card (Subgroup.center ↥(U 0 ⊔ U 1 ⊔ conjSub w (U 1)))) :
    ∃ π : PhanB3Group →* G, Function.Surjective π := by
  obtain ⟨E, hU, hker⟩ := exists_familyB3_three htw hcomm h01 h12
  obtain ⟨w, hw, hcw, h3w⟩ := hH3
  have hw' : w ∈ (E.ι 2).range := by
    rw [hU 2]
    exact hw
  have hcw' : ∀ a ∈ (E.ι 1).range, ∀ b ∈ conjSub w (E.ι 1).range, a * b = b * a := by
    rw [hU 1]
    exact hcw
  have hconj := conjSub_eq_b3W E hker hw' hcw'
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (b3Gens6 E)))) := by
    rw [closure_b3Gens6_eq, ← hconj, hU 0, hU 1]
    exact h3w
  refine ⟨b3Hom E h3, ?_⟩
  rw [← MonoidHom.range_eq_top, range_b3Hom]
  exact closure_b3Gens_eq_top E hU hgen

end CFSG.ClassicalInvolution.Phan.Q3G
