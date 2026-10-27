module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.A3Extend
public import CFSG.ClassicalInvolution.Phan.PhanDn.WeakPhan

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable def thetaD {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) (i j : Fin m) : Su K 2 1 3 →* G :=
  if e : edgeD m i j then F₀.θ i j e
  else if e' : edgeD m j i then (F₀.θ j i e').comp (revSU3 K 2 1).toMonoidHom
  else 1

private theorem thetaD_of_edge {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (e : edgeD m i j) :
    thetaD F₀ i j = F₀.θ i j e := by
  unfold thetaD
  rw [dif_pos e]

private theorem thetaD_of_rev {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (h : ¬ edgeD m i j) (e : edgeD m j i) :
    thetaD F₀ i j = (F₀.θ j i e).comp (revSU3 K 2 1).toMonoidHom := by
  unfold thetaD
  rw [dif_neg h, dif_pos e]

private theorem thetaD_apply_of_edge {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (e : edgeD m i j) (x : Su K 2 1 3) :
    thetaD F₀ i j x = F₀.θ i j e x := by
  rw [thetaD_of_edge F₀ e]

private theorem thetaD_apply_of_rev {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (h : ¬ edgeD m i j) (e : edgeD m j i)
    (x : Su K 2 1 3) :
    thetaD F₀ i j x = F₀.θ j i e (revSU3 K 2 1 x) := by
  rw [thetaD_of_rev F₀ h e]
  rfl

private theorem thetaD_left_of_edge {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (e : edgeD m i j) :
    (thetaD F₀ i j).comp (embSUid (unitaryInvolution K 2 1) 2) = F₀.ι i := by
  rw [thetaD_of_edge F₀ e]
  exact F₀.left i j e

private theorem thetaD_right_of_edge {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (e : edgeD m i j) :
    (thetaD F₀ i j).comp (embSUid (unitaryInvolution K 2 1) 0) = F₀.ι j := by
  rw [thetaD_of_edge F₀ e]
  exact F₀.right i j e

private theorem thetaD_left_of_rev {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (h : ¬ edgeD m i j) (e : edgeD m j i) :
    (thetaD F₀ i j).comp (embSUid (unitaryInvolution K 2 1) 2) = F₀.ι i := by
  rw [thetaD_of_rev F₀ h e, MonoidHom.comp_assoc, revSU3_comp_embSUid_two]
  exact F₀.right j i e

private theorem thetaD_right_of_rev {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m} (h : ¬ edgeD m i j) (e : edgeD m j i) :
    (thetaD F₀ i j).comp (embSUid (unitaryInvolution K 2 1) 0) = F₀.ι j := by
  rw [thetaD_of_rev F₀ h e, MonoidHom.comp_assoc, revSU3_comp_embSUid_zero]
  exact F₀.left j i e

private theorem not_edgeD_of_edgeD {m : ℕ} (hm : 4 ≤ m) {i j : Fin m}
    (e : edgeD m i j) : ¬ edgeD m j i :=
  fun e' => lt_asymm (edgeD_lt hm e') (edgeD_lt hm e)

private theorem edgeD_of_three {m : ℕ} (hm : 4 ≤ m) {i j : Fin m}
    (hij : CFSG.StandardType.ggCoxeterMatrixD m i j = 3) (h : ¬ edgeD m i j) :
    edgeD m j i := by
  rcases (ggCoxeterMatrixD_eq_three_iff hm i j).1 hij with e | e
  · exact absurd e h
  · exact e

private theorem thetaD_left {m : ℕ} {G : Type} [Group G] (hm : 4 ≤ m)
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m}
    (hij : CFSG.StandardType.ggCoxeterMatrixD m i j = 3) :
    (thetaD F₀ i j).comp (embSUid (unitaryInvolution K 2 1) 2) = F₀.ι i := by
  by_cases e : edgeD m i j
  · exact thetaD_left_of_edge F₀ e
  · exact thetaD_left_of_rev F₀ e (edgeD_of_three hm hij e)

private theorem thetaD_right {m : ℕ} {G : Type} [Group G] (hm : 4 ≤ m)
    (F₀ : PhanFamilyD K 2 1 m G) {i j : Fin m}
    (hij : CFSG.StandardType.ggCoxeterMatrixD m i j = 3) :
    (thetaD F₀ i j).comp (embSUid (unitaryInvolution K 2 1) 0) = F₀.ι j := by
  by_cases e : edgeD m i j
  · exact thetaD_right_of_edge F₀ e
  · exact thetaD_right_of_rev F₀ e (edgeD_of_three hm hij e)

private theorem range_revSU3 :
    ((revSU3 K 2 1).toMonoidHom : Su K 2 1 3 →* Su K 2 1 3).range = ⊤ :=
  MonoidHom.range_eq_top.2 (revSU3 K 2 1).surjective

private theorem thetaD_range_of_edge {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {W : Fin m → Fin m → Subgroup G}
    (hW : ∀ i j (e : edgeD m i j), (F₀.θ i j e).range = W i j) {i j : Fin m}
    (e : edgeD m i j) : (thetaD F₀ i j).range = W i j := by
  rw [thetaD_of_edge F₀ e]
  exact hW i j e

private theorem thetaD_range_of_rev {m : ℕ} {G : Type} [Group G]
    (F₀ : PhanFamilyD K 2 1 m G) {W : Fin m → Fin m → Subgroup G}
    (hW : ∀ i j (e : edgeD m i j), (F₀.θ i j e).range = W i j)
    (hsymm : ∀ i j, W j i = W i j) {i j : Fin m}
    (h : ¬ edgeD m i j) (e : edgeD m j i) : (thetaD F₀ i j).range = W i j := by
  rw [thetaD_of_rev F₀ h e, MonoidHom.range_comp, range_revSU3, Subgroup.map_top,
    hW j i e, hsymm j i]

private theorem thetaD_range {m : ℕ} {G : Type} [Group G] (hm : 4 ≤ m)
    (F₀ : PhanFamilyD K 2 1 m G) {W : Fin m → Fin m → Subgroup G}
    (hW : ∀ i j (e : edgeD m i j), (F₀.θ i j e).range = W i j)
    (hsymm : ∀ i j, W j i = W i j) {i j : Fin m}
    (hij : CFSG.StandardType.ggCoxeterMatrixD m i j = 3) :
    (thetaD F₀ i j).range = W i j := by
  by_cases e : edgeD m i j
  · exact thetaD_range_of_edge F₀ hW e
  · exact thetaD_range_of_rev F₀ hW hsymm e (edgeD_of_three hm hij e)

theorem QTwoWeakPhanSystemD.exists_family (hmark : QTwoA3Mark) {m : ℕ} (hm : 4 ≤ m)
    {G : Type} [Group G] {H : Subgroup G} {U : Fin m → Subgroup G}
    {W : Fin m → Fin m → Subgroup G} (h : QTwoWeakPhanSystemD K m H U W) :
    ∃ F : QTwoPhanFamily K (CFSG.StandardType.ggCoxeterMatrixD m) G,
      (∀ i, (F.ι i).range = U i) ∧
      ∀ i j, CFSG.StandardType.ggCoxeterMatrixD m i j = 3 → (F.θ i j).range = W i j := by
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [h.card_four]
    norm_num
  have hsymm : ∀ i j : Fin m, CFSG.StandardType.ggCoxeterMatrixD m i j =
      CFSG.StandardType.ggCoxeterMatrixD m j i :=
    fun i j => (CFSG.StandardType.ggCoxeterMatrixD m).symmetric i j
  have hcomm : ∀ i j : Fin m, i ≠ j → ¬ edgeD m i j → ¬ edgeD m j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij h1 h2
    exact h.comm i j ((ggCoxeterMatrixD_eq_two_iff hm i j).2 ⟨hij, h1, h2⟩)
  have hpair : ∀ i j : Fin m, edgeD m i j →
      UnitaryBlockStandardPair K 2 1 (W i j) (U i) (U j) := by
    intro i j hj
    exact h.pair i j ((ggCoxeterMatrixD_eq_three_iff hm i j).2 (Or.inl hj))
  obtain ⟨F₀, hι_range, -, -, hθ_range⟩ :=
    CFSG.ClassicalInvolution.PhanDn.exists_family (p := 2) (f := 1) hm hK U W hcomm hpair
  have hmemι : ∀ (i : Fin m) (a : Su K 2 1 2), F₀.ι i a ∈ U i := by
    intro i a
    rw [← hι_range i]
    exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hmemθ : ∀ (i j : Fin m) (e : edgeD m i j) (b : Su K 2 1 3),
      F₀.θ i j e b ∈ W i j := by
    intro i j e b
    rw [← hθ_range i j e]
    exact MonoidHom.mem_range.mpr ⟨b, rfl⟩
  have hrev : (revSU3 K 2 1).toMonoidHom.comp (revSU3 K 2 1).toMonoidHom =
      MonoidHom.id (Su K 2 1 3) := by
    refine MonoidHom.ext fun x => ?_
    exact revSU3_revSU3 K 2 1 hK x
  let F : QTwoPhanFamily K (CFSG.StandardType.ggCoxeterMatrixD m) G :=
    { ι := F₀.ι
      θ := fun i j => thetaD F₀ i j
      left := fun i j hij => thetaD_left hm F₀ hij
      right := fun i j hij => thetaD_right hm F₀ hij
      rev := fun i j hij => by
        by_cases e : edgeD m i j
        · rw [thetaD_of_edge F₀ e, thetaD_of_rev F₀ (not_edgeD_of_edgeD hm e) e]
        · have e' := edgeD_of_three hm hij e
          rw [thetaD_of_rev F₀ e e', thetaD_of_edge F₀ e', MonoidHom.comp_assoc, hrev,
            MonoidHom.comp_id]
      comm := fun i j hij a b => h.comm i j hij (F₀.ι i a) (hmemι i a) (F₀.ι j b)
        (hmemι j b)
      a3 := fun i j k hij hjk hik => by
        obtain ⟨κ, hκ, hκ012, hκ123, hκU1, hκU2, hκU3⟩ :=
          hmark K h.card_four (U i) (U j) (U k) (W i j) (W j k)
            (h.pair i j hij) (h.pair j k hjk) (h.comm i k hik)
            (h.adjA3 i j k hij hjk hik)
        have hbij : (B12 K 2 1).map (thetaD F₀ i j) =
            (B12 K 2 1).map (κ.comp (blk012 K)) := by
          rw [hκU1,
            show B12 K 2 1 = (embSUid (unitaryInvolution K 2 1) 2).range from rfl,
            MonoidHom.map_range, thetaD_left hm F₀ hij, hι_range i]
        have hcij : (B23 K 2 1).map (thetaD F₀ i j) =
            (B23 K 2 1).map (κ.comp (blk012 K)) := by
          rw [hκU2,
            show B23 K 2 1 = (embSUid (unitaryInvolution K 2 1) 0).range from rfl,
            MonoidHom.map_range, thetaD_right hm F₀ hij, hι_range j]
        have hbjk : (B23 K 2 1).map (thetaD F₀ j k) =
            (B23 K 2 1).map (κ.comp (blk123 K)) := by
          rw [hκU3,
            show B23 K 2 1 = (embSUid (unitaryInvolution K 2 1) 0).range from rfl,
            MonoidHom.map_range, thetaD_right hm F₀ hjk, hι_range k]
        obtain ⟨κ', h1, h2⟩ :=
          qTwoA3_extend h.card_four hκ
            (by rw [thetaD_range hm F₀ hθ_range (fun i j => h.symm j i) hij, hκ012])
            hbij hcij
            (by rw [thetaD_range hm F₀ hθ_range (fun i j => h.symm j i) hjk, hκ123])
            hbjk
            (by rw [thetaD_right hm F₀ hij, thetaD_left hm F₀ hjk])
        exact ⟨κ', h1, h2⟩
      farNodeEdge := fun i j k hjk hij hik a b => by
        by_cases e : edgeD m j k
        · rw [thetaD_apply_of_edge F₀ e]
          exact h.farNodeEdge i j k hjk hij hik (F₀.ι i a) (hmemι i a)
            (F₀.θ j k e b) (hmemθ j k e b)
        · have e' := edgeD_of_three hm hjk e
          rw [thetaD_apply_of_rev F₀ e e']
          exact h.farNodeEdge i k j ((hsymm j k) ▸ hjk) hik hij (F₀.ι i a) (hmemι i a)
            (F₀.θ k j e' (revSU3 K 2 1 b)) (hmemθ k j e' (revSU3 K 2 1 b))
      farEdgeEdge := fun i k j l hik3 hjl3 hij2 hil2 hkj2 hkl2 a b => by
        by_cases e1 : edgeD m i k
        · by_cases e2 : edgeD m j l
          · rw [thetaD_apply_of_edge F₀ e1, thetaD_apply_of_edge F₀ e2]
            exact h.farEdgeEdge i k j l hik3 hjl3 hij2 hil2 hkj2 hkl2
              (F₀.θ i k e1 a) (hmemθ i k e1 a) (F₀.θ j l e2 b) (hmemθ j l e2 b)
          · have e2' := edgeD_of_three hm hjl3 e2
            rw [thetaD_apply_of_edge F₀ e1, thetaD_apply_of_rev F₀ e2 e2']
            exact h.farEdgeEdge i k l j hik3 ((hsymm j l) ▸ hjl3) hil2 hij2 hkl2 hkj2
              (F₀.θ i k e1 a) (hmemθ i k e1 a)
              (F₀.θ l j e2' (revSU3 K 2 1 b)) (hmemθ l j e2' (revSU3 K 2 1 b))
        · have e1' := edgeD_of_three hm hik3 e1
          by_cases e2 : edgeD m j l
          · rw [thetaD_apply_of_rev F₀ e1 e1', thetaD_apply_of_edge F₀ e2]
            exact h.farEdgeEdge k i j l ((hsymm i k) ▸ hik3) hjl3 hkj2 hkl2 hij2 hil2
              (F₀.θ k i e1' (revSU3 K 2 1 a)) (hmemθ k i e1' (revSU3 K 2 1 a))
              (F₀.θ j l e2 b) (hmemθ j l e2 b)
          · have e2' := edgeD_of_three hm hjl3 e2
            rw [thetaD_apply_of_rev F₀ e1 e1', thetaD_apply_of_rev F₀ e2 e2']
            exact h.farEdgeEdge k i l j ((hsymm i k) ▸ hik3) ((hsymm j l) ▸ hjl3)
              hkl2 hkj2 hil2 hij2
              (F₀.θ k i e1' (revSU3 K 2 1 a)) (hmemθ k i e1' (revSU3 K 2 1 a))
              (F₀.θ l j e2' (revSU3 K 2 1 b)) (hmemθ l j e2' (revSU3 K 2 1 b)) }
  refine ⟨F, hι_range, ?_⟩
  intro i j hij
  exact thetaD_range hm F₀ hθ_range (fun i j => h.symm j i) hij

end CFSG.ClassicalInvolution.PhanDn.QTwo

end
