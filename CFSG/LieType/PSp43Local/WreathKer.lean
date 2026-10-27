module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LieType.PSp43Local

open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

@[expose] def wProd : W3 →* M3 where
  toFun w := ∏ i, w.left i
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, (a * b).left i) = (∏ i, a.left i) * (∏ i, b.left i)
    rw [RegularWreathProduct.mul_left]
    simp only [Pi.mul_apply, Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft a.right⁻¹)
      (fun i => b.left (a.right⁻¹ * i)) b.left (fun _ => rfl)

private theorem M3_eq_one_or (s : M3) : s = 1 ∨ s = Multiplicative.ofAdd 1 ∨
    s = Multiplicative.ofAdd 2 := by
  revert s
  decide

private theorem prod_univ_M3 (f : M3 → M3) :
    ∏ x, f x = f 1 * f (Multiplicative.ofAdd 1) * f (Multiplicative.ofAdd 2) := by
  rw [show (Finset.univ : Finset M3) =
    insert 1 (insert (Multiplicative.ofAdd 1) {Multiplicative.ofAdd 2}) by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp [mul_assoc]

private theorem pow_three_left (w : W3) (x : M3) :
    (w ^ 3).left x =
      w.left x * w.left (w.right⁻¹ * x) * w.left (w.right⁻¹ * (w.right⁻¹ * x)) := by
  rw [pow_succ, pow_succ]
  simp [RegularWreathProduct.mul_left, Pi.mul_apply, mul_assoc]

theorem mem_wBase_or_wProd_eq_one {w : W3} (hw : w ^ 3 = 1) :
    w ∈ wBase ∨ wProd w = 1 := by
  by_cases hs : w.right = 1
  · exact Or.inl (mem_wBase.mpr hs)
  · right
    have h1 : w.left 1 * w.left (w.right⁻¹ * (1 : M3)) *
        w.left (w.right⁻¹ * (w.right⁻¹ * 1)) = 1 := by
      have h := congrFun (congrArg RegularWreathProduct.left hw) 1
      rw [pow_three_left w 1] at h
      simpa using h
    have hcases := M3_eq_one_or w.right
    rw [wProd]
    show ∏ x, w.left x = 1
    rw [prod_univ_M3]
    rcases hcases with h | h | h
    · exact absurd h hs
    · rw [h] at h1
      have hinv : (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ = Multiplicative.ofAdd 2 := by
        decide
      have hsq : (Multiplicative.ofAdd (2 : ZMod 3)) *
          Multiplicative.ofAdd 2 = Multiplicative.ofAdd 1 := by decide
      simp only [hinv, mul_one, hsq] at h1 ⊢
      rw [mul_assoc, mul_comm (w.left (Multiplicative.ofAdd 1))
        (w.left (Multiplicative.ofAdd 2)), ← mul_assoc]
      exact h1
    · rw [h] at h1
      have hinv : (Multiplicative.ofAdd (2 : ZMod 3))⁻¹ = Multiplicative.ofAdd 1 := by
        decide
      have hsq : (Multiplicative.ofAdd (1 : ZMod 3)) *
          Multiplicative.ofAdd 1 = Multiplicative.ofAdd 2 := by decide
      simp only [hinv, mul_one, hsq] at h1 ⊢
      exact h1

private theorem wProd_surjective : Function.Surjective wProd := by
  intro t
  refine ⟨⟨fun x => if x = 1 then t else 1, 1⟩, ?_⟩
  show ∏ x : M3, (if x = 1 then t else 1) = t
  rw [Finset.prod_ite_eq']
  simp

theorem card_ker_wProd : Nat.card wProd.ker = 27 := by
  have h := Subgroup.card_ker_mul_card_of_surjective (f := wProd) wProd_surjective
  rw [card_W3, card_M3] at h
  omega

theorem eq_ker_wProd {D : Subgroup W3} (hD : Nat.card D = 27)
    (h3 : ∀ x ∈ D, x ^ 3 = 1) (hne : D ≠ wBase) : D = wProd.ker := by
  have hsub : (D : Set W3) ⊆ (wBase : Set W3) ∪ (wProd.ker : Set W3) := by
    intro x hx
    rcases mem_wBase_or_wProd_eq_one (h3 x hx) with h | h
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ (MonoidHom.mem_ker.mpr h)
  rcases (SubgroupClass.subset_union.mp hsub) with h | h
  · exact absurd (Subgroup.eq_of_le_of_card_ge h (by rw [card_wBase, hD])) hne
  · exact Subgroup.eq_of_le_of_card_ge h (by rw [card_ker_wProd, hD])

section Transport

variable {X : Type*} [Group X] {P : Subgroup X}

theorem mem_of_pow_three_eq_one_of_not_mem_baseIn (e : ↥P ≃* W3) {D : Subgroup X}
    (hDP : D ≤ P) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hne : D ≠ baseIn e) {g : X} (hgP : g ∈ P) (hg3 : g ^ 3 = 1)
    (hg : g ∉ baseIn e) : g ∈ D := by
  have hD' : Nat.card ((D.subgroupOf P).map e.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv]
    exact hD
  have h3' : ∀ x ∈ (D.subgroupOf P).map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    have hdX : (d : X) ^ 3 = 1 := h3 d hd
    have hd3 : d ^ 3 = 1 := Subtype.ext (by simpa using hdX)
    rw [← map_pow, hd3, map_one]
  have hne' : (D.subgroupOf P).map e.toMonoidHom ≠ wBase := by
    intro h
    apply hne
    have hsub : D.subgroupOf P = wBase.map e.symm.toMonoidHom := by
      rw [← h, Subgroup.map_map]
      have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rw [baseIn, ← hsub, Subgroup.map_subgroupOf_eq_of_le hDP]
  have hD'ker : (D.subgroupOf P).map e.toMonoidHom = wProd.ker :=
    eq_ker_wProd hD' h3' hne'
  have hg'3 : (e ⟨g, hgP⟩) ^ 3 = 1 := by
    have h3P : (⟨g, hgP⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [← map_pow, h3P, map_one]
  have hg'b : e ⟨g, hgP⟩ ∉ wBase := by
    intro hb
    apply hg
    have hmap : e.symm (e ⟨g, hgP⟩) ∈ wBase.map e.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem e.symm.toMonoidHom hb
    have hmap' : (⟨g, hgP⟩ : ↥P) ∈ wBase.map e.symm.toMonoidHom := by
      simpa using hmap
    change g ∈ (wBase.map e.symm.toMonoidHom).map P.subtype
    exact Subgroup.mem_map_of_mem P.subtype hmap'
  have hg'ker : e ⟨g, hgP⟩ ∈ wProd.ker := by
    rcases mem_wBase_or_wProd_eq_one hg'3 with h | h
    · exact absurd h hg'b
    · exact MonoidHom.mem_ker.mpr h
  have hmem : e ⟨g, hgP⟩ ∈ (D.subgroupOf P).map e.toMonoidHom := hD'ker ▸ hg'ker
  obtain ⟨d, hd, hde⟩ := Subgroup.mem_map.mp hmem
  have hdg : d = ⟨g, hgP⟩ := e.injective hde
  have : (d : X) ∈ D := hd
  rwa [hdg] at this

end Transport

end CFSG.LieType.PSp43Local
