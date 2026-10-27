module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.NodeBound

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

@[expose] def centerU : Fin 8 → List (Fin 4) :=
  ![[], [0, 2, 3, 2, 0], [1, 0, 2, 1, 0], [1, 2, 3, 2, 1], [0, 2, 3, 1, 2, 0], [1, 2, 3, 0, 2, 1],
    [3, 2, 1, 0, 2, 3], [3, 2, 1, 0, 2, 3, 1, 0, 2, 1, 0]]

@[expose] def vCenter : Fin Tag.D4.rank → ℤ := (![2, 2, 4, 2] : Fin 4 → ℤ)

@[expose] def centerUL : List (List (Fin 4)) := List.ofFn centerU

@[expose] def centerW : List (List (Fin 4)) :=
  [[], [3], [1], [0], [2], [0, 2], [3, 1], [2, 3], [2, 1], [1, 2], [3, 0], [3, 2], [1, 0], [2, 0],
    [0, 2, 0], [1, 0, 2], [3, 0, 2], [1, 2, 1], [2, 3, 2], [3, 1, 2], [3, 1, 0], [3, 1, 0, 2],
    [2, 3, 1, 0], [2, 3, 1, 0, 2]]

@[expose] def centerX : List (List ℤ) :=
  [[-2, 0, 1, 0], [-1, -1, 0, 1], [-1, -1, 1, -1], [-1, -1, 1, 1], [-1, -1, 2, -1], [-1, 1, -1, 1],
    [-1, 1, 0, -1], [-1, 1, 0, 1], [-1, 1, 1, -1], [0, -2, 1, 0], [0, 0, -1, 0], [0, 0, -1, 2],
    [0, 0, 1, -2], [0, 0, 1, 0], [0, 2, -1, 0], [1, -1, -1, 1], [1, -1, 0, -1], [1, -1, 0, 1],
    [1, -1, 1, -1], [1, 1, -2, 1], [1, 1, -1, -1], [1, 1, -1, 1], [1, 1, 0, -1], [2, 0, -1, 0]]

@[expose] def centerV : List ℤ := [2, 2, 4, 2]

private theorem wordProd_smul_D4
    (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem .D4).wordProd l • v = l.foldr (reflect .D4) v :=
  wordProd_smul' (τ := .D4) l v

private theorem ofFn_foldr_reflectG_D4 (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    List.ofFn (l.foldr (reflect .D4) v) = l.foldr (reflectLG .D4) (List.ofFn v) :=
  ofFn_foldr_reflectG (τ := .D4) l v

private theorem centerU_foldr_single : ∀ j : Fin 8,
    (centerU j).foldr (reflectLG .D4) (List.ofFn (Pi.single (2 : Fin 4) 1 :
      Fin Tag.D4.rank → ℤ)) = List.ofFn (Pi.single (2 : Fin 4) 1 : Fin Tag.D4.rank → ℤ) := by
  decide +kernel

private theorem centerU_distinct : ∀ j j' : Fin 8, j ≠ j' →
    (centerU j).foldr (reflectLG .D4) (List.ofFn (vCenter : Fin Tag.D4.rank → ℤ)) ≠
      (centerU j').foldr (reflectLG .D4) (List.ofFn (vCenter : Fin Tag.D4.rank → ℤ)) := by
  decide +kernel

theorem centerU_smul (j : Fin 8) :
    (coxeterSystem .D4).wordProd (centerU j) • (Pi.single (2 : Fin 4) 1 : Fin Tag.D4.rank → ℤ) =
      Pi.single (2 : Fin 4) 1 := by
  apply List.ofFn_injective
  rw [wordProd_smul_D4, ofFn_foldr_reflectG_D4]
  exact centerU_foldr_single j

theorem centerU_smul_injective
    (j j' : Fin 8) (h : j ≠ j') :
    (coxeterSystem .D4).wordProd (centerU j) • vCenter ≠
      (coxeterSystem .D4).wordProd (centerU j') • vCenter := by
  intro he
  have h1 : (centerU j).foldr (reflect .D4) vCenter =
      (centerU j').foldr (reflect .D4) vCenter := by
    simpa only [wordProd_smul_D4] using he
  have h2 := congrArg List.ofFn h1
  rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
  exact centerU_distinct j j' h h2

theorem centerTab_hv0len : centerV.length = Tag.D4.rank := by decide

theorem centerTab_hv0 : ∀ j : Fin 4, j ≠ (2 : Fin 4) →
    reflectLG .D4 j centerV = centerV := by
  decide +kernel

theorem centerTab_hU1 : ∀ j : Fin 8,
    (centerUL.getD j []).foldr (refELG .D4) (List.ofFn (alphaF .D4 (2 : Fin 4))) =
      List.ofFn (alphaF .D4 (2 : Fin 4)) := by
  decide +kernel

theorem centerTab_hU2 : ∀ j : Fin 8,
    (centerUL.getD j []).foldr (reflectLG .D4) (List.ofFn (Pi.single (2 : Fin 4) 1 :
      Fin Tag.D4.rank → ℤ)) = List.ofFn (Pi.single (2 : Fin 4) 1 : Fin Tag.D4.rank → ℤ) := by
  decide +kernel

theorem centerTab_hdist : ∀ j j' : Fin 8, j ≠ j' →
    (centerUL.getD j []).foldr (reflectLG .D4) centerV ≠
      (centerUL.getD j' []).foldr (reflectLG .D4) centerV := by
  decide +kernel

theorem centerTab_hβ : ∀ i i' : Fin 24, i ≠ i' →
    1 ≤ contentL (subL ((centerW.getD i []).foldr (refELG .D4)
      (List.ofFn (alphaF .D4 (2 : Fin 4))))
      ((centerW.getD i' []).foldr (refELG .D4) (List.ofFn (alphaF .D4 (2 : Fin 4))))) ∧
    contentL (subL ((centerW.getD i []).foldr (refELG .D4)
      (List.ofFn (alphaF .D4 (2 : Fin 4))))
      ((centerW.getD i' []).foldr (refELG .D4) (List.ofFn (alphaF .D4 (2 : Fin 4))))) ≤ 2 := by
  decide +kernel

theorem centerTab_hbdβ : ∀ i : Fin 24,
    ∀ c ∈ (centerW.getD i []).foldr (refELG .D4) (List.ofFn (alphaF .D4 (2 : Fin 4))), |c| ≤ 2 := by
  decide +kernel

theorem centerTab_hY : ∀ j j' : Fin 8, j ≠ j' →
    (centerUL.getD j []).foldr (refELG .D4) (List.ofFn (omegaF .D4 (2 : Fin 4))) ≠
      (centerUL.getD j' []).foldr (refELG .D4) (List.ofFn (omegaF .D4 (2 : Fin 4))) := by
  decide +kernel

theorem centerTab_hbdX : ∀ (i : Fin 24) (j : Fin 8),
    ∀ c ∈ (centerW.getD i []).foldr (refELG .D4)
      ((centerUL.getD j []).foldr (refELG .D4) (List.ofFn (omegaF .D4 (2 : Fin 4)))), |c| ≤ 2 := by
  decide +kernel

theorem centerTab_hmem : ∀ (i : Fin 24) (j : Fin 8),
    (centerW.getD i []).foldr (refELG .D4)
      ((centerUL.getD j []).foldr (refELG .D4) (List.ofFn (omegaF .D4 (2 : Fin 4)))) ∈ centerX := by
  decide +kernel

theorem centerTab_hxorb : ∀ x ∈ centerX, ∀ y ∈ centerX, x ≠ y →
    1 ≤ contentL (subL x y) ∧ contentL (subL x y) ≤ 2 := by
  decide +kernel

@[expose] def centerTab : NodeTab .D4 (2 : Fin 4) where
  A := 24
  B := 8
  wTab := centerW
  uTab := centerUL
  v0 := centerV
  xorb := centerX
  hv0len := centerTab_hv0len
  hv0 := centerTab_hv0
  hU1 := centerTab_hU1
  hU2 := centerTab_hU2
  hdist := centerTab_hdist
  hβ := centerTab_hβ
  hbdβ := centerTab_hbdβ
  hY := centerTab_hY
  hbdX := centerTab_hbdX
  hmem := centerTab_hmem
  hxorb := centerTab_hxorb

section Chev

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
  {k V : Type} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V] [Module k V]
  [Module.Finite k V] {ρ : Representation k (adjointGroup .D4 K) V} {y : V}
  {χ : adjointGroup .D4 K → k} {J : Finset (Fin Tag.D4.rank)}

private theorem reflect_vCenter : ∀ j : Fin Tag.D4.rank, j ≠ (2 : Fin 4) →
    reflect .D4 j vCenter = vCenter := by
  intro j hj
  apply List.ofFn_injective
  rw [ofFn_reflectG, show List.ofFn (vCenter : Fin Tag.D4.rank → ℤ) = centerV from rfl]
  exact centerTab_hv0 j hj

theorem linearIndependent_centerU (hρ : IsSimpleRep ρ) (ht : IsChevType .D4 K 2 hw ρ y χ J)
    (hJ : (2 : Fin 4) ∉ J) :
    LinearIndependent k
      (fun j : Fin 8 => ρ (nWC .D4 K ((coxeterSystem .D4).wordProd (centerU j))) y) := by
  refine linearIndependent_translates_of_isChevType (hw := hw) hρ ht hJ (v₀ := vCenter)
    (fun j hj => reflect_vCenter j hj)
    (fun j : Fin 8 => (coxeterSystem .D4).wordProd (centerU j)) ?_
  intro i j hij
  exact centerU_smul_injective i j hij

theorem copies_center_finrank {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hρ : IsSimpleRep ρ) (ht : IsChevType .D4 K 2 hw ρ y χ J) (hJ : (2 : Fin 4) ∉ J)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC .D4 K (2 : Fin 4) z) ^ (2 ^ g) = χ (dC .D4 K (2 : Fin 4) z)) :
    8 * 2 ^ (n / g) ≤ Module.finrank k V := by
  have h1 := node_copies (hw := hw) centerTab hρ ht hJ
  have h2 := two_pow_le_finrank_orbitSpan hn hK hρ ht hJ hg hgn hper
  calc 8 * 2 ^ (n / g)
      ≤ 8 * Module.finrank k (orbitSpan (ρ.comp (rankOne .D4 K (2 : Fin 4))) y) :=
        Nat.mul_le_mul_left _ h2
    _ ≤ Module.finrank k V := h1

theorem node_center_finrank {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hρ : IsSimpleRep ρ) (ht : IsChevType .D4 K 2 hw ρ y χ J)
    (hJ : ∀ s' : Fin Tag.D4.rank, s' ≠ (2 : Fin 4) → s' ∈ J) (hs : (2 : Fin 4) ∉ J)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (h2 : 2 ≤ n / g)
    (hper : ∀ z : Kˣ, χ (dC .D4 K (2 : Fin 4) z) ^ (2 ^ g) = χ (dC .D4 K (2 : Fin 4) z)) :
    192 ≤ Module.finrank k V := by
  obtain ⟨J', hJ', hε, hJ0, hdim, hvec⟩ := string_wt_vec (hw := hw) hK hρ ht hJ
  have hne := string_nonempty hn hK ht hs hε hJ0
  have hper' := periodic_dvd hK hε hper
  have hcardt := card_ge_of_periodic hg hgn hJ' hne hper'
  have ha0 : 0 < ∑ i ∈ J', 2 ^ i := by
    obtain ⟨b, hb⟩ := id hne
    have hcase : 2 ≤ J'.card ∨ J'.card = 1 := by
      have := hne.card_pos
      omega
    rcases hcase with hc | hc
    · exact lt_of_le_of_lt (Nat.zero_le _) (pair_le_sum hc hb)
    · obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 hc
      simp
  have hcj : 2 ≤ J'.card := by omega
  have hbig := node_dim_big (hw := hw) centerTab hn hK hρ ht hJ hs hJ' hcj
    (fun _ => Or.inl (gcd_ge_three hg hgn h2 hper' ha0)) hvec
  have hAB : centerTab.A * centerTab.B = 192 := rfl
  rw [hAB] at hbig
  exact hbig

end Chev

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
