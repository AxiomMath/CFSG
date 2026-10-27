module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NormFormType
public import CFSG.ClassicalInvolution.Phan.PhanDn.BaseChange
public import CFSG.RankThree.PartOne.KC.OrthogonalHypCoordinates
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.LieType.Universal.SpinOmega.Range

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.ExtensionDescent

open QuadraticMap CFSG.ClassicalInvolution.PhanDn CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.RankThree.OrthogonalInvolutions

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K]
  {σ : K ≃+* K} [CharP K 2] {n : ℕ}

private def fixedPair (E : QuadExt F K σ)
    (h : (Qn E n).IsometryEquiv (quadPlus n F)) (i : Fin n) : HypPair (quadPlus n K) where
  e := jEmb E n (h.symm (Pi.single (Sum.inl i) 1))
  f := jEmb E n (h.symm (Pi.single (Sum.inr i) 1))
  Q_e := by
    rw [quadPlus_jEmb, h.symm.map_app]
    simp [quadPlus_apply]
  Q_f := by
    rw [quadPlus_jEmb, h.symm.map_app]
    simp [quadPlus_apply]
  polar_ef := by
    rw [polar_jEmb, h.symm.polar_apply, polar_quadPlus_single_inr]
    simp

omit [Finite K] [CharP K 2] in
private theorem fixedPair_orth (E : QuadExt F K σ)
    (h : (Qn E n).IsometryEquiv (quadPlus n F)) {i j : Fin n} (hij : i ≠ j) :
    (fixedPair E h i).Orth (fixedPair E h j) := by
  constructor
  · dsimp only [fixedPair]
    rw [polar_jEmb, h.symm.polar_apply, polar_quadPlus_single_inl]
    simp
  · dsimp only [fixedPair]
    rw [polar_jEmb, h.symm.polar_apply, polar_quadPlus_single_inr]
    simp [hij.symm]
  · dsimp only [fixedPair]
    rw [polar_jEmb, h.symm.polar_apply, polar_quadPlus_single_inl]
    simp [hij.symm]
  · dsimp only [fixedPair]
    rw [polar_jEmb, h.symm.polar_apply, polar_quadPlus_single_inr]
    simp


omit [Finite K] [CharP K 2] in
private theorem fixedPair_perp_eq_bot (E : QuadExt F K σ)
    (h : (Qn E n).IsometryEquiv (quadPlus n F)) : pairsPerp (fixedPair E h) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have hd : Module.finrank K (pairsPerp (fixedPair E h)) + 2 * n =
      Module.finrank K (Fin n ⊕ Fin n → K) :=
    finrank_pairsPerp (fun i j hij => fixedPair_orth E h hij)
      (nondegenerate_polarBilin_quadPlus n K)
  have hdim : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by simp; omega
  rw [hdim] at hd
  omega

omit [Finite K] [CharP K 2] in
private theorem splitCoord_inl {P : Fin n → HypPair (quadPlus n K)}
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (hU : pairsPerp P = ⊥)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    hypCoordSplitIsometry hP hU v (Sum.inl i) = polar (quadPlus n K) v (P i).f := by
  change (hypCoordEquiv hP v).1 (Sum.inl i) = _
  have hc := polar_hypCoordSymm_f hP (hypCoordEquiv hP v).1 (hypCoordEquiv hP v).2 i
  have hv : hypCoordSymm P (hypCoordEquiv hP v) = v := (hypCoordEquiv hP).symm_apply_apply v
  rw [hv] at hc
  exact hc.symm

omit [Finite K] [CharP K 2] in
private theorem splitCoord_inr {P : Fin n → HypPair (quadPlus n K)}
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (hU : pairsPerp P = ⊥)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    hypCoordSplitIsometry hP hU v (Sum.inr i) = polar (quadPlus n K) v (P i).e := by
  change (hypCoordEquiv hP v).1 (Sum.inr i) = _
  have hc := polar_hypCoordSymm_e hP (hypCoordEquiv hP v).1 (hypCoordEquiv hP v).2 i
  have hv : hypCoordSymm P (hypCoordEquiv hP v) = v := (hypCoordEquiv hP).symm_apply_apply v
  rw [hv] at hc
  exact hc.symm

omit [Finite K] [CharP K 2] in
theorem exists_flipLang_isometry_of_norm_isometry (E : QuadExt F K σ)
    (h : (Qn E n).IsometryEquiv (quadPlus n F)) :
    ∃ g : (quadPlus n K).IsometryEquiv (quadPlus n K),
      ∀ v : Fin n ⊕ Fin n → K, g (dFlip σ v) = fun i => σ (g v i) := by
  have hP : ∀ i j, i ≠ j → (fixedPair E h i).Orth (fixedPair E h j) :=
    fun i j hij => fixedPair_orth E h hij
  have hU := fixedPair_perp_eq_bot E h
  refine ⟨hypCoordSplitIsometry hP hU, ?_⟩
  intro v
  ext i
  cases i with
  | inl i =>
      simp only [splitCoord_inl]
      have hf : dFlip σ (fixedPair E h i).f = (fixedPair E h i).f :=
        dFlip_jEmb E n _
      nth_rw 1 [← hf]
      exact polar_dFlip v _
  | inr i =>
      simp only [splitCoord_inr]
      have he : dFlip σ (fixedPair E h i).e = (fixedPair E h i).e :=
        dFlip_jEmb E n _
      nth_rw 1 [← he]
      exact polar_dFlip v _

theorem exists_flipLang_isometry (E : QuadExt F K σ) (hn : Even n) :
    ∃ g : (quadPlus n K).IsometryEquiv (quadPlus n K),
      ∀ v : Fin n ⊕ Fin n → K, g (dFlip σ v) = fun i => σ (g v i) := by
  obtain ⟨h⟩ := nonempty_isometryEquiv_quadPlus E hn
  exact exists_flipLang_isometry_of_norm_isometry E h


omit [Finite K] [CharP K 2] in
private theorem fieldMap_polar (σ : K ≃+* K) (u v : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (fun i => σ (u i)) (fun i => σ (v i)) =
      σ (polar (quadPlus n K) u v) := by
  rw [polar_quadPlus, polar_quadPlus, map_sum]
  simp only [map_add, map_mul]

omit [Finite K] [CharP K 2] in
private theorem reflect_fieldMap (hn : 0 < n) (σ : K ≃+* K)
    (v : Fin n ⊕ Fin n → K) :
    reflect (quadPlus n K) ((plusPair (K := K) ⟨0, hn⟩).e + (plusPair (K := K) ⟨0, hn⟩).f)
        (fun i => σ (v i)) =
      fun i => σ (reflect (quadPlus n K)
        ((plusPair (K := K) ⟨0, hn⟩).e + (plusPair (K := K) ⟨0, hn⟩).f) v i) := by
  let a : Fin n ⊕ Fin n → K :=
    (plusPair (K := K) ⟨0, hn⟩).e + (plusPair (K := K) ⟨0, hn⟩).f
  have ha : quadPlus n K a = 1 := by
    dsimp only [a]
    rw [QuadraticMap.map_add (quadPlus n K), (plusPair (K := K) ⟨0, hn⟩).Q_e,
      (plusPair (K := K) ⟨0, hn⟩).Q_f, (plusPair (K := K) ⟨0, hn⟩).polar_ef]
    simp
  have hfa : (fun i => σ (a i)) = a := by
    ext i
    cases i <;> simp [a, plusPair, Pi.single_apply]
  have hp : polar (quadPlus n K) a (fun i => σ (v i)) =
      σ (polar (quadPlus n K) a v) := by
    nth_rw 1 [← hfa]
    exact fieldMap_polar σ a v
  have hane : quadPlus n K a ≠ 0 := by rw [ha]; exact one_ne_zero
  change reflect (quadPlus n K) a _ = _
  ext i
  rw [reflect_apply hane, reflect_apply hane]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, ha,
    div_one, hp, congrFun hfa i]


theorem exists_elementary_flipLang (E : QuadExt F K σ) (hn : Even n) (hn3 : 3 ≤ n) :
    ∃ g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K),
      g ∈ elementaryGroup (quadPlus n K) ∧
      ∀ v, g (dFlip σ v) = fun i => σ (g v i) := by
  obtain ⟨g, hg⟩ := exists_flipLang_isometry E hn
  let Q := quadPlus n K
  have hQ := nondegenerate_polarBilin_quadPlus n K
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let go : O := ⟨g.toLinearEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr g.map_app⟩
  let D := dicksonHom Q hQ
  have htoE : ∀ t : O, D t = 1 → (t : (Fin n ⊕ Fin n → K) ≃ₗ[K] _) ∈ elementaryGroup Q := by
    intro t ht
    apply CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le hQ
      (by simp [Module.finrank_fintype_fun_eq_card]; omega)
    have hk : t ∈ D.ker := ht
    rw [dicksonHom_ker] at hk
    exact Subgroup.mem_subgroupOf.mp hk
  by_cases hgo : D go = 1
  · exact ⟨go, htoE go hgo, hg⟩
  · let a : Fin n ⊕ Fin n → K :=
      (plusPair (K := K) ⟨0, by omega⟩).e + (plusPair (K := K) ⟨0, by omega⟩).f
    have ha : Q a = 1 := by
      dsimp only [Q, a]
      rw [QuadraticMap.map_add (quadPlus n K), (plusPair (K := K) ⟨0, by omega⟩).Q_e,
        (plusPair (K := K) ⟨0, by omega⟩).Q_f, (plusPair (K := K) ⟨0, by omega⟩).polar_ef]
      simp
    let r : O := ⟨reflect Q a, reflect_mem_orthogonalGroup Q a⟩
    have hr : D r = Multiplicative.ofAdd (1 : ZMod 2) := dicksonHom_reflect hQ (by rw [ha]; exact one_ne_zero)
    have hgo1 : D go = Multiplicative.ofAdd (1 : ZMod 2) := by
      have hcases : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by
        decide +kernel
      exact (hcases (D go)).resolve_left hgo
    have hd : D (r * go) = 1 := by
      rw [map_mul, hr, hgo1]
      decide +kernel
    refine ⟨r * go, htoE (r * go) hd, ?_⟩
    intro v
    change reflect Q a (g (dFlip σ v)) = _
    rw [hg v]
    exact reflect_fieldMap (by omega) σ (g v)

theorem exists_spin_flipLang (E : QuadExt F K σ) (hn : Even n) (hn3 : 3 ≤ n) :
    ∃ s : spinGroup (quadPlus n K), ∀ v : Fin n ⊕ Fin n → K,
      spinAction (quadPlus n K) s (dFlip σ v) = fun i => σ (spinAction (quadPlus n K) s v i) := by
  obtain ⟨g, hg, hflip⟩ := exists_elementary_flipLang E hn hn3
  rw [← range_spinAction_quadPlus hn3] at hg
  obtain ⟨s, hs⟩ := hg
  exact ⟨s, by simpa only [hs] using hflip⟩

end CFSG.ClassicalGroups.Orthogonal.ExtensionDescent
