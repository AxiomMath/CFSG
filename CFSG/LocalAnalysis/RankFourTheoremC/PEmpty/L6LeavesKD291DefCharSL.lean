module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharLev
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExDef
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

section SL

variable {n : ℕ} {K : Type} [Field K]

@[expose] def finPos (n : ℕ) : Fin n → ℕ := fun i => i

@[expose] noncomputable def slElem (n : ℕ) (K : Type) [Field K] (i j : Fin n) (hij : i ≠ j)
    (c : K) : ↥(StatedSL n K) :=
  specialLinearGroupEquivStatedSL n K
    ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

theorem matrixHom_slElem (i j : Fin n) (hij : i ≠ j) (c : K) :
    matrixHom (StatedSL n K) (slElem n K i j hij c) = 1 + Matrix.single i j c := rfl

theorem slElem_mem_Lev [Finite K] (i j : Fin n) (hij : i ≠ j) (c : K) {k : ℕ} (hk : 1 ≤ k)
    (hjk : (j : ℕ) = i + k) :
    slElem n K i j hij c ∈ Lev (matrixHom (StatedSL n K)) (finPos n) k hk := by
  rw [mem_Lev, matrixHom_slElem, add_sub_cancel_left]
  intro a b hab
  refine Matrix.single_apply_of_ne i j c a b ?_
  rintro ⟨rfl, rfl⟩
  simp only [finPos] at hab
  omega

theorem Lev_one_index_not_dvd_sl {p : ℕ} [hp : Fact p.Prime] [Finite K] [CharP K p] (hn : 1 ≤ n) :
    ¬ p ∣ (Lev (matrixHom (StatedSL n K)) (finPos n) 1 le_rfl).index := by
  have heq : Lev (matrixHom (StatedSL n K)) (finPos n) 1 le_rfl =
      (LinearFlag.unitriangular n K).map (specialLinearGroupEquivStatedSL n K).toMonoidHom := by
    ext g
    obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL n K).surjective g
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, LinearFlag.mem_unitriangular, mem_Lev,
      mem_Fil]
    have hA : ∀ a b : Fin n, matrixHom (StatedSL n K) (specialLinearGroupEquivStatedSL n K A) a b
        = (A : Matrix (Fin n) (Fin n) K) a b := fun a b => rfl
    constructor
    · intro h
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · have := h i j (by simp only [finPos]; omega)
        simp only [Matrix.sub_apply, hA, Matrix.one_apply_ne (ne_of_gt hij), sub_zero] at this
        exact this
      · have := h i i (by simp only [finPos]; omega)
        simp only [Matrix.sub_apply, hA, Matrix.one_apply_eq] at this
        exact sub_eq_zero.mp this
    · rintro ⟨h1, h2⟩ a b hab
      simp only [Matrix.sub_apply, hA]
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exfalso
        simp only [finPos] at hab
        have : (a : ℕ) < b := hlt
        omega
      · subst heq
        rw [h2 a, Matrix.one_apply_eq, sub_self]
      · rw [h1 a b hgt, Matrix.one_apply_ne (ne_of_gt hgt), sub_self]
  have hidx : (Subgroup.map (specialLinearGroupEquivStatedSL n K).toMonoidHom
      (LinearFlag.unitriangular n K)).index = (LinearFlag.unitriangular n K).index :=
    Subgroup.index_map_of_bijective (f := (specialLinearGroupEquivStatedSL n K).toMonoidHom)
      (specialLinearGroupEquivStatedSL n K).bijective _
  rw [heq, hidx]
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := K) p hn
  rw [← hP]
  exact P.not_dvd_index

end SL

theorem rankThreeCent_psl {p n f : ℕ} [hp : Fact p.Prime] (hn : 4 ≤ n) {G : Type} [Group G]
    [Finite G] (h : StatedClassicalModel G .PSL n p f) : RankThreeCent p G := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K p := charP_of_card_eq_prime_pow hadm.2.1 hK
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let H : Subgroup (GL (Fin n) K) := StatedSL n K
  let π : ↥H →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf H))
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπinj : ∀ u ∈ Lev (matrixHom H) (finPos n) 1 le_rfl, π u = 1 → u = 1 := by
    intro u hu hu1
    refine mk_injOn_Lev H (finPos n) u hu ?_
    have := e.symm.injective (hu1.trans (map_one e.symm).symm)
    exact this
  have i0lt : 0 < n := by omega
  have i1lt : 1 < n := by omega
  have jm2lt : n - 2 < n := by omega
  have jm1lt : n - 1 < n := by omega
  let i0 : Fin n := ⟨0, i0lt⟩
  let i1 : Fin n := ⟨1, i1lt⟩
  let jm2 : Fin n := ⟨n - 2, jm2lt⟩
  let jm1 : Fin n := ⟨n - 1, jm1lt⟩
  have h02 : i0 ≠ jm2 := fun h => by simp [i0, jm2, Fin.ext_iff] at h; omega
  have h1m : i1 ≠ jm1 := fun h => by simp [i1, jm1, Fin.ext_iff] at h; omega
  have h0m : i0 ≠ jm1 := fun h => by simp [i0, jm1, Fin.ext_iff] at h; omega
  have hk : 1 ≤ n - 2 := by omega
  have hentry : ∀ (i j : Fin n) (hij : i ≠ j) (a b : Fin n),
      (matrixHom H (slElem n K i j hij 1) - 1) a b = if i = a ∧ j = b then 1 else 0 := by
    intro i j hij a b
    rw [matrixHom_slElem, add_sub_cancel_left]
    rfl
  have hb₀1 : slElem n K i0 jm1 h0m 1 ≠ 1 := by
    intro h
    have h1 := hentry i0 jm1 h0m i0 jm1
    rw [h, map_one, sub_self, if_pos ⟨rfl, rfl⟩] at h1
    exact zero_ne_one h1
  refine rankThreeCent_of_corner (ρ := matrixHom H) (pos := finPos n) (matrixHom_injective H) hk
    (fun a b => by simp only [finPos]; have := b.2; omega) π hπ hπinj
    (Lev_one_index_not_dvd_sl (by omega))
    (g₁ := slElem n K i0 jm2 h02 1) (g₂ := slElem n K i1 jm1 h1m 1)
    (b₀ := slElem n K i0 jm1 h0m 1)
    (slElem_mem_Lev i0 jm2 h02 1 hk (by simp [i0, jm2]))
    (slElem_mem_Lev i1 jm1 h1m 1 hk (by simp [i1, jm1]; omega))
    (by
      have := slElem_mem_Lev (K := K) i0 jm1 h0m 1 (k := n - 2 + 1) (by omega)
        (by simp [i0, jm1]; omega)
      exact this)
    hb₀1 (a₁ := i0) (b₁ := jm2) (a₂ := i1) (b₂ := jm1) (by simp [finPos, i0, jm2])
    (by simp [finPos, i1, jm1]; omega) ?_ ?_ ?_ ?_
  · rw [hentry, if_pos ⟨rfl, rfl⟩]
  · rw [hentry, if_neg]
    rintro ⟨h, -⟩
    simp [i0, i1, Fin.ext_iff] at h
  · rw [hentry, if_neg]
    rintro ⟨h, -⟩
    simp [i0, i1, Fin.ext_iff] at h
  · rw [hentry, if_pos ⟨rfl, rfl⟩]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
