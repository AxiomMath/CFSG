module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Core
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Linear
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSolv

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists

theorem isSolvable_gl_of_coprime_three (hGL : GLIrrQuasisimpleThreeDvd) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {d : ℕ} (hd : d ≤ 3) (X : Subgroup (GL (Fin d) (ZMod r)))
    (h3 : Nat.Coprime 3 (Nat.card X)) : Group.IsSolvable X := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    refine isSolvable_of_coprime_three_of_quasisimple (ι := Fin d) (by simp; omega) ?_ X h3 ?_
    · intro d' hd' Y hY
      rw [Fintype.card_fin] at hd'
      exact ih d' hd' (by omega) Y hY
    · intro Y _ hYq hYi
      exact hGL r hr2 d hd Y hYq hYi

private def spMult {r : ℕ} [Fact r.Prime] (x : GL (Fin 2 ⊕ Fin 2) (ZMod r)) : ZMod r :=
  (((x : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) * (x : Matrix _ _ (ZMod r)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod r)) (Sum.inl 0) (Sum.inr 0))

private lemma spMult_spec {r : ℕ} [Fact r.Prime] {x : GL (Fin 2 ⊕ Fin 2) (ZMod r)}
    (hx : ∃ μ : ZMod r, (x : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) *
      (x : Matrix _ _ (ZMod r)) = μ • spFourJ (ZMod r)) :
    (x : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) * (x : Matrix _ _ (ZMod r)) =
      spMult x • spFourJ (ZMod r) := by
  obtain ⟨μ, hμ⟩ := hx
  have : spMult x = μ := by
    rw [spMult, hμ]
    simp
  rw [this, hμ]

private def spMultHom {r : ℕ} [Fact r.Prime] (X : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r)))
    (hX : ∀ x ∈ X, ∃ μ : ZMod r, (x : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) *
      (x : Matrix _ _ (ZMod r)) = μ • spFourJ (ZMod r)) : X →* ZMod r where
  toFun x := spMult (x : GL (Fin 2 ⊕ Fin 2) (ZMod r))
  map_one' := by simp [spMult, Matrix.fromBlocks]
  map_mul' x y := by
    have hx := spMult_spec (hX x x.2)
    have hy := spMult_spec (hX y y.2)
    have hxy : ((x * y : GL (Fin 2 ⊕ Fin 2) (ZMod r)) : Matrix _ _ (ZMod r))ᵀ *
        spFourJ (ZMod r) * ((x * y : GL (Fin 2 ⊕ Fin 2) (ZMod r)) : Matrix _ _ (ZMod r)) =
        (spMult (x : GL (Fin 2 ⊕ Fin 2) (ZMod r)) * spMult (y : GL (Fin 2 ⊕ Fin 2) (ZMod r))) •
          spFourJ (ZMod r) := by
      rw [Units.val_mul, show ∀ A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod r),
          (A * B)ᵀ * spFourJ (ZMod r) * (A * B) = Bᵀ * (Aᵀ * spFourJ (ZMod r) * A) * B from
          fun _ _ => by simp only [Matrix.transpose_mul, Matrix.mul_assoc],
        hx, Matrix.mul_smul, Matrix.smul_mul, hy, smul_smul]
    have := congrFun (congrFun hxy (Sum.inl 0)) (Sum.inr 0)
    simpa [spMult, Matrix.fromBlocks] using this

theorem le_statedSp_of_isPerfect {r : ℕ} [Fact r.Prime]
    {X Y : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r))}
    (hX : ∀ x ∈ X, ∃ μ : ZMod r, (x : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) *
      (x : Matrix _ _ (ZMod r)) = μ • spFourJ (ZMod r))
    (hYX : Y ≤ X) (hY : Group.IsPerfect Y) : Y ≤ CFSG.Open.StatedSp 2 (ZMod r) := by
  intro y hy
  let f : Y →* (ZMod r)ˣ := ((spMultHom X hX).toHomUnits).comp (Subgroup.inclusion hYX)
  have hker : (⟨y, hy⟩ : Y) ∈ f.ker :=
    Abelianization.commutator_subset_ker f (by simp)
  have h1 : spMult y = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hker)
    simpa [f, spMultHom] using this
  apply Subgroup.subset_closure
  show (y : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) * (y : Matrix _ _ (ZMod r)) =
    spFourJ (ZMod r)
  rw [spMult_spec (hX y (hYX hy)), h1, one_smul]

theorem isSolvable_gsp_of_coprime_three (hGL : GLIrrQuasisimpleThreeDvd)
    (hSp : SpFourQuasisimpleThreeDvd) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (X : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r)))
    (hX : ∀ x ∈ X, ∃ μ : ZMod r, (x : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) *
      (x : Matrix _ _ (ZMod r)) = μ • spFourJ (ZMod r))
    (h3 : Nat.Coprime 3 (Nat.card X)) : Group.IsSolvable X := by
  refine isSolvable_of_coprime_three_of_quasisimple (by simp) ?_ X h3 ?_
  · intro d hd Y hY
    simp only [Fintype.card_sum, Fintype.card_fin] at hd
    exact isSolvable_gl_of_coprime_three hGL hr2 (by omega) Y hY
  · intro Y hYX hYq _
    exact hSp r hr2 Y (le_statedSp_of_isPerfect hX hYX hYq.1) hYq

private lemma isSolvable_of_pGroup_ker {r : ℕ} [Fact r.Prime] {G H : Type*} [Group G] [Finite G]
    [Group H] (f : G →* H) (hker : IsPGroup r f.ker) (hrange : Group.IsSolvable f.range) :
    Group.IsSolvable G := by
  have := hker.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem kFactAutRankThreeSolvable_of (hGL : GLIrrQuasisimpleThreeDvd)
    (hSp : SpFourQuasisimpleThreeDvd) : KFactAutRankThreeSolvable := by
  intro r R _ _ hr hr2 hR hrk B h3
  have : Fact r.Prime := ⟨hr⟩
  have hc {H : Type} [Group H] (f : B →* H) : Nat.Coprime 3 (Nat.card f.range) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_range_dvd f) h3
  rcases exists_linear_of_pRank_le_three hr2 hR hrk B with ⟨d, hd, f, hf⟩ | ⟨f, hf, hJ⟩
  · exact isSolvable_of_pGroup_ker f hf (isSolvable_gl_of_coprime_three hGL hr2 hd _ (hc f))
  · refine isSolvable_of_pGroup_ker f hf (isSolvable_gsp_of_coprime_three hGL hSp hr2 _ ?_ (hc f))
    rintro _ ⟨b, rfl⟩
    exact hJ b

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
