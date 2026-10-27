module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Defs
public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.SubgroupLists.QuasisimpleLayer
public import CFSG.RankThree.PartOne.KF.F1322OmegaIdx

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists

private theorem false_of_dim_le_one {d : ℕ} (hd : d ≤ 1) {K : Type*} [Field K]
    {Y : Subgroup (GL (Fin d) K)} (hY : CFSG.IsQuasisimple Y) : False := by
  have := hY.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have : Subsingleton (Fin d) := Fin.subsingleton_iff_le_one.mpr hd
  refine Group.IsPerfect.not_isSolvable Y (isSolvable_of_comm fun a b => ?_)
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  obtain rfl := Subsingleton.elim i j
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i]
  exact mul_comm _ _

private def toSL {n : ℕ} {K : Type*} [Field K] (Y : Subgroup (GL (Fin n) K))
    (hdet : ∀ y : Y, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) :
    Y →* SpecialLinearGroup (Fin n) K where
  toFun y := ⟨(y : GL (Fin n) K), hdet y⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem toSL_injective {n : ℕ} {K : Type*} [Field K] (Y : Subgroup (GL (Fin n) K))
    (hdet : ∀ y : Y, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) :
    Function.Injective (toSL Y hdet) := fun _ _ h =>
  Subtype.ext (Units.ext (congrArg Subtype.val h))

private theorem false_of_dim_two
    (hD : ∀ (p : ℕ) [Fact p.Prime]
      (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))),
      ¬ 3 ∣ Nat.card H → Group.IsSolvable H)
    (r : ℕ) [Fact r.Prime] {Y : Subgroup (GL (Fin 2) (ZMod r))} (hY : CFSG.IsQuasisimple Y)
    (h3 : ¬ 3 ∣ Nat.card Y) : False := by
  have := hY.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have hdet : ∀ y : Y, ((y : GL (Fin 2) (ZMod r)) : Matrix (Fin 2) (Fin 2) (ZMod r)).det = 1 := by
    intro y
    have h := Abelianization.commutator_subset_ker
      ((Matrix.GeneralLinearGroup.det).comp Y.subtype) (Group.IsPerfect.mem_commutator (g := y))
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]
  set φ := toSL Y hdet
  set ψ := (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r)))).comp φ
  have : Group.IsSolvable ψ.range :=
    hD r ψ.range fun h => h3 (h.trans (Subgroup.card_range_dvd ψ))
  have : Group.IsSolvable ψ.ker := isSolvable_of_comm fun a b => by
    have ha : φ a ∈ Subgroup.center _ := by
      have := a.2
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
    refine Subtype.ext (toSL_injective Y hdet ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp ha (φ b)).symm
  exact Group.IsPerfect.not_isSolvable Y (Group.isSolvable_of_ker_le_range ψ.ker.subtype
    ψ.rangeRestrict (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]))

theorem glThree_eq_of_normal_irreducible {p : ℕ} [Fact p.Prime]
    {Y H : Subgroup (GL (Fin 3) (ZMod p))} (hY : CFSG.IsQuasisimple Y) (hHY : H ≤ Y)
    (hn : ∀ g ∈ Y, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hH : IsIrreducibleOn H) : H = Y := by
  have := hY.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have hN : (H.subgroupOf Y).Normal := ⟨fun n hn' g => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    exact hn g.1 g.2 n.1 hn'⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hY hN with h | h
  · refine le_antisymm hHY fun y hy => ?_
    have : (⟨y, hy⟩ : Y) ∈ H.subgroupOf Y := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    let := commutantField hH
    have hc : ∀ y : Y, ((y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) ∈
        commutant H := fun y => mem_commutant.mpr fun g hg => by
      have hz : (⟨g, hHY hg⟩ : Y) ∈ Subgroup.center Y := h (Subgroup.mem_subgroupOf.mpr hg)
      have := congrArg (fun z : Y => ((z : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p))) (Subgroup.mem_center_iff.mp hz y)
      simpa using this.symm
    refine Group.IsPerfect.not_isSolvable Y (isSolvable_of_comm fun a b => ?_)
    refine Subtype.ext (Units.ext ?_)
    exact congrArg Subtype.val (mul_comm (⟨_, hc a⟩ : commutant H) ⟨_, hc b⟩)

private theorem three_dvd_card_omegaGL {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    (hY : CFSG.IsQuasisimple (omegaGL M)) (h3 : 3 ∣ p * (p ^ 2 - 1)) :
    3 ∣ Nat.card (omegaGL M) := by
  have := hY.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have hcardS := card_soGL_three hp2 hMt hdet
  have hp : p.Prime := Fact.out
  rcases (by have := hp.two_le; have := hp.eq_one_or_self_of_dvd 2; omega :
      p = 3 ∨ 5 ≤ p) with rfl | hp5
  · by_contra h
    have hdvd : Nat.card (omegaGL M) ∣ 2 ^ 3 := by
      have := Subgroup.card_dvd_of_le (CFSG.RankThree.PartOne.LIT.omegaGL_le_soGL M)
      rw [hcardS, show 3 * (3 ^ 2 - 1) = 3 * 2 ^ 3 by norm_num] at this
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h)
        ).dvd_of_dvd_mul_left this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Group.IsPerfect.not_isNilpotent _ (IsPGroup.of_card_dvd_pow hdvd).isNilpotent
  · have h := Subgroup.card_mul_index ((omegaGL M).subgroupOf (soGL M))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.RankThree.PartOne.LIT.omegaGL_le_soGL M)).toEquiv, hcardS,
      CFSG.RankThree.PartOne.KF1322.index_omegaGL_soGL hp5 hMt hdet] at h
    exact Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) (h ▸ h3)

private theorem three_dvd_of_dim_three (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Subgroup (GL (Fin 3) (ZMod p))}
    (hY : CFSG.IsQuasisimple Y) (hirr : IsIrreducibleOn Y) : 3 ∣ Nat.card Y := by
  have := hY.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have h3 : 3 ∣ p * (p ^ 2 - 1) := by
    rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
    all_goals
      refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ?_)) _
      simp [Nat.pow_mod, h]
  obtain ⟨H, hHY, hn, hHirr, hcase⟩ := hB p hp2 (isIrreducibleOn_iff.mp hirr)
  obtain rfl := glThree_eq_of_normal_irreducible hY hHY hn (isIrreducibleOn_iff.mpr hHirr)
  rcases hcase with rfl | ⟨M, hMt, hdet, rfl⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, hZ, -⟩ | ⟨hcyc, -⟩ |
      ⟨h27, -⟩ | ⟨-, hmon⟩
  · rw [CFSG.Open.StatedAPI.card_statedSL_three, Nat.card_zmod]
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact Dvd.dvd.mul_right (dvd_pow h (by norm_num)) _
    · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h _) _
  · exact three_dvd_card_omegaGL hp2 hMt hdet hY h3
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  · exact (dvd_of_eq hZ.symm).trans (Subgroup.card_subgroup_dvd_card _)
  · exact absurd (IsCyclic.isMulCommutative (α := H)) (Group.IsPerfect.not_isMulCommutative H)
  · rw [h27]
    norm_num
  · exact absurd hmon not_isTransitiveMonomial_of_perfect

theorem glIrrQuasisimpleThreeDvd_of (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    (hD : ∀ (p : ℕ) [Fact p.Prime]
      (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))),
      ¬ 3 ∣ Nat.card H → Group.IsSolvable H) :
    GLIrrQuasisimpleThreeDvd := by
  intro r _ hr2 d hd Y hY hirr
  by_contra h3
  rcases (by omega : d ≤ 1 ∨ d = 2 ∨ d = 3) with hd1 | rfl | rfl
  · exact false_of_dim_le_one hd1 hY
  · exact false_of_dim_two hD r hY h3
  · exact h3 (three_dvd_of_dim_three hB hr2 hY hirr)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
