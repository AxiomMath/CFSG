module

public import CFSG.GH74.Generic.BProg.B2.FixFourS3
public import CFSG.GH74.Generic.BProg.B2.Thm2Comp
public import CFSG.GH74.Generic.BProg.B1.PilotS1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

namespace S3Rk2Rank

section Diag

variable {F : Type} [Field F]

@[expose] def diagSet (F : Type) [Field F] : Set (GL (Fin 3) F) :=
  {x | (x : Matrix (Fin 3) (Fin 3) F).IsDiag ∧ x * x = 1 ∧ (x : Matrix (Fin 3) (Fin 3) F).det = 1}

theorem sq_eq_one_iff_pm {a : F} : a * a = 1 ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    have : (a - 1) * (a + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  · rintro (rfl | rfl) <;> ring

theorem diag_entry_sq {x : GL (Fin 3) F} (hd : (x : Matrix (Fin 3) (Fin 3) F).IsDiag) (hx : x * x = 1)
    (i : Fin 3) : (x : Matrix (Fin 3) (Fin 3) F) i i = 1 ∨ (x : Matrix (Fin 3) (Fin 3) F) i i = -1 := by
  have h1 : ((x * x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by rw [hx]; rfl
  rw [Units.val_mul] at h1
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Fintype.sum_eq_single i (fun j hj => by
    rw [hd (Ne.symm hj), zero_mul])] at h2
  simp only [Matrix.one_apply_eq] at h2
  exact sq_eq_one_iff_pm.1 h2

theorem ncard_diagSet_le : (diagSet F).ncard ≤ 4 := by
  let f : GL (Fin 3) F → F × F := fun x =>
    ((x : Matrix (Fin 3) (Fin 3) F) 0 0, (x : Matrix (Fin 3) (Fin 3) F) 1 1)
  have hmaps : ∀ x ∈ diagSet F, f x ∈ (({1, -1} : Set F) ×ˢ ({1, -1} : Set F)) := by
    intro x hx
    obtain ⟨hd, hsq, -⟩ := hx
    exact ⟨diag_entry_sq hd hsq 0, diag_entry_sq hd hsq 1⟩
  have hinj : Set.InjOn f (diagSet F) := by
    intro x hx y hy hxy
    obtain ⟨hdx, hsx, hdetx⟩ := hx
    obtain ⟨hdy, hsy, hdety⟩ := hy
    have h0 : (x : Matrix (Fin 3) (Fin 3) F) 0 0 = (y : Matrix (Fin 3) (Fin 3) F) 0 0 :=
      congrArg Prod.fst hxy
    have h1 : (x : Matrix (Fin 3) (Fin 3) F) 1 1 = (y : Matrix (Fin 3) (Fin 3) F) 1 1 :=
      congrArg Prod.snd hxy
    have hx' := (Matrix.IsDiag.diagonal_diag hdx).symm
    have hy' := (Matrix.IsDiag.diagonal_diag hdy).symm
    rw [hx', Matrix.det_diagonal, Fin.prod_univ_three] at hdetx
    rw [hy', Matrix.det_diagonal, Fin.prod_univ_three] at hdety
    have hdetx' : (x : Matrix (Fin 3) (Fin 3) F) 0 0 * (x : Matrix (Fin 3) (Fin 3) F) 1 1 *
        (x : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := hdetx
    have hdety' : (y : Matrix (Fin 3) (Fin 3) F) 0 0 * (y : Matrix (Fin 3) (Fin 3) F) 1 1 *
        (y : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := hdety
    have hne : (x : Matrix (Fin 3) (Fin 3) F) 0 0 * (x : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := by
      intro h; rw [h, zero_mul] at hdetx'; exact zero_ne_one hdetx'
    have h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 2 = (y : Matrix (Fin 3) (Fin 3) F) 2 2 := by
      rw [← h0, ← h1] at hdety'
      exact mul_left_cancel₀ hne (hdetx'.trans hdety'.symm)
    apply Units.ext
    rw [hx', hy']
    congr 1
    ext i
    fin_cases i <;> simp [Matrix.diag, h0, h1, h2]
  have hfin : (({1, -1} : Set F) ×ˢ ({1, -1} : Set F)).Finite :=
    (Set.toFinite _).prod (Set.toFinite _)
  calc (diagSet F).ncard ≤ (({1, -1} : Set F) ×ˢ ({1, -1} : Set F)).ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj hfin
    _ = ({1, -1} : Set F).ncard * ({1, -1} : Set F).ncard := Set.ncard_prod
    _ ≤ 2 * 2 := Nat.mul_le_mul ((Set.ncard_insert_le _ _).trans (by simp))
        ((Set.ncard_insert_le _ _).trans (by simp))
    _ = 4 := rfl

end Diag

section Lin

variable {F : Type} [Field F] [Finite F]

theorem card_le_four_projectiveSL3 (hF : ringChar F ≠ 2)
    {D : Subgroup (LinearFlag.projectiveSL 3 F)} (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    Nat.card ↥D ≤ 4 := by
  obtain ⟨B, σ, hσπ, hσ⟩ := B2.FixFourS3.exists_diag_lift_sl3 hF D hD
  have hmem : ∀ d : ↥D, B⁻¹ * SpecialLinearGroup.toGL (σ d) * B ∈ diagSet F := by
    intro d
    obtain ⟨hdiag, hsq⟩ := hσ d
    refine ⟨hdiag, ?_, ?_⟩
    · have h1 : (B⁻¹ * SpecialLinearGroup.toGL (σ d) * B) * (B⁻¹ * SpecialLinearGroup.toGL (σ d) * B) =
          B⁻¹ * (SpecialLinearGroup.toGL (σ d) * SpecialLinearGroup.toGL (σ d)) * B := by group
      rw [h1, ← map_mul, hsq, map_one]
      group
    · rw [B2.FixFourS3.det_conj_gl]
      exact (σ d).2
  have hinj : Function.Injective (fun d : ↥D => B⁻¹ * SpecialLinearGroup.toGL (σ d) * B) := by
    intro a b hab
    have h1 : SpecialLinearGroup.toGL (σ a) = SpecialLinearGroup.toGL (σ b) := by
      have := hab
      simp only [mul_left_inj, mul_right_inj] at this
      exact this
    have h2 : σ a = σ b := SpecialLinearGroup.toGL_injective h1
    have h3 := congrArg (LinearFlag.proj 3 F) h2
    rw [hσπ a, hσπ b] at h3
    exact Subtype.ext h3
  have hsub : Set.range (fun d : ↥D => B⁻¹ * SpecialLinearGroup.toGL (σ d) * B) ⊆
      diagSet F := by
    rintro _ ⟨d, rfl⟩
    exact hmem d
  calc Nat.card ↥D = (Set.range (fun d : ↥D => B⁻¹ * SpecialLinearGroup.toGL (σ d) * B)).ncard := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    _ ≤ (diagSet F).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := ncard_diagSet_le

end Lin

section Uni

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem card_le_four_statedSU3 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {D : Subgroup (StatedProj (StatedSU 3 (p ^ f) K))} (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    Nat.card ↥D ≤ 4 := by
  obtain ⟨B, ρ, -, hρ, hmk⟩ :=
    B2.exists_diag_lift_of_odd_unitary hp hp2 hK (by decide) D hD
  have hmem : ∀ d : ↥D, B⁻¹ * ρ d * B ∈ diagSet K := by
    intro d
    obtain ⟨hdiag, hsq⟩ := hρ d
    obtain ⟨hdS, -⟩ := hmk d
    refine ⟨hdiag, ?_, ?_⟩
    · have h1 : (B⁻¹ * ρ d * B) * (B⁻¹ * ρ d * B) = B⁻¹ * (ρ d * ρ d) * B := by group
      rw [h1, hsq]
      group
    · rw [B2.FixFourS3.det_conj_gl]
      exact det_eq_one_of_mem_statedSU hdS
  have hinj : Function.Injective (fun d : ↥D => B⁻¹ * ρ d * B) := by
    intro a b hab
    have h1 : ρ a = ρ b := by
      have := hab
      simp only [mul_left_inj, mul_right_inj] at this
      exact this
    obtain ⟨ha, hma⟩ := hmk a
    obtain ⟨hb, hmb⟩ := hmk b
    apply Subtype.ext
    rw [← hma, ← hmb]
    congr 1
    exact Subtype.ext h1
  have hsub : Set.range (fun d : ↥D => B⁻¹ * ρ d * B) ⊆ diagSet K := by
    rintro _ ⟨d, rfl⟩
    exact hmem d
  calc Nat.card ↥D = (Set.range (fun d : ↥D => B⁻¹ * ρ d * B)).ncard := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    _ ≤ (diagSet K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := ncard_diagSet_le

end Uni

theorem card_le_four_of_qShape3 {Kt : Type} [Group Kt] [Finite Kt] (hKt : QShape3 Kt)
    {D : Subgroup Kt} (hD : CFSG.IsElementaryAbelian 2 ↥D) : Nat.card ↥D ≤ 4 := by
  obtain ⟨p, f, hp, hp2, -, hm | hm⟩ := hKt
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := B2.GenLocL5Out.stated_PSL hm
    let ψ : Kt ≃* LinearFlag.projectiveSL 3 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    have hF2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
    have h := card_le_four_projectiveSL3 hF2 (B2.FixFourS3.isElementaryAbelian_map_equiv ψ hD)
    rwa [Subgroup.card_map_of_injective ψ.injective] at h
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := B2.GenLocL5Out.stated_PSU hm
    have h := card_le_four_statedSU3 hp hp2 hK (B2.FixFourS3.isElementaryAbelian_map_equiv e hD)
    rwa [Subgroup.card_map_of_injective e.injective] at h

theorem card_le_four_of_le {G : Type} [Group G] [Finite G] {K E : Subgroup G}
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) (hEK : E ≤ K) (hEel : CFSG.IsElementaryAbelian 2 ↥E) :
    Nat.card ↥E ≤ 4 := by
  set E' : Subgroup ↥K := E.subgroupOf K with hE'
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' := CFSG.IsElementaryAbelian.subgroupOf hEK
  have hE'p : IsPGroup 2 ↥E' := CFSG.IsElementaryAbelian.isPGroup 2 ↥E'
  have hcard : Nat.card ↥E' = Nat.card ↥E := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv]
  have hmapel : CFSG.IsElementaryAbelian 2 ↥(E'.map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) :=
    CFSG.IsElementaryAbelian.map (QuotientGroup.mk' (pPrimeCore 2 ↥K))
  have hmcard : Nat.card ↥(E'.map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) = Nat.card ↥E' :=
    B1.PilotS1.card_map_eq_of_inj _ E' (B2.Thm2Comp.eq_one_of_isPGroup hE'p)
  have := card_le_four_of_qShape3 h3 hmapel
  omega

end S3Rk2Rank

end CFSG.GH74.Generic.BProg.B3
