module

public import CFSG.CGT.T75P.A8ExclUT
public import CFSG.GH74.KGroups.L34Base

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.Blueprint

private abbrev F4 : Type := CFSG.GH74.KGroups.GF4

private lemma a8xUT_central_in_U {F : Type} [Field F] (c : F) :
    (⟨CFSG.CGT.T75P.a8xUT 0 0 c,
      CFSG.CGT.T75P.a8xUT_mem (F := F) 0 0 c⟩ : CFSG.CGT.T75P.a8xU F) ∈
        Subgroup.center (CFSG.CGT.T75P.a8xU F) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨g, hg⟩
  rcases hg with ⟨⟨a, b, c'⟩, rfl⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [CFSG.CGT.T75P.a8xUT_mul, CFSG.CGT.T75P.a8xUT_mul]
  simp only [add_zero, zero_add, mul_zero]
  congr 1 <;> ring

private lemma a8xU_inf_center_eq_bot {F : Type} [Field F] :
    CFSG.CGT.T75P.a8xU F ⊓ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxC⟩
  rw [Subgroup.mem_bot]
  rcases hxU with ⟨⟨a, b, c⟩, rfl⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxC
  have ha : a = 0 := by
    have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) hr
    simp [Matrix.scalar_apply, CFSG.CGT.T75P.a8xUT_apply, Matrix.of_apply] at h01
    exact h01.symm
  have hb : b = 0 := by
    have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 2) hr
    simp [Matrix.scalar_apply, CFSG.CGT.T75P.a8xUT_apply, Matrix.of_apply] at h12
    exact h12.symm
  have hc : c = 0 := by
    have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) hr
    simp [Matrix.scalar_apply, CFSG.CGT.T75P.a8xUT_apply, Matrix.of_apply] at h02
    exact h02.symm
  rw [ha, hb, hc]
  simpa using (CFSG.CGT.T75P.a8xUT_zero (F := F))

theorem not_l34_of_center_two {X : Type} [Group X] [Finite X]
    (hZ : ∀ S : Sylow 2 X, Nat.card (Subgroup.center ↥(S : Subgroup X)) = 2) :
    ¬ LieModel X .PSL 3 2 2 := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := F4) 3 2 2 (by norm_num)
    (CFSG.GH74.KGroups.L34.card_F) h
  let U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F4) := CFSG.CGT.T75P.a8xU F4
  let π : Matrix.SpecialLinearGroup (Fin 3) F4 →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4 :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4))
  let Ubar : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4) := U.map π
  have hker : U ⊓ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) = ⊥ :=
    a8xU_inf_center_eq_bot
  have hinj : Function.Injective (π.comp U.subtype) := by
    intro x y hxy
    change π (x : Matrix.SpecialLinearGroup (Fin 3) F4) = π (y : _) at hxy
    have hker' : ((x : Matrix.SpecialLinearGroup (Fin 3) F4)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin 3) F4)) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4))]
      rw [MonoidHom.mem_ker]
      show π ((x : Matrix.SpecialLinearGroup (Fin 3) F4)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin 3) F4)) = 1
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hU' : ((x : Matrix.SpecialLinearGroup (Fin 3) F4)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin 3) F4)) ∈ U := U.mul_mem (U.inv_mem x.2) y.2
    have hbot : ((x : Matrix.SpecialLinearGroup (Fin 3) F4)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin 3) F4)) = 1 := by
      have hmem : ((x : Matrix.SpecialLinearGroup (Fin 3) F4)⁻¹ *
          (y : Matrix.SpecialLinearGroup (Fin 3) F4)) ∈
          U ⊓ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) := ⟨hU', hker'⟩
      rw [hker] at hmem
      simpa using hmem
    exact Subtype.ext (inv_mul_eq_one.mp hbot)
  have hrange : (π.comp U.subtype).range = Ubar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eU : U ≃* Ubar := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hU_card : Nat.card U = 64 := by
    rw [CFSG.CGT.T75P.a8xU_card, CFSG.GH74.KGroups.L34.card_F]
    norm_num
  have hUbar_card : Nat.card Ubar = 64 := by
    rw [← hU_card]
    exact (Nat.card_congr eU.toEquiv).symm
  have hcenter_eq : Nat.card (Subgroup.center U) = Nat.card (Subgroup.center Ubar) :=
    Nat.card_congr (Subgroup.centerCongr eU).toEquiv
  have hcenter_le : Nat.card F4 ≤ Nat.card (Subgroup.center U) := by
    refine Nat.card_le_card_of_injective
      (fun c : F4 => (⟨⟨CFSG.CGT.T75P.a8xUT 0 0 c,
        CFSG.CGT.T75P.a8xUT_mem (F := F4) 0 0 c⟩, a8xUT_central_in_U c⟩ :
          Subgroup.center U)) ?_
    intro c c' hcc
    have h1 : CFSG.CGT.T75P.a8xUT 0 0 c = CFSG.CGT.T75P.a8xUT 0 0 c' := by
      have := congrArg
        (fun z : Subgroup.center U =>
          (((z : U) : CFSG.CGT.T75P.a8xU F4) : Matrix.SpecialLinearGroup (Fin 3) F4)) hcc
      simpa using this
    have h2 : c = c' := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F4 =>
        (g : Matrix (Fin 3) (Fin 3) F4) 0 2) h1
      simpa [CFSG.CGT.T75P.a8xUT_apply, Matrix.of_apply] using this
    exact h2
  have h4 : 4 ≤ Nat.card (Subgroup.center Ubar) := by
    rw [← hcenter_eq]
    calc 4 = Nat.card F4 := by rw [CFSG.GH74.KGroups.L34.card_F]; norm_num
      _ ≤ Nat.card (Subgroup.center U) := hcenter_le
  have hYcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4) = 20160 :=
    CFSG.GH74.KGroups.L34.card_psl
  have hfact : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4)).factorization 2 = 6 := by
    rw [hYcard]
    rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd]
  let SY : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4) :=
    Sylow.ofCard Ubar (by rw [hUbar_card, hfact]; norm_num)
  let SX : Sylow 2 X := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective SY
  have hcenterX : Nat.card (Subgroup.center ↥(SX : Subgroup X)) =
      Nat.card (Subgroup.center
        ↥(SY : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4))) := by
    have hmap : (SX : Subgroup X) =
        (SY : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4)).map e.symm.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    rw [hmap]
    exact (Nat.card_congr (Subgroup.centerCongr
      (e.symm.subgroupMap (SY :
        Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4)))).toEquiv).symm
  have h4X : 4 ≤ Nat.card (Subgroup.center ↥(SX : Subgroup X)) := by
    rw [hcenterX]
    dsimp only [SY]
    exact h4
  have h2 := hZ SX
  omega

end CFSG.EvenSporadicStandard.HNRecog.GH73
