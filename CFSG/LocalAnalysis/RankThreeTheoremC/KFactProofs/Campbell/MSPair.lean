module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Sqtk
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row17Comp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.isSimple_quot (h : CampbellHyp X K R P) :
    IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨f, hf, hker⟩ := h.quot
  have hker' : f.ker = CFSG.pCore 2 ↥K := by
    rw [h.pCore_K_eq]
    ext k
    exact hker k
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* GL32 :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  haveI : IsSimpleGroup GL32 := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  exact e.isSimpleGroup

theorem CampbellHyp.K_mem_cComp (h : CampbellHyp X K R P) : K ∈ CFSG.Quasithin.cComp X :=
  CFSG.Quasithin.Stellmacher.L3YC.mem_cComp_of_modO2_simple h.K_le
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.K_le).2 h.K_normal) h.K_perfect
    h.isSimple_quot
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem lie2_exists_hom (h : CampbellHyp X K R P) :
    ∃ f : ↥K →* GL32, Function.Surjective f ∧ f.ker = CFSG.pCore 2 ↥K := by
  obtain ⟨f, hf, hker⟩ := h.quot
  refine ⟨f, hf, ?_⟩
  rw [h.pCore_K_eq]
  ext k
  exact hker k

theorem lie2_nonempty_quotEquiv (h : CampbellHyp X K R P) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* GL32) := by
  obtain ⟨f, hf, hker⟩ := lie2_exists_hom h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem lie2_center_GL32 : Subgroup.center GL32 = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨r, rfl⟩
  rw [Subsingleton.elim r 1, map_one]
  exact Subgroup.one_mem _

theorem lie2_center_eq_bot {G : Type} [Group G] (e : G ≃* GL32) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  have h1 : e x ∈ Subgroup.center GL32 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg e (hx (e.symm g))
    simpa using h2
  rw [lie2_center_GL32, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem lie2_nonempty_equiv_psl (h : CampbellHyp X K R P) :
    Nonempty (((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨e₁⟩ := lie2_nonempty_quotEquiv h
  obtain ⟨e₂⟩ := nonempty_mulEquiv_GL32_psl
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (lie2_center_eq_bot e₁)).trans
    QuotientGroup.quotientBot).trans (e₁.trans e₂)⟩

theorem CampbellHyp.isRankTwoLie2Derived (h : CampbellHyp X K R P) :
    CFSG.Quasithin.IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  obtain ⟨e⟩ := lie2_nonempty_equiv_psl h
  exact Or.inl ⟨1, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

theorem CampbellHyp.exists_modO2Surj (h : CampbellHyp X K R P) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥K →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ∧ CFSG.Quasithin.IsModO2Surj K α := by
  obtain ⟨f, hf, hker⟩ := lie2_exists_hom h
  have hmem : ∀ k : ↥K, f k ∈ StatedSL 3 (ZMod 2) := fun k => by
    rw [statedSL_zmod_two_eq_top]
    trivial
  refine ⟨ZMod 2, inferInstance, inferInstance, f.codRestrict (StatedSL 3 (ZMod 2)) hmem,
    ZMod.card 2, ?_, ?_⟩
  · intro y
    obtain ⟨k, hk⟩ := hf y.1
    exact ⟨k, Subtype.ext hk⟩
  · rw [MonoidHom.ker_codRestrict]
    exact hker
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.isMSPair (h : CampbellHyp X K R P) :
    CFSG.Quasithin.IsMSPair X (pCoreOf 2 P) := by
  refine ⟨⟨h.isSQTKIn, h.charTwo, K, h.K_mem_cComp, h.X_eq_mul, h.isRankTwoLie2Derived⟩,
    Or.inl ⟨P, h.P_lt_X, ?_, rfl⟩, fun C hC hne hchar => h.pushUp C hC hne hchar⟩
  show ¬ 2 ∣ (P.subgroupOf X).index
  rw [h.P_index]
  decide
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
