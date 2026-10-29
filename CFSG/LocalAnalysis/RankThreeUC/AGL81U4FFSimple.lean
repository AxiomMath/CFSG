module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open

theorem statedScalars_subgroupOf_statedSU4_eq_bot (K : Type) [Field K] [CharP K 2] (N : ℕ) :
    (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 N K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [hc]
    exact StatedAPI.det_of_mem_statedSU g.2
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : ((c : K) - 1) ^ 4 = (c : K) ^ 4 - 1 := by
    linear_combination (-2 * (c : K) ^ 3 + 3 * (c : K) ^ 2 - 2 * (c : K) + 1) * h2
  have h0 : ((c : K) - 1) ^ 4 = 0 := by rw [h4, hdet, sub_self]
  have hc1 : c = 1 := Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h0))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

noncomputable def statedProj_statedSU4_equiv (K : Type) [Field K] [CharP K 2] (N : ℕ) :
    StatedProj (StatedSU 4 N K) ≃* ↥(StatedSU 4 N K) :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSU4_eq_bot K N)).trans
    QuotientGroup.quotientBot

theorem exists_statedSU4_iso_twistedA3 (q : TauCeti.PrimePower) (hq : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ q.exponent) ^ 2 ∧
      Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩ ≃*
        ↥(StatedSU 4 (2 ^ q.exponent) F)) := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : CharP K q.p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
  rw [hq] at hchar hcard e
  exact ⟨K, hK, hKf, hcard, ⟨e.trans (statedProj_statedSU4_equiv K (2 ^ q.exponent))⟩⟩

theorem isSimpleGroup_twistedA3 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) :
    IsSimpleGroup (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _))).2

theorem exists_noncomm_of_isPerfect (G : Type) [Group G] [Nontrivial G] [Group.IsPerfect G] :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative G ⟨⟨fun a b => h a b⟩⟩

theorem isPerfect_twistedA3 (q : TauCeti.PrimePower) (hq : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) :
    Group.IsPerfect (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) := by
  obtain ⟨F, hF, hFf, hcard, ⟨e⟩⟩ := exists_statedSU4_iso_twistedA3 q hq hv
  haveI : Group.IsPerfect ↥(StatedSU 4 (2 ^ q.exponent) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard (by norm_num) (by simp)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

section Main

variable {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = 2)
  (hd : d.1 = .twistedA 3 q)
include hq hd

theorem u4Group_isSimple : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d1, hv⟩ := d
  have hd' : d1 = TauCeti.LieTypeIndex.twistedA 3 q := hd
  subst hd'
  exact isSimpleGroup_twistedA3 q hv

theorem u4Group_nonabelian : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a := by
  obtain ⟨d1, hv⟩ := d
  have hd' : d1 = TauCeti.LieTypeIndex.twistedA 3 q := hd
  subst hd'
  haveI := isSimpleGroup_twistedA3 q hv
  haveI := isPerfect_twistedA3 q hq hv
  exact exists_noncomm_of_isPerfect (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩)

end Main

end CFSG.LocalAnalysis.RankThreeUC
