module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LargeExtraspecial.S14C13Model
public import CFSG.LargeExtraspecial.S7SevenMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Matrix Module CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.EvenSource CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.Bridge CFSG.GroupTheory.WeirSylow

namespace OmegaPlus

variable (n : ℕ)

noncomputable def F :
    (Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) (ZMod 2) (ZMod 2)

theorem plusForm_F (v : Fin n ⊕ Fin n → ZMod 2) :
    timmesfeldPlusForm n (F n v) = StatedQuadPlus n (ZMod 2) v := by
  simp only [timmesfeldPlusForm, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, F]
  rfl

noncomputable def toGL :
    ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) ≃*
      GL (Fin n ⊕ Fin n) (ZMod 2) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).symm.trans
    (sourceGLEquiv (Pi.basisFun (ZMod 2) (Fin n ⊕ Fin n)))

theorem toGL_symm_apply (A : GL (Fin n ⊕ Fin n) (ZMod 2)) (v : Fin n ⊕ Fin n → ZMod 2) :
    ((toGL n).symm A) v = (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) *ᵥ v := by
  have h := equivFun_sourceGLEquiv_symm (Pi.basisFun (ZMod 2) (Fin n ⊕ Fin n)) A v
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] at h
  exact h

theorem map_isometries_toGL :
    (timmesfeldIsometries (StatedQuadPlus n (ZMod 2))).map (toGL n).toMonoidHom =
      matrixOrthogonal (StatedQuadPlus n (ZMod 2)) := by
  ext A
  rw [Subgroup.mem_map_equiv]
  change (∀ v, StatedQuadPlus n (ZMod 2) (((toGL n).symm A) v) = StatedQuadPlus n (ZMod 2) v) ↔
    ∀ v, StatedQuadPlus n (ZMod 2)
      ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) *ᵥ v) = StatedQuadPlus n (ZMod 2) v
  simp only [toGL_symm_apply]

noncomputable def Φ :
    (((Fin n → ZMod 2) × (Fin n → ZMod 2)) ≃ₗ[ZMod 2] ((Fin n → ZMod 2) × (Fin n → ZMod 2))) ≃*
      GL (Fin n ⊕ Fin n) (ZMod 2) :=
  (conjLinearEquiv (F n)).symm.trans (toGL n)

theorem map_isometries_Φ :
    (timmesfeldIsometries (timmesfeldPlusForm n)).map (Φ n).toMonoidHom =
      matrixOrthogonal (StatedQuadPlus n (ZMod 2)) := by
  ext A
  rw [Subgroup.mem_map_equiv]
  have h1 : (Φ n).symm A = conjLinearEquiv (F n) ((toGL n).symm A) := rfl
  rw [h1, conj_mem_isometries_iff (F n) (plusForm_F n)]
  rw [← map_isometries_toGL, Subgroup.mem_map_equiv]

theorem map_omegaPlus :
    (timmesfeldOmegaPlus n).map (Φ n).toMonoidHom = StatedOmega (StatedQuadPlus n (ZMod 2)) := by
  unfold timmesfeldOmegaPlus
  rw [Subgroup.map_commutator, map_isometries_Φ, statedOmega_eq_commutator]

theorem statedScalars_zmod_two : StatedScalars (Fin n ⊕ Fin n) (ZMod 2) = ⊥ := by
  ext A
  simp only [StatedScalars, MonoidHom.mem_range, Subgroup.mem_bot]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c = 1 := by revert c; decide
    subst hc
    exact map_one _
  · rintro rfl
    exact ⟨1, map_one _⟩

noncomputable def projEquiv (H : Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))) : H ≃* StatedProj H :=
  (QuotientGroup.quotientBot).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (by rw [statedScalars_zmod_two]; exact (Subgroup.bot_subgroupOf H).symm))

end OmegaPlus

theorem statedClassicalModel_timmesfeldOmegaPlus (n : ℕ) (hn : 4 ≤ n) :
    StatedClassicalModel (timmesfeldOmegaPlus n) .POmegaPlus n 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, hn⟩, ZMod 2, inferInstance, inferInstance, by simp,
    ⟨(equivOfMapEq (OmegaPlus.Φ n) (OmegaPlus.map_omegaPlus n)).trans
      (OmegaPlus.projEquiv n _)⟩⟩

theorem nonempty_mulEquiv_timmesfeldOmegaPlus_of_lieModel {X : Type} [Group X] (n : ℕ)
    (hn : 4 ≤ n) (h : LieModel X .POmegaPlus n 2 1) : Nonempty (X ≃* timmesfeldOmegaPlus n) :=
  nonempty_mulEquiv_of_statedClassicalModel (h.statedClassicalModel (by decide))
    (statedClassicalModel_timmesfeldOmegaPlus n hn)

theorem lieModel_of_mulEquiv_timmesfeldOmegaPlus {X : Type} [Group X] (n : ℕ) (hn : 4 ≤ n)
    (e : X ≃* timmesfeldOmegaPlus n) : LieModel X .POmegaPlus n 2 1 := by
  obtain ⟨hadm, K, hF, hfin, hK, ⟨e'⟩⟩ := statedClassicalModel_timmesfeldOmegaPlus n hn
  exact Or.inl ⟨by decide, hadm, K, hF, hfin, hK, ⟨e.trans e'⟩⟩

theorem exists_form_omegaPlus_four :
    ∃ q : QuadraticForm (ZMod 2) (Fin 8 → ZMod 2), timmesfeldNondegenerate q ∧
      timmesfeldPlusType q ∧ Nonempty (timmesfeldOmegaPlus 4 ≃* timmesfeldOmega q) := by
  set Q := CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)
  have h8 : finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨q', hnd', hplus', ⟨e1⟩, -⟩ := exists_fin_form Q h8
  have hplus : IsPlusType Q := isPlusType_quadPlus (ZMod 2) 4
  obtain ⟨e2⟩ := CFSG.LargeExtraspecial.S14.nonempty_omegaGroup_equiv_omegaPlus hQ
    (m := 4) (by rw [h8]) (by norm_num) hplus
  have h3 : timmesfeldOmega (Q : (Fin 4 ⊕ Fin 4 → ZMod 2) → ZMod 2) =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    CFSG.LargeExtraspecial.S7.timmesfeldOmega_eq Q hQ
  refine ⟨q', hnd' ((polarBilin_nondegenerate_iff Q).mp hQ), hplus' ?_, ?_⟩
  · obtain ⟨W, hW, hWQ⟩ := hplus
    exact ⟨W, by simpa [h8] using hW, hWQ⟩
  · exact ⟨e2.symm.trans ((MulEquiv.subgroupCongr h3).symm.trans e1)⟩

theorem exists_noncomm_of_fstar_centralizer {M : Type} [Group M] [Finite M] [IsSimpleGroup M]
    (t : M)
    (hcard : Nat.card (generalizedFitting (Subgroup.centralizer ({t} : Set M))) = 2 ^ 17) :
    ∃ a b : M, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  letI : CommGroup M := { ‹Group M› with mul_comm := fun a b => hcomm a b }
  have hp : (Nat.card M).Prime := IsSimpleGroup.prime_card
  have hdvd1 : Nat.card (generalizedFitting (Subgroup.centralizer ({t} : Set M))) ∣
      Nat.card (Subgroup.centralizer ({t} : Set M)) := Subgroup.card_subgroup_dvd_card _
  have hdvd2 : Nat.card (Subgroup.centralizer ({t} : Set M)) ∣ Nat.card M :=
    Subgroup.card_subgroup_dvd_card _
  rw [hcard] at hdvd1
  have h2 : 2 ∣ Nat.card M := (dvd_pow_self 2 (by norm_num)).trans (hdvd1.trans hdvd2)
  have h3 : Nat.card M = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have h4 := hdvd1.trans hdvd2
  rw [h3] at h4
  exact absurd (Nat.le_of_dvd (by norm_num) h4) (by norm_num)

end CFSG.GF2Type.SmithTypeE
