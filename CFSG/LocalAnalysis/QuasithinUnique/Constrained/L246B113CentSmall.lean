module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentInner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LieType.SteinbergBRAutGL32
public import Certificates.Certificate4122
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Alternating

theorem card_mulAut_alt_eq_two_mul {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = 2 ^ 1 * Nat.card (alternatingGroup (Fin n)) := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  have h1 : Nat.card (MulAut (alternatingGroup (Fin n))) = Nat.card (Equiv.Perm (Fin n)) :=
    (Nat.card_eq_of_bijective _ hb).symm
  have h2 : Nat.card (alternatingGroup (Fin n)) * (alternatingGroup (Fin n)).index =
      Nat.card (Equiv.Perm (Fin n)) := Subgroup.card_mul_index _
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [alternatingGroup.index_eq_two] at h2
  omega

theorem sylowAutTrivial_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) : SylowAutTrivial S := by
  have hn5 : 5 ≤ n := by omega
  have : IsSimpleGroup (alternatingGroup (Fin n)) := alt_isSimple hn5
  have hOv : Over.Overgroups (alternatingGroup (Fin n)) := Over.overgroups_alt hn (MulEquiv.refl _)
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card (alternatingGroup (Fin n)) = Nat.factorial n / 2 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  refine SylowAutTrivial.of_mulEquiv e ?_
  rcases hn with rfl | rfl | rfl
  · exact sylowAutTrivial_of_overgroups (alt_exists_noncomm hn5)
      (by rw [hcard]; decide) hOv (card_mulAut_alt_eq_two_mul hn5 (by norm_num))
  · refine sylowAutTrivial_of_overgroups (alt_exists_noncomm hn5) (by rw [hcard]; decide) hOv
      (a := 2) ?_
    rw [Setup.X3Aut.card_mulAut_alt6, hcard]
    decide
  · exact sylowAutTrivial_of_overgroups (alt_exists_noncomm hn5)
      (by rw [hcard]; decide) hOv (card_mulAut_alt_eq_two_mul hn5 (by norm_num))

end Alternating

section LThree

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem sylowAutTrivial_sl_three_two :
    SylowAutTrivial (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have := slThree_isSimple
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Nat.card_congr e₃.toEquiv]
    exact CFSG.LieType.SteinbergBR.AutGL32.card_GL32
  have ha : Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) = 336 := by
    rw [Nat.card_congr (MulAut.congr e₃).toEquiv]
    exact CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32
  exact sylowAutTrivial_of_overgroups slThree_nonabelian (by rw [hc]; norm_num)
    Over.CertL32.overgroups_sl (a := 1) (by rw [ha, hc]; norm_num)

end LThree

section UThree

theorem sylowAutTrivial_psu_three_three {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (h : StatedClassicalModel S .PSU 3 3 1) :
    SylowAutTrivial S := by
  have := hS
  have hL : LieModel S .PSU 3 3 1 := Or.inl ⟨by decide, h⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
  have hc : Nat.card S = 6048 := by
    rw [Nat.card_congr e.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      (CFSG.GH74.KGroups.U33.QP_valid).2]
  refine sylowAutTrivial_of_overgroups hnc (by rw [hc]; norm_num)
    (Over.CertU33.overgroups_of_lieModel hL) (a := 1) ?_
  rw [CFSG.GH74.KGroups.U33.card_mulAut e, hc]
  norm_num

end UThree

section Seven

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem sq_eq_one_of_commute_dGens :
    ∀ σ : P7, (∀ g ∈ dGens, σ * g = g * σ) → σ ^ 2 = 1 :=
  Certificates.certificate4122

theorem sylowAutTrivial_alt_seven : SylowAutTrivial (alternatingGroup (Fin 7)) := by
  have hp : IsPGroup 2 T7 := isSylowTwoOf_T7.2.1
  have hi : ¬ 2 ∣ T7.index := by
    have h := isSylowTwoOf_T7.2.2
    rwa [index_subgroupOf_top] at h
  let P₀ : Sylow 2 (alternatingGroup (Fin 7)) := hp.toSylow hi
  refine SylowAutTrivial.of_sylow P₀ fun α hα hfix => ?_
  obtain ⟨σ, rfl⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)).2 α
  have hc : ∀ g ∈ dGens, σ * g = g * σ := by
    intro g hg
    have hgA : g ∈ A7s := D7_le_A7s (Subgroup.subset_closure hg)
    have hgT : (⟨g, hgA⟩ : alternatingGroup (Fin 7)) ∈ T7 :=
      Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hg)
    have h1 := congrArg Subtype.val (hfix ⟨g, hgA⟩ hgT)
    rw [MulAut.conjNormal_apply] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have h2 : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 7))) ^ 2 = 1 := by
    rw [← map_pow, sq_eq_one_of_commute_dGens σ hc, map_one]
  have hdvd : orderOf (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 7))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (orderOf (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 7)))) 2 :=
    hα.coprime_two_right
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)

end Seven

section Models

theorem sylowAutTrivial_model_five {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 2 5 1) : SylowAutTrivial S := by
  obtain ⟨e⟩ := Setup.Family.alternating_five_of_model_five h
  exact sylowAutTrivial_alt (Or.inl rfl) e

theorem sylowAutTrivial_model_nine {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 2 3 2) : SylowAutTrivial S := by
  obtain ⟨e⟩ := Setup.Family.alternating_six_of_model_nine h
  exact sylowAutTrivial_alt (Or.inr (Or.inl rfl)) e

theorem sylowAutTrivial_model_seven {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 2 7 1) : SylowAutTrivial S := by
  obtain ⟨e⟩ := Over.nonempty_equiv_sl_three_two_of_model_seven h
  exact SylowAutTrivial.of_mulEquiv e sylowAutTrivial_sl_three_two

theorem sylowAutTrivial_psl_three_two {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 3 2 1) : SylowAutTrivial S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : S ≃* StatedProj (StatedSL 3 K) := e
  exact SylowAutTrivial.of_mulEquiv
    (e'.trans (Setup.Family.statedProjSL_equiv_of_card_two 3 K (by simpa using hK)))
    sylowAutTrivial_sl_three_two

theorem sylowAutTrivial_psl_four_two {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 4 2 1) : SylowAutTrivial S := by
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff S).mp
    (Or.inl ⟨by decide, h⟩)
  exact sylowAutTrivial_alt (Or.inr (Or.inr rfl)) e

end Models

end CFSG.QuasithinUnique.Bridge
