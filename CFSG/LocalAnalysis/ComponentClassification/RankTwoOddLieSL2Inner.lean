module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieSL2Three
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Core

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
  CFSG.ComponentClassification.AschbacherKnownGroup
open scoped MatrixGroups commutatorElement

theorem map_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx g']
  · intro hy
    refine ⟨e.symm y, fun g => e.injective ?_, by simp⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy (e g)]

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Open.IsQuasisimple A) : Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

variable {F : Type*} [Field F]

theorem isQuasisimple_sl2 [Finite F] (h4 : 4 ≤ Nat.card F) : Open.IsQuasisimple SL(2, F) :=
  ⟨(sl2_isPerfect h4).commutator_eq_top, Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩

theorem hasDihedralSylowTwo_of_gw {G : Type*} [Group G] [Finite G]
    (h : CFSG.GorensteinWalter.HasDihedralSylowTwo G) : HasDihedralSylowTwo G := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨m, hm, ⟨e⟩⟩ := h S
  refine ⟨S, m + 1, by omega, ⟨?_⟩⟩
  rw [Nat.add_sub_cancel]
  exact e

theorem hasDihedralSylowTwo_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : HasDihedralSylowTwo X) : HasDihedralSylowTwo Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, n, hn, ⟨eS⟩⟩ := h
  exact ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, n, hn,
    ⟨((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eS⟩⟩

theorem isOddPrimePower_of_odd [Finite F] (hF : Odd (Nat.card F)) :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  exact ⟨ringChar F, n, hp, hp.odd_of_ne_two (ringChar_ne_two_of_odd hF), n.pos,
    by rw [Nat.card_eq_fintype_card, hn]⟩

variable {H : Type} [Group H] {B T X : Subgroup H}

theorem Hyp46.not_le_centralizerJoin [Finite H] (h : Hyp46 B T X)
    (hBX : ¬ B ≤ normalizer (X : Set H)) {U : Subgroup H} (hUT : U ≤ T) :
    ¬ B ≤ centralizerJoin U B := fun hle => hBX (hle.trans (iSup₂_le fun _ hu => iSup_le fun hu1 =>
      (inf_le_inf_right _ le_sup_right).trans (h.inf_centralizer_le_of_mem (hUT hu) hu1)))

theorem Hyp46.exists_isFourGroup_mem [Finite H] (h : Hyp46 B T X) {t : H} (ht : t ∈ T)
    (ht1 : t ≠ 1) : ∃ U : Subgroup H, U ≤ T ∧ IsFourGroup U ∧ t ∈ U := by
  obtain ⟨s, hs, hs1, hst⟩ := h.exists_ne ht
  refine ⟨closure ({t, s} : Set H), ?_, Lemma38.isFourGroup_closure_pair (h.elem.2 t ht)
    (h.elem.2 s hs) ht1 hs1 (Ne.symm hst)
    (congrArg Subtype.val (h.elem.1.is_comm.comm ⟨t, ht⟩ ⟨s, hs⟩)), subset_closure (by simp)⟩
  rw [closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact ht
  · exact hs

theorem Hyp46.le_sup_centralizer_of_sl2 [Finite H] [Finite F] (h : Hyp46 B T X)
    (e : B ≃* SL(2, F)) (hF : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    T ≤ B ⊔ centralizer (B : Set H) := by
  have hBq : Open.IsQuasisimple B := isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 (by omega))
  have hd : HasDihedralSylowTwo (B ⧸ center B) :=
    hasDihedralSylowTwo_of_mulEquiv' (QuotientGroup.congr _ _ e (map_center_mulEquiv e)).symm
      (hasDihedralSylowTwo_of_gw (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
        (isOddPrimePower_of_odd hF)))
  have hz : (Nat.card (center B)).factorization 2 ≤ 1 := by
    rw [natCard_center_of_equiv_sl2 hF e, Nat.Prime.factorization_self Nat.prime_two]
  have hBX : ¬ B ≤ normalizer (X : Set H) := by
    intro hBX
    have hTC := h.le_centralizer_of_le_normalizer e hF h.le_normalizer hBX
    have hT1 : T = ⊥ := by rw [← h.faithful]; exact (inf_eq_left.mpr hTC).symm
    have := h.four_le
    rw [hT1, Subgroup.card_bot] at this
    omega
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]; exact one_mem _
  obtain ⟨U, hUT, hU, htU⟩ := h.exists_isFourGroup_mem ht ht1
  exact (FactsL2.dihedral_cover_generation_holds H B U hBq hd hz (hUT.trans h.le_normalizer) hU
    (h.not_le_centralizerJoin hBX hUT)).2 htU

theorem Hyp46.false_of_sl2 [Finite H] [Finite F] (h : Hyp46 B T X) (e : B ≃* SL(2, F))
    (hF : Odd (Nat.card F)) : False := by
  by_cases h3 : Nat.card F = 3
  · exact h.false_of_sl2_three e h3
  · have h5 : 5 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rcases hF with ⟨m, hm⟩
      omega
    exact h.false_of_centralInv_mem e hF
      (h.centralInv_mem_of_le_sup e hF (h.le_sup_centralizer_of_sl2 e hF h5))

end CFSG.ComponentClassification.RankTwoOddLie
