module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
import CFSG.Adapters.StatedPSLTwoNine

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.Assembly.LowTwoRank

theorem center_specialLinear_two_eq_bot (K : Type) [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hA⟩ := hA
  have h1 : r = 1 := by
    have h2 : (r - 1) ^ 2 = 0 := by
      have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have hr2 : r ^ 2 = 1 := by simpa using hr
      calc (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        _ = 0 := by rw [h20, hr2]; ring_nf; simpa using h20
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)
  subst h1
  apply Subtype.ext
  rw [← hA]
  simp

noncomputable def statedProjSL_two_equiv (K : Type) [Field K] [CharP K 2] :
    StatedProj (StatedSL 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_specialLinear_two_eq_bot K))).trans
    QuotientGroup.quotientBot

noncomputable def ringEquivZMod2 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    K ≃+* ZMod 2 := by
  letI : Fintype K := Fintype.ofFinite K
  exact FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK]; simp)

noncomputable def specialLinearEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (n : ℕ)
    (f : R ≃+* S) : Matrix.SpecialLinearGroup (Fin n) R ≃* Matrix.SpecialLinearGroup (Fin n) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map f.toRingHom)
    (Matrix.SpecialLinearGroup.map f.symm.toRingHom)
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem center_specialLinear_eq_bot_of_card_two (n : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hA⟩ := hA
  have hall : ∀ r : K, r = 0 ∨ r = 1 := by
    classical
    have : Fintype K := Fintype.ofFinite K
    have hc : ({0, 1} : Finset K).card = Fintype.card K := by
      rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
    intro r
    have h := Finset.eq_univ_of_card _ hc
    have hr' : r ∈ ({0, 1} : Finset K) := h ▸ Finset.mem_univ r
    simpa using hr'
  apply Subtype.ext
  rw [← hA]
  rcases hall r with rfl | rfl
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · ext i j
      exact i.elim0
    · exfalso
      rw [Fintype.card_fin, zero_pow hn.ne'] at hr
      exact zero_ne_one hr
  · simp

noncomputable def statedProjSL_equiv_of_card_two (n : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    StatedProj (StatedSL n K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  (((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_specialLinear_eq_bot_of_card_two n K hK))).trans
    QuotientGroup.quotientBot).trans (specialLinearEquivOfRingEquiv n (ringEquivZMod2 K hK))

theorem specialLinear_two_equiv_alternating_five
    (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := 2)
    (by rw [hK]; norm_num)
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl hK)
  exact ⟨(statedProjSL_two_equiv K).symm.trans e⟩

theorem alternating_five_of_model_five {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 5 1) : Nonempty (S ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr (by simpa using hK))
  exact ⟨e.trans e'⟩

theorem alternating_six_of_model_nine {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 3 2) : Nonempty (S ≃* alternatingGroup (Fin 6)) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine h

end CFSG.QuasithinUnique.Setup.Family
