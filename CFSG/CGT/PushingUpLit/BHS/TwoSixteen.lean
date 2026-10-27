module

public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.Offender
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

theorem isQuasisimple_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 : (commutator A).map e.toMonoidHom = commutator B := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [← h1, hperf]
    exact Subgroup.map_top_of_surjective _ e.surjective
  · have hc : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
      Subgroup.map_center_eq e
    have := hsimple
    exact (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hc).symm.isSimpleGroup

theorem commutator_eq_top_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ IsMulCommutative G) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h0 | h1
  · exfalso
    apply h
    refine ⟨⟨fun a b => ?_⟩⟩
    have : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h1

theorem isQuasisimple_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    CFSG.Open.IsQuasisimple (alternatingGroup (Fin n)) := by
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup hcard
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin n)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
    omega
  have hcen : Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (alternatingGroup (Fin n))) with h | h
    · exact h
    · exfalso
      apply hnc
      exact ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm⟩⟩
  refine ⟨commutator_eq_top_of_simple_nonabelian hnc, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientBot (G := alternatingGroup (Fin n)))).symm.symm.isSimpleGroup

theorem isQuasisimple_special_linear_two {F : Type*} [Field F]
    (h4 : ∃ s : Finset F, s.card = 4) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h4)
  exact ⟨Group.isPerfect_def.mp hperf, hsimple⟩

theorem offender_le_normalizer_of_isComponentOf {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G A E : Subgroup (MulAut V)} (hA : IsOff A) (hAG : A ≤ G)
    (hE : CFSG.Open.IsComponentOf E G) : A ≤ Subgroup.normalizer (E : Set (MulAut V)) :=
  CFSG.Quasithin.B15P4.asB15Part4 V hV G A (offender_iff.mpr ⟨hAG, hA⟩) E hE

theorem two_sixteen_a_alt {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 2 ≤ m) {G A E : Subgroup (MulAut V)} {P Z : Subgroup V} (hA : IsOff A) (hAG : A ≤ G)
    (hEG : E ≤ G) (hsub : CFSG.Open.IsSubnormal E G) (hnat : IsAltNatSection E P Z (2 * m + 1)) :
    A ≤ Subgroup.normalizer (E : Set (MulAut V)) := by
  obtain ⟨-, θ, -⟩ := hnat
  have hq : CFSG.Open.IsQuasisimple ↥E :=
    isQuasisimple_of_mulEquiv' θ.symm (isQuasisimple_alternatingGroup (by omega))
  exact offender_le_normalizer_of_isComponentOf hV hA hAG ⟨hEG, hsub, hq⟩

theorem exists_finset_card_four_galoisField {k : ℕ} (hk : 2 ≤ k) :
    ∃ s : Finset (GaloisField 2 k), s.card = 4 := by
  have := Fintype.ofFinite (GaloisField 2 k)
  have hcard : Fintype.card (GaloisField 2 k) = 2 ^ k := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 k (by omega)
  have h4 : 4 ≤ (Finset.univ : Finset (GaloisField 2 k)).card := by
    rw [Finset.card_univ, hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  exact ⟨s, hs⟩

theorem two_sixteen_a_sl {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ}
    (hk : 2 ≤ k) {G A E : Subgroup (MulAut V)} {P Z : Subgroup V} (hA : IsOff A) (hAG : A ≤ G)
    (hEG : E ≤ G) (hsub : CFSG.Open.IsSubnormal E G) (hnat : IsSLNatSection E P Z k) :
    A ≤ Subgroup.normalizer (E : Set (MulAut V)) := by
  obtain ⟨-, θ, -⟩ := hnat
  have hq : CFSG.Open.IsQuasisimple ↥E :=
    isQuasisimple_of_mulEquiv' θ.symm
      (isQuasisimple_special_linear_two (exists_finset_card_four_galoisField hk))
  exact offender_le_normalizer_of_isComponentOf hV hA hAG ⟨hEG, hsub, hq⟩

end CFSG.CGT.PushingUpLit.BHS
