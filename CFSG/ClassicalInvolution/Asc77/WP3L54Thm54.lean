module

public import CFSG.ClassicalInvolution.Asc77.WP3L54Thm53

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

namespace Lemma54Proof

section Alpha

variable {G : Type} [Group G] [Finite G] {B A D : Subgroup G}

omit [Finite G] in
theorem alphaOf_eq (A : Subgroup G) :
    alphaOf A = (⨆ a ∈ A, ⨆ (_ : a ≠ 1), ⁅involutionOddCore a, A⁆) ⊔ deltaCore A := rfl

omit [Finite G] in
theorem centralizer_le_singleton {d : G} (hd : d ∈ D) :
    Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({d} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd)

theorem commutator_eq_iSup_centralizer {J : Subgroup G} (hDel : IsElemAbelian 2 D)
    (hD4 : Nat.card D = 4) (hDJ : D ≤ Subgroup.normalizer (J : Set G)) (hJ : Odd (Nat.card J)) :
    ⁅J, D⁆ = ⨆ d ∈ D, ⨆ (_ : d ≠ 1), ⁅J ⊓ Subgroup.centralizer ({d} : Set G), D⁆ := by
  have hDp : IsPGroup 2 D := isPGroup_two hDel
  have hgen := CFSG.SignalizerFunctor.Helpers.solvable_normalized_order_fixed_commutator_generation
    2 1 2 Nat.prime_two Nat.prime_two D D J hDel (by rw [hD4]; norm_num) hDp
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hJ) hDJ hDJ
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hDel.1.is_comm.comm (⟨y, hy⟩ : D) ⟨x, hx⟩))
    (Nat.coprime_two_left.mpr hJ) (Nat.coprime_two_left.mpr hJ)
  rw [hgen]
  apply le_antisymm
  · refine iSup₂_le fun S hS => ?_
    obtain ⟨d, hdS, hd1⟩ := CFSG.SignalizerFunctorTheorem.exists_ne_one_of_mem_E1 Nat.prime_two hS
    have hzp : Subgroup.zpowers d = S :=
      CFSG.SignalizerFunctorTheorem.eq_zpowers_of_card_eq_prime Nat.prime_two
        (by rw [hS.2, pow_one]) hdS hd1
    rw [← hzp, CFSG.SignalizerFunctorTheorem.centralizer_zpowers]
    exact le_iSup₂_of_le d (hS.1 hdS) (le_iSup_of_le hd1 le_rfl)
  · refine iSup₂_le fun d hd => iSup_le fun hd1 => ?_
    have hz := CFSG.SignalizerFunctorTheorem.zpowers_mem_E1 Nat.prime_two hDel hd hd1
    refine le_iSup₂_of_le (Subgroup.zpowers d) hz ?_
    rw [CFSG.SignalizerFunctorTheorem.centralizer_zpowers]

theorem commutator_involutionOddCore_le_alphaOf (hR : RankThreeBalance B) (hAB : A ≤ B)
    (hDB : D ≤ B) (hD4 : Nat.card D = 4) {α : G} (hα : α ∈ B) (hα1 : α ≠ 1) :
    ⁅involutionOddCore α, A⁆ ≤ alphaOf D := by
  have hB := hR.elem
  have hcomm := comm_of_isElemAbelian hB
  have hAel : IsElemAbelian 2 A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hAB
  have hDel : IsElemAbelian 2 D :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hDB
  have hAp : IsPGroup 2 A := isPGroup_two hAel
  have hDp : IsPGroup 2 D := isPGroup_two hDel
  have hBO := le_normalizer_involutionOddCore hB hα
  have hOodd : Odd (Nat.card (involutionOddCore α)) :=
    odd_card_oddCoreIn (Subgroup.centralizer ({α} : Set G))
  have hAO : A ≤ Subgroup.normalizer (involutionOddCore α : Set G) := fun x hx => hBO (hAB hx)
  have hJB := le_normalizer_commutator hB hAB hα
  set J : Subgroup G := ⁅involutionOddCore α, A⁆ with hJ
  have hJle : J ≤ involutionOddCore α := commutator_le_self hAO
  have hJodd : Odd (Nat.card J) := hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hJle)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := fun x hx => hJB (hAB hx)
  have hDJ : D ≤ Subgroup.normalizer (J : Set G) := fun x hx => hJB (hDB hx)
  have hJA : ⁅J, A⁆ = J := commutator_commutator_eq hAp hAO hOodd
  have hAJD : A ≤ Subgroup.normalizer ((⁅J, D⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_commutator (hAJ hx) (le_normalizer_of_le hcomm hDB (hAB hx))
  have hF7 : ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆ ≤ deltaCore D := by
    refine le_deltaCore fun d hd hd1 => ?_
    calc ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆
        ≤ ⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), B⁆ :=
          Subgroup.commutator_mono (le_inf (inf_le_left.trans hJle)
            (inf_le_right.trans (centralizer_le_singleton hd))) hAB
      _ ≤ involutionOddCore d := hR.weak α hα hα1 d (hDB hd) hd1
  have hF8 : ⁅J, D⁆ ≤ alphaOf D := by
    rw [commutator_eq_iSup_centralizer hDel hD4 hDJ hJodd]
    refine iSup₂_le fun d hd => iSup_le fun hd1 => ?_
    have hdC : ∀ x ∈ B, x ∈ Subgroup.centralizer ({d} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx d (hDB hd))
    have hZB : B ≤ Subgroup.normalizer
        ((involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_inf (hBO hx) (Subgroup.le_normalizer (hdC x hx))
    have hDZ := fun x (hx : x ∈ D) => hZB (hDB hx)
    have hZodd : Odd (Nat.card
        (involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G)) :=
      hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have h1 : ⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), D⁆ ≤
        involutionOddCore d :=
      (Subgroup.commutator_mono le_rfl hDB).trans (hR.weak α hα hα1 d (hDB hd) hd1)
    calc ⁅J ⊓ Subgroup.centralizer ({d} : Set G), D⁆
        ≤ ⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), D⁆ :=
          Subgroup.commutator_mono (le_inf (inf_le_left.trans hJle) inf_le_right) le_rfl
      _ = ⁅⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), D⁆, D⁆ :=
          (commutator_commutator_eq hDp hDZ hZodd).symm
      _ ≤ ⁅involutionOddCore d, D⁆ := Subgroup.commutator_mono h1 le_rfl
      _ ≤ alphaOf D := commutator_le_alphaOf D hd hd1
  have hJQ : J ≤ ⁅J, D⁆ ⊔ ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆ := by
    calc J = ⁅J, A⁆ := hJA.symm
      _ ≤ ⁅J, D⁆ ⊔ ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆ := by
        rw [Subgroup.commutator_le]
        intro j hj a ha
        obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem hDp hDJ hJodd hj
        have e : ⁅p * q, a⁆ = p * ⁅q, a⁆ * (a * p⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hp)
          (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq ha)))
          (Subgroup.mem_sup_left ?_)
        exact (Subgroup.mem_normalizer_iff.mp (hAJD ha) p⁻¹).mp ((⁅J, D⁆).inv_mem hp)
  exact hJQ.trans (sup_le hF8 (hF7.trans (iInf_le_alphaOf D)))

theorem deltaCore_le_alphaOf (hR : RankThreeBalance B) (hAB : A ≤ B) (hDB : D ≤ B)
    (hA4 : Nat.card A = 4) (hD4 : Nat.card D = 4) : deltaCore A ≤ alphaOf D := by
  have hB := hR.elem
  have hDel : IsElemAbelian 2 D :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hDB
  have hDp : IsPGroup 2 D := isPGroup_two hDel
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_inf hR.card hA4 hD4 hAB hDB
  have hDK : D ≤ Subgroup.normalizer ((deltaCore A : Subgroup G) : Set G) := fun x hx =>
    normalizer_deltaCore hB.1 hAB (hDB hx)
  have hKodd : Odd (Nat.card (deltaCore A)) := odd_card_deltaCore hz.1 hz1
  refine (commutator_sup_centralizer hDp hDK hKodd).symm.le.trans (sup_le ?_ ?_)
  · exact (Subgroup.commutator_mono (deltaCore_le_involutionOddCore hz.1 hz1) le_rfl).trans
      (commutator_le_alphaOf D hz.2 hz1)
  · refine (le_deltaCore fun d hd hd1 => ?_).trans (iInf_le_alphaOf D)
    calc deltaCore A ⊓ Subgroup.centralizer (D : Set G)
        ≤ deltaCore A ⊓ Subgroup.centralizer ({d} : Set G) :=
          inf_le_inf_left _ (centralizer_le_singleton hd)
      _ ≤ involutionOddCore d := hR.two A ⟨hAB, by rw [hA4]; norm_num⟩ d (hDB hd) hd1

theorem alphaOf_le_alphaOf_of_rankThreeBalance (hR : RankThreeBalance B) (hAB : A ≤ B)
    (hDB : D ≤ B) (hA4 : Nat.card A = 4) (hD4 : Nat.card D = 4) : alphaOf A ≤ alphaOf D := by
  rw [alphaOf_eq A]
  exact sup_le (iSup₂_le fun a ha => iSup_le fun ha1 =>
    commutator_involutionOddCore_le_alphaOf hR hAB hDB hD4 (hAB ha) ha1)
    (deltaCore_le_alphaOf hR hAB hDB hA4 hD4)

theorem alphaOf_le_uCore (hR : RankThreeBalance B) (hAB : A ≤ B) (hA4 : Nat.card A = 4) :
    alphaOf A ≤ uCore A := by
  rw [alphaOf_eq A]
  refine sup_le (iSup₂_le fun a ha => iSup_le fun ha1 => ?_) ?_
  · exact (commutator_le_involutionOddCore hR.elem hAB (hAB ha)).trans
      (involutionOddCore_le_uCore ha ha1)
  · obtain ⟨z, hz, hz1⟩ := exists_ne_one_of_card_eq_two_pow (S := A) (n := 2) (by norm_num)
      (by rw [hA4]; norm_num)
    exact deltaCore_le_uCore hz hz1

end Alpha

end Lemma54Proof

section Lemma54

open Lemma54Proof

variable {G : Type} [Group G] [Finite G] {B A D : Subgroup G}

theorem alphaOf_eq_alphaOf_of_rankThreeBalance (hR : RankThreeBalance B) (hAB : A ≤ B)
    (hDB : D ≤ B) (hA4 : Nat.card A = 4) (hD4 : Nat.card D = 4) : alphaOf A = alphaOf D :=
  le_antisymm (alphaOf_le_alphaOf_of_rankThreeBalance hR hAB hDB hA4 hD4)
    (alphaOf_le_alphaOf_of_rankThreeBalance hR hDB hAB hD4 hA4)

theorem odd_card_alphaOf_of_rankThreeBalance (hR : RankThreeBalance B) (hAB : A ≤ B)
    (hA4 : Nat.card A = 4) : Odd (Nat.card (alphaOf A)) :=
  (odd_card_iSup_involutionOddCore hR.elem hR.card.ge hR.weak hAB).of_dvd_nat
    (Subgroup.card_dvd_of_le (alphaOf_le_uCore hR hAB hA4))

@[expose] def Lemma54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G), Hyp51 B → ∀ A D : Subgroup G, A ≤ B →
    D ≤ B → IsElemAbelian2 A 2 → IsElemAbelian2 D 2 →
      alphaOf A = alphaOf D ∧ Odd (Nat.card ↥(alphaOf A))

theorem lemma54 : Lemma54 := fun _ _ _ B hB _ _ hAB hDB hA hD =>
  ⟨alphaOf_eq_alphaOf_of_rankThreeBalance (lemma52 _ B hB) hAB hDB hA.1 hD.1,
    odd_card_alphaOf_of_rankThreeBalance (lemma52 _ B hB) hAB hA.1⟩

theorem lemma54_odd_and_eq {B D : Subgroup G} (hB : Hyp51 B) (hDB : D ≤ B)
    (hD : IsElemAbelian2 D 2) :
    Odd (Nat.card ↥(alphaOf D)) ∧
      ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = alphaOf D :=
  ⟨(lemma54 G B hB D D hDB hDB hD hD).2,
    fun A hAB hA => (lemma54 G B hB A D hAB hDB hA hD).1⟩

end Lemma54

end CFSG.ClassicalInvolution.Asc77
