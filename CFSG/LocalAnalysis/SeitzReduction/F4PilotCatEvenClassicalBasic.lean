module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

@[expose] def ClassicalOrSuzukiTag (t : StatedLieTag) : Prop :=
  t ∈ classicalTags ∨ t = .twistedB2

theorem classicalOrSuzukiTag_of_admissible {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hn : 1 ≤ n) : ClassicalOrSuzukiTag t := by
  obtain ⟨-, -, h⟩ := hadm
  cases t
  all_goals first
    | exact Or.inl (by decide)
    | exact Or.inr rfl
    | (exfalso; simp only at h; omega)

@[expose] def Sp6EvenTypeDet : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ), ClassicalOrSuzukiTag t →
    LieModel X .PSp 3 2 f → StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' →
      t = .PSp ∧ n = 3 ∧ f' = f

theorem sp6EvenTypeDet_of_forall
    (h : ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
      LieModel X .PSp 3 2 f → StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' →
        t = .PSp ∧ n = 3 ∧ f' = f) : Sp6EvenTypeDet :=
  fun X _ f t n f' _ h1 h2 h3 => h X f t n f' h1 h2 h3

@[expose] def NotSp6Components (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, IsPComponent 2 P →
    ∃ (t : StatedLieTag) (n f : ℕ), ClassicalOrSuzukiTag t ∧ StatedLieAdmissible t n 2 f ∧
      LieModel P t n 2 f ∧ ¬ (t = .PSp ∧ n = 3)

theorem notSp6Components_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : NotSp6Components Y) : NotSp6Components X := by
  intro P hP
  obtain ⟨t, n, f, hT, hadm, hm, hne⟩ :=
    h _ (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP)
  exact ⟨t, n, f, hT, hadm,
    LieType.CurtisTits.lieModel_of_mulEquiv (P.equivMapOfInjective e.toMonoidHom e.injective).symm
      hm, hne⟩

theorem notSp6Components_of_forall_not {X : Type} [Group X]
    (h : ∀ P : Subgroup X, ¬ IsPComponent 2 P) : NotSp6Components X :=
  fun P hP => absurd hP (h P)

theorem notSp6Components_of_isCharacteristicP {X : Type} [Group X] [Finite X]
    (h : IsCharacteristicP 2 X) : NotSp6Components X :=
  notSp6Components_of_forall_not
    (ComponentClassification.CatLeafProof.not_isPComponent_of_isCharacteristicP h)

theorem notSp6Components_of_isSimpleGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n f : ℕ} (hT : ClassicalOrSuzukiTag t) (hadm : StatedLieAdmissible t n 2 f)
    (hm : LieModel X t n 2 f) (hne : ¬ (t = .PSp ∧ n = 3)) : NotSp6Components X := by
  intro P hP
  have htop := ComponentClassification.GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hP
  exact ⟨t, n, f, hT, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hm, hne⟩

theorem two_dvd_card_of_lieModel_PSp_three_two {D : Type} [Group D] {f : ℕ}
    (h : LieModel D .PSp 3 2 f) : 2 ∣ Nat.card D := by
  have hf : 1 ≤ f := (statedClassicalModel_of_lieModel_psp h).1.2.1
  rw [card_of_lieModel_PSp_three_two h]
  exact Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _

theorem two_pow_nine_dvd_card_of_lieModel_PSp_three_two {D : Type} [Group D] {f : ℕ}
    (h : LieModel D .PSp 3 2 f) : 2 ^ 9 ∣ Nat.card D := by
  have hf : 1 ≤ f := (statedClassicalModel_of_lieModel_psp h).1.2.1
  rw [card_of_lieModel_PSp_three_two h]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 9) _

theorem isPComponent_of_isComponent_lieModel_PSp {X : Type} [Group X] [Finite X]
    {D : Subgroup X} (hD : IsComponent D) {f : ℕ} (hD6 : LieModel D .PSp 3 2 f) :
    IsPComponent 2 D := by
  refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hD fun hle => ?_
  have h2 : 2 ∣ Nat.card (pPrimeCore 2 X) :=
    (two_dvd_card_of_lieModel_PSp_three_two hD6).trans (Subgroup.card_dvd_of_le hle)
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)

theorem false_of_notSp6Components (hdet : Sp6EvenTypeDet) {X : Type} [Group X] [Finite X]
    (h : NotSp6Components X) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hD6 : LieModel D .PSp 3 2 f) : False := by
  obtain ⟨t, n, f', hT, hadm, hm, hne⟩ := h D (isPComponent_of_isComponent_lieModel_PSp hD hD6)
  obtain ⟨ht, hn, -⟩ := hdet D f t n f' hT hD6 hadm hm
  exact hne ⟨ht, hn⟩

theorem eq_top_of_isComponent_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    {D : Subgroup X} (hD : IsComponent D) : D = ⊤ := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hD.2 with h | h
  · exfalso
    have hnt : Nontrivial D := LocalCores.isQuasisimple_nontrivial hD.1
    rw [h] at hnt
    exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
  · exact h

theorem sp6_of_isComponent_statedSp (hdet : Sp6EvenTypeDet) {X : Type} [Group X] [Finite X]
    {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hD6 : LieModel D .PSp 3 2 f) : r = 3 ∧ g = f ∧ LieModel X .PSp 3 2 f := by
  have hg : 1 ≤ g := by
    by_contra h0
    have hk1 : Nat.card k = 1 := by rw [hk, show g = 0 by omega, pow_zero]
    exact absurd hk1 (ne_of_gt Finite.one_lt_card)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have hcardX : Nat.card X = Nat.card k ^ (r ^ 2) *
      ∏ j ∈ Finset.Icc 1 r, (Nat.card k ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv]
    exact LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r
  have h29 : 2 ^ 9 ∣ Nat.card X :=
    (two_pow_nine_dvd_card_of_lieModel_PSp_three_two hD6).trans (Subgroup.card_subgroup_dvd_card D)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at h29
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd h29 (by decide)
    · exact absurd h29 (by decide)
  obtain ⟨t, r', hr', hX, hadm, hm, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ), 1 ≤ r' ∧
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g ∧
        (t = .PSp → r' = r) := by
    rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
    · have hg2 : 2 ≤ g := by omega
      obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := k)
      have h4 : 4 ≤ 2 ^ g :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hadm : StatedLieAdmissible .PSL 2 2 g := ⟨Nat.prime_two, hg, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel X .PSL 2 2 g :=
        ⟨hadm, k, inferInstance, inferInstance, hk,
          ⟨(Φ.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm).trans
            e₂⟩⟩
      exact ⟨.PSL, 2, by norm_num, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩, fun h => absurd h (by decide)⟩
    · have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
        · exact Or.inr (Or.inr ⟨by rw [hk, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        small_standard_source_even_simple_symplectic_parameters_stated (X := StatedSp r k) hk
          (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, by omega, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        fun _ => rfl⟩
  have hDtop := eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  obtain ⟨htt, hr3, hgf⟩ := hdet D f t r' g (classicalOrSuzukiTag_of_admissible hadm hr') hD6 hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hm)
  have hrr := ht htt
  subst htt
  refine ⟨hrr ▸ hr3, hgf, LieType.CurtisTits.lieModel_of_mulEquiv eD hD6⟩

@[expose] def SpFixedOrNotSp6 (X : Type) [Group X] (R : ℕ → ℕ → Prop) : Prop :=
  (∃ (k : Type) (_ : Field k) (_ : Finite k) (r g : ℕ), Nat.card k = 2 ^ g ∧ 1 ≤ r ∧ R r g ∧
      Nonempty (X ≃* StatedSp r k)) ∨ NotSp6Components X

theorem spFixedOrNotSp6_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {R : ℕ → ℕ → Prop} (h : SpFixedOrNotSp6 Y R) : SpFixedOrNotSp6 X R := by
  rcases h with ⟨k, _, _, r, g, hk, hr, hR, ⟨Φ⟩⟩ | h
  · exact Or.inl ⟨k, inferInstance, inferInstance, r, g, hk, hr, hR, ⟨e.trans Φ⟩⟩
  · exact Or.inr (notSp6Components_of_mulEquiv e h)

theorem sp6_of_spFixedOrNotSp6 (hdet : Sp6EvenTypeDet) {X : Type} [Group X] [Finite X]
    {R : ℕ → ℕ → Prop} (h : SpFixedOrNotSp6 X R) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hD6 : LieModel D .PSp 3 2 f) : R 3 f ∧ LieModel X .PSp 3 2 f := by
  rcases h with ⟨k, _, _, r, g, hk, hr, hR, ⟨Φ⟩⟩ | h
  · obtain ⟨rfl, rfl, hX⟩ := sp6_of_isComponent_statedSp hdet hk hr Φ hD hD6
    exact ⟨hR, hX⟩
  · exact (false_of_notSp6Components hdet h hD hD6).elim

end CFSG.SeitzReduction.F4Pilot
