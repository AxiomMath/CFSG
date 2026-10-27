module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eExc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eUni
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwMain

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

@[expose] def FamCases (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t n p f →
    Blueprint.LieModel X t n p f → ∀ g : X, orderOf (MulAut.conj g) = 2 →
      ∀ L : Subgroup (fixedSubgroup (MulAut.conj g)), IsComponent L →
        NoSpin7 p L ∨ ∃ (τ : StatedLieTag) (m e : ℕ), ¬ (τ = .POmegaOdd ∧ m = 3) ∧
          StatedLieAdmissible τ m p e ∧ Blueprint.LieModel (↥L ⧸ center ↥L) τ m p e

theorem FamNoSpin7.famCases {t : StatedLieTag} (h : FamNoSpin7 t) : FamCases t :=
  fun X _ n p f hp hp2 hadm hX g hg L hL => Or.inl (h X n p f hp hp2 hadm hX g hg L hL)

theorem FamCases.famNoSpin7 (hO : LieOrderFormulasInput) {t : StatedLieTag} (h : FamCases t) :
    FamNoSpin7 t := by
  intro X _ n p f hp hp2 hadm hX g hg L hL
  have : Finite X := (hO X t n p f hadm hX).1
  have : Group.IsPerfect L := hL.1.1
  rcases h X n p f hp hp2 hadm hX g hg L hL with h | ⟨τ, m, e, hτ, hadm', hLM⟩
  · exact h
  · exact noSpin7_of_lieModel_ne hO hp2 hadm' hLM hτ

theorem famNoSpin7_of_char_two {t : StatedLieTag}
    (ht : ∀ n p f, StatedLieAdmissible t n p f → p = 2) : FamNoSpin7 t :=
  fun _ _ n p f _ hp2 hadm => absurd (ht n p f hadm) hp2

theorem admissible_of_lieModel_any {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : Blueprint.LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem orderOf_conj_eq_two {X : Type} [Group X] (hZ : center X = ⊥) {z : X}
    (hz : orderOf z = 2) : orderOf (MulAut.conj z) = 2 := by
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  · have hzc : z ∈ center X := by
      rw [mem_center_iff]
      intro g
      have h2 := congrArg (fun α : MulAut X => α g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [hZ, mem_bot] at hzc
    rw [hzc, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem centralizer_eq_fixedSubgroup {X : Type} [Group X] (z : X) :
    centralizer ({z} : Set X) = FixedCommutingProduct.fixedSubgroup (MulAut.conj z) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change _ ↔ MulAut.conj z x = x
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem not_isCoverOf_of_famCases
    (hPSp : FamCases .PSp) (hOdd : FamCases .POmegaOdd) (hPlus : FamCases .POmegaPlus)
    (hMinus : FamCases .POmegaMinus) (X : Type) [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsSimpleChevalleyOver p X) {z : X} (hz : orderOf z = 2)
    {J : Subgroup X} (hJ : IsTwoComponentIn J (centralizer {z})) {r : ℕ} (hr : 1 ≤ r) :
    ¬ IsCoverOf .POmegaOdd 3 p r 2 (↥J ⧸ pPrimeCore 2 ↥J) := by
  have hO : LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  obtain ⟨τ, n, f, hm⟩ := hX
  have hadm := admissible_of_lieModel_any hm
  have hfam : FamNoSpin7 τ := by
    cases τ with
    | PSL => exact famNoSpin7_psl hO
    | PSU => exact famNoSpin7_psu hO
    | PSp => exact hPSp.famNoSpin7 hO
    | POmegaOdd => exact hOdd.famNoSpin7 hO
    | POmegaPlus => exact hPlus.famNoSpin7 hO
    | POmegaMinus => exact hMinus.famNoSpin7 hO
    | G2 => exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_G2_holds
    | F4 => exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_F4_holds
    | E6 => exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_E6_holds
    | E7 => exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_E7_holds
    | E8 => exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_E8_holds
    | twistedE6 =>
      exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_twistedE6_holds
    | trialityD4 =>
      exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_trialityD4
    | twistedG2 => exact famNoSpin7_of_excFamilyModel hO Burgoyne.X10.excFamilyModel_twistedG2
    | twistedB2 => exact famNoSpin7_of_char_two fun _ _ _ h => h.2.2.2.1
    | twistedF4 => exact famNoSpin7_of_char_two fun _ _ _ h => h.2.2.2.1
    | Tits => exact famNoSpin7_of_char_two fun _ _ _ h => h.2.2.2.1
  obtain ⟨hJA, hsub, hJq⟩ := hJ
  have hna : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJq.2.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun h => hab ?_⟩
    have h' : a * b = b * a := Subtype.ext h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, h']
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      have hb : b ∈ center X := by
        rw [h]
        exact mem_top b
      exact absurd (mem_center_iff.1 hb a) hab
  have hz2 := orderOf_conj_eq_two hZ hz
  have hCF := centralizer_eq_fixedSubgroup z
  set F := FixedCommutingProduct.fixedSubgroup (MulAut.conj z) with hF
  have hJF : J ≤ F := hCF ▸ hJA
  have hsub' : (J.subgroupOf F).IsSubnormal := hCF ▸ hsub
  have hJ' : IsTwoComponentIn J F := ⟨hJF, hsub', hJq⟩
  have hP2 := (isTwoComponentIn_iff hJF).1 hJ'
  have hB := fixedTwoComponentsQuasisimple_of_oddLieType hna ⟨τ, n, p, f, hp, hp2, hadm, hm⟩
  have hc2 : MulAut.conj z * MulAut.conj z = 1 := by
    rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hc1 : MulAut.conj z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hLq : IsQuasisimple ↥(J.subgroupOf F) := hB (MulAut.conj z) hc2 hc1 _ hP2
  have hLc : IsComponent (J.subgroupOf F) := ⟨hLq, hsub'⟩
  have hN : NoSpin7 p ↥(J.subgroupOf F) := hfam X n p f hp hp2 hadm hm z hz2 _ hLc
  exact not_isCoverOf_of_noSpin7
    (LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJF) hLq)
    (NoSpin7.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJF).symm hN) hr

theorem harris82Lemma51e_of_famCases
    (hPSp : FamCases .PSp) (hOdd : FamCases .POmegaOdd) (hPlus : FamCases .POmegaPlus)
    (hMinus : FamCases .POmegaMinus) : Harris82Lemma51e := by
  intro X _ _ _ p hp hp2 hX z hz J hJ _ r h5
  refine not_isCoverOf_of_famCases hPSp hOdd hPlus hMinus X hp hp2 hX hz hJ ?_
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · rw [h0, pow_zero] at h5
    omega
  · exact h0

end CFSG.ComponentClassification.HarrisLit.T1.P51e
