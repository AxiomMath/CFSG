module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnClassical
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutFixed

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.GLTheoremA.TriD4 CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement
open CFSG.LieType.Chevalley (fixSubfield)

theorem not_isD42Type_primeFormP {n f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    ¬ IsCatalogLieIso (primeFormP h (idGram K n)) IsD42Index := by
  intro hD
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n))
  let e : primeFormP h (idGram K n) ≃* StatedProj (StatedSU n (2 ^ f) K) :=
    eP.trans (unitaryPSUEquiv h (by omega))
  obtain ⟨-, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := f) h.card_eq_sq hn (fun hc => hq (Prod.mk_inj.1 hc))
  let eZ := QuotientGroup.quotientMulEquivOfEq hZ
  have hc : Nat.card (↥(StatedSU n (2 ^ f) K) ⧸
      Subgroup.center ↥(StatedSU n (2 ^ f) K)) = 174182400 := by
    rw [Nat.card_congr eZ.toEquiv]
    exact card_of_isD42Type (IsCatalogLieIso.of_mulEquiv e hD)
  exact card_centerQuot_su_ne hn h.one_le rfl
    (fun hc => hq (Prod.mk_inj.1 hc)) h.card_eq_sq (MulEquiv.refl _) hc

theorem not_upD42Pumpup_primeFormD {q : TauCeti.PrimePower} {r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData q.p q.exponent K) (hr : 3 ≤ r + 1)
    (hq : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2)) (hp : q.p = 2)
    {β : MulAut (primeFormP h (idGram K (r + 1)))}
    (hβ : β ∈ primeFormD h (idGram K (r + 1))) :
    ¬ UpD42Pumpup (primeFormP h (idGram K (r + 1))) β := by
  intro hx
  haveI := h.finite
  have hlayer := perfectInLayer_primeFormP h hr hq Nat.prime_three
    (by norm_num) (by omega) β hx.1
  exact not_upD42Pumpup_of_componentsNoD4 hlayer
    (componentsNoD4_primeFormP_diag h hr hp hβ hx.1) hx

theorem not_upD42Pumpup_primeFormFieldHom {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hℓ : ℓ = 2)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ¬ UpD42Pumpup (primeFormP h (idGram K n))
      (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  intro hx
  subst ℓ
  classical
  haveI := h.finite
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  let h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ
  let j := primeSubfieldPSU h hp hp2 hσ n
  have hinj : Function.Injective j := subfieldPSU_injective h h₀ hbar n (by omega)
  have hJC : j.range ≤ fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :=
    range_subfieldPSU_le h n h₀ hbar
  have hCC := commutator_fixed_le_range (n := n) h hσ
  let eJ : primeFormP h₀ (idGram (fixSubfield σ) n) ≃* ↥j.range :=
    MonoidHom.ofInjective hinj
  by_cases hq0 : n = 3 ∧ 2 ^ (f / 3) = 2
  · obtain ⟨rfl, hq2⟩ := hq0
    have hcard72 := card_primeFormP_three_two h₀ hq2
    haveI : Group.IsSolvable (primeFormP h₀ (idGram (fixSubfield σ) 3)) :=
      CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg.isSolvable_of_card_dvd_seventy_two
        (by rw [hcard72])
    haveI : Group.IsSolvable ↥j.range :=
      Group.isSolvable_of_isSolvable_injective (f := eJ.symm.toMonoidHom) eJ.symm.injective
    obtain ⟨-, -, I, hI, -⟩ := hx
    have hIJ : I ≤ j.range := by
      calc I = ⁅I, I⁆ := (glaPComponent_perfect hI).symm
        _ ≤ _ := Subgroup.commutator_mono hI.1 hI.1
        _ ≤ j.range := hCC
    haveI : Group.IsSolvable ↥I :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hIJ)
    haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hI)
    haveI : Nontrivial ↥I :=
      (Subgroup.nontrivial_iff_ne_bot I).mpr (Lemma510Ns.glaPComponent_ne_bot hI)
    exact Group.IsPerfect.not_isSolvable ↥I inferInstance
  · haveI hs₀ := isSimpleGroup_primeFormP_one h₀ hn hq0
    have hsJ : IsSimpleGroup ↥j.range := eJ.symm.isSimpleGroup
    have hnab₀ : ∃ a b : primeFormP h₀ (idGram (fixSubfield σ) n), a * b ≠ b * a := by
      have hnc := not_commute_primeFormP_one h₀ hn hq0
      push Not at hnc
      exact hnc
    have hnabJ : ∃ a b : ↥j.range, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab₀
      refine ⟨eJ a, eJ b, fun he => hab ?_⟩
      exact eJ.injective (by simpa only [map_mul] using he)
    have hD := isD42Type_of_upD42Pumpup_of_simple_normal_comm hx j.range hJC hCC hsJ hnabJ
    exact not_isD42Type_primeFormP h₀ hn hq0 (IsCatalogLieIso.of_mulEquiv eJ.symm hD)

theorem upD42Chev2Out_unitary_holds : UpD42Chev2Out
    (fun d => match d with | .twistedA _ _ => True | _ => False) := by
  intro S _ _ _ _ ⟨d, hv⟩ hF hc ⟨e⟩ α _ hx
  cases d with
  | twistedA r q =>
    let d : TauCeti.ValidLieTypeIndex := ⟨.twistedA r q, hv⟩
    obtain ⟨r', q', K, _, hU, hr, hd, hne, ⟨eP⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx
        (d := d) trivial
    have hp : q'.p = 2 := by
      rw [← TauCeti.LieTypeIndex.characteristic_twistedA r' q', ← hd]
      simpa only [d, TauCeti.LieTypeIndex.characteristic_twistedA] using (show q.p = 2 from hc)
    have hq : ¬(r' + 1 = 3 ∧ q'.p ^ q'.exponent = 2) := fun h =>
      hne ⟨h.1, (TauCeti.PrimePower.card_def q').trans h.2⟩
    let e' : S ≃* primeFormP hU (idGram K (r' + 1)) := e.trans eP.symm
    haveI := hU.finite
    have hx' := hx.congr e'
    let β := MulAut.congr e' α
    by_cases hσ : primeFormFieldFactor hU (isPrimeFormGram_one (n := r' + 1))
        (by omega) hq β = 1
    · have hβ : β ∈ primeFormD hU (idGram K (r' + 1)) := by
        rw [← ker_primeFormFieldFactor hU isPrimeFormGram_idGram (by omega) hq]
        exact hσ
      exact (not_upD42Pumpup_primeFormD hU (by omega) hq hp hβ hx').elim
    · obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one hU
        (by omega) hq hx'.1 hσ
      have he : MulAut.congr u⁻¹ (MulAut.congr e' α) =
          primeFormFieldHom hU isPrimeFormGram_idGram σ := by
        rw [hu]
        ext x
        simp [MulAut.congr_apply, MulAut.mul_apply]
      have hx'' := hx'.congr u⁻¹
      rw [he] at hx''
      exact (not_upD42Pumpup_primeFormFieldHom hU (by omega) hp hσord hx'').elim
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
