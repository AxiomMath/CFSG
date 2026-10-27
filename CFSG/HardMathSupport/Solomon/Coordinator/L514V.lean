module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.CycThree
import CFSG.GH74.KGroups.L3EpsLin
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

@[expose, reducible, deprecated innAutDerivedVocab (since := "2026-10-15")]
noncomputable def coordInndiagVocab : InndiagVocab := innAutDerivedVocab

@[deprecated "use `commutator_le_innAutDerived`" (since := "2026-10-15")]
theorem commutator_le_coordInndiagVocab (Y : Type) [Group Y] :
    commutator (MulAut Y) ≤ innAutDerivedVocab.innDiag Y :=
  commutator_le_innAutDerived Y

section Dichotomy

theorem dichotomy_of_model {Y M C : Type} [Group Y] [Group M] [Group C] [IsCyclic C] [Finite C]
    (e : Y ≃* M) (P : PinnedAut M) (hP : GoodPinned P) (fld : C →* MulAut M)
    (h3 : ∀ β : MulAut M, β ^ 3 = 1 → ∃ d ∈ P.inndiag, ∃ c : C, β = d * fld c)
    (α β : MulAut Y) (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) :
    α ∈ commutator (MulAut Y) ∨ ∃ j : ℕ, β * α ^ j ∈ commutator (MulAut Y) := by
  set q : MulAut M →* Abelianization (MulAut M) := Abelianization.of with hq
  set R : Subgroup (Abelianization (MulAut M)) := (q.comp fld).range with hR
  have hRcyc : IsCyclic ↥R := isCyclic_of_surjective (q.comp fld).rangeRestrict
    (q.comp fld).rangeRestrict_surjective
  have : Finite ↥R := Finite.of_surjective (q.comp fld).rangeRestrict
    (q.comp fld).rangeRestrict_surjective
  have hmem : ∀ γ : MulAut M, γ ^ 3 = 1 → q γ ∈ R := by
    intro γ hγ
    obtain ⟨d, hd, c, hdc⟩ := h3 γ hγ
    have hqd : q d = 1 := by
      have : d ∈ commutator (MulAut M) := hP.up hd
      rw [← Abelianization.ker_of] at this
      exact this
    refine ⟨c, ?_⟩
    show q (fld c) = q γ
    rw [hdc, map_mul, hqd, one_mul]
  have hα' : (MulAut.congr e α) ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hβ' : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  let x : ↥R := ⟨q (MulAut.congr e α), hmem _ hα'⟩
  let y : ↥R := ⟨q (MulAut.congr e β), hmem _ hβ'⟩
  have hx3 : x ^ 3 = 1 := Subtype.ext (by
    show q (MulAut.congr e α) ^ 3 = 1
    rw [← map_pow, hα', map_one])
  have hy3 : y ^ 3 = 1 := Subtype.ext (by
    show q (MulAut.congr e β) ^ 3 = 1
    rw [← map_pow, hβ', map_one])
  have hker : ∀ z : MulAut Y, q (MulAut.congr e z) = 1 → z ∈ commutator (MulAut Y) := by
    intro z hz
    have : MulAut.congr e z ∈ commutator (MulAut M) := by
      rw [← Abelianization.ker_of]
      exact hz
    exact (mem_commutator_congr (MulAut.congr e)).1 this
  rcases cyc_three hx3 hy3 with h1 | ⟨j, h2⟩
  · left
    exact hker α (congrArg Subtype.val h1)
  · right
    refine ⟨j, hker _ ?_⟩
    have := congrArg Subtype.val h2
    simpa [x, y, map_mul, map_pow] using this

theorem finite_ringEquiv (F : Type) [Field F] [Finite F] : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) (fun _ _ h => RingEquiv.ext (congrFun h))

theorem dichotomy_L {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (e : Y ≃* projectiveSL 3 F) (α β : MulAut Y) (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) :
    α ∈ commutator (MulAut Y) ∨ ∃ j : ℕ, β * α ^ j ∈ commutator (MulAut Y) := by
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  have := finite_ringEquiv F
  refine dichotomy_of_model e (stdPinnedPSL 3 F) (goodPinned_psl F) (fieldAut 3 F) ?_ α β hα hβ
  intro γ hγ
  have hd : orderOf γ ∣ 3 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hγ
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  obtain ⟨A, σ', hA⟩ := mem_semilinearAutGroup_iff.1
    (CFSG.Quasithin.A318P.mem_semilinear_of_orderOf_three_pow hk)
  exact ⟨conjAut 3 F A, by
    rw [stdPinnedPSL_inndiag]; exact conjAut_mem_linearAutGroup A, σ', hA⟩

theorem dichotomy_U {Y : Type} [Group Y] {p f : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p f F) (hq : 2 < p ^ f)
    (e : Y ≃* unitaryPSU hF 3) (α β : MulAut Y) (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) :
    α ∈ commutator (MulAut Y) ∨ ∃ j : ℕ, β * α ^ j ∈ commutator (MulAut Y) := by
  have hfin := hF.finite
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  have := finite_ringEquiv F
  refine dichotomy_of_model e (stdPinnedPSU3 hF) (goodPinned_psu hF hq) (psuField hF) ?_ α β hα hβ
  intro γ _
  obtain ⟨A, σ', hA⟩ := exists_psuConj_mul_psuField hq γ
  exact ⟨psuConj hF A, ⟨A, rfl⟩, σ', hA⟩

end Dichotomy

section Fields

@[deprecated (since := "2026-10-15")]
alias mem_coordInndiagVocab_of_commutator := mem_innAutDerivedVocab_of_commutator

theorem diagAut_mem_commutator_of_center_bot {Y : Type} [Group Y]
    (hY : CFSG.Open.IsQuasisimple Y) (hZ : Subgroup.center Y = ⊥) {α : MulAut Y}
    (h : α ∈ Lemma513Ns.diagAut Y) : α ∈ commutator (MulAut Y) := by
  have h1 := diagAut_descend_mem_commutator hY h
  have := (mem_commutator_congr (MulAut.congr (barEquivBot hZ))).2 h1
  rwa [congr_barEquivBot hZ α] at this

theorem two_lt_pow_of_quasisimple_statedSU {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    (e : Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) : 2 < p ^ f := by
  by_contra hle
  have hs := isSolvable_statedProj_of_pow_eq_two hF (pow_eq_two_of_not_two_lt hF hle)
  exact false_of_quasisimple_of_solvable hY
    (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

theorem l3_std {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) {r : ℕ}
    (hr : IsL3Raw r Y) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Y ≃* projectiveSL 3 F),
        Subgroup.center Y = ⊥) ∨
      ∃ (p f : ℕ) (F : Type) (_ : Field F) (hF : UnitaryFieldData p f F) (_ : 2 < p ^ f)
        (_ : Y ≃* unitaryPSU hF 3), Subgroup.center Y = ⊥ := by
  rcases hr with ⟨F, _, hfin, hc, ⟨e⟩⟩ | ⟨F, _, hfin, hc, ⟨e⟩⟩
  · exact Or.inl ⟨F, inferInstance, hfin, e.trans (psiO F),
      center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (psiO F))
        CFSG.GH74.KGroups.L3Eps.center_projectiveSL_three_eq_bot⟩
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hc
    have hq : 2 < p ^ f := two_lt_pow_of_quasisimple_statedSU hY hF e
    exact Or.inr ⟨p, f, F, inferInstance, hF, hq, e.trans (psuO hF).symm,
      center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (psuO hF).symm)
        (center_unitaryPSU_three_eq_bot hF hq)⟩

theorem inputL3fld_holds : InputL3fld innAutDerivedVocab := by
  intro G _ _ K g r hY hr hg hg3 hnot
  have hα3 := barAut_pow_three hg hg3
  by_contra hcon
  apply hnot
  refine ⟨hg, mem_innAutDerivedVocab_of_commutator ?_⟩
  rcases l3_std hY hr with ⟨F, _, _, e, hZ⟩ | ⟨p, f, F, _, hF, hq, e, hZ⟩
  · rcases diag_or_field_L ((barEquivBot hZ).trans e) hα3 with h | h
    · exact diagAut_mem_commutator_of_center_bot hY hZ h
    · exact absurd ⟨hg, h⟩ hcon
  · rcases diag_or_field_U hF hq ((barEquivBot hZ).trans e) hα3 with h | h
    · exact diagAut_mem_commutator_of_center_bot hY hZ h
    · exact absurd ⟨hg, h⟩ hcon

theorem inputL3out_holds : InputL3out innAutDerivedVocab := by
  intro G _ _ K g h r hY hr hg hh hg3 hh3 _
  have hα3 := barAut_pow_three hg hg3
  have hβ3 := barAut_pow_three hh hh3
  have key : barAut 3 K ⟨g, hg⟩ ∈ commutator (MulAut (barOf 3 K)) ∨
      ∃ j : ℕ, barAut 3 K ⟨h, hh⟩ * barAut 3 K ⟨g, hg⟩ ^ j ∈ commutator (MulAut (barOf 3 K)) := by
    rcases l3_std hY hr with ⟨F, _, _, e, hZ⟩ | ⟨p, f, F, _, hF, hq, e, hZ⟩
    · exact dichotomy_L e _ _ hα3 hβ3
    · exact dichotomy_U hF hq e _ _ hα3 hβ3
  rcases key with h1 | ⟨j, h2⟩
  · exact Or.inl ⟨hg, mem_innAutDerivedVocab_of_commutator h1⟩
  · refine Or.inr ⟨j, mul_mem hh (pow_mem hg j), ?_⟩
    have : barAut 3 K ⟨h * g ^ j, mul_mem hh (pow_mem hg j)⟩ =
        barAut 3 K ⟨h, hh⟩ * barAut 3 K ⟨g, hg⟩ ^ j := by
      rw [← map_pow, ← map_mul]
      rfl
    rw [this]
    exact mem_innAutDerivedVocab_of_commutator h2

end Fields

end CFSG.HardMathSupport.Solomon.Coordinator
