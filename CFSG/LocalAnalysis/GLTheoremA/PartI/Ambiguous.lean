module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem amb_fixSubgroup_one {K : Type*} [Group K] :
    fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem amb_isSubnormal_top {T : Type} [Group T] [IsSimpleGroup T] {H K : Subgroup T}
    (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K hle hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hle))
    · subst hM
      haveI : H.Normal :=
        ⟨fun n hn' g => (Subgroup.normal_subgroupOf_iff le_top).1 hn n g hn' (Subgroup.mem_top g)⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

private theorem amb_center_eq_bot {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

private theorem amb_pSimple_top_equiv {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hnc : ∃ a b : T, a * b ≠ b * a) {I : Subgroup T}
    (hI : GLAPComponent p (⊤ : Subgroup T) I) : Nonempty (PSimple p I ≃* T) := by
  have hIeq : I = ⊤ := by
    rcases amb_isSubnormal_top hI.2.1 rfl with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · exact h
  subst hIeq
  have hq : CFSG.Open.IsQuasisimple (PQuot p (⊤ : Subgroup T)) :=
    isQuasisimple_pQuot_of_glaPComponent hp hI
  have hnt : Nontrivial (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T)) := by
    haveI : Nontrivial (PQuot p (⊤ : Subgroup T) ⧸ Subgroup.center (PQuot p (⊤ : Subgroup T))) :=
      hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center (PQuot p (⊤ : Subgroup T)))).nontrivial
  have hOb : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊥ := by
    let ψ : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
    haveI : ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom).Normal :=
      Subgroup.Normal.map (GLAPPrimeCore.normal p _) ψ.toMonoidHom ψ.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom) with h | h
    · exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h
    · exfalso
      have htop : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊤ := by
        apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
        rw [h, Subgroup.map_top_of_surjective _ ψ.surjective]
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T))
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _
  have hZtop : Subgroup.center ↥(⊤ : Subgroup T) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup T) ≃* T)
    rw [amb_center_eq_bot hnc] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 h1
  let e1 : PQuot p (⊤ : Subgroup T) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hOb).trans QuotientGroup.quotientBot
  let e2 : PSimple p (⊤ : Subgroup T) ≃*
      (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) :=
    QuotientGroup.congr _ _ e1 (Subgroup.map_center_eq e1)
  let e3 : (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans QuotientGroup.quotientBot
  exact ⟨e2.trans (e3.trans Subgroup.topEquiv)⟩

private theorem amb_kLevel_eq_one {p : ℕ} {S : Type} [Group S] (h : IsChevSimple p S) :
    kLevel p S = 1 := by
  unfold kLevel
  rw [if_pos h]

private theorem amb_nonab_of_card_not_prime {T : Type} [Group T] [IsSimpleGroup T]
    (hc : ¬ (Nat.card T).Prime) : ∃ a b : T, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup T := { ‹Group T› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := T)).1 ‹IsSimpleGroup T›)

private theorem amb_false_of_solvable_component {p : ℕ} {S : Type} [Group S] [Finite S]
    {X I : Subgroup S} (hsolv : Group.IsSolvable ↥X) (hI : GLAPComponent p X I) : False := by
  haveI := hsolv
  have hJX : I ≤ X := hI.1
  have hperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
  have hne : I ≠ ⊥ := glaPComponent_ne_bot' hI
  have hJ'ne : I.subgroupOf X ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJX, h0, Subgroup.map_bot]
  have hlt : ⁅I.subgroupOf X, I.subgroupOf X⁆ < I.subgroupOf X :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅I.subgroupOf X, I.subgroupOf X⁆ = I.subgroupOf X := by
    apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJX]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

private theorem amb_isSolvable_of_card_six {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 6) : Group.IsSolvable G := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  decide

private theorem amb_card_L2_two {F₀ : Type} [Field F₀] [Finite F₀] (h2 : Nat.card F₀ = 2) :
    Nat.card (StatedProj (StatedSL 2 F₀)) = 6 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F₀) (n := 2) (by norm_num),
    h2]
  norm_num

private def ambQ8 : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩

private theorem amb_valid_A1_ambQ8 : (TauCeti.LieTypeIndex.A 1 ambQ8).Valid := by
  simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, ambQ8, TauCeti.PrimePower.card_def]

private theorem amb_isChev_l2 (F : Type) [Field F] [Finite F] (hF8 : Nat.card F = 8) :
    IsChevSimple 3 (StatedProj (StatedSL 2 F)) := by
  haveI : Fact ambQ8.p.Prime := ⟨ambQ8.prime_p⟩
  have hv : (TauCeti.LieTypeIndex.A 1 ambQ8).Valid := amb_valid_A1_ambQ8
  have hamb : ambiguousChev 3 (TauCeti.CFSGIndex.lie ⟨.A 1 ambQ8, hv⟩) :=
    Or.inr ⟨by norm_num [ambQ8, TauCeti.PrimePower.card_def], rfl⟩
  have e : StatedProj (StatedSL 2 F) ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 ambQ8, hv⟩).Group :=
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 3 (by norm_num)
      (by rw [hF8] <;> norm_num)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ambQ8 hv).symm
  exact Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ambQ8, hv⟩, hamb, ⟨e⟩⟩

theorem downLe_one_alt {n p : ℕ} (h : (n = 5 ∧ p = 5) ∨ (n = 6 ∧ p = 3)) :
    DownLe p 1 (alternatingGroup (Fin n)) := by
  have hn : 5 ≤ n := by rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hp : p.Prime := by rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hp2 : p ≠ 2 := by rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hAmb : ambiguousChev p (TauCeti.CFSGIndex.alternating n hn) := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ambiguousChev]
  have hT : IsChevSimple p (alternatingGroup (Fin n)) :=
    Or.inr ⟨TauCeti.CFSGIndex.alternating n hn, hAmb, ⟨MulEquiv.refl _⟩⟩
  intro α hα I hI
  by_cases hα1 : α = 1
  · subst hα1
    rw [amb_fixSubgroup_one] at hI
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have hnp : ¬ (Nat.card (alternatingGroup (Fin n))).Prime := by
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num [Nat.factorial]
    obtain ⟨f⟩ := amb_pSimple_top_equiv hp (amb_nonab_of_card_not_prime hnp) hI
    exact (kLevel_congr p f).trans_le (amb_kLevel_eq_one hT).le
  · exfalso
    obtain ⟨m, hm5, hmn, -⟩ := kdAltDown_holds n p hn hp hp2 α hα hα1 I hI
    have h5 : 5 ≤ m := le_trans (le_max_left 5 p) hm5
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem downLe_one_l2_eight (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 8) :
    DownLe 3 1 (StatedProj (StatedSL 2 F)) := by
  have hF8 : Nat.card F = 8 := by rw [Nat.card_eq_fintype_card, hF]
  intro α hα I hI
  by_cases hα1 : α = 1
  · subst hα1
    rw [amb_fixSubgroup_one] at hI
    haveI : IsSimpleGroup (StatedProj (StatedSL 2 F)) :=
      CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 2) F le_rfl
        (Or.inr (by omega)) (Or.inr (by omega))
    have hcard : Nat.card (StatedProj (StatedSL 2 F)) = 504 := by
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2)
        (by norm_num), hF8]
      norm_num
    have hnc : ∃ a b : StatedProj (StatedSL 2 F), a * b ≠ b * a :=
      amb_nonab_of_card_not_prime (by rw [hcard]; norm_num)
    obtain ⟨f⟩ := amb_pSimple_top_equiv (by norm_num : Nat.Prime 3) hnc hI
    exact (kLevel_congr 3 f).trans_le (amb_kLevel_eq_one (amb_isChev_l2 F hF8)).le
  · have hsolv : Group.IsSolvable ↥(fixSubgroup α) := by
      rcases CFSG.HardMathSupport.Solomon.Coordinator.l2Aut3Classification_holds F α hα with
        h | h | ⟨σ, φ, γ, hφ, hβ⟩
      · exact absurd h hα1
      · exact h
      · obtain ⟨F₀, _, _, hcard, ⟨ψ⟩⟩ :=
          CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds F α hα hα1 σ φ γ hφ hβ
        have h8 : Nat.card F₀ ^ 3 = 2 ^ 3 := by rw [← hcard, hF8] <;> norm_num
        have h2 : Nat.card F₀ = 2 := Nat.pow_left_injective (n := 3) (by norm_num) h8
        have ψ' : ↥(fixSubgroup α) ≃* StatedProj (StatedSL 2 F₀) := ψ
        exact amb_isSolvable_of_card_six
          ((Nat.card_congr ψ'.toEquiv).trans (amb_card_L2_two h2))
    exact (amb_false_of_solvable_component hsolv hI).elim

private theorem amb_downLe_l2_lie (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq8 : q.card = 8) :
    DownLe 3 1 (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  letI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField q.p q.exponent) = 8 := by
    rw [← Nat.card_eq_fintype_card, hK, hq8]
  have e : StatedProj (StatedSL 2 (GaloisField q.p q.exponent)) ≃*
      (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField q.p q.exponent)).symm.trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm
  exact downLe_of_mulEquiv e (downLe_one_l2_eight (GaloisField q.p q.exponent) hc)

theorem ambiguous_downLe {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hU42 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid),
      q.card = 2 → DownLe 3 1 (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
    (i : TauCeti.CFSGIndex) (hi : ambiguousChev p i) : DownLe p 1 i.Group := by
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | alternating n hn =>
    simp only [ambiguousChev] at hi
    rcases hi with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h⟩
    · exact (hp2 h).elim
    · subst h
      exact downLe_one_alt (n := 5) (p := 5) (Or.inl ⟨rfl, rfl⟩)
    · exact (hp2 h).elim
    · subst h
      exact downLe_one_alt (n := 6) (p := 3) (Or.inr ⟨rfl, rfl⟩)
    · exact (hp2 h).elim
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld
    case A r q =>
      rcases r with _ | _ | r
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        rcases hi with ⟨-, h2⟩ | ⟨hq8, rfl⟩
        · exact (hp2 h2).elim
        · exact amb_downLe_l2_lie q hv hq8
      · simp [ambiguousChev] at hi
    case twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        exact (hp2 hi.2).elim
      · simp only [ambiguousChev] at hi
        obtain ⟨hq2, rfl⟩ := hi
        exact hU42 q hv hq2
      · simp [ambiguousChev] at hi
    all_goals simp [ambiguousChev] at hi
  | sporadic s => simp [ambiguousChev] at hi

end CFSG.LocalAnalysis.GLTheoremA
