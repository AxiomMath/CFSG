module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open Matrix CFSG.ClassicalModels TauCeti CFSG.Yardstones.Md0ec50421ce4

private theorem eq_two_nine_of_order (q m : ℕ) (hq : 2 ≤ q) (hm : 2 ≤ m)
    (h : q ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 2 m, (q ^ i - 1) = 360 * m.gcd (q - 1)) :
    m = 2 ∧ q = 9 := by
  have hcop : Nat.Coprime (q ^ (m * (m - 1) / 2)) (m.gcd (q - 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right m (q - 1)) ?_
    have : Nat.Coprime (q - 1 + 1) (q - 1) := by simp
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hdvd : q ^ (m * (m - 1) / 2) ∣ 360 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [← h]
    exact Dvd.intro _ rfl
  have hle : q ^ (m * (m - 1) / 2) ≤ 360 := Nat.le_of_dvd (by norm_num) hdvd
  have hm4 : m ≤ 4 := by
    by_contra hcon
    have h5 : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega : 5 ≤ m) (by omega : 4 ≤ m - 1)
    have h10 : 10 ≤ m * (m - 1) / 2 := by omega
    have : 2 ^ 10 ≤ q ^ (m * (m - 1) / 2) :=
      (Nat.pow_le_pow_left hq 10).trans (Nat.pow_le_pow_right (by omega) h10)
    omega
  interval_cases m
  · simp at h
    have hg : (2 : ℕ).gcd (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hq9 : q ≤ 9 := by
      by_contra hcon
      have h10 : 10 ≤ q := by omega
      have : q * (q ^ 2 - 1) ≥ 10 * (10 ^ 2 - 1) := by
        apply Nat.mul_le_mul h10
        exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h10 2) 1
      omega
    interval_cases q <;> simp_all
  · have hI : Finset.Icc 2 3 = {2, 3} := by decide
    simp [hI] at h hle
    have hq7 : q ≤ 7 := by
      by_contra hcon
      have h8 : 8 ≤ q := by omega
      have : 8 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h8 3
      omega
    interval_cases q <;> simp_all
  · have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
    simp [hI] at h hle
    have hq2 : q ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ q := by omega
      have : 3 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left h3 6
      omega
    interval_cases q <;> simp_all

theorem slAltSixFacts_holds : SLAltSixFacts := by
  intro E _ _ m hm ⟨e⟩
  have hq : 2 ≤ Nat.card E := Nat.succ_le_of_lt Finite.one_lt_card
  have h360 : Nat.card (Matrix.SpecialLinearGroup (Fin m) E ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hsl := CFSG.OrderReductions.LinearOrders.card_specialLinear E m (by omega)
  have hz := CFSG.OrderReductions.LinearOrders.card_specialLinear_center E m (by omega)
  have hmul := (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin m) E)).card_eq_card_quotient_mul_card_subgroup
  rw [h360, hz, hsl] at hmul
  obtain ⟨h2, h9⟩ := eq_two_nine_of_order (Nat.card E) m hq hm hmul
  exact ⟨h2, by rwa [← Nat.card_eq_fintype_card]⟩

private theorem nonempty_alt5_of_simple_card_sixty {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : Nat.card G = 60) : Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hG, show (60 : ℕ) = 5 * 12 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnot_normal : ¬ (P : Subgroup G).Normal := fun hN => by
    rcases hN.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP
      omega
    · rw [h, Subgroup.card_top, hG] at hP
      omega
  have hcard : Nat.card (Sylow 5 G) = 6 := by
    have hmod := card_sylow_modEq_one 5 G
    have hdvd : Nat.card (Sylow 5 G) ∣ 12 := by
      have h := P.card_dvd_index
      rwa [(P : Subgroup G).index_eq_card, show Nat.card (G ⧸ (P : Subgroup G)) = 12 by
        have := (P : Subgroup G).card_mul_index
        rw [hP, hG, (P : Subgroup G).index_eq_card] at this
        omega] at h
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card (Sylow 5 G) ≠ 1 := fun h1 => by
      have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnot_normal (Sylow.normal_of_subsingleton P)
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 G) <;> simp_all
  have hfaithful : FaithfulSMul G (Sylow 5 G) := by
    let φ := MulAction.toPermHom G (Sylow 5 G)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · refine ⟨fun {g h} hgh => ?_⟩
      have : φ g = φ h := Equiv.ext hgh
      exact (MonoidHom.ker_eq_bot_iff φ).mp hk this
    · refine absurd ?_ hnot_normal
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp
        (congrArg (fun σ : Equiv.Perm (Sylow 5 G) => σ P) hg)
  exact CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    (Ω := Sylow 5 G) inferInstance hcard hG

private theorem nonempty_psl2_alt5 {E : Type} [Field E] [Finite E]
    (h : Nat.card E = 4 ∨ Nat.card E = 5) :
    Nonempty (ProjectiveSpecialLinearGroup (Fin 2) E ≃* alternatingGroup (Fin 5)) := by
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) E) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hcard : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) E) = 60 := by
    rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear E 2 (by norm_num)]
    rcases h with h | h <;> rw [h] <;> norm_num [Finset.Icc_self]
  exact nonempty_alt5_of_simple_card_sixty hcard

private theorem nonempty_psl3_psl2_seven_of_card_two {E : Type} [Field E] [Finite E]
    (h : Nat.card E = 2) :
    Nonempty (ProjectiveSpecialLinearGroup (Fin 3) E ≃*
      ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h]
  let φ : E ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  let e₁ : ProjectiveSpecialLinearGroup (Fin 3) E ≃*
      ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    projectiveSpecialLinearFieldEquiv φ (Fin 3)
  let e₂ : ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨(((e₁.trans e₂).trans e₃).trans e₄)⟩

private theorem nonempty_psl4_alt8_of_card_two {E : Type} [Field E] [Finite E]
    (h : Nat.card E = 2) :
    Nonempty (ProjectiveSpecialLinearGroup (Fin 4) E ≃* alternatingGroup (Fin 8)) :=
  ⟨(((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 E).trans
    (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo h 4)).trans
    (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo h 4)).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm⟩

private theorem ringChar_eq_of_card {E : Type} [Field E] [Fintype E] {a b : ℕ} (ha : a.Prime)
    (h : Fintype.card E = a ^ b) : ringChar E = a := by
  haveI : Fact a.Prime := ⟨ha⟩
  haveI : CharP E a := charP_of_card_eq_prime_pow h
  exact ringChar.eq E a

private theorem isChevSimple_of_valid {E : Type} [Field E] [Fintype E] (r : ℕ)
    (hp : (ringChar E).Prime) (n : ℕ) (hn : 0 < n) (hcard : Fintype.card E = ringChar E ^ n)
    (hv : (LieTypeIndex.A r ⟨ringChar E, n, hp, hn⟩).Valid) :
    IsChevSimple (ringChar E) (Matrix.SpecialLinearGroup (Fin (r + 1)) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) E)) := by
  let q : PrimePower := ⟨ringChar E, n, hp, hn⟩
  haveI : Fact (ringChar E).Prime := ⟨hp⟩
  have hK : Nat.card E = ringChar E ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  let eF := finiteFieldEquivGaloisField E (ringChar E) n hn hK
  let eP := projectiveSpecialLinearFieldEquiv eF (Fin (r + 1))
  let eC := linearCatalogCandidateEquivPSL r q hv
  exact Or.inl ⟨.lie ⟨LieTypeIndex.A r q, hv⟩, LieTypeIndex.characteristic_A r q,
    ⟨eP.trans eC.symm⟩⟩

private theorem isChevSimple_sl {E : Type} [Field E] [Fintype E] (m : ℕ) (hm : 2 ≤ m)
    (hE4 : m = 2 → 4 ≤ Fintype.card E) :
    IsChevSimple (ringChar E) (Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n, hp, hcard⟩ := FiniteField.card E (ringChar E)
  have hn : 0 < (n : ℕ) := n.pos
  let q : PrimePower := ⟨ringChar E, n, hp, hn⟩
  by_cases hv : (LieTypeIndex.A r q).Valid
  · exact isChevSimple_of_valid r hp n hn hcard hv
  · have hdup : (LieTypeIndex.A r q).IsDuplicateRepresentative := by
      by_contra hd
      refine hv ((LieTypeIndex.valid_iff _).2 ⟨?_, hd⟩)
      rw [LieTypeIndex.inStandardRange_iff]
      refine ⟨by omega, fun hr => ?_⟩
      have := hE4 (by omega)
      rw [hcard] at this
      simpa [q, PrimePower.card_def] using this
    rw [LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    simp only [PrimePower.card_def, q] at hdup
    have h56 : 5 ≤ 6 := by norm_num
    have h58 : 5 ≤ 8 := by norm_num
    rcases hdup with ⟨hr, h4 | h5 | h9⟩ | ⟨hr, h2⟩ | ⟨hr, h2⟩
    · subst hr
      have hc4 : Fintype.card E = 4 := hcard.trans h4
      have hch : ringChar E = 2 :=
        ringChar_eq_of_card Nat.prime_two (b := 2) (by rw [hc4]; norm_num)
      obtain ⟨e⟩ := nonempty_psl2_alt5 (E := E) (Or.inl (by rw [Nat.card_eq_fintype_card, hc4]))
      exact Or.inr ⟨.alternating 5 le_rfl, Or.inl ⟨rfl, Or.inl hch⟩, ⟨e⟩⟩
    · subst hr
      have hc5 : Fintype.card E = 5 := hcard.trans h5
      have hch : ringChar E = 5 :=
        ringChar_eq_of_card (by norm_num) (b := 1) (by rw [hc5]; norm_num)
      obtain ⟨e⟩ := nonempty_psl2_alt5 (E := E) (Or.inr (by rw [Nat.card_eq_fintype_card, hc5]))
      exact Or.inr ⟨.alternating 5 le_rfl, Or.inl ⟨rfl, Or.inr hch⟩, ⟨e⟩⟩
    · subst hr
      have hc9 : Fintype.card E = 9 := hcard.trans h9
      have hch : ringChar E = 3 :=
        ringChar_eq_of_card (by norm_num) (b := 2) (by rw [hc9]; norm_num)
      obtain ⟨e⟩ :=
        CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine
          (F := E) (by rw [Nat.card_eq_fintype_card, hc9])
      exact Or.inr ⟨.alternating 6 h56, Or.inr (Or.inl ⟨rfl, Or.inr hch⟩), ⟨e⟩⟩
    · subst hr
      have hc2 : Fintype.card E = 2 := hcard.trans h2
      have hch : ringChar E = 2 :=
        ringChar_eq_of_card Nat.prime_two (b := 1) (by rw [hc2]; norm_num)
      obtain ⟨e⟩ :=
        nonempty_psl3_psl2_seven_of_card_two (E := E) (by rw [Nat.card_eq_fintype_card, hc2])
      haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
      let q7 : PrimePower := ⟨7, 1, Nat.prime_seven, one_pos⟩
      have hv7 : (LieTypeIndex.A 1 q7).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        simp only [PrimePower.card_def, q7]
        omega
      let eF7 : ZMod 7 ≃+* GaloisField 7 1 :=
        finiteFieldEquivGaloisField (ZMod 7) 7 1 one_pos (by simp [Nat.card_zmod])
      let eC7 := linearCatalogCandidateEquivPSL 1 q7 hv7
      exact Or.inr ⟨.lie ⟨LieTypeIndex.A 1 q7, hv7⟩,
        Or.inl ⟨by simp [q7, PrimePower.card_def], hch⟩,
        ⟨(e.trans (projectiveSpecialLinearFieldEquiv eF7 (Fin 2))).trans eC7.symm⟩⟩
    · subst hr
      have hc2 : Fintype.card E = 2 := hcard.trans h2
      have hch : ringChar E = 2 :=
        ringChar_eq_of_card Nat.prime_two (b := 1) (by rw [hc2]; norm_num)
      obtain ⟨e⟩ :=
        nonempty_psl4_alt8_of_card_two (E := E) (by rw [Nat.card_eq_fintype_card, hc2])
      exact Or.inr ⟨.alternating 8 h58, Or.inr (Or.inr ⟨rfl, hch⟩), ⟨e⟩⟩

theorem slFactorFacts_holds : SLFactorFacts := by
  intro E _ _ m hm hE4
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) := by
    by_cases h2 : m = 2
    · subst h2
      exact specialLinear_isPerfect_two_of_four_le_card E
        (by rw [Nat.card_eq_fintype_card]; exact hE4 rfl)
    · exact specialLinear_isPerfect_of_three_le (by omega)
  refine ⟨hperf.commutator_eq_top, isChevSimple_sl m hm hE4, ?_⟩
  rintro ⟨e⟩
  obtain ⟨hm2, hq9⟩ := slAltSixFacts_holds E m hm ⟨e⟩
  subst hm2
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center E 2 (by norm_num),
    Nat.card_eq_fintype_card, hq9]
  decide

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
