module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Exc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Diag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Weir
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Sp62Embed
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.L4U4
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Sp4
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.Quasithin.Background.F918G2
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open TauCeti (PrimePower LieTypeIndex)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.OuterArith
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (NoE27 noE27_pslGoodThree noE27_psuGoodThree
  noE27_pspLow)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (diagGL det_diagGL
  exists_elemAbelian_four_projDiag)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree (exists_orderOf_eq_of_dvd_card_sub_one
  PSUThree.diagGL_mem)
open Arith

section Transfer

variable {K M : Type} [Group K] [Finite K] [Group M]

theorem Shape.not_noE27_equiv (h : Shape K) (e : K ≃* M) (hM : NoE27 M) : False :=
  h.not_noE27 (CFSG.HardMathSupport.Dickson.Sec6.I1431.NoE27.of_mulEquiv e hM)

theorem Shape.not_witness_equiv [Finite M] (h : Shape K) (e : K ≃* M) (hM : Witness M) : False :=
  h.not_witness (hM.of_mulEquiv e.symm)

theorem Shape.not_elemAbelian81_equiv (h : Shape K) (e : K ≃* M) {E : Subgroup M}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 4) : False :=
  h.not_elemAbelian81 (E := E.map e.symm.toMonoidHom) (hE.map _)
    (by rw [card_map_of_injective e.symm.injective, hc])

theorem Shape.not_abelian_nine_equiv (h : Shape K) (e : K ≃* M) {A : Subgroup M}
    (hA : IsPGroup 3 A) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h27 : 27 ≤ Nat.card A)
    {a : M} (ha : a ∈ A) (ha3 : a ^ 3 ≠ 1) : False := by
  refine h.not_abelian_nine (A := A.map e.symm.toMonoidHom) (hA.map _) ?_
    (by rw [card_map_of_injective e.symm.injective]; exact h27) (a := e.symm a) ⟨a, ha, rfl⟩ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  · rw [← map_pow]
    intro h1
    exact ha3 (e.symm.injective (by rw [h1, map_one]))

theorem three_dvd_card_of_equiv (e : K ≃* M) (h : 3 ∣ Nat.card M) : 3 ∣ Nat.card K := by
  rwa [Nat.card_congr e.toEquiv]

theorem three_dvd_of_witness [Finite M] (e : K ≃* M) (hM : Witness M) : 3 ∣ Nat.card K := by
  obtain ⟨E, -, hE, -⟩ := hM.of_mulEquiv e.symm
  have h := Subgroup.card_subgroup_dvd_card E
  rw [hE] at h
  exact (show 3 ∣ 27 by norm_num).trans h

theorem three_dvd_of_card81 (e : K ≃* M) {E : Subgroup M} (hc : Nat.card E = 3 ^ 4) :
    3 ∣ Nat.card K := by
  refine three_dvd_card_of_equiv e ?_
  have h := Subgroup.card_subgroup_dvd_card E
  rw [hc] at h
  exact (show 3 ∣ 3 ^ 4 by norm_num).trans h

end Transfer

namespace ClassicalArith

theorem three_dvd_psl {q n : ℕ} (hq : ¬ 3 ∣ q) (hn : 2 ≤ n) :
    3 ∣ lieOrderNumerator .PSL n q := by
  simp only [lieOrderNumerator]
  exact Dvd.dvd.mul_left ((dvd_sq_sub_one_of_not_dvd hq).trans
    (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.2 ⟨le_rfl, hn⟩))) _

theorem three_dvd_psu {q n : ℕ} (hq : ¬ 3 ∣ q) (hn : 2 ≤ n) :
    3 ∣ lieOrderNumerator .PSU n q := by
  simp only [lieOrderNumerator]
  have h := Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1)
    (Finset.mem_Icc.2 ⟨le_rfl, hn⟩)
  simp only [even_two, ↓reduceIte] at h
  exact Dvd.dvd.mul_left ((dvd_sq_sub_one_of_not_dvd hq).trans h) _

theorem three_dvd_psp {q n : ℕ} (hq : ¬ 3 ∣ q) (hn : 1 ≤ n) :
    3 ∣ lieOrderNumerator .PSp n q := by
  simp only [lieOrderNumerator]
  exact Dvd.dvd.mul_left ((three_dvd_even hq 1).trans
    (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨le_rfl, hn⟩))) _

theorem orderOf_neg_card_zmod_three {q : ℕ} (hq : q % 3 = 1) : orderOf (-(q : ZMod 3)) = 2 := by
  have h1 : -(q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, hq]
    decide
  rw [h1]
  exact orderOf_eq_prime (by decide) (by decide)

theorem nine_dvd_of_factorization {N m : ℕ} (hN : N ≠ 0) (hm : m ≠ 0)
    (hfac : N.factorization 3 = 2 * padicValNat 3 m) (h27 : 27 ∣ N) : 9 ∣ m := by
  have h3 : 3 ≤ N.factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hN).1 (by simpa using h27)
  have := (padicValNat_dvd_iff_le (p := 3) hm).2 (show 2 ≤ padicValNat 3 m by omega)
  simpa using this

theorem three_dvd_of_factorization {N m : ℕ} (hN : N ≠ 0) (hm : m ≠ 0)
    (hfac : N.factorization 3 = 2 * padicValNat 3 m) (h3 : 3 ∣ m) : 3 ∣ N := by
  have hv : 1 ≤ padicValNat 3 m := one_le_padicValNat_of_dvd hm h3
  exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hN).2 (by omega)

end ClassicalArith

open ClassicalArith

theorem nonempty_psp43_of_psu42 {G : Type} [Group G] (h : StatedClassicalModel G .PSU 4 2 1) :
    Nonempty (G ≃* CFSG.GH74.Exceptional.PSp43) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype CFSG.Blueprint.Fischer.K := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card CFSG.Blueprint.Fischer.K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.Fischer.Classification.Unitary.card_K]
  let e₁ := CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 1)
  exact ⟨(e.trans e₁).trans (CFSG.GH74.Exceptional.u2FourEquiv.symm.trans
    CFSG.GH74.Exceptional.psp43EquivU2.symm)⟩

theorem familyAt_U33 (q : PrimePower) (hq : q.card = 3) : FamilyAt (.twistedA 2 q) := by
  intro hv K _ _ _ ⟨e⟩ _ hSh
  exfalso
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [PrimePower.card_def] at hq
  have hp : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1
    (by rw [← hq]; exact dvd_pow_self _ q.exponent_pos.ne')
  have hf : q.exponent = 1 := by
    rw [hp] at hq
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hq.trans (pow_one 3).symm)
  have hC' : CFSG.Quasithin.IsPSU 3 3 1 K := by
    rw [hp, hf] at hC
    exact hC
  have hrk := CFSG.Quasithin.pRank_three_psu33 hC'
  obtain ⟨E, -, -, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup K)
  rw [hrk] at hEc
  have h3 : 3 ∣ Nat.card K := by
    have h := Subgroup.card_subgroup_dvd_card E
    rw [hEc] at h
    exact (show 3 ∣ 3 ^ 2 by norm_num).trans h
  obtain ⟨E', hE', hE'c⟩ := (hSh h3).exists_E
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : E' ≤ ⊤) hE' (k := 3)
    (by rw [hE'c]; norm_num)
  omega

theorem familyAt_C (r : ℕ) (q : PrimePower) (hq : q.p = 2) : FamilyAt (.C r q) := by
  intro hv
  exact absurd hq ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).2

section Families


theorem familyAt_L27 (q : PrimePower) (hq : q.card = 7) : FamilyAt (.A 1 q) := by
  intro hv K _ _ _ ⟨e⟩ _ hSh
  exfalso
  have hC := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hm : LieModel K .PSL (1 + 1) q.p q.exponent := Or.inl ⟨by decide, hC⟩
  have hN := card_mul_divisor hC.1 hm
  rw [PrimePower.card_def] at hq
  simp only [lieOrderNumerator, lieOrderDivisor, hq] at hN
  have hK : Nat.card K = 168 := by
    norm_num [Finset.Icc_self] at hN
    omega
  have h27 := (hSh (by rw [hK]; norm_num)).dvd27
  rw [hK] at h27
  norm_num at h27

theorem familyAt_A (r : ℕ) (q : PrimePower) (hq : q.p = 2) : FamilyAt (.A r q) := by
  intro hv K _ _ _ ⟨e⟩ _ hSh
  exfalso
  have hC := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hm : LieModel K .PSL (r + 1) q.p q.exponent := Or.inl ⟨by decide, hC⟩
  have hN := card_mul_divisor hC.1 hm
  obtain ⟨hadm, F, _, _, hF, ⟨e'⟩⟩ := hC
  have hr1 : 1 ≤ r := by have := hadm.2.2.1; omega
  obtain ⟨hQ2, h3Q⟩ := two_pow_facts hq
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      q.exponent_pos (by rw [hF, hq])
  have hF3 : ¬ 3 ∣ Nat.card F := by rw [hF]; exact h3Q
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | rfl | rfl | hr5
  ·
    have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
      (fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num)) (three_dvd_psl h3Q le_rfl)
    exact (hSh h3).not_noE27_equiv e' (noE27_projSL hF3 (by norm_num)
      (lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)))
  ·
    by_cases h1 : 3 ∣ q.p ^ q.exponent - 1
    · have hfac := psl_three_factorization hQ2 h1 hN
      have hm0 : q.p ^ q.exponent - 1 ≠ 0 := by omega
      have hS := hSh (three_dvd_of_factorization hK0 hm0 hfac h1)
      have h9 := nine_dvd_of_factorization hK0 hm0 hfac hS.dvd27
      obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd_card_sub_one (F := F) (d := 9)
        (by rw [hF]; exact h9)
      obtain ⟨A, hA, hc, h27, a, ha, ha3⟩ := exists_abelian_nine hζ (StatedSL 3 F)
        fun u _ hprod => by
          rw [CFSG.Open.StatedAPI.mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod,
            Units.val_one]
      exact hS.not_abelian_nine_equiv e' hA hc h27 ha ha3
    · have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
        (fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))) (three_dvd_psl h3Q (by norm_num))
      refine (hSh h3).not_noE27 (noE27_pslGoodThree K .PSL (2 + 1) q.p q.exponent hadm
        (by decide) ⟨rfl, rfl, ?_, by rw [hq]; norm_num⟩ hm)
      exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h1)
  ·
    by_cases h1 : 3 ∣ q.p ^ q.exponent - 1
    · have hW := Four.witness_projSL4 (F := F) (by rw [hF]; exact h1)
      exact (hSh (three_dvd_of_witness e' hW)).not_witness_equiv e' hW
    · have hmod : q.p ^ q.exponent % 3 = 2 := by omega
      have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
        (fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))) (three_dvd_psl h3Q (by norm_num))
      exact (hSh h3).not_noE27_equiv e' (noE27_projSL hF3 (by norm_num)
        (by rw [hF, orderOf_card_zmod_three hmod]; norm_num))
  ·
    by_cases h1 : 3 ∣ q.p ^ q.exponent - 1
    · obtain ⟨ω, hω⟩ := exists_orderOf_eq_of_dvd_card_sub_one (F := F) (d := 3)
        (by rw [hF]; exact h1)
      obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_four_projDiag Nat.prime_three (n := 4 + 1)
        (by norm_num) (Or.inr (by norm_num)) hω (StatedSL (4 + 1) F) fun u _ _ hprod => by
          rw [CFSG.Open.StatedAPI.mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod,
            Units.val_one]
      exact (hSh (three_dvd_of_card81 e' hEc)).not_elemAbelian81_equiv e' hE hEc
    · have hmod : q.p ^ q.exponent % 3 = 2 := by omega
      have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
        (fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))) (three_dvd_psl h3Q (by norm_num))
      exact (hSh h3).not_noE27_equiv e' (noE27_projSL hF3 (by norm_num)
        (by rw [hF, orderOf_card_zmod_three hmod]; norm_num))
  ·
    obtain ⟨m, hm6⟩ : ∃ m, r + 1 = 6 + m := ⟨r + 1 - 6, by omega⟩
    rw [hm6] at e'
    have hW := Sp62.witness_projSL (F := F) m
    exact (hSh (three_dvd_of_witness e' hW)).not_witness_equiv e' hW

theorem familyAt_twistedA (r : ℕ) (q : PrimePower) (hq : q.p = 2) :
    FamilyAt (.twistedA r q) := by
  intro hv K _ _ _ ⟨e⟩ _ hSh
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have hm : LieModel K .PSU (r + 1) q.p q.exponent := Or.inl ⟨by decide, hC⟩
  have hN := card_mul_divisor hC.1 hm
  have hC' := hC
  obtain ⟨hadm, L, _, _, hL, ⟨e'⟩⟩ := hC
  have hr2 : 2 ≤ r := by have := hadm.2.2.1; omega
  obtain ⟨hQ2, h3Q⟩ := two_pow_facts hq
  have hq0 : q.p ^ q.exponent ≠ 0 := by omega
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hdvd : ∀ d, d ∣ q.p ^ q.exponent + 1 → d ∣ Nat.card L - 1 := by
    intro d hd
    rw [hL, show (q.p ^ q.exponent) ^ 2 - 1 = (q.p ^ q.exponent) ^ 2 - 1 ^ 2 by norm_num,
      Nat.pow_two_sub_pow_two]
    exact hd.mul_right _
  have hdiag : ∀ {ζ : Lˣ} {d : ℕ}, orderOf ζ = d → d ∣ q.p ^ q.exponent + 1 → ∀ (m : ℕ)
      (u : Fin m → Lˣ), (∀ i, u i ∈ zpowers ζ) → ∏ i, u i = 1 →
        diagGL m u ∈ StatedSU m (q.p ^ q.exponent) L := by
    intro ζ d hζ hd m u hu hprod
    refine PSUThree.diagGL_mem hq0 u (fun i => ?_) hprod
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_of_mem_zpowers (hu i)).trans (hζ ▸ hd)
  rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | rfl | hr5
  ·
    exfalso
    by_cases h1 : 3 ∣ q.p ^ q.exponent + 1
    · have hfac := psu_three_factorization hQ2 h1 hN
      have hm0 : q.p ^ q.exponent + 1 ≠ 0 := by omega
      have hS := hSh (three_dvd_of_factorization hK0 hm0 hfac h1)
      have h9 := nine_dvd_of_factorization hK0 hm0 hfac hS.dvd27
      obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd_card_sub_one (hdvd 9 h9)
      obtain ⟨A, hA, hc, h27, a, ha, ha3⟩ :=
        exists_abelian_nine hζ (StatedSU 3 (q.p ^ q.exponent) L) (hdiag hζ h9 3)
      exact hS.not_abelian_nine_equiv e' hA hc h27 ha ha3
    · have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
        (fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))) (three_dvd_psu h3Q (by norm_num))
      exact (hSh h3).not_noE27 (noE27_psuGoodThree K .PSU (2 + 1) q.p q.exponent hadm
        (by decide) ⟨rfl, rfl, fun h => h1 (h.trans (Nat.gcd_dvd_right _ _)),
          by rw [hq]; norm_num⟩ hm)
  ·
    by_cases h1 : 3 ∣ q.p ^ q.exponent + 1
    · by_cases hf1 : q.exponent = 1
      ·
        have h421 : StatedClassicalModel K .PSU 4 2 1 := by
          rw [hq, hf1] at hC'
          exact hC'
        exact nonempty_psp43_of_psu42 h421
      · exfalso
        have hf2 : 2 ≤ q.exponent := by have := q.exponent_pos; omega
        rw [hq] at hL e' h1
        have hW := Four.witness_projSU4 hf2 hL h1
        exact (hSh (three_dvd_of_witness e' hW)).not_witness_equiv e' hW
    · exfalso
      have hmod : q.p ^ q.exponent % 3 = 1 := by omega
      have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
        (fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))) (three_dvd_psu h3Q (by norm_num))
      exact (hSh h3).not_noE27_equiv e' (noE27_projSU hL h3Q (by norm_num) (by norm_num)
        (by rw [orderOf_neg_card_zmod_three hmod]; norm_num))
  ·
    exfalso
    by_cases h1 : 3 ∣ q.p ^ q.exponent + 1
    · obtain ⟨ω, hω⟩ := exists_orderOf_eq_of_dvd_card_sub_one (hdvd 3 h1)
      obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_four_projDiag Nat.prime_three (n := 4 + 1)
        (by norm_num) (Or.inr (by norm_num)) hω (StatedSU (4 + 1) (q.p ^ q.exponent) L)
        fun u hu _ hprod => hdiag hω h1 (4 + 1) u hu hprod
      exact (hSh (three_dvd_of_card81 e' hEc)).not_elemAbelian81_equiv e' hE hEc
    · have hmod : q.p ^ q.exponent % 3 = 1 := by omega
      have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
        (fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))) (three_dvd_psu h3Q (by norm_num))
      exact (hSh h3).not_noE27_equiv e' (noE27_projSU hL h3Q (by norm_num) (by norm_num)
        (by rw [orderOf_neg_card_zmod_three hmod]; norm_num))
  ·
    exfalso
    obtain ⟨m, hm6⟩ : ∃ m, r + 1 = 6 + m := ⟨r + 1 - 6, by omega⟩
    rw [hm6, hq] at e'
    rw [hq] at hL
    haveI : CharP L 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (k := 2 * q.exponent) (by have := q.exponent_pos; omega) (by rw [hL]; ring)
    have hW := Sp62.witness_projSU (L := L) q.exponent_pos hL m
    exact (hSh (three_dvd_of_witness e' hW)).not_witness_equiv e' hW

theorem familyAt_B (r : ℕ) (q : PrimePower) (hq : q.p = 2) : FamilyAt (.B r q) := by
  intro hv K _ _ _ ⟨e⟩ _ hSh
  exfalso
  obtain ⟨hQ2, h3Q⟩ := two_pow_facts hq
  have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  ·
    have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    have hm : LieModel K .PSp 2 q.p q.exponent := Or.inl ⟨by decide, hC⟩
    have hN := card_mul_divisor hC.1 hm
    have h3 : 3 ∣ Nat.card K := three_dvd_of_order hN
      (fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num))
      (three_dvd_psp h3Q (by norm_num))
    exact (hSh h3).not_noE27 (noE27_pspLow K .PSp 2 q.p q.exponent hC.1 (by decide)
      ⟨rfl, rfl, by rw [hq]; norm_num⟩ hm)
  ·
    obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq hr3 e
    haveI : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        q.exponent_pos (by rw [hF, hq])
    have hW := Sp62.witness_projSp (K := F) hr3
    exact (hSh (three_dvd_of_witness e' hW)).not_witness_equiv e' hW

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev
