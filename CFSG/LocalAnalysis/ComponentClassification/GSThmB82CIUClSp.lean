module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUClLin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClSp
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.ComponentClassification.GSThmB.QPUJ6Cl

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjAut conjSp statedSp_le_gsp
  conjAut_proj coe_conjSp)
open CFSG.ComponentClassification.CatFactsSp4 (fixOf mem_fixOf)
open scoped MatrixGroups

theorem card_mul_le_of_isL4U4Mod4 {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hX : IsL4U4Mod4 X p f) :
    ∃ g c : ℕ, 0 < g ∧ g ≤ 4 ∧ (p ^ f) ^ 3 - 1 ≤ c ∧
      Nat.card X * g = (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) * c := by
  rcases hX with ⟨hX, -⟩ | ⟨hX, -⟩
  · exact ⟨_, _, Nat.gcd_pos_of_pos_left _ (by norm_num), Nat.gcd_le_left _ (by norm_num),
      le_rfl, card_mul_of_lieModel_psl_four hp2 hX⟩
  · exact ⟨_, _, Nat.gcd_pos_of_pos_left _ (by norm_num), Nat.gcd_le_left _ (by norm_num),
      by omega, card_mul_of_lieModel_psu_four hp2 hX⟩

theorem pow_six_sub_one (q : ℕ) : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    zify [h1, h6]
    ring

theorem exists_prime_dvd_not_dvd_psp4_sq {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : IsL4U4Mod4 X p f) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ Nat.card X ∧
      ¬ ℓ ∣ (p ^ f) ^ 8 * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 8 - 1)) := by
  set q := p ^ f with hq
  have hf : 1 ≤ f := by
    rcases hX with ⟨hX, -⟩ | ⟨hX, -⟩
    · rcases hX with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact h.1.2.1
      all_goals exact absurd h0 (by norm_num)
    · rcases hX with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact h.1.2.1
      all_goals exact absurd h0 (by norm_num)
  have hq3 : 3 ≤ q := (show 3 ≤ p by have := hp.two_le; omega).trans
    (Nat.le_self_pow (by omega) p)
  have hq0 : 0 < q := by omega
  have hodd : Odd q := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have key : ∀ {ℓ : ℕ}, ℓ.Prime → ¬ ℓ ∣ q - 1 → ¬ ℓ ∣ q ^ 2 - 1 →
      ((q : ZMod ℓ) ^ 3 = 1 ∨ (q : ZMod ℓ) ^ 6 = 1) →
      ¬ ℓ ∣ q ^ 8 * ((q ^ 4 - 1) * (q ^ 8 - 1)) := by
    intro ℓ hℓ h1 h2 h36 hdvd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have h1' : (q : ZMod ℓ) ^ 1 ≠ 1 := fun e =>
      h1 (by simpa using (SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hq0 1).2 e)
    have h2' : (q : ZMod ℓ) ^ 2 ≠ 1 := fun e =>
      h2 ((SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hq0 2).2 e)
    rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with h8 | h48
    ·
      have hℓq : ℓ ∣ q := hℓ.dvd_of_dvd_pow h8
      have hz : (q : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff q ℓ).2 hℓq
      rcases h36 with e | e <;> rw [hz] at e <;> simp at e
    rcases (Nat.Prime.dvd_mul hℓ).1 h48 with h4 | h8'
    · have e4 := (SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hq0 4).1 h4
      rcases h36 with e | e
      · exact h1' (by rw [pow_one]; linear_combination e4 - (q : ZMod ℓ) * e)
      · exact h2' (by linear_combination e - (q : ZMod ℓ) ^ 2 * e4)
    · have e8 := (SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hq0 8).1 h8'
      rcases h36 with e | e
      · exact h2' (by linear_combination e8 - (q : ZMod ℓ) ^ 2 * ((q : ZMod ℓ) ^ 3 + 1) * e)
      · exact h2' (by linear_combination e8 - (q : ZMod ℓ) ^ 2 * e)
  have hℓg : ∀ {ℓ g : ℕ}, ℓ.Prime → ¬ ℓ ∣ q - 1 → g ∣ 4 → ¬ ℓ ∣ g := by
    intro ℓ g hℓ h1 hg hℓg
    have h4 : ℓ ∣ 2 ^ 2 := (hℓg.trans hg).trans (by norm_num)
    have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h4)
    subst hℓ2
    obtain ⟨k, hk⟩ := hodd
    exact h1 ⟨k, by omega⟩
  rcases hX with ⟨hX, -⟩ | ⟨hX, -⟩
  ·
    obtain ⟨ℓ, hℓ, hℓ3, hprim⟩ :=
      SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hq3 (le_refl 3)
    have h1 := hprim 1 (by norm_num) (by norm_num)
    have h2 := hprim 2 (by norm_num) (by norm_num)
    rw [pow_one] at h1
    have hc := card_mul_of_lieModel_psl_four hp2 hX
    refine ⟨ℓ, hℓ, ?_, key hℓ h1 h2 (Or.inl
      ((SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hq0 3).1 hℓ3))⟩
    have hdvd : ℓ ∣ Nat.card X * Nat.gcd 4 (q - 1) := by
      rw [hc]
      exact Dvd.dvd.mul_left hℓ3 _
    rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with h | h
    · exact h
    · exact absurd h (hℓg hℓ h1 (Nat.gcd_dvd_left _ _))
  ·
    obtain ⟨ℓ, hℓ, hℓ6, hprim⟩ :=
      SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hq3 (by norm_num : 3 ≤ 6)
    have h1 := hprim 1 (by norm_num) (by norm_num)
    have h2 := hprim 2 (by norm_num) (by norm_num)
    have h3 := hprim 3 (by norm_num) (by norm_num)
    rw [pow_one] at h1
    have hℓ3 : ℓ ∣ q ^ 3 + 1 := by
      rw [pow_six_sub_one] at hℓ6
      rcases (Nat.Prime.dvd_mul hℓ).1 hℓ6 with h | h
      · exact absurd h h3
      · exact h
    have hc := card_mul_of_lieModel_psu_four hp2 hX
    refine ⟨ℓ, hℓ, ?_, key hℓ h1 h2 (Or.inr
      ((SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hq0 6).1 hℓ6))⟩
    have hdvd : ℓ ∣ Nat.card X * Nat.gcd 4 (q + 1) := by
      rw [hc]
      exact Dvd.dvd.mul_left hℓ3 _
    rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with h | h
    · exact h
    · exact absurd h (hℓg hℓ h1 (Nat.gcd_dvd_left _ _))

theorem false_of_barData6_statedSp_two {K : Type} [Field K] [Finite K] {p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = p ^ f₀) (hZ : center (StatedProj (StatedSp 2 K)) = ⊥)
    (hcard : Nat.card (StatedProj (StatedSp 2 K)) * 2 =
      (p ^ f₀) ^ 4 * (((p ^ f₀) ^ 2 - 1) * ((p ^ f₀) ^ 4 - 1)))
    {E : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} {L : Subgroup (StatedProj (StatedSp 2 K))}
    {t : StatedProj (StatedSp 2 K)} {J J₀ : Subgroup (StatedProj (StatedSp 2 K))}
    (h : BarData6 E L t J J₀ p f) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLlt : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) < Nat.card (StatedProj (StatedSp 2 K)) :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
      (lt_of_le_of_ne (Subgroup.card_le_card_group L)
        fun h1 => h.hLtop ((Subgroup.card_eq_iff_eq_top L).1 h1))
  obtain ⟨g, c, hg0, hg4, hc, hLc⟩ := card_mul_le_of_isL4U4Mod4 hp2 h.hLm
  have hq3 : 3 ≤ p ^ f := (show 3 ≤ p by have := hp.two_le; omega).trans
    (Nat.le_self_pow (by omega) p)
  have hqq : p ^ f < p ^ f₀ := by
    by_contra hge
    have hle := QPUCl.psp4_order_le (not_lt.mp hge)
    have hq27 : 27 ≤ (p ^ f) ^ 3 :=
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hA : (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) * 26 ≤
        (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) * c := by
      have h1 : (p ^ f) ^ 4 ≤ (p ^ f) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) (by omega)
    have hgle : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) * g ≤
        Nat.card (↥L ⧸ pPrimeCore 2 ↥L) * 4 := Nat.mul_le_mul_left _ hg4
    omega
  have hq₀ : 5 ≤ p ^ f₀ := by
    obtain ⟨k, hk⟩ := (hp.eq_two_or_odd'.resolve_left hp2).pow (n := f₀)
    omega
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective t
  set A : gsp 2 K := ⟨(g' : GL (Fin 2 ⊕ Fin 2) K), statedSp_le_gsp g'.2⟩ with hAdef
  have hα : ∀ x, conjAut 2 K A x = (g' : StatedProj (StatedSp 2 K)) * x *
      (g' : StatedProj (StatedSp 2 K))⁻¹ := QPUCl.conjAut_statedSp_apply g'
  have hcent : centralizer ({(g' : StatedProj (StatedSp 2 K))} : Set _) =
      fixOf (conjAut 2 K A) := by
    ext x
    rw [mem_centralizer_singleton_iff, mem_fixOf, hα]
    constructor
    · intro hx
      rw [← hx, mul_inv_cancel_right]
    · intro hx
      calc x * (g' : StatedProj (StatedSp 2 K)) =
          (g' : StatedProj (StatedSp 2 K)) * x * (g' : StatedProj (StatedSp 2 K))⁻¹ * g' := by
            rw [hx]
        _ = (g' : StatedProj (StatedSp 2 K)) * x := by group
  have hα1 : conjAut 2 K A ≠ 1 := fun h1 => h.ht1 (by
    have hgZ : (g' : StatedProj (StatedSp 2 K)) ∈ center (StatedProj (StatedSp 2 K)) :=
      mem_center_iff.mpr fun x => by
        have hx := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ x) h1
        simp only [MulAut.one_apply, hα] at hx
        calc x * (g' : StatedProj (StatedSp 2 K)) =
            (g' : StatedProj (StatedSp 2 K)) * x * (g' : StatedProj (StatedSp 2 K))⁻¹ * g' := by
              rw [hx]
          _ = (g' : StatedProj (StatedSp 2 K)) * x := by group
    rw [hZ] at hgZ
    exact mem_bot.mp hgZ)
  obtain ⟨d, hAA⟩ := QPUCl.exists_mul_self_eq_smul_one g' h.ht2
  have hJX : J ≤ fixOf (conjAut 2 K A) := h.hJt.trans hcent.le
  have hJc' : IsPComponent 2 (J.subgroupOf (fixOf (conjAut 2 K A))) := by
    rw [← hcent]
    exact h.hJc
  have hJs : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := QPUCl.lieModel_psl_two_isSimpleGroup h.hJm
  have : Group.IsPerfect ↥J := QPUCl.isPerfect_of_isPComponent hJX hJc'
  have : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
      (QuotientGroup.mk'_surjective _)
  have hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := QPUCl.center_eq_bot_of_simple_perfect'
  have hJ2 := QPUCl.card_mul_two_of_lieModel_psl_two hp hp2 h.hJm
  have hsimple : IsSimpleGroup ↥J →
      Nat.card ↥J * 2 = p ^ (2 * f) * ((p ^ (2 * f)) ^ 2 - 1) := fun hs => by
    have hO : pPrimeCore 2 ↥J = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥J) with hO | hO
      · exact hO
      · exfalso
        have : Subsingleton (↥J ⧸ pPrimeCore 2 ↥J) := by
          rw [hO]
          exact QuotientGroup.subsingleton_quotient_top
        exact hJs.toNontrivial.exists_pair_ne.elim
          fun x hx => hx.elim fun y hxy => hxy (Subsingleton.elim x y)
    rw [← hJ2, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hO).trans
      QuotientGroup.quotientBot).toEquiv]
  have hq2 : 1 ≤ p ^ (2 * f) := Nat.one_le_pow _ _ hp.pos
  rcases X10Sp4.inner_cases hp hp2 hf₀ hK hq₀ A d hAA hα1 hJX hJc' with
    hS1 | ⟨-, hs, hJcard⟩ | ⟨hs, hJcard⟩
  ·
    obtain ⟨eS⟩ := hS1
    have hchar : ringChar K ≠ 2 := by
      have : CharP K p :=
        LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf₀ hK
      rw [ringChar.eq K p]
      exact hp2
    set z : ↥J := eS.symm (-1) with hzdef
    have hzc : ∀ w : ↥J, w * z = z * w := fun w => by
      apply eS.injective
      simp only [hzdef, map_mul, MulEquiv.apply_symm_apply, mul_neg_one, neg_one_mul]
    have hne : (-1 : SL(2, K)) ≠ 1 := fun h1 => by
      have h00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
      have hm1 : ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = -1 := by
        rw [SpecialLinearGroup.coe_neg]
        rfl
      have hp1 : ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := rfl
      exact Ring.neg_one_ne_one_of_char_ne_two hchar (hm1.symm.trans (h00.trans hp1))
    have hzo : orderOf z = 2 := by
      rw [hzdef, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [neg_one_sq]) hne
    have hzO : z ∈ pPrimeCore 2 ↥J := by
      have hc' : QuotientGroup.mk' (pPrimeCore 2 ↥J) z ∈ center (↥J ⧸ pPrimeCore 2 ↥J) :=
        mem_center_iff.mpr fun w => by
          obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) w
          rw [← map_mul, ← map_mul, hzc w']
      rw [hZJ, mem_bot] at hc'
      exact (QuotientGroup.eq_one_iff z).1 hc'
    have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2) hzO
    rw [hzo] at hcop
    exact absurd hcop (by decide)
  ·
    rw [GorensteinWalter.sl2_card_formula K, hK, hsimple hs] at hJcard
    have he := QPUCl.eq_of_mul_sq_sub_one_eq hq2 (by omega) hJcard
    obtain ⟨ℓ, hℓ, hℓL, hℓP⟩ := exists_prime_dvd_not_dvd_psp4_sq hp hp2 h.hLm
    have hdvdP : ℓ ∣ Nat.card (StatedProj (StatedSp 2 K)) :=
      hℓL.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L))
    apply hℓP
    have hq₀ : p ^ f₀ = (p ^ f) ^ 2 := by rw [← he, ← pow_mul, mul_comm]
    rw [hq₀] at hcard
    have e4 : ((p ^ f) ^ 2) ^ 4 = (p ^ f) ^ 8 := by ring
    have e2 : ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 := by ring
    rw [e4, e2] at hcard
    rw [← hcard]
    exact Dvd.dvd.mul_right hdvdP 2
  ·
    rw [hsimple hs] at hJcard
    have he := QPUCl.eq_of_mul_sq_sub_one_eq hq2 (Nat.one_le_pow _ _ (by omega)) hJcard
    have hlt : (p ^ f) ^ 2 < (p ^ f₀) ^ 2 := Nat.pow_lt_pow_left hqq (by norm_num)
    rw [← pow_mul, mul_comm] at hlt
    omega

theorem false_of_barConfig6_psp {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hP : StatedClassicalModel P .PSp n p f₀) (h : BarConfig6 P p f) : False := by
  have hadm : StatedLieAdmissible .PSp n p f₀ := hP.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hf₀ : 1 ≤ f₀ := hadm.2.1
  have hLM : LieModel P .PSp n p f₀ := Or.inl ⟨by decide, hP⟩
  have : IsSimpleGroup P :=
    ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp P n p f₀ hP
  have hFT : FixedTwoComponentsQuasisimple P := fixedTwoComponentsQuasisimple_psp hp2 hP
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hP
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (StatedProj (StatedSp n K)) := e.symm.isSimpleGroup
  obtain ⟨E, L, t, J, J₀, hd⟩ := h
  have hd' := hd.map e
  have hZ := center_eq_bot_of_barData6 hd'
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  ·
    have hcard : Nat.card (StatedProj (StatedSp 2 K)) * 2 =
        (p ^ f₀) ^ 4 * (((p ^ f₀) ^ 2 - 1) * ((p ^ f₀) ^ 4 - 1)) := by
      rw [← Nat.card_congr e.toEquiv]
      exact QPUCl.card_mul_two_of_lieModel_psp_two hp hp2 hLM
    exact false_of_barData6_statedSp_two hp hp2 hf hf₀ hK hZ hcard hd'
  ·
    have hQ : FixedTwoComponentsQuasisimple (StatedProj (StatedSp n K)) :=
      FixedTwoComponentsQuasisimple.of_mulEquiv e.symm hFT
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e t)
    obtain ⟨hA, J', hJ'c, hJ'z, hJ'm⟩ := exists_component_of_J hQ hZ hd'.ht2 hd'.ht1 hd'.hJt
      hd'.hJc hd'.hJm _ (fun x => by rw [QPUCl.conjAut_statedSp_apply g x, hg])
    rcases CatLeafProof.X10Sp.inner_psp_component_cases hp hp2 hK hadm hn3 _ hA hJ'c with
      ⟨z, hz, hzc, hzz, hz1⟩ | hcm | ⟨-, hcm⟩ | hcm
    · exact hz1 (hJ'z z hz hzc hzz)
    · obtain ⟨-, hk2, -⟩ :=
        QPUCl.eq_of_centralModel_of_lieModel hp hp2 (by omega) hJ'm (Or.inl rfl) hcm
      omega
    · obtain ⟨ht, -, -⟩ :=
        QPUCl.eq_of_centralModel_of_lieModel hp hp2 (by omega) hJ'm (Or.inr (Or.inr (Or.inl rfl)))
          hcm
      exact absurd ht (by decide)
    · obtain ⟨ht, -, -⟩ :=
        QPUCl.eq_of_centralModel_of_lieModel hp hp2 (by omega) hJ'm (Or.inr (Or.inl rfl)) hcm
      exact absurd ht (by decide)

end CFSG.ComponentClassification.GSThmB.QPUJ6Cl
