module

public import CFSG.LargeExtraspecial.DW2AOut
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.H13.A7Nat1233
public import CFSG.Sporadic.J2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3139
public import Certificates.Certificate10019
public import CFSG.LargeExtraspecial.DW2AOutInput
public import CFSG.LargeExtraspecial.Types
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Timmesfeld.Outcome
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.LargeExtraspecial.S12Insp4

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem sub_one_dvd_pow_sub_one (q i : ℕ) : q - 1 ∣ q ^ i - 1 :=
  Nat.sub_one_dvd_pow_sub_one q i

theorem pow_dvd_mul_div {q a P d : ℕ} (hd : d ∣ P) : q ^ a ∣ q ^ a * P / d := by
  rw [Nat.mul_div_assoc _ hd]
  exact dvd_mul_right _ _

theorem two_pow_mul_dvd {f a N : ℕ} (h : (2 ^ f) ^ a ∣ N) : 2 ^ (f * a) ∣ N := by
  rwa [pow_mul]

theorem pow_dvd_ordA {q n : ℕ} (hn : 1 ≤ n) : q ^ (n * (n + 1) / 2) ∣ ordA n q := by
  unfold ordA
  refine pow_dvd_mul_div ((Nat.gcd_dvd_right _ _).trans
    ((sub_one_dvd_pow_sub_one q 2).trans ?_))
  exact Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)

theorem pow_dvd_ordBC {q n : ℕ} (hn : 1 ≤ n) : q ^ (n * n) ∣ ordBC n q := by
  unfold ordBC
  refine pow_dvd_mul_div ((Nat.gcd_dvd_right _ _).trans
    ((sub_one_dvd_pow_sub_one q (2 * 1)).trans ?_))
  exact Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)

theorem pow_dvd_ordD (q n : ℕ) : q ^ (n * (n - 1)) ∣ ordD n q := by
  unfold ordD
  rw [mul_assoc]
  exact pow_dvd_mul_div (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _)

theorem pow_dvd_ordTwistedD (q n : ℕ) : q ^ (n * (n - 1)) ∣ ordTwistedD n q := by
  unfold ordTwistedD
  rw [mul_assoc]
  exact pow_dvd_mul_div (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _)

theorem pow_dvd_ordG2 (q : ℕ) : q ^ 6 ∣ ordG2 q := by
  unfold ordG2
  rw [mul_assoc]
  exact dvd_mul_right _ _

theorem pow_dvd_ordTrialityD4 (q : ℕ) : q ^ 12 ∣ ordTrialityD4 q := by
  unfold ordTrialityD4
  simp only [mul_assoc]
  exact dvd_mul_right _ _

theorem pow_dvd_ordF4 (q : ℕ) : q ^ 24 ∣ ordF4 q := by
  unfold ordF4
  simp only [mul_assoc]
  exact dvd_mul_right _ _

theorem pow_dvd_ordE6 (q : ℕ) : q ^ 36 ∣ ordE6 q := by
  unfold ordE6
  simp only [mul_assoc]
  exact pow_dvd_mul_div (dvd_mul_of_dvd_left
    ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_pow_sub_one q 12)) _)

theorem pow_dvd_ordTwistedE6 (q : ℕ) : q ^ 36 ∣ ordTwistedE6 q := by
  unfold ordTwistedE6
  simp only [mul_assoc]
  refine pow_dvd_mul_div (Dvd.dvd.mul_left (dvd_mul_of_dvd_left
    ((Nat.gcd_dvd_right _ _).trans ?_) _) _)
  simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 9)

theorem pow_dvd_ordE7 (q : ℕ) : q ^ 63 ∣ ordE7 q := by
  unfold ordE7
  simp only [mul_assoc]
  exact pow_dvd_mul_div (dvd_mul_of_dvd_left
    ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_pow_sub_one q 18)) _)

theorem pow_dvd_ordE8 (q : ℕ) : q ^ 120 ∣ ordE8 q := by
  unfold ordE8
  simp only [mul_assoc]
  exact dvd_mul_right _ _

theorem false_of_two_pow_dvd {X : Type} [Group X] (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7)
    {a : ℕ} (ha : 8 ≤ a) (hd : 2 ^ a ∣ Nat.card X) : False := by
  have := h2 a hd
  omega

theorem false_of_three_pow_dvd {X : Type} [Group X]
    (h3 : 3 ^ 4 ∣ Nat.card X * Nat.card (Outer X)) {a b : ℕ} (ha : Nat.card X ∣ a)
    (hb : Nat.card (Outer X) ∣ b) (hab : ¬ 3 ^ 4 ∣ a * b) : False :=
  hab (h3.trans (Nat.mul_dvd_mul ha hb))

theorem false_of_psl {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (h : LieModel X .PSL n 2 f) (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7)
    (h3 : 3 ^ 4 ∣ Nat.card X * Nat.card (Outer X)) : False := by
  have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).1 rfl
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) hn Nat.prime_two hf hcl).1
  have hk := h2 _ (two_pow_mul_dvd (show (2 ^ f) ^ ((n - 1) * (n - 1 + 1) / 2) ∣ Nat.card X by
    rw [hc]; exact pow_dvd_ordA (by omega)))
  have hn4 : n ≤ 4 := by
    by_contra hlt
    have h20 : 4 * 5 ≤ (n - 1) * (n - 1 + 1) :=
      Nat.mul_le_mul (by omega : 4 ≤ n - 1) (by omega : 5 ≤ n - 1 + 1)
    have := Nat.le_mul_of_pos_left ((n - 1) * (n - 1 + 1) / 2) hf
    omega
  simp only [CFSG.RankThree.OuterOrder.determinantParameter] at hout
  interval_cases n
  · have hf2 : f ≤ 2 := by norm_num at hk; omega
    interval_cases f
    · exact false_of_three_pow_dvd h3 (a := 168) (b := 2) (by rw [hc]; decide)
        (by norm_num at hout; exact hout) (by decide)
    · exact false_of_three_pow_dvd h3 (a := 20160) (b := 12) (by rw [hc]; decide)
        (by norm_num at hout; exact hout) (by decide)
  · have hf1 : f = 1 := by norm_num at hk; omega
    subst hf1
    exact false_of_three_pow_dvd h3 (a := 20160) (b := 2) (by rw [hc]; decide)
      (by norm_num at hout; exact hout) (by decide)

theorem false_of_exceptional {X : Type} [Group X] {τ : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {f : ℕ} (hf : 1 ≤ f)
    (hτ : τ ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} :
      Finset CFSG.Assembly.LowTwoRank.StatedLieTag))
    (hG2 : τ = .G2 → 2 ≤ f) (h : LieModel X τ 0 2 f)
    (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7) : False := by
  have hce := DW.chevalleyExceptionalModel_of_lieModel (by revert hτ; cases τ <;> decide) h
  have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hce
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := hG2 rfl
    exact false_of_two_pow_dvd h2 (a := f * 6) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordG2 _))
  · exact false_of_two_pow_dvd h2 (a := f * 12) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordTrialityD4 _))
  · exact false_of_two_pow_dvd h2 (a := f * 24) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordF4 _))
  · exact false_of_two_pow_dvd h2 (a := f * 36) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordE6 _))
  · exact false_of_two_pow_dvd h2 (a := f * 36) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordTwistedE6 _))
  · exact false_of_two_pow_dvd h2 (a := f * 63) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordE7 _))
  · exact false_of_two_pow_dvd h2 (a := f * 120) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordE8 _))

theorem false_of_outcome {X : Type} [Group X] [Finite X] (hX : CFSG.Timmesfeld.Outcome X)
    (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7) (h3 : 3 ^ 4 ∣ Nat.card X * Nat.card (Outer X)) :
    False := by
  rcases hX with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
    ⟨f, hf, τ, hτ, h⟩ | h | he | hJ
  · exact false_of_psl hn hf h h2 h3
  · have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl
    have h9 : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
    have := Nat.le_mul_of_pos_left (n * n) hf
    exact false_of_two_pow_dvd h2 (a := f * (n * n)) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordBC (by omega)))
  · have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.1 rfl
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
    exact false_of_two_pow_dvd h2 (a := f * (n * (n - 1))) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordD _ _))
  · have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.2 rfl
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
    exact false_of_two_pow_dvd h2 (a := f * (n * (n - 1))) (by omega)
      (two_pow_mul_dvd (by rw [hc]; exact pow_dvd_ordTwistedD _ _))
  · exact false_of_exceptional (by omega) (by decide) (fun _ => hf) h h2
  · exact false_of_exceptional hf (by revert hτ; cases τ <;> decide)
      (fun hG => by subst hG; exact absurd hτ (by decide)) h h2
  · obtain ⟨e⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel h
    have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) le_rfl Nat.prime_three le_rfl hcl).1
    simp only [CFSG.RankThree.OuterOrder.determinantParameter] at hout
    exact false_of_three_pow_dvd h3 (a := 6048) (b := 2)
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.Quasithin.H13.A7.nat_card_psu331_dvd)
      (by norm_num at hout; exact hout) (by decide)
  · obtain ⟨e⟩ := he
    have hcX : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (DW.isPGroup_outer_alt6 e)
    have hcop : Nat.Coprime (3 ^ 4) (Nat.card (Outer X)) := by
      rw [hk]
      exact Nat.Coprime.pow _ _ (by decide)
    have h360 := hcop.dvd_of_dvd_mul_right h3
    rw [hcX] at h360
    exact absurd h360 (by decide)
  · obtain ⟨e⟩ := hJ
    have e' : X ≃* NativeSporadic.J2 := e
    have hcX : Nat.card X = 604800 :=
      (Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.J2.card_J2
    obtain ⟨-, -, -, -, -, ⟨eO⟩⟩ :=
      CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model
    have hO : Nat.card (Outer X) = 2 := by
      rw [Nat.card_congr ((equivalence e').trans eO).toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card]
    exact false_of_three_pow_dvd h3 (a := 604800) (b := 2) (dvd_of_eq hcX) (dvd_of_eq hO)
      (by decide)

end CFSG.LargeExtraspecial.S12Insp4
