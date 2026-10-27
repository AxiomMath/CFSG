module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsL33
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv
open scoped MatrixGroups

section Numeric

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem conj_injective_of_center_eq_bot' (h : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have hc : k ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro a
    have h1 := congrArg (fun f : MulAut K => f a) hk
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc a * k = (k * a * k⁻¹) * k := by rw [h1]
      _ = k * a := by group
  rw [h] at hc
  exact hc

theorem mem_innAut_of_card (hZ : Subgroup.center K = ⊥)
    (hcard : Nat.card (MulAut K) ≤ 2 * Nat.card K ∨ Nat.card (MulAut K) = 4 * Nat.card K)
    (g : MulAut K) (hg : g ^ 3 = 1) : g ∈ innAut K := by
  by_contra hgn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  have := innAut_normal K
  let π : MulAut K →* MulAut K ⧸ innAut K := QuotientGroup.mk' (innAut K)
  have hπg : π g ≠ 1 := fun h => hgn ((QuotientGroup.eq_one_iff g).mp h)
  have hπ3 : (π g) ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have hord : orderOf (π g) = 3 := orderOf_eq_prime hπ3 hπg
  have hdvd : 3 ∣ Nat.card (MulAut K ⧸ innAut K) := hord ▸ orderOf_dvd_natCard (π g)
  have hcard2 : Nat.card (MulAut K) = Nat.card (MulAut K ⧸ innAut K) * Nat.card (innAut K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hinn : Nat.card (innAut K) = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center_eq_bot' hZ)).toEquiv).symm
  have h3 : 3 * Nat.card K ∣ Nat.card (MulAut K) := by
    rw [hcard2, hinn]
    exact Nat.mul_dvd_mul_right hdvd _
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hApos : 0 < Nat.card (MulAut K) := Nat.card_pos
  rcases hcard with h | h
  · have := Nat.le_of_dvd hApos h3
    omega
  · rw [h] at h3
    have : 3 ∣ 4 := Nat.dvd_of_mul_dvd_mul_right hKpos h3
    omega

end Numeric

section Cards

theorem card_mulAut_alt {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = 2 * Nat.card (alternatingGroup (Fin n)) := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  have h1 : Nat.card (MulAut (alternatingGroup (Fin n))) = Nat.card (Equiv.Perm (Fin n)) :=
    (Nat.card_eq_of_bijective _ hb).symm
  have h2 : Nat.card (alternatingGroup (Fin n)) * (alternatingGroup (Fin n)).index =
      Nat.card (Equiv.Perm (Fin n)) := Subgroup.card_mul_index _
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [alternatingGroup.index_eq_two] at h2
  omega

theorem card_mulAut_psl2_le_two_mul (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hK : Nat.card K = p) (h3 : 3 < p) (heven : 2 ∣ p * (p ^ 2 - 1)) :
    Nat.card (MulAut PSL(2, K)) ≤ 2 * Nat.card PSL(2, K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hodd, le_rfl, by rw [hK, pow_one]⟩
  have h3' : 3 < Nat.card K := by rw [hK]; exact h3
  have hsub := CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime K hK
  have hR : Nat.card (K ≃+* K) = 1 := by
    have : Unique (K ≃+* K) :=
      { default := RingEquiv.refl K, uniq := fun _ => Subsingleton.elim _ _ }
    exact Nat.card_unique
  have hP : Nat.card (CFSG.GorensteinWalter.PGammaL2 K) = p * (p ^ 2 - 1) := by
    rw [SemidirectProduct.card, CFSG.GorensteinWalter.pgl2_card_formula, hR, hK, mul_one]
  have hp2 : 1 < p ^ 2 := by nlinarith
  have : Finite (CFSG.GorensteinWalter.PGammaL2 K) :=
    Nat.finite_of_card_ne_zero (by rw [hP]; exact Nat.mul_ne_zero hp.ne_zero (by omega))
  have h1 : Nat.card (MulAut PSL(2, K)) ≤ Nat.card (CFSG.GorensteinWalter.PGammaL2 K) :=
    Nat.card_le_card_of_surjective _
      (CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective K (p := p) (f := 1)
        (by rw [hK, pow_one]) hpp h3')
  rw [hP] at h1
  have h2 := CFSG.Walter.Suzuki.card_psl2_of_card K hpp hK
  obtain ⟨m, hm⟩ := heven
  rw [h2, hm]
  have : 2 * m / 2 = m := by omega
  rw [this]
  omega

end Cards

section Eight

variable {G : Type} [Group G] [Finite G]

theorem kInEight_card_aut
    {K : Subgroup G} (hK : KInEight K) :
    Nat.card (MulAut ↥K) ≤ 2 * Nat.card ↥K ∨ Nat.card (MulAut ↥K) = 4 * Nat.card ↥K := by
  have hcongr : ∀ {X : Type} [Group X], (↥K ≃* X) →
      Nat.card (MulAut ↥K) = Nat.card (MulAut X) ∧ Nat.card ↥K = Nat.card X := fun e =>
    ⟨Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv⟩
  unfold KInEight at hK
  rcases hK with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | hm17 | hm33 | ⟨⟨e⟩⟩
  · obtain ⟨h1, h2⟩ := hcongr e
    left
    rw [h1, h2, card_mulAut_alt (by norm_num) (by norm_num)]
  · right
    rw [card_mulAut_alt6 e, Nat.card_congr e.toEquiv, card_alt6']
  · obtain ⟨h1, h2⟩ := hcongr e
    left
    rw [h1, h2, card_mulAut_alt (by norm_num) (by norm_num)]
  · obtain ⟨h1, h2⟩ := hcongr e
    left
    rw [h1, h2, card_mulAut_alt (by norm_num) (by norm_num)]
  · obtain ⟨h1, h2⟩ := hcongr e
    left
    rw [h1, h2]
    have hF : Nat.card (ZMod 7) = 7 := Nat.card_zmod 7
    exact card_mulAut_psl2_le_two_mul (ZMod 7) (by norm_num) (by decide) hF (by norm_num)
      (by norm_num)
  · obtain ⟨-, F, hFfield, hFfin, hcard, ⟨e⟩⟩ := hm17
    let e' : ↥K ≃* PSL(2, F) :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    obtain ⟨h1, h2⟩ := hcongr e'
    left
    rw [h1, h2]
    have hF : Nat.card F = 17 := by simpa using hcard
    exact card_mulAut_psl2_le_two_mul F (by norm_num) (by decide) hF (by norm_num) (by norm_num)
  · left
    exact (l33AutFacts G K hm33).aut_card
  · obtain ⟨h1, h2⟩ := hcongr e
    left
    rw [h1, h2]
    have h3 : Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M11)) ≤
        Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
      CFSG.Sporadic.Schreier.m11_mulAut_card
    omega

omit [Finite G] in
theorem kInEight_center_eq_bot
    {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) (hK : KInEight K) :
    Subgroup.center ↥K = ⊥ := by
  have hs : IsSimpleGroup ↥K := by
    unfold KInEight at hK
    rcases hK with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | hm17 | hm33 | ⟨⟨e⟩⟩
    · exact e.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simp))
    · exact e.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simp))
    · exact e.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simp))
    · exact e.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simp))
    · exact e.isSimpleGroup_congr.mpr
        (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num))
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 17 1 hm17).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 hm33).2
    · exact e.isSimpleGroup_congr.mpr CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab ?_
    have hy : y ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hy x]

theorem kInEight_aut_three_inner
    {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) (hK : KInEight K)
    (g : MulAut ↥K) (hg : g ^ 3 = 1) : g ∈ innAut ↥K :=
  mem_innAut_of_card (kInEight_center_eq_bot hq hK) (kInEight_card_aut hK) g hg

end Eight

end CFSG.QuasithinUnique.DoubleA3
