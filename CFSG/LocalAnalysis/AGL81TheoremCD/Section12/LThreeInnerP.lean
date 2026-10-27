module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

variable {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

private theorem card_outer_psl_three_zmod_dvd :
    Nat.card (Outer (PSL(3, ZMod p))) ∣ 2 * Nat.gcd 3 (p - 1) := by
  have h := higher_linear_outer_order_divides_field_gcd_bound
    (k := ZMod p) (p := p) (f := 1) (n := 3) Fact.out le_rfl (by norm_num) (by simp)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      (ZMod p))).toEquiv]
  simpa using h

private theorem not_dvd_card_outer_of_isPSLType_three (hp5 : 5 ≤ p) {K : Type} [Group K]
    (hK : IsPSLType 3 (ZMod p) K) : ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨e⟩ := hK
  have hout : Nat.card (Outer K) ∣ 2 * Nat.gcd 3 (p - 1) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact card_outer_psl_three_zmod_dvd (p := p)
  intro h
  have hp : p.Prime := Fact.out
  rcases hp.dvd_mul.mp (h.trans hout) with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    omega
  · have h3' : p ∣ 3 := h3.trans (Nat.gcd_dvd_left 3 (p - 1))
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'
    omega

theorem le_sup_centralizer_of_isPGroup_of_isPSLType_three {K R : Subgroup A}
    (hp5 : 5 ≤ p) (hK : IsPSLType 3 (ZMod p) ↥K) (hR : IsPGroup p R)
    (hRK : R ≤ Subgroup.normalizer (K : Set A)) :
    R ≤ K ⊔ Subgroup.centralizer (K : Set A) := by
  classical
  let φ : ↥R →* Outer ↥K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)).comp
      (K.normalizerMonoidHom.comp (Subgroup.inclusion hRK))
  have htop : IsPGroup p (⊤ : Subgroup ↥R) := hR.of_equiv Subgroup.topEquiv.symm
  have hrange : IsPGroup p φ.range := by
    rw [MonoidHom.range_eq_map]
    exact htop.map φ
  have hdvd : Nat.card φ.range ∣ Nat.card (Outer ↥K) := by
    simpa using Subgroup.card_dvd_of_le (H := φ.range) (K := ⊤) le_top
  have hrange1 : Nat.card φ.range = 1 := by
    obtain ⟨n, hn⟩ := hrange.exists_card_eq
    cases n with
    | zero => simpa using hn
    | succ m =>
      exfalso
      exact not_dvd_card_outer_of_isPSLType_three hp5 hK
        ((hn ▸ dvd_pow_self p (Nat.succ_ne_zero m)).trans hdvd)
  intro r hr
  have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp hrange1
  have hmem : φ ⟨r, hr⟩ ∈ φ.range := MonoidHom.mem_range.mpr ⟨⟨r, hr⟩, rfl⟩
  rw [hbot] at hmem
  have hinner :
      K.normalizerMonoidHom ⟨r, hRK hr⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := by
    apply (QuotientGroup.eq_one_iff _).mp
    have hinc : (Subgroup.inclusion hRK) ⟨r, hr⟩ = ⟨r, hRK hr⟩ := rfl
    simpa [φ, hinc] using Subgroup.mem_bot.mp hmem
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hinner
  exact CFSG.StandardType.GGRootNorm.mem_sup_centralizer_of_induced_inner (hRK hr) hk.symm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
