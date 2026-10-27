module

public import CFSG.GH74.Generic.Certificates
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.GH74.Filter.Lie.Suzuki

public section

namespace CFSG.GH74.E2

open CFSG.GH74.Generic CFSG.Assembly.LowTwoRank

theorem rankCertified_of_injective_elementary {G : Type*} [Group G] {A : Type} [Group A] [Finite A]
    (α : A →* G) (hα : Function.Injective α) (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a ^ 2 = 1) {r : ℕ} (hcard : 2 ^ r < Nat.card A) : RankCertified G r :=
  ⟨A, A, inferInstance, inferInstance, inferInstance, α, MonoidHom.id A, Function.surjective_id,
    hcomm, hsq, hcard, by rw [(MonoidHom.ker_eq_bot_iff α).2 hα]; exact bot_le⟩

theorem rankCertified_of_lt_pRank {G : Type} [Group G] [Finite G] {r : ℕ}
    (h : r < CFSG.Open.pRank 2 (⊤ : Subgroup G)) : RankCertified G r := by
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 2 (⊤ : Subgroup G) (by omega)
  have hc : IsMulCommutative E := hE.1
  refine rankCertified_of_injective_elementary E.subtype E.subtype_injective
    (fun a b => mul_comm' a b) (fun a => Subtype.ext ?_) ?_
  · simpa using hE.2 a a.2
  · rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) h

theorem rankCertified_psl_even {F : Type} [Field F] [Finite F] {n f r : ℕ}
    (hF : Nat.card F = 2 ^ f) (hn : 2 ≤ n) (hr : r < f * (n / 2 * ((n + 1) / 2))) :
    RankCertified (StatedProj (StatedSL n F)) r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := n) (a := n / 2) (b := (n + 1) / 2)
    (by omega) (by omega) hF
  exact rankCertified_of_lt_pRank (lt_of_lt_of_le hr h)

theorem rankCertified_suzukiGroup
    {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ} (hr : r < 2 * a + 1) :
    RankCertified (CFSG.Blueprint.suzukiGroup a K) r := by
  obtain ⟨h2, -⟩ := CFSG.LieType.Ree.suzuki_frob_data a hK
  let Sf : K → CFSG.Blueprint.suzukiGroup a K := fun v => CFSG.LieType.Ree.suzukiSElt a K 0 v
  have h0 : Sf 0 = 1 := CFSG.LieType.Ree.suzukiSElt_zero_zero hK
  have hmul : ∀ v w, Sf v * Sf w = Sf (v + w) := fun v w => by
    simp only [Sf]
    rw [CFSG.LieType.Ree.suzukiSElt_mul hK]
    congr 1 <;> simp
  have hinj : Function.Injective Sf := fun v w h => (CFSG.LieType.Ree.suzukiSElt_inj.1 h).2
  refine rankCertified_of_injective_elementary (CFSG.GH74.Filter.Lie.additiveFamilyHom Sf h0 hmul)
    (CFSG.GH74.Filter.Lie.additiveFamilyHom_injective Sf h0 hmul hinj)
    (fun x y => mul_comm x y) (fun x => ?_) ?_
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    calc Multiplicative.toAdd x + Multiplicative.toAdd x = 2 * Multiplicative.toAdd x := by ring
      _ = 0 := by rw [h2, zero_mul]
  · rw [show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK]
    exact Nat.pow_lt_pow_right (by norm_num) hr

end CFSG.GH74.E2
