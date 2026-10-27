module

public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric

public section

namespace CFSG.AGLEmbedding.KFactProofs.TargetTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem finite_mulAut {L : Type} [Group L] [Finite L] : Finite (MulAut L) :=
  Finite.of_injective (fun f : MulAut L => (f : L → L)) (fun _ _ h => MulEquiv.ext (congrFun h))

theorem card_mulAut_dvd {L : Type} [Group L] [Finite L] :
    Nat.card (MulAut L) ∣ Nat.card (Outer L) * Nat.card L := by
  have := finite_mulAut (L := L)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner L)]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_range_dvd _)

theorem target_of_data {p a n m ℓ : ℕ} (hp : p.Prime) {L : Type} [Group L] [Finite L]
    (hsimple : IsSimpleGroup L) (hcard : Nat.card L = p ^ a * n) (hn : ¬ p ∣ n) (ha : 2 ≤ a)
    (hrank : 2 ≤ Open.pRank p (⊤ : Subgroup L))
    (hOutc : IsCyclic (Outer L)) (hOutn : Nat.card (Outer L) ∣ p * m) (hm : ¬ p ∣ m)
    (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hℓn : ℓ ∣ Nat.card L)
    (hℓk : ∀ k, 0 < k → k ≤ a + 1 → ¬ ℓ ∣ p ^ k - 1) :
    JStarTargetTwo p (p ^ (a + 1)) L ∧ JStarTargetCard p a (p ^ (a + 1)) L := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ^ 2 ∣ Nat.card L := hcard ▸ (Dvd.dvd.mul_right (pow_dvd_pow p ha) n)
  have hnc : ∃ x y : L, x * y ≠ y * x := nonabelian_of_simple_of_sq_dvd hp hp2
  let _ : CommGroup (Outer L) := IsCyclic.commGroup
  refine ⟨⟨⟨hsimple, hnc, hrank, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · infer_instance
  · refine ⟨ℓ, hℓ, hℓp, hℓn, fun k hk hkB => hℓk k hk ?_⟩
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hkB
  · intro S
    exact Subgroup.normal_of_isMulCommutative _
  · intro S
    have hf : (Nat.card L).factorization p = a := by
      rw [hcard, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
        (by rintro rfl; exact hn (dvd_zero p)), Finsupp.add_apply,
        Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hn, add_zero]
    rw [Sylow.card_eq_multiplicity, hf]
  · intro S hS
    have := finite_mulAut (L := L)
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have h1 : Nat.card S ∣ Nat.card (MulAut L) := Subgroup.card_subgroup_dvd_card S
    have h2 := h1.trans (card_mulAut_dvd (L := L))
    have h3 : Nat.card (Outer L) * Nat.card L ∣ p ^ (a + 1) * (m * n) := by
      have := Nat.mul_dvd_mul hOutn (dvd_of_eq hcard)
      calc Nat.card (Outer L) * Nat.card L ∣ p * m * (p ^ a * n) := this
        _ = p ^ (a + 1) * (m * n) := by ring
    have h4 : p ^ k ∣ p ^ (a + 1) * (m * n) := by rw [← hk]; exact h2.trans h3
    have hcop : Nat.Coprime (p ^ k) (m * n) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro h
        rcases hp.dvd_mul.1 h with h | h
        · exact hm h
        · exact hn h))
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right h4

end CFSG.AGLEmbedding.KFactProofs.TargetTwo
