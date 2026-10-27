module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.OddCentral
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Radical

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {B Ã : Type} [Group B] [Finite B] [Group Ã] [Finite Ã]

theorem eq_lift2_map (φ : B →* Ã) (hker : φ.ker ≤ Subgroup.center B)
    (hodd : Odd (Nat.card φ.ker)) (hsurj : Function.Surjective φ) {P : Subgroup B}
    (hP2 : IsPGroup 2 ↥P) : P = lift2 φ (P.map φ) := by
  have hPle : P ≤ lift2 φ (P.map φ) :=
    le_lift2 φ hker (hP2.map φ) (Subgroup.le_comap_map φ P) hP2
  refine Subgroup.eq_of_le_of_card_ge hPle ?_
  refine le_of_eq ?_
  calc Nat.card ↥(lift2 φ (P.map φ)) = Nat.card ↥((lift2 φ (P.map φ)).map φ) :=
        (card_map_of_isPGroup φ hodd (lift2_isPGroup φ _)).symm
    _ = Nat.card ↥(P.map φ) := by rw [map_lift2 φ hker hodd hsurj (hP2.map φ)]
    _ = Nat.card ↥P := card_map_of_isPGroup φ hodd hP2

theorem isTwoRadicalIn_map_of_odd (φ : B →* Ã) (hker : φ.ker ≤ Subgroup.center B)
    (hodd : Odd (Nat.card φ.ker)) (hsurj : Function.Surjective φ) {P : Subgroup B}
    (hP : IsTwoRadicalIn ⊤ P) : IsTwoRadicalIn ⊤ (P.map φ) := by
  obtain ⟨-, hne, hP2, hmax⟩ := isTwoRadicalIn_iff.1 hP
  have hPeq := eq_lift2_map φ hker hodd hsurj hP2
  refine isTwoRadicalIn_iff.2 ⟨le_top, ?_, hP2.map φ, ?_⟩
  · intro h
    apply hne
    have h1 := card_map_of_isPGroup φ hodd hP2
    rw [h, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq P h1.symm
  · intro T' hT' hT'2 hTn
    have hN1 : ∀ n, n ∈ Subgroup.normalizer (P : Set B) →
        φ n ∈ Subgroup.normalizer ((P.map φ : Subgroup Ã) : Set Ã) := fun n hn =>
      Subgroup.le_normalizer_map φ ⟨n, hn, rfl⟩
    have hTle : lift2 φ T' ≤ ⊤ ⊓ Subgroup.normalizer (P : Set B) := by
      intro t ht
      refine ⟨trivial, ?_⟩
      have h1 : φ t ∈ T' := lift2_le_comap φ T' ht
      have h2 := mem_normalizer_lift2 φ hker (hP2.map φ) (n := t) (hT' h1).2
      rwa [← hPeq] at h2
    have hnormal : ((lift2 φ T').subgroupOf (⊤ ⊓ Subgroup.normalizer (P : Set B))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hTle]
      intro x k hx hk
      have hk' : φ k ∈ Subgroup.normalizer ((P.map φ : Subgroup Ã) : Set Ã) := hN1 k hk.2
      have hkinv' : φ k⁻¹ ∈ Subgroup.normalizer ((P.map φ : Subgroup Ã) : Set Ã) := by
        rw [map_inv]; exact Subgroup.inv_mem _ hk'
      have hφk : φ k ∈ Subgroup.normalizer (T' : Set Ã) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        refine ⟨fun hy => (Subgroup.normal_subgroupOf_iff hT').1 hTn y (φ k) hy ⟨trivial, hk'⟩,
          fun hy => ?_⟩
        have := (Subgroup.normal_subgroupOf_iff hT').1 hTn _ (φ k⁻¹) hy ⟨trivial, hkinv'⟩
        simpa [map_inv, mul_assoc] using this
      have := mem_normalizer_lift2 φ hker hT'2 hφk
      exact (Subgroup.mem_normalizer_iff.1 this x).1 hx
    have hTP := hmax _ hTle (lift2_isPGroup φ T') hnormal
    calc T' = (lift2 φ T').map φ := (map_lift2 φ hker hodd hsurj hT'2).symm
      _ ≤ P.map φ := Subgroup.map_mono hTP

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
