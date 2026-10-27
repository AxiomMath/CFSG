module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1F4
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise
public import CFSG.RankThree.PartOne.KE.E8RootCharacterTorus

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free)

theorem e8_normalForm
    {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hk : ∃ f : ℕ, 1 ≤ f ∧ Nat.card k = p ^ f) (α : MulAut (adjointGroup .E8 k)) :
    ∃! gφ : adjointGroup .E8 k × (k ≃+* k), ∀ h : adjointGroup .E8 k,
      (α h : ModGL .E8 k) = (gφ.1 : ModGL .E8 k) *
        Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL .E8 k) * (gφ.1 : ModGL .E8 k)⁻¹ :=
  (inner_field_automorphism_normal_form_of_params hp hk.choose_spec.1 hk.choose_spec.2
    (fun _ hβ => exists_exactNormalAut_zero_eq_E7_E8 (Or.inr rfl) hβ)
    (fun a => RankThree.PartOne.KE.rootDiagUnit_E8_mem_adjointGroup a)).1 α

theorem burgOddCoreRow_E8
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : BurgOddCoreRow (adjointGroup .E8 K) := by
  intro α hα
  have hf := one_le_of_card_eq_pow hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inr (Or.inl rfl)) hKodd hα2 with
    ⟨g, a, hαg⟩ | ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · refine burgOddCoreFor_innerDiagonal (Or.inr (Or.inr rfl)) hK2 (fun _ => True)
      (fun b hb => (exists_mem_rootCharKernel_of_isRoot_add (i := 0) (j := 2) hb
        (mem_rootFinset.1 (by decide +kernel))).imp fun γ hγ => ⟨hγ, fun _ _ _ => trivial⟩)
      (fun b hb hb1 => pPrimeCore_toralCentralizer_E8 hK2 hb hb1)
      (fun k _ h hU Z hZ η hη _ => (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free
        .E8 (Or.inr (Or.inr rfl)) K (AlgebraicClosure K) k 1 h hU Z hZ).2.2.2 rfl η hη) hαg hα
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    have hdet : Tag.E8.cartan.transpose.det = 1 := by
      rw [Matrix.det_transpose]
      exact exceptional_Lang_exact_root_arithmetic.{0}.1.2.2.2.2.2
    exact burgOddCoreFor_quadratic_field .E8 hdet hq hp2 he hKe δ hδ
      (fun k _ _ hk => e8_normalForm hq hk) hαg hα

end CFSG.ComponentClassification.CatLeafProof
