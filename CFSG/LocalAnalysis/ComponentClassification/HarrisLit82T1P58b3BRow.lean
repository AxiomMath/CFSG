module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BX
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieB

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

namespace P58b3

section XLevel

variable {X : Type} [Group X] [Finite X]

theorem odd_of_isTwoComponentIn (hX : IsQuasisimple X) (hZ2 : Nat.card (center X) = 2) {n : ℕ}
    (hn4 : 4 ≤ n) (hm : Blueprint.LieModel (X ⧸ center X) .POmegaOdd n 3 1) {c t : X}
    (hcZ : c ∈ center X) (hc2 : orderOf c = 2) (ht2 : orderOf t = 2) (htZ : t ∉ center X)
    {Q₁ L : Subgroup X} (hQ₁ : IsSolvableTwoComponentIn Q₁ (centralizer {t})) (hcQ₁ : c ∈ Q₁)
    (hL : IsTwoComponentIn L (centralizer {t})) (htL : t ∈ L) : Odd n := by
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hcm := hc
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
  have hK3 : Nat.card K = 3 := by rw [hKc, pow_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n K)
    (regular_coordinateQuadOdd n K h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadOdd n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  set θ := (coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
  have hker : OKer (oQ R) := OKer.transport 1 1 hS₁ (oKer_coordinateOdd hcm K hKc e)
  obtain ⟨α, hα⟩ := exists_spin_compat_three hK3 h2 hn4 hX hZ2 e
  set s := α.symm t with hs
  have hss : s * s = 1 := by
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at this
    rw [hs, ← map_mul, htt, map_one]
  obtain ⟨T', hT'p, hT'm⟩ := P58b.OLie.coordinateOdd_proj_spin h2 hn hS₁ s
  have hθT' : θ (QuotientGroup.mk t) = projH _ T' := by
    have ht : t = α s := by rw [hs, MulEquiv.apply_symm_apply]
    change oTransport 1 1 hS₁ (statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n K)
      (coe_quadOdd n K) (e (QuotientGroup.mk t))) = projH _ T'
    rw [ht, hα s]
    exact hT'p
  have hM2 : (spinMatrix (quadOdd n K) s).val * (spinMatrix (quadOdd n K) s).val = 1 := by
    rw [← Units.val_mul, ← map_mul, hss, map_one, Units.val_one]
  have hT'2 : T'.val.val * T'.val.val = 1 := by
    rw [hT'm, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hM2, Matrix.submatrix_one_equiv]
  have hrank' := rank_lift_eq_three hK3 ⟨n, rfl⟩ hR hker θ hZ2 hcZ hc2 htZ T'.2 hT'2 hθT' hQ₁
    hcQ₁ hL htL
  have hrankM : ((spinMatrix (quadOdd n K) s).val + 1).rank = 3 := by
    calc ((spinMatrix (quadOdd n K) s).val + 1).rank =
        (Matrix.reindex (oddIndexEquiv n) (oddIndexEquiv n)
          ((spinMatrix (quadOdd n K) s).val + 1)).rank :=
          (Matrix.rank_reindex _ _ _).symm
      _ = (T'.val.val + 1).rank := by
          rw [hT'm, Matrix.reindex_apply, Matrix.reindex_apply]
          congr 1
          ext i j
          simp [Matrix.one_apply]
      _ = 3 := hrank'
  have hcardσ : Fintype.card (Fin n ⊕ Fin n ⊕ Unit) = 2 * n + 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    ring
  have hker' := P58b.OLie.finrank_ker_add_rank (quadOdd n K) s
  rw [hrankM, hcardσ] at hker'
  have hev := P58b.OLie.even_choose_finrank_ker h2 (nondegenerate_polarBilin_quadOdd n K h2) s hss
  have hmk : Module.finrank K (LinearMap.ker ((spinAction (quadOdd n K) s :
      (Fin n ⊕ Fin n ⊕ Unit → K) →ₗ[K] Fin n ⊕ Fin n ⊕ Unit → K) + LinearMap.id)) =
      2 * (n - 1) := by omega
  rw [hmk, Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ two_pos, Nat.even_mul] at hev
  rcases hev with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨j, by omega⟩
  · omega

theorem false_of_isSolvableTwoComponentIn (hX : IsQuasisimple X)
    (hZ2 : Nat.card (center X) = 2) {n : ℕ} (hn4 : 4 ≤ n)
    (hm : Blueprint.LieModel (X ⧸ center X) .POmegaOdd n 3 1) {c t : X} (hcZ : c ∈ center X)
    (hc2 : orderOf c = 2) (ht2 : orderOf t = 2) (htZ : t ∉ center X) {Q₁ Q₂ : Subgroup X}
    (hQ₁ : IsSolvableTwoComponentIn Q₁ (centralizer {t})) (hcQ₁ : c ∈ Q₁)
    (hQ₂ : IsSolvableTwoComponentIn Q₂ (centralizer {t})) (htQ₂ : t ∈ Q₂) : False := by
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hcm := hc
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
  have hK3 : Nat.card K = 3 := by rw [hKc, pow_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n K)
    (regular_coordinateQuadOdd n K h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadOdd n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  set θ := (coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
  have hker : OKer (oQ R) := OKer.transport 1 1 hS₁ (oKer_coordinateOdd hcm K hKc e)
  obtain ⟨α, hα⟩ := exists_spin_compat_three hK3 h2 hn4 hX hZ2 e
  set s := α.symm t with hs
  have hss : s * s = 1 := by
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at this
    rw [hs, ← map_mul, htt, map_one]
  obtain ⟨T', hT'p, hT'm⟩ := P58b.OLie.coordinateOdd_proj_spin h2 hn hS₁ s
  have hθT' : θ (QuotientGroup.mk t) = projH _ T' := by
    have ht : t = α s := by rw [hs, MulEquiv.apply_symm_apply]
    change oTransport 1 1 hS₁ (statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n K)
      (coe_quadOdd n K) (e (QuotientGroup.mk t))) = projH _ T'
    rw [ht, hα s]
    exact hT'p
  have hM2 : (spinMatrix (quadOdd n K) s).val * (spinMatrix (quadOdd n K) s).val = 1 := by
    rw [← Units.val_mul, ← map_mul, hss, map_one, Units.val_one]
  have hT'2 : T'.val.val * T'.val.val = 1 := by
    rw [hT'm, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hM2, Matrix.submatrix_one_equiv]
  exact false_of_lift hK3 ⟨n, rfl⟩ (by omega) hR hker θ hZ2 hcZ hc2 htZ T'.2 hT'2 hθT' hQ₁ hcQ₁
    hQ₂ htQ₂

end XLevel

theorem harris82Lemma58bThreeRowAt_POmegaOdd_one (hGA : TBLit.GriessMultipliersAllModels)
    (n : ℕ) : Harris82Lemma58bThreeRowAt .POmegaOdd n 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ hL₂ hz₁L hz₂L _ hKc hO₁ hO₂ hN hz₂K hz₂Z hm
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  have hz₁Z := mem_center_of_le_centralizer hKc.1 hz₁K
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥K
  set X := ↥K ⧸ pPrimeCore 2 ↥K with hXdef
  have hX : IsQuasisimple X := hKc.2.2.2
  have hO : pPrimeCore 2 X = ⊥ := CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
  have hmX : Blueprint.LieModel (X ⧸ center X) .POmegaOdd n 3 1 :=
    GSThmB.OddQuot.lieModel_of_equiv eZ hm
  set c : X := QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ with hcdef
  set t : X := QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩ with htdef
  have hc2 : orderOf c = 2 := P58b.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hz₁)
  have ht2 : orderOf t = 2 := P58b.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hz₂)
  have hcZ : c ∈ center X := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) g
    rw [hcdef, ← map_mul, ← map_mul, mem_center_iff.mp hz₁Z g]
  have htZ : t ∉ center X := hz₂Z
  have hZ2 := P58b.card_center_eq_two_of_POmegaOdd hGA hX hO hc2 hcZ hmX
  have hcov : IsCoverOf .POmegaOdd n 3 1 2 X := ⟨hX, hZ2, hmX⟩
  have ha := oddAutInner_of_isCoverOf_POmegaOdd_three Nat.prime_three (by norm_num) hcov
  have hb := cyclicCenterTwo_of_card_center_eq_two hZ2
  have hQ₁ := lemma57_fourGroup_map hz₂ hL₁ hKc.1 hO₁ hN hz₂K ha hb
  have hcQ₁ : c ∈ ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
    ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
  have hn3 : 3 ≤ n := by
    obtain ⟨-, -, h⟩ := P58b.admissible_of_lieModel hm
    exact h.1
  refine ⟨⟨n, hcov⟩, ?_, ?_⟩
  ·
    rintro ⟨hL₂', -⟩
    have : Group.IsPerfect ↥L₂ := hL₂'.2.2.1
    have hL₂K : L₂ ≤ K :=
      (Sol78.le_oPrimeResidualOf le_rfl primeResidual_eq_top_of_isPerfect).trans hO₂
    have hle : K ⊓ centralizer {z₂} ≤ centralizer {z₁} ⊓ centralizer {z₂} :=
      inf_le_inf_right _ hKc.1
    have hJ : IsTwoComponentIn L₂ (K ⊓ centralizer {z₂}) :=
      ⟨le_inf hL₂K (hL₂'.1.trans inf_le_right), F3L57.isSubnormal_subgroupOf_of_le hle hL₂'.2.1,
        hL₂'.2.2⟩
    have hz₂z₂ : (⟨z₂, hz₂K⟩ : ↥K) * ⟨z₂, hz₂K⟩ = 1 := by
      have h := pow_orderOf_eq_one (⟨z₂, hz₂K⟩ : ↥K)
      rwa [Subgroup.orderOf_mk, hz₂, pow_two] at h
    have hLb := P58b.isTwoComponentIn_map_mk hz₂z₂ (isTwoComponentIn_subgroupOf_inf hz₂K hJ)
    have htLb : t ∈ (L₂.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
      ⟨⟨z₂, hz₂K⟩, mem_subgroupOf.mpr hz₂L, rfl⟩
    rcases (show n = 3 ∨ 4 ≤ n by omega) with h3 | h4
    · subst h3
      exact ((lemma410c_three (by norm_num : 3 ^ 1 = 3) hcov hcZ
        (fun h => by rw [h, orderOf_one] at hc2; exact absurd hc2 (by norm_num)) ht2 htZ).1 _
        hLb).elim
    · have hodd := odd_of_isTwoComponentIn hX hZ2 h4 hmX hcZ hc2 ht2 htZ hQ₁ hcQ₁ hLb htLb
      refine ⟨n, hodd, ?_, hcov⟩
      obtain ⟨k, hk⟩ := hodd
      omega
  ·
    rintro ⟨e₂⟩
    rcases (show n = 3 ∨ 4 ≤ n by omega) with h3 | h4
    · subst h3
      exact hcov
    · exfalso
      have hL₂s : IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) := by
        rcases hL₂ with h | h
        · exfalso
          have : Group.IsSolvable ↥L₂ := isSolvable_of_coreQuot (Or.inr ⟨e₂⟩)
          have : Group.IsPerfect ↥L₂ := h.2.2.1
          have : Nontrivial ↥L₂ := ⟨⟨⟨z₂, hz₂L⟩, 1, fun h' => by
            have h1 : z₂ = 1 := congrArg Subtype.val h'
            rw [h1, orderOf_one] at hz₂
            exact absurd hz₂ (by norm_num)⟩⟩
          exact Group.IsPerfect.not_isSolvable ↥L₂ inferInstance
        · exact h
      have hQ₂ := lemma57_fourGroup_map hz₂ hL₂s hKc.1 hO₂ hN hz₂K ha hb
      have htQ₂ : t ∈ ((L₂ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
        ⟨⟨z₂, hz₂K⟩, mem_subgroupOf.mpr ⟨hz₂L, hz₂K⟩, rfl⟩
      exact false_of_isSolvableTwoComponentIn hX hZ2 h4 hmX hcZ hc2 ht2 htZ hQ₁ hcQ₁ hQ₂ htQ₂

theorem harris82Lemma58bThreeRow_POmegaOdd_of (hGA : TBLit.GriessMultipliersAllModels) {n : ℕ}
    (h : ∀ f : ℕ, 2 ≤ f → Harris82Lemma58bThreeRowAt .POmegaOdd n f) :
    Harris82Lemma58bThreeRow .POmegaOdd n :=
  harris82Lemma58bThreeRow_of_at fun f hf => by
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | h2
    · exact harris82Lemma58bThreeRowAt_POmegaOdd_one hGA n
    · exact h f h2

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
