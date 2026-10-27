module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3U3
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution Matrix Q5GL2 Q5L3 QuaternionGroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem smallSimpleLeaf_l3Ne3 : SmallSimpleLeaf SmallL3Ne3 := by
  intro Y _ _ _ _ hnab _ hPF R S t hD hc _
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hPF
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hnab
  set N := genFittingFStar Y with hN
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hm
  let e : ↥N ≃* projectiveSL 3 K :=
    (e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  have hoddK : Odd (Nat.card K) := hK ▸ hodd
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  let ι : Y →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥N)
  have hιapp : ∀ (y : Y) (n : ↥N), ι y (e n) = e (MulAut.conjNormal y n) := fun y n => by
    show e ((MulAut.conjNormal y) (e.symm (e n))) = _
    rw [MulEquiv.symm_apply_apply]
  have hιN : ∀ y : Y,
      ι y ∈ ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) → y ∈ N := by
    rintro y ⟨m, hm⟩
    have key : ∀ x : ↥N, (e.symm m : ↥N) * x * (e.symm m)⁻¹ = MulAut.conjNormal y x := by
      intro x
      apply e.injective
      have h1 := DFunLike.congr_fun hm (e x)
      rw [hιapp] at h1
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    have hcen : ((e.symm m : ↥N) : Y)⁻¹ * y ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg Subtype.val (key ⟨x, hx⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h2
      calc x * (((e.symm m : ↥N) : Y)⁻¹ * y) =
          ((e.symm m : ↥N) : Y)⁻¹ * (((e.symm m : ↥N) : Y) * x * ((e.symm m : ↥N) : Y)⁻¹) * y := by
            group
        _ = ((e.symm m : ↥N) : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
        _ = ((e.symm m : ↥N) : Y)⁻¹ * y * x := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    rw [← hcen]
    exact (e.symm m).2
  obtain ⟨φ, hφi, hφR, hφt⟩ := datum_exists_q8 hD
  have hq4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have htN : t ∈ N := by
    have hq : (a 1 : QuaternionGroup 2) * xa 0 * (a 1)⁻¹ * (xa 0)⁻¹ = a 1 ^ 2 := by decide
    have ht' : t = φ (a 1) * φ (xa 0) * (φ (a 1))⁻¹ * (φ (xa 0))⁻¹ := by
      rw [← hφt, ← map_pow, ← hq, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hD' : ι t ∈ linearAutGroup 3 K := by
      rw [ht', map_mul ι, map_mul ι, map_mul ι, map_inv ι, map_inv ι]
      exact commutator_mem_linearAutGroup le_rfl _ _
    have ht2 : t ^ 2 = 1 := by rw [← hD.order, pow_orderOf_eq_one]
    have h2 : ι t ^ 2 ^ 1 = 1 := by rw [← map_pow, pow_one, ht2, map_one]
    exact hιN t (mem_inner_of_pow hD' h2)
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ := exists_frame hoddK e htN hD.order
  have hRJ := TightDatum.le_centralizer_of_gl2 hD hrange hk hoddK (by omega) slPartTopEquiv
  have hfix : ∀ g ∈ R, ∀ B : SL(2, K),
      ι g (proj 3 K ((blkP Q).comp SpecialLinearGroup.toGL B)) =
        proj 3 K ((blkP Q).comp SpecialLinearGroup.toGL B) := by
    intro g hg B
    let x : ↥N := e.symm (proj 3 K (blkP Q (SpecialLinearGroup.toGL B)))
    have hxJ : (x : Y) ∈ (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π :=
      ⟨⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩,
        mem_slPart.mpr (SpecialLinearGroup.coeToGL_det B), hπ _⟩
    have hgx : (x : Y) * g = g * x := Subgroup.mem_centralizer_iff.mp (hRJ hg) _ hxJ
    have hconj : MulAut.conjNormal g x = x := Subtype.ext (by
      rw [MulAut.conjNormal_apply, ← hgx, mul_inv_cancel_right])
    have hex : proj 3 K (blkP Q (SpecialLinearGroup.toGL B)) = e x :=
      (MulEquiv.apply_symm_apply e _).symm
    show ι g (proj 3 K (blkP Q (SpecialLinearGroup.toGL B))) =
      proj 3 K (blkP Q (SpecialLinearGroup.toGL B))
    rw [hex, hιapp, hconj]
  have hs : ∃ s ∈ R, s ∈ N ∧ orderOf s = 4 := by
    have hE : ∃ q : QuaternionGroup 2, ¬ q ^ 2 ^ 1 = 1 ∧ ι (φ q) ∈ semilinearAutGroup 3 K := by
      by_cases ha : ι (φ (a 1)) ∈ semilinearAutGroup 3 K
      · exact ⟨a 1, by decide, ha⟩
      by_cases hb : ι (φ (xa 0)) ∈ semilinearAutGroup 3 K
      · exact ⟨xa 0, by decide, hb⟩
      refine ⟨a 1 * xa 0, by decide, ?_⟩
      rw [map_mul φ, map_mul ι]
      exact mul_mem_semilinearAutGroup ha hb
    obtain ⟨q, hq2, hqE⟩ := hE
    have hqD := mem_linearAutGroup_of_fix (by omega) ((blkP Q).comp SpecialLinearGroup.toGL)
      (trace_blkP Q) hqE (hfix _ (hφR q))
    have hq4' : ι (φ q) ^ 2 ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, hq4, map_one, map_one]
    have hqN := hιN _ (mem_inner_of_pow hqD hq4')
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨φ q, hφR q, hqN, ?_⟩
    rw [orderOf_injective φ hφi q]
    exact orderOf_eq_prime_pow hq2 (by rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]; exact hq4 q)
  obtain ⟨s, hsR, hsN, hs4⟩ := hs
  exact Or.inl (TightDatum.tightEx_of_gl2 hD hc hrange hk slCentScalar_top (N1 := ⟨-1, _⟩) rfl
    hπ1 hoddK (by omega) slPartTopEquiv hsR hsN hs4)

end CFSG.ClassicalInvolution.Q3.TA3
