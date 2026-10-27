module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerPSpL4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer StabU HBlocks
  UnitaryOut UnitaryConj Matrix

variable {H : Type} [Group H] [Finite H]

theorem innerPSp_U4 (h : Hyp52 H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hZ : center (OddBar h.K) = ⊥) (hq : p ^ f % 4 = 1) {K : Type} [Field K]
    (hU : UnitaryFieldData p f K) (e : OddBar h.K ≃* StatedProj (StatedSU 4 (p ^ f) K))
    (ℓ : OddBar h.K) (hℓ2 : ℓ ^ 2 = 1) : InnerPSpAt (p ^ f) p f ℓ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := hU.finite
  have hKa : conjugate h.K h.a = h.K := by
    obtain ⟨-, -, -, -, -, -, hKa, -⟩ := hrow
    exact hKa
  obtain ⟨ℓ₀, -, hℓZ, hℓ2₀, hJC, hJp, hcard, ⟨s, hs, hs2, hsq, -, hsJ⟩, -⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  obtain ⟨y'', hy''⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  have hs1 : s ≠ 1 := hs.one_lt.ne'
  have hsimp : IsSimpleGroup (OddBar h.K) := isSimpleGroup_of_center_eq_bot' h.isQuasisimple_K hZ
  by_cases hℓ1 : ℓ = 1
  · subst hℓ1
    refine innerPSpAt_one (exists_ne_comm h.isQuasisimple_K.1.commutator_eq_top)
      (y₀ := (y'' : OddBar h.K)) ?_ ?_ _ _ _
    · intro h1
      have : orderOf (y'' : OddBar h.K) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_coe, hy''] at this
      exact hs1 this
    · rw [Subgroup.orderOf_coe, hy'']
      exact hs.odd_of_ne_two hs2
  obtain ⟨X, hX⟩ := QuotientGroup.mk_surjective (e ℓ)
  have hXX : X * X ∈ scal p f K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hX, ← map_mul, ← sq, hℓ2, map_one]
  obtain ⟨c, hc⟩ : (X * X : StatedSU 4 (p ^ f) K).1 ∈ StatedScalars (Fin 4) K := hXX
  have hcS : GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) K := by
    rw [hc]
    exact (X * X).2
  have hXXm : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) =
      (c : K) • 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, ← hc, GeneralLinearGroup.coe_scalar,
      Matrix.smul_one_eq_diagonal]
    rfl
  have hX1 : (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) ≠ 1 := by
    rw [hX, Ne, MulEquiv.map_eq_one_iff]
    exact hℓ1
  apply InnerPSpAt.of_equiv e
  rw [← hX]
  rcases scalar_eq_one_or_neg_one_U4 hU hq hcS with h1 | h1
  ·
    rw [h1, Units.val_one, one_smul] at hXXm
    exact innerPSpAt_t_U4 hU hp2 hq X hXXm hX1
  ·
    rw [h1, Units.val_neg, Units.val_one, neg_smul, one_smul] at hXXm
    have hℓ1₀ : ℓ₀ ≠ 1 := fun h1 => hℓZ (by rw [h1]; exact one_mem _)
    have hℓ2₀' : ℓ₀ ^ 2 = 1 := by rw [hZ] at hℓ2₀; exact mem_bot.1 hℓ2₀
    obtain ⟨X₀, hX₀⟩ := QuotientGroup.mk_surjective (e ℓ₀)
    have hXX₀ := sq_eq_neg_one_of_comm_orderOf_U4 hU hp2 (u := e ℓ₀)
      (v := e (y'' : OddBar h.K)) (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1₀)
      (by rw [← map_pow, hℓ2₀', map_one]) hs hs2 hsq
      (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy''])
      (by rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp (hJC y''.2)).symm]) X₀ hX₀
    obtain ⟨w, hw⟩ := exists_conj_of_sq_eq_neg_one_U4 hU hp2 hq X₀ X hXX₀ hXXm
    obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
      let : Fintype K := Fintype.ofFinite K
      have hcK : Fintype.card K % 4 = 1 := by
        rw [Fintype.card_eq_nat_card, hU.card, pow_mul, Nat.pow_mod]
        rw [show p ^ 2 % 4 = 1 by
          rcases Nat.even_or_odd p with he | ho
          · exfalso
            exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
              (even_iff_two_dvd.1 he)).symm
          · obtain ⟨t, rfl⟩ := ho
            ring_nf
            omega]
        simp
      obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
      exact ⟨r, by rw [sq, ← hr]⟩
    have hbl : hU.bar l * l = -1 := by
      have := norm_eq_neg_one_of_sq hU hq hl
      rw [UnitaryFieldData.norm, mul_comm] at this
      exact this
    obtain ⟨Pm, hPm, hXP⟩ := exists_hyperbolic_basis hU hp2 hq X hXXm hl
    have hPdet : Pm.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hPm
      have hGd : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
      rw [det_mul, h0, mul_zero, hGd] at this
      exact zero_ne_one this
    set P : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Pm hPdet with hPdef
    have hPv : (P : Matrix (Fin 4) (Fin 4) K) = Pm := GeneralLinearGroup.val_mkOfDetNeZero _ _
    have hP : uStar hU (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG := by
      rw [hPv]
      exact hPm
    have hXeq : X = hypSU hU P hP (X1 l) (unitary_X1 hU hbl) (det_X1 hl) := by
      apply eq_of_cP_eq P
      rw [cP_hypSU, cP, Matrix.mul_assoc, hPv, hXP, ← Matrix.mul_assoc, ← hPv, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mul, X1_eq_stdDl]
    set J' := ((imJB h).map e.toMonoidHom).map (MulAut.conj w).toMonoidHom with hJ'
    have hJk : J' ≤ centralizer {(QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K))} := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [← hw, mem_centralizer_singleton_iff, hX₀]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hc := mem_centralizer_singleton_iff.mp (hJC hy)
      have hc' : e y * e ℓ₀ = e ℓ₀ * e y := by rw [← map_mul, ← map_mul, hc]
      calc w * e y * w⁻¹ * (w * e ℓ₀ * w⁻¹) = w * (e y * e ℓ₀) * w⁻¹ := by group
        _ = w * (e ℓ₀ * e y) * w⁻¹ := by rw [hc']
        _ = w * e ℓ₀ * w⁻¹ * (w * e y * w⁻¹) := by group
    have hJp' : ⁅J', J'⁆ = J' := by rw [hJ', ← map_commutator, ← map_commutator, hJp]
    have hcardJ' : Nat.card J' = Nat.card (imJB h) := by
      rw [hJ', card_map_of_injective (MulAut.conj w).injective,
        card_map_of_injective e.injective]
    have hcard' : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J' := by
      rw [hcardJ']
      exact hcard
    rw [hXeq] at hJk ⊢
    obtain ⟨-, -, hJle⟩ := eq_of_perfect_U4 hU hp2 P hP hl hbl hJk hJp' hcard'
    have hJle' : Nat.card (imJB h) ≤ Nat.card (OddBar h.J) := by
      have h2 : 2 * Nat.card (OddBar h.J) = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
        rw [card_of_lieModel_psl_two hp2 hJ, pow_mul, two_mul_ordA_one]
        · ring_nf
        · exact ((hp.odd_of_ne_two hp2).pow (n := 2)).pow
      rw [hcardJ', show (p ^ f) ^ 4 = ((p ^ f) ^ 2) ^ 2 by ring] at hJle
      omega
    have hJs := isSimpleGroup_imJB h hKa hJ hJle'
    have eJ : ↥(imJB h) ≃* ↥J' :=
      ((e.subgroupMap (imJB h)).trans ((MulAut.conj w).subgroupMap _))
    have : Nontrivial ↥J' := eJ.toEquiv.symm.nontrivial
    have : IsSimpleGroup ↥J' := IsSimpleGroup.isSimpleGroup_of_surjective eJ.toMonoidHom
      eJ.surjective
    exact innerPSpAt_J_U4 hU hp2 hq P hP hl hbl hJk hJp' hcard'

end CFSG.ComponentClassification.CatFactsL4U4
