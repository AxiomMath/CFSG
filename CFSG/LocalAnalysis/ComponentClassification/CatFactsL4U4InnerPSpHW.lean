module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerHW
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerPSpL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Row516NoPSp

public section

namespace CFSG.ComponentClassification.CatFactsL4U4HW

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4 Matrix

section Hyp

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem nonempty_imJB_equiv (hKa : conjugate h.K h.a = h.K)
    (hc : Nat.card (imJB h) ≤ Nat.card (OddBar h.J)) : Nonempty (imJB h ≃* OddBar h.J) := by
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  set φ := jbToK h hKa with hφ
  let e₁ : ↥(GSLit.fixedLayer h.J h.B) ⧸ φ.ker ≃* imJB h :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr (range_jbToK h hKa))
  let g : ↥(GSLit.fixedLayer h.J h.B) ⧸ φ.ker →* OddBar h.J :=
    e.toMonoidHom.comp (QuotientGroup.map _ _ (MonoidHom.id _) (ker_jbToK_le h hKa))
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk x', rfl⟩
  let g' : imJB h →* OddBar h.J := g.comp e₁.symm.toMonoidHom
  have hg' : Function.Surjective g' := hg.comp e₁.symm.surjective
  exact ⟨MulEquiv.ofBijective g' (hg'.bijective_of_nat_card_le hc)⟩

theorem isSimpleGroup_imJB (hKa : conjugate h.K h.a = h.K) {p f : ℕ}
    (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hc : Nat.card (imJB h) ≤ Nat.card (OddBar h.J)) : IsSimpleGroup ↥(imJB h) := by
  obtain ⟨e⟩ := nonempty_imJB_equiv h hKa hc
  have : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
  have : Nontrivial ↥(imJB h) := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

end Hyp

section L4

open CFSG.ComponentClassification.CatFactsL4U4.StabL
  CFSG.ComponentClassification.CatFactsL4U4.Blocks CFSG.ComponentClassification.CatFactsL4U4.PSpL

variable {H : Type} [Group H] [Finite H]

theorem innerPSp_L4 (h : Hyp52W H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hZ : center (OddBar h.K) = ⊥) (hq : p ^ f % 4 = 3) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = p ^ f) (e : OddBar h.K ≃* StatedProj (StatedSL 4 F))
    (ℓ : OddBar h.K) (hℓ2 : ℓ ^ 2 = 1) : InnerPSpAt (p ^ f) p f ℓ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKa : conjugate h.K h.a = h.K := by
    obtain ⟨-, -, -, -, -, -, hKa, -⟩ := hrow
    exact hKa
  obtain ⟨ℓ₀, -, hℓZ, hℓ2₀, hJC, hJp, hcard, ⟨s, hs, hs2, hsq, -, hsJ⟩, -⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  have hF' : Fintype.card F % 4 = 3 := by rw [hF]; exact hq
  have hKF : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨y'', hy''⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  have hℓ1₀ : ℓ₀ ≠ 1 := fun h1 => hℓZ (by rw [h1]; exact one_mem _)
  have hℓ2₀' : ℓ₀ ^ 2 = 1 := by rw [hZ] at hℓ2₀; exact mem_bot.1 hℓ2₀
  obtain ⟨X₀, hX₀⟩ := QuotientGroup.mk_surjective (e ℓ₀)
  have hXX₀ := sq_eq_neg_one_of_comm_orderOf (u := e ℓ₀) (v := e (y'' : OddBar h.K))
    ⟨Fintype.card F / 2, by omega⟩ (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1₀)
    (by rw [← map_pow, hℓ2₀', map_one]) hs hs2 (by rw [hF]; exact hsq)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy''])
    (by rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp (hJC y''.2)).symm]) X₀ hX₀
  obtain ⟨e₀, he₀⟩ := exists_normalized_equiv hF' e X₀ hX₀ hXX₀
  set J' := (imJB h).map e₀.toMonoidHom with hJ'
  have hJk : J' ≤ centralizer {LinearFlag.proj 4 F k₀} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← he₀, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hJC hy)]
  have hJp' : ⁅J', J'⁆ = J' := by rw [hJ', ← map_commutator, hJp]
  have hcardJ' : Nat.card J' = Nat.card (imJB h) := card_map_of_injective e₀.injective
  have hcard' : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J' := by
    rw [hcardJ', hKF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring]
    exact hcard
  have hJ'eq : J' = J₀ F := eq_J₀ hF' hJk hJp' hcard'
  have hQ : Odd (p ^ (2 * f)) := (hp.odd_of_ne_two hp2).pow
  have hpf : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have h2J : 2 * Nat.card (OddBar h.J) = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
    rw [card_of_lieModel_psl_two hp2 hJ, two_mul_ordA_one hQ, hpf, ← pow_mul (p ^ f) 2 2]
  have hJle : Nat.card (imJB h) ≤ Nat.card (OddBar h.J) := by
    have h1 := two_mul_card_J₀_le hF'
    rw [← hJ'eq, hcardJ', hKF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring] at h1
    omega
  have hJsimp := isSimpleGroup_imJB h hKa hJ hJle
  have eJ : ↥(imJB h) ≃* ↥(J₀ F) := (e₀.subgroupMap (imJB h)).trans (MulEquiv.subgroupCongr hJ'eq)
  have : Nontrivial ↥(J₀ F) := eJ.symm.toEquiv.nontrivial
  have hJ₀s : IsSimpleGroup ↥(J₀ F) :=
    IsSimpleGroup.isSimpleGroup_of_surjective eJ.toMonoidHom eJ.surjective
  have hJ₀p : ⁅J₀ F, J₀ F⁆ = J₀ F := by rw [← hJ'eq]; exact hJp'
  have hcard₀ : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card (J₀ F) := by
    rw [← hJ'eq]; exact hcard'
  have hs1 : s ≠ 1 := hs.one_lt.ne'
  have hodd0 : ∃ y ∈ J₀ F, y ≠ 1 ∧ Odd (orderOf y) := by
    refine ⟨e₀ (y'' : OddBar h.K), by rw [← hJ'eq]; exact ⟨y'', y''.2, rfl⟩, ?_, ?_⟩
    · rw [Ne, MulEquiv.map_eq_one_iff]
      intro h1
      have : orderOf (y'' : OddBar h.K) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_coe, hy''] at this
      exact hs1 this
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy'']
      exact hs.odd_of_ne_two hs2
  have hZ₀ : center (LinearFlag.projectiveSL 4 F) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : e₀.symm z ∈ center (OddBar h.K) := by
      rw [mem_center_iff]
      intro g
      apply e₀.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mem_center_iff.mp hz]
    rw [hZ, mem_bot] at this
    rw [mem_bot]
    simpa using congrArg e₀ this
  have hsimp : IsSimpleGroup (OddBar h.K) := isSimpleGroup_of_center_eq_bot' h.isQuasisimple_K hZ
  by_cases hℓ1 : ℓ = 1
  · subst hℓ1
    refine innerPSpAt_one (exists_ne_comm h.isQuasisimple_K.1.commutator_eq_top)
      (y₀ := (y'' : OddBar h.K)) ?_ ?_
      _ _ _
    · intro h1
      have : orderOf (y'' : OddBar h.K) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_coe, hy''] at this
      exact hs1 this
    · rw [Subgroup.orderOf_coe, hy'']
      exact hs.odd_of_ne_two hs2
  set e' := e.trans (projEquiv F) with he'
  obtain ⟨X, hX⟩ := LinearFlag.proj_surjective 4 F (e' ℓ)
  have hXs : X * X ∈ LinearFlag.scalars 4 F := by
    rw [← LinearFlag.proj_eq_one_iff, map_mul, hX, ← map_mul, ← sq, hℓ2, map_one]
  obtain ⟨c, hc4, hc⟩ := LinearFlag.mem_scalars.1 hXs
  have hc4' : (c : F) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
  rw [Matrix.SpecialLinearGroup.coe_mul] at hc
  have hX1 : LinearFlag.proj 4 F X ≠ 1 := by
    rw [hX, Ne, MulEquiv.map_eq_one_iff]
    exact hℓ1
  rcases eq_one_or_eq_neg_one_of_pow_four hF' hc4' with h1 | h1
  ·
    rw [h1, map_one] at hc
    apply InnerPSpAt.of_equiv e'
    rw [← hX]
    exact innerPSpAt_t_L4 hF' hp hKF X hc hX1
  ·
    rw [h1, map_neg, map_one] at hc
    obtain ⟨eℓ, heℓ⟩ := exists_normalized_equiv' hF' e' X hX hc
    apply InnerPSpAt.of_equiv eℓ
    rw [heℓ]
    exact innerPSpAt_k₀ hF' hp hKF hJ₀p hcard₀ hodd0 hZ₀

end L4

section U4

open CFSG.ComponentClassification.CatFactsL4U4.StabU
  CFSG.ComponentClassification.CatFactsL4U4.HBlocks
  CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut
  CFSG.ComponentClassification.CatFactsL4U4.UnitaryConj

variable {H : Type} [Group H] [Finite H]

theorem innerPSp_U4 (h : Hyp52W H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
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

end U4

theorem cfRow516InnerPSpHW : CFRow516InnerPSpHW := by
  intro H _ _ h hrow hin p f hp hp2 hf hJ ℓ hℓ2
  obtain ⟨hZ, p', f', hp', hp2', hf', hJ', hK⟩ := inner_structure h hrow hin
  obtain ⟨rfl, rfl⟩ := eq_of_lieModel_psl_two hp' hp2' hf' hp hp2 hJ' hJ
  rcases hK with ⟨hq, F, _, _, hF, ⟨e⟩⟩ | ⟨hq, K', _, hUF, ⟨e⟩⟩
  · exact innerPSp_L4 h hrow hin hp' hp2' hJ' hZ hq hF e ℓ hℓ2
  · exact innerPSp_U4 h hrow hin hp' hp2' hJ' hZ hq hUF e ℓ hℓ2

end CFSG.ComponentClassification.CatFactsL4U4HW
