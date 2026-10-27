module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTL4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer StabL Blocks
  Matrix PSpL

theorem exists_normalized_equiv' {Y F : Type} [Group Y] [Field F] [Fintype F]
    (hF : Fintype.card F % 4 = 3) (e : Y ≃* LinearFlag.projectiveSL 4 F) {ℓ : Y}
    (X : SpecialLinearGroup (Fin 4) F) (hX : LinearFlag.proj 4 F X = e ℓ)
    (hXX : (X : Matrix (Fin 4) (Fin 4) F) * X = -1) :
    ∃ e' : Y ≃* LinearFlag.projectiveSL 4 F, e' ℓ = LinearFlag.proj 4 F k₀ := by
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  obtain ⟨g, hgd, hgX⟩ := exists_conj_of_sq_eq_neg_one (by omega) hns hXX stdJ_mul_stdJ
  set gS : SpecialLinearGroup (Fin 4) F := ⟨g, hgd⟩ with hgS
  refine ⟨e.trans (MulAut.conj (LinearFlag.proj 4 F gS)), ?_⟩
  rw [MulEquiv.trans_apply, ← hX, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hgi' : g * ((gS⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 :=
    congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
      (mul_inv_cancel gS)
  change g * (X : Matrix (Fin 4) (Fin 4) F) *
    ((gS⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = stdJ
  rw [hgX, Matrix.mul_assoc, hgi', Matrix.mul_one]

theorem exists_ne_comm {Q : Type*} [Group Q] [IsSimpleGroup Q] (hc : commutator Q = ⊤) :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  have h1 : commutator Q = ⊥ := by
    rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact hall y x
  rw [h1] at hc
  exact bot_ne_top hc

variable {H : Type} [Group H] [Finite H]

theorem innerPSp_L4 (h : Hyp52 H) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K)
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

end CFSG.ComponentClassification.CatFactsL4U4
