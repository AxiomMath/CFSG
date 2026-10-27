module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSL3
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinThree

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem blkSL_injective : Function.Injective (blkSL F) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, h⟩ hgh
  have h1 := congrArg (fun z : StatedSp 2 F =>
    ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hgh
  simp only [coe_blkSL, OneMemClass.coe_one, Units.val_one] at h1
  rw [← blk_one_one] at h1
  obtain ⟨hg, hh⟩ := blk_injective _ _ _ _ h1
  exact Prod.ext (Subtype.ext hg) (Subtype.ext hh)

variable (F) in
@[expose] def sp4J₂ : Subgroup ↥(StatedSp 2 F) := ((blkSL F).comp (MonoidHom.inr _ _)).range

variable (F) in
@[expose] def sp4J₄ : Subgroup ↥(StatedSp 2 F) := ((blkSL F).comp (MonoidHom.inl _ _)).range

variable (F) in
@[expose] def sp4X : ↥(StatedSp 2 F) := blkSL F (negOneSL, negOneSL)

theorem T1_eq_blkSL : T1 F = blkSL F (1, negOneSL) := sp_ext rfl

theorem negOneSL_mul_self : (negOneSL : SL(2, F)) * negOneSL = 1 :=
  Subtype.ext (by simp [coe_negOneSL])

theorem negOneSL_comm (g : SL(2, F)) : g * negOneSL = negOneSL * g :=
  Subtype.ext (by simp [coe_negOneSL])

theorem sp4X_mul_T1 : sp4X F * T1 F = blkSL F (negOneSL, 1) := by
  rw [sp4X, T1_eq_blkSL, ← map_mul, Prod.mk_mul_mk, mul_one, negOneSL_mul_self]

theorem blkSL_conj (a b : SL(2, F) × SL(2, F)) :
    blkSL F a * blkSL F b * (blkSL F a)⁻¹ = blkSL F (a.1 * b.1 * a.1⁻¹, a.2 * b.2 * a.2⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem sp4_frame (h2 : (2 : F) ≠ 0) :
    Frame (⊤ : Subgroup ↥(StatedSp 2 F)) F (sp4X F) (T1 F) (sp4J₂ F) (sp4J₄ F) where
  le₂ := le_top
  le₄ := le_top
  mem₂ := ⟨negOneSL, by rw [T1_eq_blkSL]; rfl⟩
  mem₄ := ⟨negOneSL, by rw [sp4X_mul_T1]; rfl⟩
  orderOf_xt := by
    rw [sp4X_mul_T1, show blkSL F (negOneSL, 1) = ((blkSL F).comp (MonoidHom.inl _ _)) negOneSL
      from rfl, orderOf_injective _ (blkSL_injective.comp (Prod.mk_left_injective 1)),
      orderOf_negOneSL h2]
  ne_one := fun h => by
    have := blkSL_injective (h.trans (map_one _).symm)
    exact one_ne_neg_one_mat h2 (congrArg Subtype.val (congrArg Prod.fst this)).symm
  equiv₂ := ⟨(MonoidHom.ofInjective (f := (blkSL F).comp (MonoidHom.inr _ _))
    (blkSL_injective.comp (Prod.mk_right_injective 1))).symm⟩
  equiv₄ := ⟨(MonoidHom.ofInjective (f := (blkSL F).comp (MonoidHom.inl _ _))
    (blkSL_injective.comp (Prod.mk_left_injective 1))).symm⟩
  comm := by
    rintro _ ⟨h, rfl⟩ _ ⟨g, rfl⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply]
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]
  cent₂ := by
    rintro _ ⟨h, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, T1_eq_blkSL]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply]
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, negOneSL_comm]
  norm₂ := by
    intro g _ hg _ ⟨h, hh⟩
    obtain ⟨a, rfl⟩ :=
      (mem_centralizer_T1_iff h2).mp (Subgroup.mem_centralizer_singleton_iff.mpr hg)
    rw [← hh]
    refine ⟨a.2 * h * a.2⁻¹, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply]
    rw [blkSL_conj]
    simp
  norm₄ := by
    intro g _ hg _ ⟨h, hh⟩
    obtain ⟨a, rfl⟩ :=
      (mem_centralizer_T1_iff h2).mp (Subgroup.mem_centralizer_singleton_iff.mpr hg)
    rw [← hh]
    refine ⟨a.1 * h * a.1⁻¹, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
    rw [blkSL_conj]
    simp

theorem sl2_zmod_three_cent : ∀ c : SL(2, ZMod 3),
    (∀ γ : SL(2, ZMod 3), γ ^ 4 = 1 → γ ^ 2 ≠ 1 → c * γ = γ * c) → c = 1 ∨ c ^ 2 = 1 := by
  decide

theorem sl2_three_cent [Finite F] (h3 : Nat.card F = 3) {c : SL(2, F)}
    (hc : ∀ γ : SL(2, F), γ ^ 4 = 1 → γ ^ 2 ≠ 1 → c * γ = γ * c) : c = 1 ∨ c ^ 2 = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have hc3 : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, h3]
  let f : SL(2, ZMod 3) ≃* SL(2, F) := sl2RingEquiv (ZMod.ringEquivOfPrime F Nat.prime_three hc3)
  obtain ⟨c₀, rfl⟩ := f.surjective c
  have hc₀ : ∀ γ₀ : SL(2, ZMod 3), γ₀ ^ 4 = 1 → γ₀ ^ 2 ≠ 1 → c₀ * γ₀ = γ₀ * c₀ :=
    fun γ₀ h4 h2 => f.injective (by
      rw [map_mul, map_mul]
      exact hc (f γ₀) (by rw [← map_pow, h4, map_one])
        (by rw [← map_pow, Ne, ← map_one f, f.injective.eq_iff]; exact h2))
  rcases sl2_zmod_three_cent c₀ hc₀ with h | h
  · exact Or.inl (by rw [h, map_one])
  · exact Or.inr (by rw [← map_pow, h, map_one])

theorem negOneSL_eq : (negOneSL : SL(2, F)) = -1 := Subtype.ext (by simp [coe_negOneSL])

theorem sp4X_coe : (((sp4X F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 := by
  rw [sp4X, coe_blkSL, coe_negOneSL, blk_neg_one_neg_one]

theorem sp4_frame3 [Finite F] (h3 : Nat.card F = 3) :
    Frame3 (⊤ : Subgroup ↥(StatedSp 2 F)) F (sp4X F) (T1 F) (sp4J₂ F) (sp4J₄ F) := by
  have hodd : Odd (Nat.card F) := by rw [h3]; decide
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  refine ⟨sp4_frame h2, h3, fun g => sp_ext ?_, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Units.val_mul, sp4X_coe, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_one, Matrix.one_mul]
  · intro n _ hnt hnn
    obtain ⟨a, rfl⟩ := (mem_centralizer_T1_iff h2).mp
      (Subgroup.mem_centralizer_singleton_iff.mpr hnt)
    rw [← map_mul, T1_eq_blkSL] at hnn
    have ha := blkSL_injective hnn
    have ha1 : a.1 * a.1 = 1 := congrArg Prod.fst ha
    rcases eq_one_or_neg_one_of_sq h2 a.1.2 (congrArg Subtype.val ha1) with h | h
    · refine ⟨blkSL F (1, a.2), ⟨a.2, rfl⟩, Or.inl ?_⟩
      rw [show a = (1, a.2) from Prod.ext (Subtype.ext h) rfl]
    · refine ⟨blkSL F (1, a.2), ⟨a.2, rfl⟩, Or.inr ?_⟩
      rw [sp4X_mul_T1, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
        show a = (negOneSL, a.2) from Prod.ext (Subtype.ext h) rfl]
  · intro g _ hgt hgb
    obtain ⟨a, rfl⟩ := (mem_centralizer_T1_iff h2).mp
      (Subgroup.mem_centralizer_singleton_iff.mpr hgt)
    have hc : ∀ γ : SL(2, F), γ ^ 4 = 1 → γ ^ 2 ≠ 1 → a.2 * γ = γ * a.2 := by
      intro γ hγ4 hγ2
      have hγ : γ * γ = negOneSL := by
        have hord : orderOf (γ ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact hγ4) hγ2
        rw [negOneSL_eq, ← sq]
        exact (sl2_orderOf_eq_two_iff hodd _).mp hord
      have h1 := hgb (blkSL F (1, γ)) ⟨γ, rfl⟩
        (by rw [← map_mul, Prod.mk_mul_mk, one_mul, hγ, T1_eq_blkSL])
      rw [← map_mul, ← map_mul, blkSL_injective.eq_iff] at h1
      simpa using congrArg Prod.snd h1
    rcases sl2_three_cent h3 hc with h | h
    · refine ⟨blkSL F (a.1, 1), ⟨a.1, rfl⟩, Or.inl ?_⟩
      rw [show a = (a.1, 1) from Prod.ext rfl h]
    · by_cases h1 : a.2 = 1
      · refine ⟨blkSL F (a.1, 1), ⟨a.1, rfl⟩, Or.inl ?_⟩
        rw [show a = (a.1, 1) from Prod.ext rfl h1]
      · have hord : orderOf a.2 = 2 := orderOf_eq_prime h h1
        have ha2 : a.2 = negOneSL := by
          rw [negOneSL_eq]; exact (sl2_orderOf_eq_two_iff hodd _).mp hord
        refine ⟨blkSL F (a.1, 1), ⟨a.1, rfl⟩, Or.inr ?_⟩
        rw [T1_eq_blkSL, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one,
          show a = (a.1, negOneSL) from Prod.ext rfl ha2]

theorem sp4_conj [Finite F] (hodd : Odd (Nat.card F)) {u : ↥(StatedSp 2 F)} (hu : u * u = 1)
    (hc : u ∉ Subgroup.center ↥(StatedSp 2 F)) : ∃ g, g * u * g⁻¹ = T1 F := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hTT : ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    have := congrArg (fun z : StatedSp 2 F =>
      ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hu
    simpa using this
  have hcen : ∀ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, (c = 1 ∨ c = -1) →
      ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ c := by
    rintro c hc' h
    apply hc
    rw [Subgroup.mem_center_iff]
    intro g
    apply sp_ext
    rcases hc' with rfl | rfl <;>
      simp [Subgroup.coe_mul, Units.val_mul, h]
  obtain ⟨g, hg⟩ := exists_conj_T1 h2 u hTT (hcen 1 (Or.inl rfl)) (hcen (-1) (Or.inr rfl))
  exact ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
