module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

namespace CFSG.QuasithinUnique.L246.C123

open Matrix

theorem card_le_factorial_index {Γ : Type} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    {H : Subgroup Γ} (hH : H ≠ ⊤) : Nat.card Γ ≤ H.index.factorial := by
  classical
  have hfin : Finite (Γ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  let φ : Γ →* Equiv.Perm (Γ ⧸ H) := MulAction.toPermHom Γ (Γ ⧸ H)
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hH
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := h ▸ Subgroup.mem_top g
      have := congrArg (fun σ : Equiv.Perm (Γ ⧸ H) => σ (QuotientGroup.mk 1))
        (MonoidHom.mem_ker.1 hg)
      simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one,
        id_eq] at this
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at this
      have h3 := QuotientGroup.eq.1 this
      rw [mul_one] at h3
      exact H.inv_mem_iff.1 h3
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hcard := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_perm] at hcard
  exact hcard

noncomputable def glEquivSL :
    Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  (MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := ZMod 2))
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : Matrix.GeneralLinearGroup.det A = 1 := by
        have : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
        exact this _
      have : A ∈ (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →*
          Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)).range := by
        rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
        exact hdet
      exact this⟩).symm

theorem card_sl_four : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Bridge.card_sl_two_field 4 (ZMod 2) (Nat.card_zmod 2), Fin.prod_univ_four]
  norm_num

theorem mulAut_facts {M : Type} [CommGroup M] [Finite M] (hM2 : ∀ m : M, m ^ 2 = 1)
    (hcard : Nat.card M = 16) : Nat.card (MulAut M) = 20160 ∧ IsSimpleGroup (MulAut M) := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := M)
    (fun a b => mul_comm a b) (fun a => hM2 a) (n := 4) (by rw [hcard]; norm_num)
  let h : MulAut M ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).trans glEquivSL
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Bridge.isSimple_sl_zmod2 4 (by norm_num)
  refine ⟨?_, h.isSimpleGroup⟩
  rw [Nat.card_congr h.toEquiv]
  exact card_sl_four

theorem normalizer_eq_of_card_2520 {M : Type} [CommGroup M] [Finite M] (hM2 : ∀ m : M, m ^ 2 = 1)
    (hcard : Nat.card M = 16) {Λ : Subgroup (MulAut M)} (hΛ : Nat.card Λ = 2520) :
    Subgroup.normalizer (Λ : Set (MulAut M)) = Λ := by
  obtain ⟨h20160, hsimple⟩ := mulAut_facts hM2 hcard
  have hΛN : Λ ≤ Subgroup.normalizer (Λ : Set (MulAut M)) := Subgroup.le_normalizer
  have hNtop : Subgroup.normalizer (Λ : Set (MulAut M)) ≠ ⊤ := by
    intro h
    have hn : Λ.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Λ with h1 | h1
    · rw [h1, Subgroup.card_bot] at hΛ; omega
    · rw [h1, Subgroup.card_top, h20160] at hΛ; omega
  have h8 : 8 ≤ (Subgroup.normalizer (Λ : Set (MulAut M))).index := by
    have h1 := card_le_factorial_index hNtop
    rw [h20160] at h1
    by_contra hlt
    push Not at hlt
    interval_cases h : (Subgroup.normalizer (Λ : Set (MulAut M))).index <;>
      simp [Nat.factorial] at h1
  have hΛidx : Λ.index = 8 := by
    have := Λ.index_mul_card
    rw [hΛ, h20160] at this
    omega
  have hdvd : (Subgroup.normalizer (Λ : Set (MulAut M))).index ∣ Λ.index :=
    Subgroup.index_dvd_of_le hΛN
  rw [hΛidx] at hdvd
  have hNidx : (Subgroup.normalizer (Λ : Set (MulAut M))).index = 8 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) h8
  have hNcard := (Subgroup.normalizer (Λ : Set (MulAut M))).index_mul_card
  rw [hNidx, h20160] at hNcard
  exact (Subgroup.eq_of_le_of_card_ge hΛN (by omega)).symm

end CFSG.QuasithinUnique.L246.C123
