module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.FixedIndex

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus.TriData

open Subgroup Module CFSG.Open CFSG.GroupTheory CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type} [Group G] [Finite G]
variable {S : Setting G} {g : G} (T : TriData S g)

theorem l_injective : Function.Injective T.l := by
  intro i j hij
  by_contra hne
  have h1 := T.l_conj_e i
  have h2 := T.l_conj_e_of_ne (i := j) (j := i) (Ne.symm hne)
  rw [← hij] at h2
  have heq : (eb T.σ i)⁻¹ = eb T.σ i := h1.symm.trans h2
  have hsq : eb T.σ i * eb T.σ i = 1 := mul_eq_one_iff_eq_inv.mpr heq.symm
  have hdvd : orderOf (eb T.σ i) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rwa [pow_two]
  rw [T.basis.orderOf_eb i] at hdvd
  exact absurd hdvd (by norm_num)

theorem exists_conj_eq_l (x : S.Mbar) (i : Fin 3) :
    ∃ y ∈ S.Mbar, y * T.l i * y⁻¹ = T.l (T.perm x i) := by
  obtain ⟨c, hc⟩ := T.conj_l x
  let y : S.O := (T.σ (Multiplicative.ofAdd c))⁻¹ * (x : S.O)
  have hσ : T.σ (Multiplicative.ofAdd c) ∈ S.Mbar :=
    S7.Obar_le_Mbar (T.basis.mem_iff.mpr ⟨c, rfl⟩)
  have hy : y ∈ S.Mbar := S.Mbar.mul_mem (S.Mbar.inv_mem hσ) x.2
  refine ⟨y, hy, ?_⟩
  calc y * T.l i * y⁻¹
      = (T.σ (Multiplicative.ofAdd c))⁻¹ *
          ((x : S.O) * T.l i * (x : S.O)⁻¹) * T.σ (Multiplicative.ofAdd c) := by
        dsimp only [y]
        group
    _ = (T.σ (Multiplicative.ofAdd c))⁻¹ *
          (T.σ (Multiplicative.ofAdd c) * T.l (T.perm x i) *
            (T.σ (Multiplicative.ofAdd c))⁻¹) * T.σ (Multiplicative.ofAdd c) := by
        rw [hc i]
    _ = T.l (T.perm x i) := by group

end CFSG.GF2Type.Smith1979.TriPlus.TriData

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.GroupTheory CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7
  CFSG.GF2Type.Smith1979.TriPlus

variable {G : Type} [Group G] [Finite G]
variable {S : Setting G} {g : G}

theorem of_card_oddCore_eq_twentyseven (hw : S.width = 4) (hnoAll : S11.NoA2All S)
    (hirr : ¬ S.IsReducible) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht)
    (hE : timmesfeldLayer S.Mbar = ⊥) (h27 : Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 3) :
    (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
      TrialityConfig S g t := by
  obtain ⟨T⟩ := nonempty_triData hw hirr H C hE h27
  obtain ⟨i0, rfl⟩ := T.exists_eq_l H C ht ht1 hVQ hΩ h4 hplus
  by_cases hfix : ∀ x : S.Mbar, T.perm x i0 = i0
  · exact Or.inl (T.iso_of_fixed hw hnoAll H C hfix)
  · push Not at hfix
    obtain ⟨x, hx⟩ := hfix
    obtain ⟨y, hy, hyconj⟩ := T.exists_conj_eq_l x i0
    refine Or.inr ⟨hE, h27, y, hy, ?_, ?_⟩
    · rw [hyconj]
      exact T.l_mem (T.perm x i0)
    · rw [hyconj]
      intro hconj
      exact hx (T.l_injective hconj)

end CFSG.GF2Type.Smith1979.OmegaPlus

end
