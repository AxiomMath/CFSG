module

public import CFSG.GH74.SectionalRank
public import CFSG.Quasithin.Background.C41PfCorr
public import CFSG.Quasithin.MS93.Amalgam

public section

namespace CFSG.GH74.QTGen4

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.MS93
open CFSG.GH74 (Gen4 SectionalTwoRankLE)
open scoped Pointwise

theorem false_of_big_elementary {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    (Z C U : Subgroup G) (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hC : C ≤ Z) (hU : U ≤ Z)
    (hC2 : ∀ x ∈ C, x * x = 1) (hU2 : ∀ x ∈ U, x * x = 1) (hCU : C ⊓ U = ⊥)
    (hc : 4 ≤ Nat.card C) (hu : 8 ≤ Nat.card U) : False := by
  let E : Subgroup G :=
    { carrier := {x | x ∈ Z ∧ x * x = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨Z.mul_mem ha hb, ?_⟩
        have hab := hZ a ha b hb
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, mul_one]
      one_mem' := ⟨Z.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨Z.inv_mem ha, ?_⟩
        rw [← mul_inv_rev, ha2, inv_one] }
  have hE : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hZ a a.2.1 b b.2.1)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact hx.2
  have hcard := SectionalTwoRankLE.card_le_of_elementary (show SectionalTwoRankLE G 4 from hG) E hE
  have hmem : ∀ p : C × U, (p.1 : G) * p.2 ∈ E := by
    rintro ⟨⟨c, hc'⟩, ⟨u, hu'⟩⟩
    refine ⟨Z.mul_mem (hC hc') (hU hu'), ?_⟩
    have hcu := hZ c (hC hc') u (hU hu')
    calc c * u * (c * u) = c * (u * c) * u := by group
      _ = c * (c * u) * u := by rw [← hcu]
      _ = (c * c) * (u * u) := by group
      _ = 1 := by rw [hC2 c hc', hU2 u hu', mul_one]
  let f : C × U → E := fun p => ⟨(p.1 : G) * p.2, hmem p⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨c, hc'⟩, ⟨u, hu'⟩⟩ ⟨⟨c', hc''⟩, ⟨u', hu''⟩⟩ h
    have h' : c * u = c' * u' := congrArg Subtype.val h
    have hmem' : c'⁻¹ * c ∈ C ⊓ U := by
      refine ⟨C.mul_mem (C.inv_mem hc'') hc', ?_⟩
      have : c'⁻¹ * c = u' * u⁻¹ := by
        calc c'⁻¹ * c = c'⁻¹ * (c * u) * u⁻¹ := by group
          _ = c'⁻¹ * (c' * u') * u⁻¹ := by rw [h']
          _ = u' * u⁻¹ := by group
      rw [this]
      exact U.mul_mem hu'' (U.inv_mem hu')
    rw [hCU, Subgroup.mem_bot] at hmem'
    have hcc : c = c' := by
      have := congrArg (c' * ·) hmem'
      simpa using this
    subst hcc
    have : u = u' := by
      have h2 : c * u = c * u' := h'
      exact mul_left_cancel h2
    subst this
    rfl
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at this
  have h32 : 32 ≤ Nat.card C * Nat.card U := by nlinarith
  have : (2 : ℕ) ^ 4 = 16 := by norm_num
  omega

theorem natural_card_exp {G : Type} [Group G] {A U : Subgroup G} {n : ℕ} {F : Type} [Field F]
    [Fintype F] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ}
    (hF : Fintype.card F = 2 ^ n) (hn : n ≠ 0)
    (h : IsSumOfNaturalModulesVia A U ⊥ α false 1) :
    8 ≤ Nat.card U ∧ ∀ x ∈ U, x * x = 1 := by
  obtain ⟨-, -, β, hβ, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  have h2 : (2 : F) = 0 := by
    have h1 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow, Nat.cast_ofNat] at h1
    exact pow_eq_zero_iff hn |>.mp h1
  refine ⟨?_, ?_⟩
  · have hc : Nat.card ↥U = Fintype.card F ^ 3 := by
      rw [Nat.card_eq_of_bijective β ⟨hinj, hβ⟩,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 1 → Fin 3 → F) ≃ _),
        Nat.card_eq_fintype_card]
      simp
    rw [hc, hF, ← pow_mul]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro x hx
    have h1 : β (⟨x, hx⟩ * ⟨x, hx⟩) = β 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i j
      show Multiplicative.toAdd (β ⟨x, hx⟩) i j + Multiplicative.toAdd (β ⟨x, hx⟩) i j = 0
      generalize Multiplicative.toAdd (β ⟨x, hx⟩) i j = a
      rw [← two_mul, h2, zero_mul]
    exact congrArg Subtype.val (hinj h1)

theorem false_of_case4Corr {G : Type} [Group G] [Finite G] (hG : Gen4 G) {G₀ R L : Subgroup G}
    (h : C134CorrLocal.IsC134Case4Corr G₀ R L) : False := by
  obtain ⟨⟨n, F, _, _, α, hF, -, hE2, hcen, hint, hU, -⟩, -⟩ := h
  have hn : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    omega
  obtain ⟨hu, hU2⟩ := natural_card_exp hF hn hU
  obtain ⟨e⟩ := hE2
  have hcardC : Nat.card ↥(c134CQ G₀ L) = 2 ^ (2 * n) := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin (2 * n) → ZMod 2) ≃ _),
      Nat.card_eq_fintype_card]
    simp
  have hC2 : ∀ x ∈ c134CQ G₀ L, x * x = 1 := by
    intro x hx
    have h1 : e (⟨x, hx⟩ * ⟨x, hx⟩) = e 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i
      show Multiplicative.toAdd (e ⟨x, hx⟩) i + Multiplicative.toAdd (e ⟨x, hx⟩) i = 0
      generalize Multiplicative.toAdd (e ⟨x, hx⟩) i = a
      revert a
      decide
    exact congrArg Subtype.val (e.injective h1)
  refine false_of_big_elementary hG (centerOf (c134Q G₀ L)) (c134CQ G₀ L) ⁅centerOf (c134Q G₀ L), L⁆
    (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx.1)
    (le_sup_left.trans hcen.symm.le) (le_sup_right.trans hcen.symm.le) hC2 hU2 hint ?_ hu
  rw [hcardC]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem c134Case4Lemma45Corr_gen4_holds :
    ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (G₀ R L : Subgroup G), IsMSPair G₀ R →
      L ∈ cComp G₀ → (G₀ : Set G) = (L : Set G) * (R : Set G) →
      C134CorrLocal.IsC134Case4Corr G₀ R L →
      ∀ y ∈ c134Q G₀ L, (∀ x ∈ c134Q G₀ L, y * x * y⁻¹ * x⁻¹ ∈ c134CQ G₀ L) →
        y ∈ frattiniIn (c134Q G₀ L) :=
  fun _ _ _ hG _ _ _ _ _ _ h4 => (false_of_case4Corr hG h4).elim

end CFSG.GH74.QTGen4

end
