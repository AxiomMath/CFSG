module

public import CFSG.LargeExtraspecial.A2ModFrCNode
public import CFSG.LargeExtraspecial.S12DWCount
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrC

open Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic
open TauCeti.QuadraticMap (orthogonalGroup)

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem two_le_ncard_singular (hA : A2Action D Q ρ) {d : X} (hd : d ∈ D) :
    2 ≤ {v | Q v = 0}.ncard := by
  have htA := hA.isTypeA hd
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hne : commSpace (ρ d) ≠ ⊥ := by
    intro h
    have h2 := htA.2.2.2.1
    rw [h, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsub : ({0, v} : Set V) ⊆ {x | Q x = 0} := by
    rintro x (rfl | rfl)
    · exact map_zero Q
    · exact htA.2.2.2.2 _ hv
  calc 2 = ({0, v} : Set V).ncard := (Set.ncard_pair (Ne.symm hv0)).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem false_of_card_eq (hA : A2Action D Q ρ) {d : X} (hd : d ∈ D) {k : ℕ}
    (hV : finrank (ZMod 2) V = 2 * k)
    (hX : Nat.card X = 2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1)) : False := by
  have hO := S12DW.card_orthogonalGroup_mul_ncard_eq hA.nondegenerate hV
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective
  have hle : Nat.card X ≤ Nat.card (orthogonalGroup Q) :=
    Nat.card_le_card_of_injective (fun x => (⟨ρ x, hA.mem_orthogonalGroup x⟩ : orthogonalGroup Q))
      fun x y h => hA.injective (congrArg Subtype.val h)
  have hZ := two_le_ncard_singular hA hd
  have hpos : 0 < Nat.card (orthogonalGroup Q) := Nat.card_pos
  have h2 : Nat.card (orthogonalGroup Q) * 2 ≤
      Nat.card (orthogonalGroup Q) * {v | Q v = 0}.ncard := Nat.mul_le_mul_left _ hZ
  rw [hO, ← hX] at h2
  omega

theorem finrank_commSpaceOf_top_of_symplectic (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {k : ℕ} (hk : 3 ≤ k) {F : Type} [Field F] (hF : Nat.card F = 2)
    (Ψ : StatedSp k F →* X) (hsurj : Function.Surjective Ψ) {i₀ : Fin k} (hi₀ : i₀.val + 1 < k)
    {d : X} (hd : d ∈ D) (hmem : (rootGroup k F (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ max (2 * k + 1) 9 ∧
      (5 ≤ k → 2 * k ≤ finrank (ZMod 2) (commSpaceOf ρ ⊤)) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF])
  have hij₀ : i₀ ≠ ⟨i₀.val + 1, hi₀⟩ := SpExtras.ne_succ' hi₀
  have hd' : Ψ (levZ (elemTv i₀ ⟨i₀.val + 1, hi₀⟩)) = d := by
    have hdm : d ∈ (rootGroup k F (Pi.single i₀ 1)).map Ψ := hmem ▸ Subgroup.mem_zpowers d
    obtain ⟨x, hx, rfl⟩ := hdm
    have hr : stdVec (.difference i₀ ⟨i₀.val + 1, hi₀⟩ hij₀) = toStd k (Pi.single i₀ 1) :=
      (SpExtras.toStd_single_of_lt' hi₀).symm
    rcases eq_one_or_eq_elt hF hr hx with rfl | rfl
    · exact absurd (map_one Ψ) (hA.ne_one hd)
    · rw [elt_difference]
  have hL : ∀ g ∈ transvectionSet k (ZMod 2), Ψ (levZ g) ∈ D :=
    levi_map_mem hDc (Ψ.comp levZ) hij₀ (by rw [MonoidHom.comp_apply, hd']; exact hd)
  obtain ⟨m, hm⟩ : ∃ i : Fin k, i.val + 1 = k := ⟨⟨k - 1, by omega⟩, by simp; omega⟩
  obtain ⟨p, hp⟩ : ∃ i : Fin k, i.val + 2 = k := ⟨⟨k - 2, by omega⟩, by simp; omega⟩
  obtain ⟨q, hq⟩ : ∃ i : Fin k, i.val + 3 = k := ⟨⟨k - 3, by omega⟩, by simp; omega⟩
  have hpm : p ≠ m := fin_ne_of_val_ne (by omega)
  have hpq : p ≠ q := fin_ne_of_val_ne (by omega)
  have hqm : q ≠ m := fin_ne_of_val_ne (by omega)
  have hnode := isLeviNode Ψ hDc hL hp hm
  set H := (Ψ.comp levZ).range ⊔ Subgroup.zpowers (Ψ (sumPos p m)) ⊔
    Subgroup.zpowers (Ψ (sumNeg p m)) with hH
  have hX : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ finrank (ZMod 2) (commSpaceOf ρ H) + 1 := by
    have h1 := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear (H := H)
      (dZero_mem Ψ hDc hL hpm) (hL _ (elemTv_mem_transvectionSet hpq))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (MonoidHom.mem_range.mpr ⟨elemTv p q, rfl⟩ : Ψ (levZ (elemTv p q)) ∈ (Ψ.comp levZ).range)))
      (dZero_mul_mem Ψ hDc hL hpm hpq hqm)
    rwa [hH, sup_zpowers_eq_top Ψ hF hsurj hpm hm] at h1
  have hHX : finrank (ZMod 2) (commSpaceOf ρ H) ≤ finrank (ZMod 2) (commSpaceOf ρ ⊤) :=
    Submodule.finrank_mono (commSpaceOf_mono ρ le_top)
  rcases (show k = 3 ∨ k = 4 ∨ 5 ≤ k by omega) with rfl | rfl | hk5
  · have := finrank_commSpaceOf_le_eight_of_three hA hnode rfl
    rw [← hH] at this
    exact ⟨by omega, by omega⟩
  · have he : (Pi.single (0 : Fin 4) (1 : ZMod 2) : Fin 4 → ZMod 2) ≠ 0 :=
      Pi.single_ne_zero_iff.mpr one_ne_zero
    have := finrank_commSpaceOf_le_eight_of_four hA hnode rfl 0
      (exists_hyperplaneCentre_of_pointCentre Ψ ρ he)
      (exists_pointCentre_of_hyperplaneCentre Ψ ρ he)
    rw [← hH] at this
    exact ⟨by omega, by omega⟩
  · have h2k := IsLeviNode.finrank_commSpaceOf_eq hA hnode hk5
    rw [← hH] at h2k
    exact ⟨by omega, fun _ => by omega⟩

theorem false_of_symplectic (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D) (hA : A2Action D Q ρ)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : 10 ≤ finrank (ZMod 2) V) {k : ℕ} (hk : 3 ≤ k) {F : Type} [Field F]
    (hF : Nat.card F = 2) (Ψ : StatedSp k F →* X) (hsurj : Function.Surjective Ψ)
    (hker : Ψ.ker ≤ Subgroup.center (StatedSp k F)) {i₀ : Fin k} (hi₀ : i₀.val + 1 < k)
    {d : X} (hd : d ∈ D) (hmem : (rootGroup k F (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    False := by
  obtain ⟨h1, h2⟩ := finrank_commSpaceOf_top_of_symplectic hDc hA hk hF Ψ hsurj hi₀ hd hmem
  rw [commSpaceOf_top_eq_top ρ hirr (hA.isTypeA hd).2.1, finrank_top] at h1 h2
  rcases lt_or_ge k 5 with hk5 | hk5
  · have : max (2 * k + 1) 9 = 9 := max_eq_right (by omega)
    omega
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF])
  have hmax : max (2 * k + 1) 9 = 2 * k + 1 := max_eq_left (by omega)
  obtain ⟨r, hr⟩ := LinearMap.BilinForm.IsAlt.even_finrank (S12DW.polarBilin_isAlt Q)
    hA.nondegenerate
  have hVk : finrank (ZMod 2) V = 2 * k := by
    have := h2 hk5
    omega
  have hZ : Subgroup.center (StatedSp k F) = ⊥ := by
    rw [center_eq, CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot]
  have hinj : Function.Injective Ψ :=
    (MonoidHom.ker_eq_bot_iff Ψ).mp (eq_bot_iff.mpr (hZ ▸ hker))
  have hcard : Nat.card X = 2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩),
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  exact false_of_card_eq hA hd hVk hcard

end CFSG.LargeExtraspecial.A2Mod.FrC
