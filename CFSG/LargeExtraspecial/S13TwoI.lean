module

public import CFSG.LargeExtraspecial.S13Fix
public import CFSG.LargeExtraspecial.S13TwoG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

theorem finrank_le_two_mul_inf_fixSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {f : V ≃ₗ[ZMod 2] V} (hff : ∀ v, f (f v) = v)
    {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, f w ∈ W) :
    finrank (ZMod 2) W ≤ 2 * finrank (ZMod 2) (W ⊓ fixSpace f : Submodule (ZMod 2) V) := by
  set ψ : W →ₗ[ZMod 2] V := ((f : V →ₗ[ZMod 2] V) - 1).comp W.subtype with hψ
  have hrange : LinearMap.range ψ ≤ W ⊓ fixSpace f := by
    rintro _ ⟨w, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · simp only [hψ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
        LinearEquiv.coe_coe, Module.End.one_apply]
      exact sub_mem (hW _ w.2) w.2
    · rw [mem_fixSpace]
      simp only [hψ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
        LinearEquiv.coe_coe, Module.End.one_apply, map_sub, hff]
      rw [← neg_sub, zmod2_neg_eq]
  have hker : (LinearMap.ker ψ).map W.subtype ≤ W ⊓ fixSpace f := by
    rintro _ ⟨w, hw, rfl⟩
    refine Submodule.mem_inf.mpr ⟨w.2, ?_⟩
    have : ψ w = 0 := hw
    simp only [hψ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearEquiv.coe_coe, Module.End.one_apply, sub_eq_zero] at this
    exact mem_fixSpace.mpr this
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  omega

theorem mul_mem_of_card_eq_two_mul {X : Type*} [Group X] [Finite X] {A B : Subgroup X}
    (hAB : A ≤ B) (hcard : Nat.card B = 2 * Nat.card A) {x y : X} (hx : x ∈ B) (hy : y ∈ B)
    (hxA : x ∉ A) (hyA : y ∉ A) : x * y ∈ A := by
  have hidx : (A.subgroupOf B).index = 2 := by
    have h := Subgroup.card_mul_index (A.subgroupOf B)
    rw [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv, hcard] at h
    have hpos : 0 < Nat.card A := Nat.card_pos
    nlinarith
  have := (mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    ⟨fun h => absurd (mem_subgroupOf.mp h) hxA, fun h => absurd (mem_subgroupOf.mp h) hyA⟩
  exact mem_subgroupOf.mp this

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

theorem finrank_fixSub_le_four (H : Hyp4 S g) {D : Subgroup S.O} (hDL : D ≤ S.Lbar g)
    {x y : S.O} (hx : x ∈ S.Lbar g) (hy : y ∈ S.Lbar g)
    (hcov : ∀ l ∈ S.Lbar g, l ∈ D ∨ l * x ∈ D ∨ l * y ∈ D ∨ l * x * y ∈ D) :
    finrank (ZMod 2) (fixSub S D) ≤ 4 := by
  have haQ := H.conj_mem
  have hinv : ∀ l ∈ S.Lbar g, ∀ v, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
    fun l hl v => by
      have h2 := congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
        (mul_self_of_mem_Lbar S haQ hl)
      simpa using h2
  have hcomm : ∀ l ∈ S.Lbar g, ∀ m ∈ S.Lbar g, ∀ v,
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun l hl m hm v => by
    have h2 := congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
      (S4.Lbar_comm S haQ hl hm)
    simpa using h2
  set W := fixSub S D with hW
  have hWinv : ∀ l ∈ S.Lbar g, ∀ w ∈ W, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := by
    intro l hl w hw d hd
    rw [hcomm d (hDL hd) l hl, hw d hd]
  set W₁ := W ⊓ fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) with hW₁
  have h1 := finrank_le_two_mul_inf_fixSpace (hinv x hx) (hWinv x hx)
  have hW₁inv : ∀ w ∈ W₁, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W₁ := by
    intro w hw'
    obtain ⟨hw, hwx⟩ := Submodule.mem_inf.mp hw'
    refine Submodule.mem_inf.mpr ⟨hWinv y hy w hw, ?_⟩
    rw [mem_fixSpace] at hwx ⊢
    rw [hcomm x hx y hy, hwx]
  have h2 := finrank_le_two_mul_inf_fixSpace (hinv y hy) hW₁inv
  have hle : W₁ ⊓ fixSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ fixSub S (S.Lbar g) := by
    intro w hw' l hl
    obtain ⟨hw'', hwy⟩ := Submodule.mem_inf.mp hw'
    obtain ⟨hw, hwx⟩ := Submodule.mem_inf.mp hw''
    rw [mem_fixSpace] at hwx hwy
    rcases hcov l hl with h | h | h | h
    · exact hw l h
    · have := hw _ h
      rwa [Subgroup.coe_mul, LinearEquiv.mul_apply, hwx] at this
    · have := hw _ h
      rwa [Subgroup.coe_mul, LinearEquiv.mul_apply, hwy] at this
    · have := hw _ h
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hwy, hwx] at this
  have h3 := Submodule.finrank_mono hle
  rw [finrank_fixSub_Lbar H] at h3
  have h1' : finrank (ZMod 2) W ≤ 2 * finrank (ZMod 2) W₁ := h1
  omega

section Index2

variable (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
  (hne : Fbar S g₁ K ≠ Fbar S g K)
include Y hg hperp hne

theorem card_Ebar_eq_two_mul :
    Nat.card (Ebar S g K) =
      2 * Nat.card (Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) : Subgroup S.O) := by
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hF₁ : Fbar S g₁ K ≠ ⊥ := fun h0 => by
    have := Y₁.finrank_Fbar
    rw [h0, finrank_bot] at this
    omega
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF₁
  obtain ⟨r, hr, hcard⟩ := card_Ebar_eq_mul Y Y₁ hperp hu₀ hu₀0 (Λ := Fbar S g K)
    (fun e he => Ebar_apply_sub_mem_Fbar_of_perp Y hperp he (Submodule.mem_sup_right hu₀))
  have h4 : Nat.card (Fbar S g K) = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Y.finrank_Fbar, Nat.card_zmod]
    norm_num
  rw [h4] at hr
  have hr4 : r ≤ 4 := Nat.le_of_dvd (by norm_num) hr
  interval_cases r
  · norm_num at hr
  · exfalso
    rw [one_mul] at hcard
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_left : Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) ≤ Ebar S g K) hcard.le
    apply hne
    have hle : Fbar S g₁ K ≤ Fbar S g K := by
      intro v hv e he
      have he' : e ∈ Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) := by rw [heq]; exact he
      exact (Subgroup.mem_inf.mp he').2 v (Submodule.mem_sup_right hv)
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [Y₁.finrank_Fbar, Y.finrank_Fbar])
  · exact hcard
  · norm_num at hr
  · exact absurd hcard (fun h4' => not_card_Ebar_eq_four_mul Y hg hperp h4')

theorem fixSub_T₀_eq :
    fixSub S (Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K)) = Fbar S g K ⊔ Fbar S g₁ K := by
  set D := Fbar S g K ⊔ Fbar S g₁ K with hD
  set T₀ := Ebar S g K ⊓ ptStab S D with hT₀
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hle : D ≤ fixSub S T₀ := fun v hv x hx => (Subgroup.mem_inf.mp hx).2 v hv
  have hcard := card_Ebar_eq_two_mul Y hg hperp hne
  obtain ⟨y, hyL, hyE⟩ := exists_not_mem_Ebar Y.H Y.fpf (K := K)
  obtain ⟨x, hxE, hxT⟩ : ∃ x ∈ Ebar S g K, x ∉ T₀ := by
    by_contra hc
    push Not at hc
    have h1 : Nat.card (Ebar S g K) ≤ Nat.card T₀ := Subgroup.card_le_of_le fun e he => hc e he
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    rw [← hT₀] at hcard
    omega
  have hT₀L : T₀ ≤ S.Lbar g := inf_le_left.trans Ebar_le_Lbar
  have hcov : ∀ l ∈ S.Lbar g, l ∈ T₀ ∨ l * x ∈ T₀ ∨ l * y ∈ T₀ ∨ l * x * y ∈ T₀ := by
    intro l hl
    by_cases hlE : l ∈ Ebar S g K
    · by_cases hlT : l ∈ T₀
      · exact Or.inl hlT
      · exact Or.inr (Or.inl (mul_mem_of_card_eq_two_mul inf_le_left hcard hlE hxE hlT hxT))
    · have hly : l * y ∈ Ebar S g K := Y.mul_mem_E hl hlE hyL hyE
      by_cases hlyT : l * y ∈ T₀
      · exact Or.inr (Or.inr (Or.inl hlyT))
      · right; right; right
        have := mul_mem_of_card_eq_two_mul inf_le_left hcard hly hxE hlyT hxT
        rwa [mul_assoc, S4.Lbar_comm S Y.haQ hyL (Ebar_le_Lbar hxE), ← mul_assoc] at this
  have h4 := finrank_fixSub_le_four Y.H hT₀L (Ebar_le_Lbar hxE) hyL hcov
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_Dbar Y Y₁ hne]; exact h4)).symm

end Index2

end CFSG.LargeExtraspecial.S13
