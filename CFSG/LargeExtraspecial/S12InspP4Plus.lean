module

public import CFSG.LargeExtraspecial.GLW4Main
public import CFSG.LargeExtraspecial.S12InspP4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

section Abstract

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {π : T.M →* (V ≃ₗ[ZMod 2] V)}
  {W₁ W₂ : Submodule (ZMod 2) T.Qt}

theorem card_map_eq_of_lat4 (hl : W4DW.Lat4 T R W₁ W₂) (A : W4Loc.Act T R π)
    (hs : ∀ f : W₁ ≃ₗ[ZMod 2] W₁, ∃ r : T.M, (r : X) ∈ R ∧
      ∀ w : W₁, ((f w : W₁) : T.Qt) = ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w)
    (hcardR : Nat.card ((R.subgroupOf T.M).map π) = 20160 ∨
      Nat.card ((R.subgroupOf T.M).map π) = 25920) :
    Nat.card ((R.subgroupOf T.M).map π) = 20160 := by
  let p : R.subgroupOf T.M →* (V ≃ₗ[ZMod 2] V) := π.comp (R.subgroupOf T.M).subtype
  let φ : R.subgroupOf T.M →* (T.Qt ≃ₗ[ZMod 2] T.Qt) :=
    (T.O.subtype.comp T.ρ).comp (R.subgroupOf T.M).subtype
  have hφ : ∀ (x : R.subgroupOf T.M) (u : T.Qt), u ∈ W₁ → φ x u ∈ W₁ :=
    fun x u hu => hl.inv₁ x.1 (mem_subgroupOf.mp x.2) u hu
  let f := S4.restrictHom φ W₁ hφ
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨r, hr, hre⟩ := hs e
    exact ⟨⟨r, mem_subgroupOf.mpr hr⟩, LinearEquiv.ext fun w => Subtype.ext (hre w).symm⟩
  have hker : p.ker ≤ f.ker := by
    intro r hr
    have hQ : (r : T.M) ∈ T.Q := A.ker_R r (mem_subgroupOf.mp r.2) hr
    refine MonoidHom.mem_ker.mpr ((S4.restrictHom_eq_one_iff φ W₁ hφ r).mpr fun u _ => ?_)
    change ((T.ρ (r : T.M) : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) u = u
    rw [T.ρ_eq_one_of_mem_Q hQ]
    rfl
  have hGL : Nat.card (W₁ ≃ₗ[ZMod 2] W₁) = 20160 := by
    rw [CFSG.GroupTheory.GLnTwoSplitting.card_linearEquiv_eq hl.finrank₁,
      CFSG.GH74.Exceptional.card_GL_four_two]
  have hf : Nat.card (W₁ ≃ₗ[ZMod 2] W₁) = f.ker.index := by
    rw [index_ker, f.range_eq_top_of_surjective hsurj, card_top]
  have hp : p.ker.index = Nat.card ((R.subgroupOf T.M).map π) := by
    rw [index_ker, MonoidHom.range_comp, range_subtype]
  have hdvd : 20160 ∣ Nat.card ((R.subgroupOf T.M).map π) := by
    rw [← hGL, hf, ← hp]
    exact index_dvd_of_le hker
  rcases hcardR with h1 | h1
  · exact h1
  · rw [h1] at hdvd
    norm_num at hdvd

theorem dvd_card_or_dvd_index_of_act (A : W4Loc.Act T R π)
    (hsimp : IsSimpleGroup ((R.subgroupOf T.M).map π)) {k : ℕ}
    (hk : Nat.card ((R.subgroupOf T.M).map π) = k) (N : Subgroup T.Mbar) [N.Normal] :
    k ∣ Nat.card N ∨ k ∣ N.index := by
  subst hk
  let ρ' : T.M →* T.Mbar := T.ρ.codRestrict T.Mbar W4Loc.ρ_mem_Mbar
  let H : Subgroup T.Mbar := (R.subgroupOf T.M).map ρ'
  let πb := W4Loc.πbar T π A.Q_le_ker
  have hmem : ∀ x : H, πb x ∈ (R.subgroupOf T.M).map π := by
    rintro ⟨_, r, hr, rfl⟩
    exact ⟨r, hr, (W4Loc.πbar_ρ A.Q_le_ker r).symm⟩
  let f : H →* (R.subgroupOf T.M).map π := (πb.comp H.subtype).codRestrict _ hmem
  have hfs : Function.Surjective f := by
    rintro ⟨_, r, hr, rfl⟩
    exact ⟨⟨ρ' r, r, hr, rfl⟩, Subtype.ext (W4Loc.πbar_ρ A.Q_le_ker r)⟩
  exact dvd_card_or_dvd_index_of_surjective f hfs N

end Abstract

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {c : Config}

theorem card_πR_of_plus (h : W4Hyp S g t c) [IsSimpleGroup G] (hNQ6 : NQPlus6Stmt)
    (hp : c = .omegaPlus6) : Nat.card ((h.R₀.subgroupOf h.S₀.M).map h.π) = 20160 := by
  have : FiniteDimensional (ZMod 2) (Vt S g t) := Module.Finite.of_finite
  obtain ⟨W₁, W₂, hl⟩ := exists_lat4 h hNQ6 hp
  have hcardR : Nat.card ((h.R₀.subgroupOf h.S₀.M).map h.π) = 20160 ∨
      Nat.card ((h.R₀.subgroupOf h.S₀.M).map h.π) = 25920 := by
    rw [h.πR_eq]
    exact O62.card_omegaGroup h.finrank_Vt h.qf_nondeg
  exact card_map_eq_of_lat4 hl h.act (surj_of h hl) hcardR

theorem dvd_card_or_dvd_index_of_plus (h : W4Hyp S g t c) [IsSimpleGroup G]
    (hNQ6 : NQPlus6Stmt) (hp : c = .omegaPlus6) (N : Subgroup h.S₀.Mbar) (hN : N.Normal) :
    20160 ∣ Nat.card N ∨ 20160 ∣ N.index := by
  have hsimp : IsSimpleGroup ↥((h.R₀.subgroupOf h.S₀.M).map h.π) := by
    rw [h.π_R₀]
    exact isSimpleGroup_RmodN_of_occurs h.occ
  exact dvd_card_or_dvd_index_of_act h.act hsimp (card_πR_of_plus h hNQ6 hp) N

end CFSG.LargeExtraspecial.GLW4
