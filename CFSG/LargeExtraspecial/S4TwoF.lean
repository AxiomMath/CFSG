module

public import CFSG.LargeExtraspecial.S4TwoE
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
public import CFSG.LargeExtraspecial.S3bTenB
public import CFSG.LargeExtraspecial.S4SevenA
public import CFSG.LargeExtraspecial.S4TwoB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
noncomputable abbrev LM : Subgroup S.Mbar := (S.Lbar g).subgroupOf S.Mbar

variable (S g) in
noncomputable abbrev M0 : Subgroup S.Mbar := normalClosure (LM S g : Set S.Mbar)

theorem LM_le_M0 : LM S g ≤ M0 S g := le_normalClosure

theorem pCore_M0_eq_bot : CFSG.pCore 2 (M0 S g) = ⊥ := by
  have h := CFSG.ABGLocalTools.map_pCore_le_of_injective_of_normal (p := 2) (M0 S g).subtype
    (M0 S g).subtype_injective (by rw [range_subtype]; exact normalClosure_normal)
  rw [S.pCore_Mbar_eq_bot, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ (M0 S g).subtype_injective] at h
  exact h

theorem map_subtype_map_conj_LM (x : S.Mbar) :
    ((LM S g).map (MulAut.conj x).toMonoidHom).map S.Mbar.subtype =
      (S.Lbar g).map (MulAut.conj (x : S.O)).toMonoidHom := by
  have hLM := S.Lbar_le_Mbar g
  ext y
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, mem_subgroupOf.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, ⟨⟨l, hLM hl⟩, mem_subgroupOf.mpr hl, rfl⟩, rfl⟩

theorem weaklyClosed_LM (C : Cons311 S g) (x : S.Mbar)
    (hx : (LM S g).map (MulAut.conj x).toMonoidHom ≤ normalizer (LM S g : Set S.Mbar)) :
    (LM S g).map (MulAut.conj x).toMonoidHom = LM S g := by
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp x.2
  have e : ((LM S g).map (MulAut.conj x).toMonoidHom).map S.Mbar.subtype =
      S.Lbar ((h : G) * g) := by
    rw [map_subtype_map_conj_LM, Lbar_mul S h, hh]
  have hnorm : S.Lbar ((h : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro y hy
    rw [← e] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    rw [← hyy]
    refine mem_normalizer_of_conj_le fun l hl => ?_
    have hl' : (⟨l, S.Lbar_le_Mbar g hl⟩ : S.Mbar) ∈ LM S g := mem_subgroupOf.mpr hl
    have := (mem_normalizer_iff.mp (hx hy') _).mp hl'
    exact mem_subgroupOf.mp this
  have h1 := C.weaklyClosed (h : G) h.2 hnorm
  apply Subgroup.map_injective S.Mbar.subtype_injective
  rw [e, h1]
  ext y
  constructor
  · intro hy
    exact ⟨⟨y, S.Lbar_le_Mbar g hy⟩, mem_subgroupOf.mpr hy, rfl⟩
  · rintro ⟨y', hy', rfl⟩
    exact mem_subgroupOf.mp hy'

theorem exists_mem_M0_conj_eq (H : Hyp4 S g) (C : Cons311 S g) (x : S.Mbar) :
    ∃ k ∈ M0 S g, (S.Lbar g).map (MulAut.conj (x : S.O)).toMonoidHom =
      (S.Lbar g).map (MulAut.conj (k : S.O)).toMonoidHom := by
  have hL2 : IsPGroup 2 (LM S g) :=
    (isPGroup_Lbar S H.conj_mem).of_equiv (Subgroup.subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).symm
  obtain ⟨k, hk, e⟩ := exists_mem_conj_eq_of_weaklyClosed (L := LM S g) (K := M0 S g) LM_le_M0
    hL2 (weaklyClosed_LM C) x
  refine ⟨k, hk, ?_⟩
  rw [← map_subtype_map_conj_LM, e, map_subtype_map_conj_LM]

noncomputable abbrev LM0 (S : Setting G) (g : G) : Subgroup (M0 S g) := (LM S g).subgroupOf (M0 S g)

theorem map_conj_LM0 (k : M0 S g) :
    (((conjSubgroup k (LM0 S g)).map (M0 S g).subtype).map S.Mbar.subtype) =
      (S.Lbar g).map (MulAut.conj ((k : S.Mbar) : S.O)).toMonoidHom := by
  rw [← map_subtype_map_conj_LM]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, mem_subgroupOf.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, ⟨⟨l, LM_le_M0 hl⟩, mem_subgroupOf.mpr hl, rfl⟩, rfl⟩

theorem conj_LM0_eq_iff (H : Hyp4 S g) (k k' : M0 S g) :
    conjSubgroup k (LM0 S g) = conjSubgroup k' (LM0 S g) ↔
      (((k : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        (((k' : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  rw [← map_conj_Lbar_eq_iff H (k : S.Mbar).2 (k' : S.Mbar).2, ← map_conj_LM0, ← map_conj_LM0]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Subgroup.map_injective (M0 S g).subtype_injective
      (Subgroup.map_injective S.Mbar.subtype_injective h)

theorem isReducible_of_meet (H : Hyp4 S g) (C : Cons311 S g)
    (hmeet : ∀ k : M0 S g, conjSubgroup k (LM0 S g) ⊓ normalizer (LM0 S g : Set (M0 S g)) ≠ ⊥) :
    S.IsReducible := by
  refine isReducible_of_polar_eq_zero H fun m => ?_
  obtain ⟨k, hk, e⟩ := exists_mem_M0_conj_eq H C ⟨S.ρ m, MonoidHom.mem_range.mpr ⟨m, rfl⟩⟩
  have hpt := (map_conj_Lbar_eq_iff H (MonoidHom.mem_range.mpr ⟨m, rfl⟩) (k.2)).mp e

  rw [hpt]
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp k.2
  rw [← hh, ρ_cl_conj_z S h H.conj_mem]
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hmeet ⟨k, hk⟩)
  obtain ⟨hxc, hxn⟩ := mem_inf.mp hx
  have hxL : ((x : S.Mbar) : S.O) ∈ S.Lbar ((h : G) * g) := by
    rw [Lbar_mul S h, hh, ← map_conj_LM0 (S := S) (g := g) ⟨k, hk⟩]
    exact ⟨_, ⟨x, hxc, rfl⟩, rfl⟩
  have hxN : ((x : S.Mbar) : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
    refine mem_normalizer_of_conj_le fun l hl => ?_
    have hl' : (⟨⟨l, S.Lbar_le_Mbar g hl⟩, LM_le_M0 (mem_subgroupOf.mpr hl)⟩ : M0 S g) ∈
        LM0 S g := mem_subgroupOf.mpr (mem_subgroupOf.mpr hl)
    have := (mem_normalizer_iff.mp hxn _).mp hl'
    exact mem_subgroupOf.mp (mem_subgroupOf.mp this)
  have hx1' : ((x : S.Mbar) : S.O) ≠ 1 := fun h1 =>
    hx1 (Subtype.ext (Subtype.ext (Subtype.ext h1)))
  have hcomm := lemma_4_1 H h ⟨_, hxL, hxN, hx1'⟩
  exact (S.polar_cl_eq_zero_iff H.conj_mem (conj_mem_QG' S h.2 H.conj_mem)).mpr hcomm

theorem isReducible_or_card_conj_le (H : Hyp4 S g) (C : Cons311 S g)
    (h2 : ConjTwoTransitive (M0 S g) (LM0 S g)) :
    S.IsReducible ∨
      Nat.card (Set.range fun k : M0 S g => conjSubgroup k (LM0 S g)) ≤ 2 * S.width + 1 := by
  set φ : M0 S g →* (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    S.O.subtype.comp (S.Mbar.subtype.comp (M0 S g).subtype) with hφ
  have hβ : S.q.polarBilin.IsAlt := fun x => by
    rw [polarBilin_apply_apply]
    exact polar_self_eq_zero S.q x
  have hiso : ∀ k, φ k ∈ TauCeti.BilinForm.isometryGroup S.q.polarBilin := fun k => by
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    simp only [polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ((k : S.Mbar) : S.O).2 x y
  rcases bender_dichotomy hβ φ hiso (S.cl (g * S.z * g⁻¹)) (conj_LM0_eq_iff H) h2 with h | h
  · left
    refine isReducible_of_polar_eq_zero H fun m => ?_
    obtain ⟨k, hk, e⟩ := exists_mem_M0_conj_eq H C ⟨S.ρ m, MonoidHom.mem_range.mpr ⟨m, rfl⟩⟩
    have hpt := (map_conj_Lbar_eq_iff H (MonoidHom.mem_range.mpr ⟨m, rfl⟩) (k.2)).mp e

    rw [hpt]
    have := h ⟨k, hk⟩
    rwa [polarBilin_apply_apply] at this
  · right
    rwa [S.finrank_Qt_eq_two_mul_width] at h

end CFSG.LargeExtraspecial.S4
