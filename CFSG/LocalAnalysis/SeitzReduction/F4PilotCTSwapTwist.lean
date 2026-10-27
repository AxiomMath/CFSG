module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapPieces

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotCTSwapTwistNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem forall_eq_one_or_forall_eq_one_of_mul_eq {S : Type*} [Group S] [IsSimpleGroup S]
    (hZ : center S = ⊥) (α β : S →* S) (hmul : ∀ x, α x * β x = x)
    (hcomm : ∀ x y, Commute (α x) (β y)) : (∀ x, α x = 1) ∨ (∀ x, β x = 1) := by
  have hnorm : α.range.Normal := by
    refine ⟨fun a ha s => ?_⟩
    obtain ⟨a', rfl⟩ := ha
    refine ⟨s * a' * s⁻¹, ?_⟩
    have hc : β s * α a' = α a' * β s := (hcomm a' s).symm.eq
    have hs := hmul s
    calc α (s * a' * s⁻¹) = α s * (β s * α a' * (β s)⁻¹) * (α s)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
      _ = (α s * β s) * α a' * (α s * β s)⁻¹ := by group
      _ = s * α a' * s⁻¹ := by rw [hs]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α.range with h | h
  · left
    intro x
    have hx : α x ∈ α.range := ⟨x, rfl⟩
    rw [h] at hx
    exact hx
  · right
    intro y
    have hy : β y ∈ center S := by
      rw [mem_center_iff]
      intro z
      have hz : z ∈ α.range := h ▸ mem_top z
      obtain ⟨x, rfl⟩ := hz
      exact (hcomm x y).eq
    rw [hZ] at hy
    exact hy

section Coordinates


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G} {N N' : AmalgamNeighbour}
  (h : SwapNeighbourIso e t N) (h' : SwapNeighbourIso e t N') {J : Finset (Fin (Tag.rank .F4))}

theorem SwapNeighbourIso.mul_eq_of_fst_eq (hJ : J ⊆ N.nodes) (hJ' : J ⊆ N'.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) {a b : N.levi K}
    (hx : h'.fst hJ' x = ((h.Φ (a, b) : neighbourCore e N) : G)) :
    a * b = ⟨x, levi_le_neighbourLevi hJ x.2⟩ ∧ b * a = ⟨x, levi_le_neighbourLevi hJ x.2⟩ := by
  have h1 := h'.fst_mul_snd hJ' x
  rw [← h'.conj_fst, hx, h.swap, ← coe_mul, ← map_mul, Prod.mk_mul_mk] at h1
  have h2 := h.diag ⟨x, levi_le_neighbourLevi hJ x.2⟩
  have h3 := h.coe_injective (h1.trans h2.symm)
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

theorem SwapNeighbourIso.commute_of_fst_eq (hJ' : J ⊆ N'.nodes)
    (x y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) {a b c d : N.levi K}
    (hx : h'.fst hJ' x = ((h.Φ (a, b) : neighbourCore e N) : G))
    (hy : h'.fst hJ' y = ((h.Φ (c, d) : neighbourCore e N) : G)) : Commute a d := by
  have h1 := h'.commute_fst_snd hJ' hJ' x y
  rw [← h'.conj_fst, hx, hy, h.swap] at h1
  have h2 := (commute_subtype_coe_iff.1 h1).map h.Φ.symm.toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h2
  exact congrArg Prod.fst h2

end Coordinates

section OneTwist


variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 K} {t : G}

theorem fst_Y_eq_fst_X_or_snd_X (hX : SwapNeighbourIso e t .X) (hY : SwapNeighbourIso e t .Y)
    (hq : 4 ≤ Nat.card K) :
    (∀ x, hY.fst one_two_subset_Y x = hX.fst one_two_subset_X x) ∨
      (∀ x, hY.fst one_two_subset_Y x = hX.snd one_two_subset_X x) := by
  have hJ2 : ({1, 2} : Finset (Fin (Tag.rank .F4))).card ≤ 2 := by decide
  have hB := levi_one_two_eq_B2Levi (K := K)
  have hmemX : ∀ x, hY.fst one_two_subset_Y x ∈ neighbourCore e .X := fun x =>
    pieceCore_le_neighbourCore e .X one_two_subset_X
      (hY.range_fst_le_pieceCore hq one_two_subset_Y hJ2 ⟨x, rfl⟩)
  obtain ⟨F, hF⟩ : ∃ F : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} →*
      AmalgamNeighbour.X.levi K × AmalgamNeighbour.X.levi K,
      ∀ x, hY.fst one_two_subset_Y x = ((hX.Φ (F x) : neighbourCore e .X) : G) :=
    ⟨hX.Φ.symm.toMonoidHom.comp ((hY.fst one_two_subset_Y).codRestrict _ hmemX), fun x => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, MonoidHom.codRestrict_apply]⟩
  have hFmem : ∀ x, ((F x).1 : adjointGroup .F4 K) ∈ B2Levi K ∧
      ((F x).2 : adjointGroup .F4 K) ∈ B2Levi K := by
    intro x
    have h1 : hY.fst one_two_subset_Y x ∈ pieceCore e {1, 2} :=
      hY.range_fst_le_pieceCore hq one_two_subset_Y hJ2 ⟨x, rfl⟩
    rw [← hX.map_leviPiece hq one_two_subset_X hJ2] at h1
    obtain ⟨z, ⟨hz₁, hz₂⟩, hz⟩ := h1
    have hzF : z = F x := hX.coe_injective (hz.trans (hF x))
    rw [← hzF, ← hB]
    refine ⟨?_, ?_⟩
    · rw [levi_f4Datum_eq, mem_subgroupOf]
      exact mem_leviPiece.1 hz₁
    · rw [levi_f4Datum_eq, mem_subgroupOf]
      exact mem_leviPiece.1 hz₂
  obtain ⟨α, hα⟩ : ∃ α : B2Levi K →* B2Levi K, ∀ x, ((α x : B2Levi K) : adjointGroup .F4 K) =
      ((F (Subgroup.inclusion hB.ge x)).1 : adjointGroup .F4 K) :=
    ⟨((AmalgamNeighbour.X.levi K).subtype.comp ((MonoidHom.fst _ _).comp
      (F.comp (Subgroup.inclusion hB.ge)))).codRestrict (B2Levi K) fun x => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
          MonoidHom.coe_fst]
        exact (hFmem _).1, fun x => by
      simp only [MonoidHom.codRestrict_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, MonoidHom.coe_fst]⟩
  obtain ⟨β, hβ⟩ : ∃ β : B2Levi K →* B2Levi K, ∀ x, ((β x : B2Levi K) : adjointGroup .F4 K) =
      ((F (Subgroup.inclusion hB.ge x)).2 : adjointGroup .F4 K) :=
    ⟨((AmalgamNeighbour.X.levi K).subtype.comp ((MonoidHom.snd _ _).comp
      (F.comp (Subgroup.inclusion hB.ge)))).codRestrict (B2Levi K) fun x => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
          MonoidHom.coe_snd]
        exact (hFmem _).2, fun x => by
      simp only [MonoidHom.codRestrict_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, MonoidHom.coe_snd]⟩
  have hmul : ∀ x, α x * β x = x := by
    intro x
    have h := (hX.mul_eq_of_fst_eq hY one_two_subset_X one_two_subset_Y
      (Subgroup.inclusion hB.ge x) (a := (F (Subgroup.inclusion hB.ge x)).1)
      (b := (F (Subgroup.inclusion hB.ge x)).2) (hF _)).1
    apply Subtype.ext
    rw [Subgroup.coe_mul, hα, hβ, ← Subgroup.coe_mul, h]
    simp only [Subgroup.coe_inclusion]
  have hcomm : ∀ x y, Commute (α x) (β y) := by
    intro x y
    have h := hX.commute_of_fst_eq hY one_two_subset_Y (Subgroup.inclusion hB.ge x)
      (Subgroup.inclusion hB.ge y) (a := (F (Subgroup.inclusion hB.ge x)).1)
      (b := (F (Subgroup.inclusion hB.ge x)).2) (c := (F (Subgroup.inclusion hB.ge y)).1)
      (d := (F (Subgroup.inclusion hB.ge y)).2) (hF _) (hF _)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hα, hβ, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h.eq]
  have := isSimpleGroup_B2Levi (K := K) hq
  rcases forall_eq_one_or_forall_eq_one_of_mul_eq center_B2Levi_eq_bot α β hmul hcomm with
    hα1 | hβ1
  ·
    right
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : B2Levi K, Subgroup.inclusion hB.ge y = x :=
      ⟨⟨x, hB.le x.2⟩, Subtype.ext rfl⟩
    have h1 := hmul y
    rw [hα1, one_mul] at h1
    have hFy : F (Subgroup.inclusion hB.ge y) = (1, ⟨_, levi_le_neighbourLevi one_two_subset_X
        (Subgroup.inclusion hB.ge y).2⟩) := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · rw [← hα, hα1, OneMemClass.coe_one, OneMemClass.coe_one]
      · rw [← hβ, h1]
        simp only [Subgroup.coe_inclusion]
    rw [hF, hFy, hX.snd_apply]
  ·
    left
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : B2Levi K, Subgroup.inclusion hB.ge y = x :=
      ⟨⟨x, hB.le x.2⟩, Subtype.ext rfl⟩
    have h1 := hmul y
    rw [hβ1, mul_one] at h1
    have hFy : F (Subgroup.inclusion hB.ge y) = (⟨_, levi_le_neighbourLevi one_two_subset_X
        (Subgroup.inclusion hB.ge y).2⟩, 1) := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · rw [← hα, h1]
        simp only [Subgroup.coe_inclusion]
      · rw [← hβ, hβ1, OneMemClass.coe_one, OneMemClass.coe_one]
    rw [hF, hFy, hX.fst_apply]

theorem exists_swapNeighbourIso_fst_eq (hX : SwapNeighbourIso e t .X)
    (hY : SwapNeighbourIso e t .Y) (hq : 4 ≤ Nat.card K) :
    ∃ hY' : SwapNeighbourIso e t .Y, ∀ x, hX.fst one_two_subset_X x = hY'.fst one_two_subset_Y x ∧
      hX.snd one_two_subset_X x = hY'.snd one_two_subset_Y x := by
  rcases fst_Y_eq_fst_X_or_snd_X hX hY hq with h | h
  · refine ⟨hY, fun x => ⟨(h x).symm, ?_⟩⟩
    rw [← hX.conj_fst, ← hY.conj_fst, h x]
  · refine ⟨hY.flip, fun x => ⟨?_, ?_⟩⟩
    · rw [hY.flip_fst, ← hY.conj_fst, h x, hX.conj_snd]
    · rw [hY.flip_snd, h x]

end OneTwist

end CFSG.SeitzReduction.F4Pilot
