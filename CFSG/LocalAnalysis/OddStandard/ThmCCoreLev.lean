module

public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LocalAnalysis.OddStandard.ThmCCoreOdd
public import CFSG.LocalAnalysis.OddStandard.ThmCCoreQuot
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.OddStandard.ThmC CFSG.OddStandard.ThmC.T CFSG.RankTwoShapes
open CFSG.GH74.GLS.Bg.TwoGroups

theorem tAmbient_swap {G : Type*} [Group G] {S Z A B : Subgroup G} (h : TAmbient S Z A B) :
    TAmbient S Z B A where
  Z_le_A := h.Z_le_B
  Z_le_B := h.Z_le_A
  A_le_S := h.B_le_S
  B_le_S := h.A_le_S
  card_S := h.card_S
  card_Z := h.card_Z
  card_A := h.card_B
  card_B := h.card_A
  A_ne_B := h.A_ne_B.symm
  mem_Z := h.mem_Z
  Z_sq := h.Z_sq
  comm_mem_Z := h.comm_mem_Z
  sq_mem_Z := h.sq_mem_Z
  A_abel := h.B_abel
  B_abel := h.A_abel
  A_sq := h.B_sq
  B_sq := h.A_sq
  AB_le_Z := fun x hxa hxb => h.AB_le_Z x hxb hxa
  A_norm := h.B_norm
  B_norm := h.A_norm
  invol := fun x hx h2 => (h.invol x hx h2).symm
  cent_A := h.cent_B
  cent_B := h.cent_A
  cent_not_A := h.cent_not_B
  cent_not_B := h.cent_not_A
  normal_dich := h.normal_dich
  elemAb_le := fun E hE hsq hc => (h.elemAb_le E hE hsq hc).symm
  extremal := h.extremal
  diag := fun g hg hz ha hb => h.diag g hg hz hb ha

theorem exists_mul_A_B {G : Type*} [Group G] {S Z A B : Subgroup G} (hS : IsT S)
    (hTA : TAmbient S Z A B) : ∀ t ∈ S, ∃ a ∈ A, ∃ b ∈ B, t = a * b := by
  obtain ⟨e, heA, heB⟩ := exists_coordinates hS hTA
  intro t ht
  set x : Tc := e ⟨t, ht⟩ with hx
  let α : Tc := ⟨x.a, 0, x.c - x.a * x.b⟩
  let β : Tc := ⟨0, x.b, 0⟩
  have hxαβ : x = α * β := by
    refine UT3.ext ?_ ?_ ?_
    · show x.a = x.a + 0
      rw [add_zero]
    · show x.b = 0 + x.b
      rw [zero_add]
    · show x.c = (x.c - x.a * x.b) + 0 + x.a * x.b
      ring
  refine ⟨((e.symm α : S) : G), (heA (e.symm α)).2 ?_, ((e.symm β : S) : G), (heB (e.symm β)).2 ?_,
    ?_⟩
  · rw [MulEquiv.apply_symm_apply]
  · rw [MulEquiv.apply_symm_apply]
  · have : (⟨t, ht⟩ : S) = e.symm α * e.symm β := by
      rw [← map_mul, ← hxαβ, hx, e.symm_apply_apply]
    exact congrArg Subtype.val this

theorem eq_top_of_solvable_quotient {Y : Type*} [Group Y] [Group.IsPerfect Y] {N : Subgroup Y}
    [N.Normal] (h : Group.IsSolvable (Y ⧸ N)) : N = ⊤ := by
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, g ∉ N := by
    by_contra hall
    exact hne (eq_top_iff.2 fun g _ => by_contra fun hg => hall ⟨g, hg⟩)
  have : Nontrivial (Y ⧸ N) :=
    ⟨⟨QuotientGroup.mk g, 1, fun h' => hg ((QuotientGroup.eq_one_iff g).1 h')⟩⟩
  exact Group.IsPerfect.not_isSolvable (Y ⧸ N) h

theorem eq_top_of_pGroup_quotient {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {N : Subgroup Y} [N.Normal] (h : IsPGroup 2 (Y ⧸ N)) : N = ⊤ := by
  have : Group.IsNilpotent (Y ⧸ N) := h.isNilpotent
  exact eq_top_of_solvable_quotient (N := N) inferInstance

section Translate

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def sylowInfL (T : Sylow 2 X) (L : Subgroup X) [L.Normal] : Sylow 2 L :=
  CFSG.QuasiDihedralFusion.sylowInfNormal T L

theorem mem_sylowInfL (T : Sylow 2 X) (L : Subgroup X) [L.Normal] (x : L) :
    x ∈ (sylowInfL T L : Subgroup L) ↔ (x : X) ∈ (T : Subgroup X) := by
  rw [sylowInfL, CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.mem_subgroupOf]

theorem map_sylowInfL (T : Sylow 2 X) (L : Subgroup X) [L.Normal] :
    (sylowInfL T L : Subgroup L).map L.subtype = (T : Subgroup X) ⊓ L := by
  rw [sylowInfL, CFSG.QuasiDihedralFusion.sylowInfNormal_coe, ← Subgroup.inf_subgroupOf_right,
    Subgroup.map_subgroupOf_eq_of_le inf_le_right]

theorem card_sylowInfL (T : Sylow 2 X) (L : Subgroup X) [L.Normal] :
    Nat.card (sylowInfL T L : Subgroup L) = Nat.card ((T : Subgroup X) ⊓ L : Subgroup X) := by
  rw [← map_sylowInfL T L, Subgroup.card_map_of_injective L.subtype_injective]

abbrev img (L : Subgroup X) (Q' : Subgroup L) : Subgroup X := Q'.map L.subtype

omit [Finite X] in
theorem mem_img {L : Subgroup X} {Q' : Subgroup L} {x : L} : (x : X) ∈ img L Q' ↔ x ∈ Q' :=
  Subgroup.mem_map_iff_mem L.subtype_injective

theorem alperin_img {T : Sylow 2 X} {Z A B L : Subgroup X} [L.Normal]
    (hTA : TAmbient (T : Subgroup X) Z A B) (hZD : Z ≤ (T : Subgroup X) ⊓ L) {Q' : Subgroup L}
    (hQ' : IsAlperinSubgroup 2 (sylowInfL T L : Subgroup L) Q') :
    img L Q' ≤ (T : Subgroup X) ⊓ L ∧ Z ≤ img L Q' := by
  have hQS := hQ'.1
  refine ⟨?_, fun z hz => ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨(mem_sylowInfL T L q).1 (hQS hq), q.2⟩
  · have hzL : z ∈ L := (hZD hz).2
    have hzT : z ∈ (T : Subgroup X) := (hZD hz).1
    have hmem : (⟨z, hzL⟩ : L) ∈ centralizer (Q' : Set L) ⊓ (sylowInfL T L : Subgroup L) := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun q hq => ?_, (mem_sylowInfL T L _).2 hzT⟩
      apply Subtype.ext
      have hqT : (q : X) ∈ (T : Subgroup X) := (mem_sylowInfL T L q).1 (hQS hq)
      exact (((hTA.mem_Z z).1 hz).2 q hqT).symm
    exact ⟨⟨z, hzL⟩, hQ'.2.2.1 hmem, rfl⟩

omit [Finite X] in
theorem mem_nzr_img {L : Subgroup X} [L.Normal] {Q' : Subgroup L} {n : L}
    (hn : n ∈ normalizer (Q' : Set L)) : (n : X) ∈ nzr (img L Q') := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨n * y * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn y).1 hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    have hxL : x ∈ L := by
      have : x = (n : X)⁻¹ * y * n := by
        rw [show (y : X) = (n : X) * x * (n : X)⁻¹ from hyx]
        group
      rw [this]
      exact L.mul_mem (L.mul_mem (L.inv_mem n.2) y.2) n.2
    have hyy : (n * ⟨x, hxL⟩ * n⁻¹ : L) = y := Subtype.ext (by simpa using hyx.symm)
    have := (Subgroup.mem_normalizer_iff.1 hn ⟨x, hxL⟩).2 (by rw [hyy]; exact hy)
    exact ⟨⟨x, hxL⟩, this, rfl⟩

omit [Finite X] in
theorem mem_centralizer_of_img {L : Subgroup X} {Q' : Subgroup L} {n : L}
    (h : ∀ q ∈ img L Q', (n : X) * q * (n : X)⁻¹ = q) : n ∈ centralizer (Q' : Set L) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  apply Subtype.ext
  have h1 := h (q : X) ⟨q, hq, rfl⟩
  calc (q : X) * n = ((n : X) * q * (n : X)⁻¹) * n := by rw [h1]
    _ = n * q := by group

end Translate

end CFSG.OddStandard.ThmC.Core
