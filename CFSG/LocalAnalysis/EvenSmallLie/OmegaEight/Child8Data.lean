module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8CaseThree
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8UArg
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Frame

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup

namespace Child8Weyl

variable {W : Type} [Group W] [Finite W] (M : Child8Weyl W)

theorem index_Wp : M.Wp.index = 2 := by
  rw [index_eq_two_iff]
  refine ⟨M.s, fun b => ?_⟩
  have hboth : ¬ (b * M.s ∈ M.Wp ∧ b ∈ M.Wp) := fun ⟨h1, h2⟩ => M.s_not_mem (by
    have h := mul_mem (inv_mem h2) h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h)
  rcases M.mem_or_mul_mem b with h | h
  · exact Or.inr ⟨h, fun h' => hboth ⟨h', h⟩⟩
  · exact Or.inl ⟨h, fun h' => hboth ⟨h, h'⟩⟩

theorem card_Wp : Nat.card M.Wp = 2 ^ 13 * 42525 := by
  have h := card_mul_index M.Wp
  rw [M.index_Wp, M.card_W] at h
  omega

@[expose] noncomputable def ιEp : Multiplicative evenSub →* M.Wp :=
  M.ιE.codRestrict M.Wp fun v => (M.ιE_mem v).2

@[expose] noncomputable def ιFp : Multiplicative evenSub →* M.Wp where
  toFun v := ⟨M.ιE1 (Multiplicative.ofAdd ((Multiplicative.toAdd v : evenSub) : FrameVec)),
    (M.ιE1_mem_iff _).2 (Multiplicative.toAdd v).2⟩
  map_one' := Subtype.ext (map_one M.ιE1)
  map_mul' a b := Subtype.ext (by
    change M.ιE1 (Multiplicative.ofAdd ((Multiplicative.toAdd a : evenSub) : FrameVec) *
      Multiplicative.ofAdd ((Multiplicative.toAdd b : evenSub) : FrameVec)) = _
    rw [map_mul]
    rfl)

theorem coe_ιEp (v : Multiplicative evenSub) : (M.ιEp v : W) = M.ιE v := rfl

theorem coe_ιFp (v : Multiplicative evenSub) : (M.ιFp v : W) =
    M.ιE1 (Multiplicative.ofAdd ((Multiplicative.toAdd v : evenSub) : FrameVec)) := rfl

theorem ιFp_injective : Function.Injective M.ιFp := fun a b h => by
  have h1 := M.ιE1_injective (congrArg Subtype.val h)
  exact Subtype.ext h1

theorem mem_range_ιFp_iff {x : M.Wp} : x ∈ M.ιFp.range ↔ (x : W) ∈ M.ιE1.range := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨v, hv⟩
    have hv' : Multiplicative.toAdd v ∈ evenSub := by
      rw [← M.ιE1_mem_iff]
      exact hv ▸ x.2
    exact ⟨Multiplicative.ofAdd ⟨_, hv'⟩, Subtype.ext hv⟩

theorem mem_range_ιEp_iff {x : M.Wp} : x ∈ M.ιEp.range ↔ (x : W) ∈ M.ιE.range :=
  ⟨fun ⟨v, hv⟩ => ⟨v, congrArg Subtype.val hv⟩, fun ⟨v, hv⟩ => ⟨v, Subtype.ext hv⟩⟩

@[expose] noncomputable def toCaseOne : CaseOneData M.Wp where
  z := ⟨M.z, M.z_mem⟩
  T := (M.T ⊓ M.Wp).subgroupOf M.Wp
  ιE := M.ιEp
  ιF := M.ιFp
  card_X := M.card_Wp
  card_T := by rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, M.card_Tp]
  center_T t ht hc := by
    rcases M.center_Tp t (mem_subgroupOf.1 ht) fun u hu =>
      congrArg Subtype.val (hc ⟨u, hu.2⟩ (mem_subgroupOf.2 hu)) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  ιE_injective a b h := M.ιE_injective (congrArg Subtype.val h)
  ιF_injective := M.ιFp_injective
  ιE_evenZ := Subtype.ext M.ιE_evenZ
  ιF_evenZ := Subtype.ext M.ιE1_frameZ
  ιE_mem v := mem_subgroupOf.2 (M.ιE_mem v)
  ιF_mem v := mem_subgroupOf.2 ⟨M.ιE1_mem_T _, (M.ιFp v).2⟩
  E_up w h := by
    obtain ⟨σ, hσ, hσw⟩ := M.E_up w w.2 fun v => by
      obtain ⟨u, hu⟩ := h v
      exact ⟨u, congrArg Subtype.val hu⟩
    exact ⟨σ, hσ, fun v => Subtype.ext (hσw v)⟩
  E_down σ hσ := by
    obtain ⟨w, hw, h⟩ := M.E_down σ hσ
    exact ⟨⟨w, hw⟩, fun v => Subtype.ext (h v)⟩
  F_gens σ hσ := by
    obtain ⟨w, hw, h⟩ := M.frame_gens σ hσ
    exact ⟨⟨w, hw⟩, fun v => Subtype.ext (h _)⟩
  F_types v hv := by
    obtain ⟨w, hw, h⟩ := M.exists_conj_mem_E hv
    exact ⟨⟨w, hw⟩, M.mem_range_ιEp_iff.2 h⟩
  not_conj w h := M.not_conj w w.2 fun v => M.mem_range_ιFp_iff.1 (h v)
  elem B hB hB2 hBc := by
    have hB' : B.map M.Wp.subtype ≤ M.T ⊓ M.Wp := by
      rintro _ ⟨b, hb, rfl⟩
      exact mem_subgroupOf.1 (hB hb)
    rcases M.elem_Tp _ hB' (by
        rintro _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hB2 b hb))
      (by rw [card_map_of_injective M.Wp.subtype_injective, hBc]) with h | h
    · left
      ext b
      have key : b ∈ B ↔ (b : W) ∈ B.map M.Wp.subtype :=
        (mem_map_iff_mem M.Wp.subtype_injective).symm
      rw [M.mem_range_ιEp_iff, key, h]
    · right
      ext b
      have key : b ∈ B ↔ (b : W) ∈ B.map M.Wp.subtype :=
        (mem_map_iff_mem M.Wp.subtype_injective).symm
      rw [M.mem_range_ιFp_iff, key, h, Subgroup.mem_inf]
      exact ⟨fun h' => h'.1, fun h' => ⟨h', b.2⟩⟩
  inv y hy := by
    obtain ⟨w, hw, h⟩ := M.inv_Wp y y.2 (congrArg Subtype.val hy)
    exact ⟨⟨w, hw⟩, M.mem_range_ιFp_iff.2 h⟩

theorem s_mem_T : M.s ∈ M.T := by
  obtain ⟨v, hv⟩ := M.s_mem
  exact hv ▸ M.ιE1_mem_T v

@[expose] noncomputable def toCaseThree : CaseThreeData M.Wp where
  toCaseOneData := M.toCaseOne
  α := M.sConj
  α_α := M.sConj_sConj
  α_T t ht := by
    change M.sConj t ∈ (M.T ⊓ M.Wp).subgroupOf M.Wp
    rw [mem_subgroupOf, M.coe_sConj]
    have ht' := Subgroup.mem_inf.1 (mem_subgroupOf.1 ht)
    exact Subgroup.mem_inf.2 ⟨M.T.mul_mem (M.T.mul_mem M.s_mem_T ht'.1) (M.T.inv_mem M.s_mem_T),
      M.conj_mem t.2 M.s⟩
  α_F v := Subtype.ext (by
    change (M.sConj (M.ιFp v) : W) = M.ιFp v
    rw [M.coe_sConj, coe_ιFp, comm_of_mem_frameRange M.s_mem ⟨_, rfl⟩]
    group)
  outer_E t h := by
    have hc : ∀ v, (t : W) * M.s * M.ιE v = M.ιE v * ((t : W) * M.s) := fun v => by
      have h1 := congrArg Subtype.val (h v)
      change (t : W) * (M.sConj (M.ιEp v) : W) * (t : W)⁻¹ = M.ιE v at h1
      rw [M.coe_sConj, coe_ιEp] at h1
      have h2 : (t : W) * M.s * M.ιE v * ((t : W) * M.s)⁻¹ = M.ιE v := by
        calc (t : W) * M.s * M.ιE v * ((t : W) * M.s)⁻¹ =
              (t : W) * (M.s * M.ιE v * M.s⁻¹) * (t : W)⁻¹ := by group
          _ = M.ιE v := h1
      calc (t : W) * M.s * M.ιE v = (t : W) * M.s * M.ιE v * ((t : W) * M.s)⁻¹ *
            ((t : W) * M.s) := by group
        _ = M.ιE v * ((t : W) * M.s) := by rw [h2]
    obtain ⟨u, hu⟩ := M.centralizer_E _ hc
    apply M.s_not_mem
    have h1 : (t : W) * M.s ∈ M.Wp := hu ▸ (M.ιE_mem u).2
    have h2 := mul_mem (inv_mem t.2) h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
  outer_F t h := by
    have hc : ∀ v ∈ evenSub, (t : W) * M.s * M.ιE1 (Multiplicative.ofAdd v) =
        M.ιE1 (Multiplicative.ofAdd v) * ((t : W) * M.s) := fun v hv => by
      have h1 := congrArg Subtype.val (h (Multiplicative.ofAdd ⟨v, hv⟩))
      change (t : W) * (M.sConj (M.ιFp _) : W) * (t : W)⁻¹ = M.ιFp _ at h1
      rw [M.coe_sConj, coe_ιFp] at h1
      change (t : W) * (M.s * M.ιE1 (Multiplicative.ofAdd v) * M.s⁻¹) * (t : W)⁻¹ =
        M.ιE1 (Multiplicative.ofAdd v) at h1
      have h2 : (t : W) * M.s * M.ιE1 (Multiplicative.ofAdd v) * ((t : W) * M.s)⁻¹ =
          M.ιE1 (Multiplicative.ofAdd v) := by
        calc (t : W) * M.s * M.ιE1 (Multiplicative.ofAdd v) * ((t : W) * M.s)⁻¹ =
              (t : W) * (M.s * M.ιE1 (Multiplicative.ofAdd v) * M.s⁻¹) * (t : W)⁻¹ := by group
          _ = M.ιE1 (Multiplicative.ofAdd v) := h1
      calc (t : W) * M.s * M.ιE1 (Multiplicative.ofAdd v) =
            (t : W) * M.s * M.ιE1 (Multiplicative.ofAdd v) * ((t : W) * M.s)⁻¹ *
              ((t : W) * M.s) := by group
        _ = M.ιE1 (Multiplicative.ofAdd v) * ((t : W) * M.s) := by rw [h2]
    have h1 := M.centralizer_E1p _ hc
    change t ∈ M.ιFp.range
    rw [M.mem_range_ιFp_iff]
    have h2 := mul_mem h1 (inv_mem M.s_mem)
    rwa [mul_inv_cancel_right] at h2
  centralizer_E t h := M.mem_range_ιEp_iff.2 (M.centralizer_E t fun v =>
    congrArg Subtype.val (h v))
  mul_ne t h := by
    have h1 := congrArg Subtype.val h
    change (t : W) * (M.sConj t : W) = M.z at h1
    rw [M.coe_sConj, M.s_inv] at h1
    exact M.mul_self_ne t t.2 (by rw [← h1]; group)

end Child8Weyl

end CFSG.EvenSmallLie.OmegaEight.Child8
