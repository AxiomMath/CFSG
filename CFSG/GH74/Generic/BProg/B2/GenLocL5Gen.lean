module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicIso4
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

namespace GenLocL5Gen

variable {M : Type} [Group M]

@[expose] def adjoinInvolution (E : Subgroup M) (u : M) (hu : u * u = 1) (hc : ∀ v ∈ E, u * v = v * u) :
    Subgroup M where
  carrier := {x | x ∈ E ∨ ∃ y ∈ E, x = y * u}
  mul_mem' := by
    rintro a b (ha | ⟨y, hy, rfl⟩) (hb | ⟨z, hz, rfl⟩)
    · exact Or.inl (E.mul_mem ha hb)
    · exact Or.inr ⟨a * z, E.mul_mem ha hz, by rw [mul_assoc]⟩
    · refine Or.inr ⟨y * b, E.mul_mem hy hb, ?_⟩
      rw [mul_assoc, hc b hb, ← mul_assoc]
    · refine Or.inl ?_
      have : y * u * (z * u) = y * z := by
        rw [mul_assoc, ← mul_assoc u z u, hc z hz, mul_assoc z u u, hu, mul_one]
      rw [this]
      exact E.mul_mem hy hz
  one_mem' := Or.inl E.one_mem
  inv_mem' := by
    rintro a (ha | ⟨y, hy, rfl⟩)
    · exact Or.inl (E.inv_mem ha)
    · refine Or.inr ⟨y⁻¹, E.inv_mem hy, ?_⟩
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
      rw [mul_inv_rev, hui, ← hc y⁻¹ (E.inv_mem hy)]

theorem mem_adjoin_of_mem {E : Subgroup M} {u : M} {hu : u * u = 1} {hc : ∀ v ∈ E, u * v = v * u}
    {x : M} (hx : x ∈ E) : x ∈ adjoinInvolution E u hu hc := Or.inl hx

theorem u_mem_adjoin {E : Subgroup M} {u : M} {hu : u * u = 1} {hc : ∀ v ∈ E, u * v = v * u} :
    u ∈ adjoinInvolution E u hu hc := Or.inr ⟨1, E.one_mem, (one_mul u).symm⟩

theorem isEA_adjoin {E : Subgroup M} (hE : CFSG.IsElementaryAbelian 2 ↥E) {u : M} {hu : u * u = 1}
    {hc : ∀ v ∈ E, u * v = v * u} :
    CFSG.IsElementaryAbelian 2 ↥(adjoinInvolution E u hu hc) := by
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hEs : ∀ x ∈ E, x * x = 1 := fun x hx =>
    congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hE (⟨x, hx⟩ : E))
  refine WeakSigGen.isElementaryAbelian_of_forall ?_ ?_
  · rintro a (ha | ⟨y, hy, rfl⟩) b (hb | ⟨z, hz, rfl⟩)
    · exact hEc a ha b hb
    · rw [← mul_assoc, hEc a ha z hz, mul_assoc, ← hc a ha, ← mul_assoc]
    · rw [mul_assoc, hc b hb, ← mul_assoc, hEc y hy b hb, mul_assoc]
    · calc y * u * (z * u) = y * z := by
            rw [mul_assoc, ← mul_assoc u z u, hc z hz, mul_assoc z u u, hu, mul_one]
        _ = z * y := hEc y hy z hz
        _ = z * u * (y * u) := by
            rw [mul_assoc, ← mul_assoc u y u, hc y hy, mul_assoc y u u, hu, mul_one]
  · rintro a (ha | ⟨y, hy, rfl⟩)
    · exact hEs a ha
    · calc y * u * (y * u) = y * y := by
            rw [mul_assoc, ← mul_assoc u y u, hc y hy, mul_assoc y u u, hu, mul_one]
        _ = 1 := hEs y hy


section Out16

@[expose] def Out16 (X : Type) [Group X] : Prop :=
  ∀ β : MulAut X, β * β = 1 → β ∉ (MulAut.conj : X →* MulAut X).range →
    ∃ V : Subgroup X, (∀ x ∈ V, β x = x) ∧ CFSG.IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 16

theorem Out16.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : Out16 X) : Out16 Y := by
  intro β hβ hβi
  let β' : MulAut X := MulAut.congr e.symm β
  have hβ'2 : β' * β' = 1 := by
    have := congrArg (MulAut.congr e.symm) hβ
    rwa [map_mul, map_one] at this
  have hβ'i : β' ∉ (MulAut.conj : X →* MulAut X).range := by
    intro hmem
    apply hβi
    have h1 : (MulAut.congr e).toMonoidHom β' ∈
        (MulAut.conj : X →* MulAut X).range.map (MulAut.congr e).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hmem
    rw [GenLocBasic.map_congr_inn e] at h1
    have h2 : (MulAut.congr e).toMonoidHom β' = β := by
      ext y
      simp [β', MulAut.congr_apply]
    rwa [h2] at h1
  obtain ⟨V, hV, hVea, hVcard⟩ := h β' hβ'2 hβ'i
  refine ⟨V.map e.toMonoidHom, ?_, CFSG.IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hV x hx
    change e.symm (β (e x)) = x at this
    change β (e x) = e x
    calc β (e x) = e (e.symm (β (e x))) := (e.apply_symm_apply _).symm
      _ = e x := by rw [this]
  · rw [Subgroup.card_map_of_injective e.injective, hVcard]


theorem not_sectional_of_out16 {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J) (h : Out16 J)
    {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut J)
    (hout : ¬ α.range ≤ (MulAut.conj : J →* MulAut J).range) :
    ¬ SectionalTwoRankLE ↥(innJoin α) 4 := by
  intro hsec
  obtain ⟨u, ⟨a, rfl⟩, hu⟩ := IsConcreteLE.not_le_iff_exists.1 hout
  have hu2 : α a * α a = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a, map_one]
  obtain ⟨V, hVfix, hVea, hVcard⟩ := h (α a) hu2 hu
  have hinj : Function.Injective (MulAut.conj : J →* MulAut J) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    by_contra hz1
    have hzc : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun y => by
      have := congrArg (fun φ : MulAut J => φ y) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * z = z * y * z⁻¹ * z := by rw [this]
        _ = z * y := by group
    have hct : Subgroup.center J = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with hb | ht
      · exact absurd (Subgroup.mem_bot.1 (hb ▸ hzc)) hz1
      · exact ht
    have hcomm : IsMulCommutative J :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (hct ▸ Subgroup.mem_top a) b).symm⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hs
    have hd : 16 ∣ Nat.card J := hVcard ▸ Subgroup.card_subgroup_dvd_card V
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 16 hd) with h1 | h1
    · omega
    · rw [← h1] at hp
      exact absurd hp (by norm_num)
  set E : Subgroup (MulAut J) := V.map (MulAut.conj : J →* MulAut J) with hEdef
  have hEinn : E ≤ (MulAut.conj : J →* MulAut J).range := Subgroup.map_le_range _ _
  have hEcard : Nat.card ↥E = 16 := by
    rw [hEdef, Subgroup.card_map_of_injective hinj, hVcard]
  have hEea : CFSG.IsElementaryAbelian 2 ↥E := CFSG.IsElementaryAbelian.map _
  have hcomm : ∀ φ ∈ E, α a * φ = φ * α a := by
    rintro _ ⟨v, hv, rfl⟩
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hVfix v hv]
  set W : Subgroup (MulAut J) := adjoinInvolution E (α a) hu2 hcomm with hWdef
  have hWea : CFSG.IsElementaryAbelian 2 ↥W := isEA_adjoin hEea
  have hWinn : W ≤ innJoin α := by
    intro x hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Subgroup.mem_sup_left (hEinn hx)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hEinn hy))
        (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hEW : E < W := by
    refine lt_of_le_of_ne (fun x hx => mem_adjoin_of_mem hx) fun hEq => ?_
    have : α a ∈ E := by rw [hEq]; exact u_mem_adjoin
    exact hu (hEinn this)
  have hcardW : 32 ≤ Nat.card ↥W := by
    have h1 := Subgroup.card_lt_of_lt hEW
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEW.le
    rw [hEcard] at h1 hk
    omega
  let W' : Subgroup ↥(innJoin α) := W.subgroupOf (innJoin α)
  have hW'card : Nat.card ↥W' = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWinn).toEquiv
  have hW'ea : CFSG.IsElementaryAbelian 2 ↥W' := by
    refine WeakSigGen.isElementaryAbelian_of_forall (G := ↥(innJoin α)) (fun x hx y hy => ?_)
      (fun x hx => ?_)
    · apply Subtype.ext
      exact congrArg (fun z : ↥W => (z : MulAut J)) (mul_comm' (⟨x.1, hx⟩ : W) ⟨y.1, hy⟩)
    · apply Subtype.ext
      exact congrArg (fun z : ↥W => (z : MulAut J))
        (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hWea (⟨x.1, hx⟩ : W))
  have hbound := hsec.card_le_of_elementary W'
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 W').1 hW'ea)
  omega

end Out16

end GenLocL5Gen

end CFSG.GH74.Generic.BProg.B2
