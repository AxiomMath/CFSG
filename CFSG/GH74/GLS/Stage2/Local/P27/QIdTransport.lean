module

public import CFSG.GH74.GLS.Stage2.Final.ModelLayerQuot
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdCfg

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Subgroup CFSG

theorem isQuasisimple_of_surjective_of_ker_eq {P A B : Type*} [Group P] [Group A] [Group B]
    (f : P →* A) (g : P →* B) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) (hA : IsQuasisimple A) : IsQuasisimple B :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq h).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg))) hA

theorem layer_transport {X : Type} [Group X] [Finite X]
    (Y M : Subgroup X) [Y.Normal] [M.Normal] (hM : Odd (Nat.card M)) (hMY : M ≤ Y)
    (hL : pLayer X 2 ≤ Y)
    {K : Type} [Group K] (θ : ↥Y →* K) (hθ : ∀ y : ↥Y, θ y = 1 ↔ (y : X) ∈ M)
    (Ω : Subgroup K) (hΩθ : Ω ≤ θ.range) (hΩn : (Ω.subgroupOf θ.range).Normal)
    (hq : IsQuasisimple ↥Ω) :
    Ω ≤ ((pLayer X 2).subgroupOf Y).map θ := by
  set Ω₁ : Subgroup ↥Y := Ω.comap θ with hΩ₁
  have hΩ₁n : Ω₁.Normal := by
    have h : Ω₁ = (Ω.subgroupOf θ.range).comap θ.rangeRestrict := Subgroup.ext fun y => Iff.rfl
    rw [h]
    exact hΩn.comap θ.rangeRestrict
  set Ω₂ : Subgroup X := Ω₁.map Y.subtype with hΩ₂
  have hΩ₂Y : Ω₂ ≤ Y := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hΩ₂sub : Ω₂.subgroupOf Y = Ω₁ :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective Ω₁
  have hΩ₂subn : Ω₂.IsSubnormal :=
    Subgroup.IsSubnormal.step Ω₂ Y hΩ₂Y (Subgroup.Normal.isSubnormal inferInstance)
      (hΩ₂sub ▸ hΩ₁n)
  set q : X →* X ⧸ M := QuotientGroup.mk' M with hqdef
  have hΩ₃subn : (Ω₂.map q).IsSubnormal := hΩ₂subn.map (QuotientGroup.mk'_surjective M)
  let f : ↥Ω₁ →* ↥Ω := (θ.comp Ω₁.subtype).codRestrict Ω (fun x => x.2)
  let g : ↥Ω₁ →* ↥(Ω₂.map q) := (q.comp (Y.subtype.comp Ω₁.subtype)).codRestrict (Ω₂.map q)
    (fun x => Subgroup.mem_map.2 ⟨((x : ↥Y) : X), Subgroup.mem_map.2 ⟨(x : ↥Y), x.2, rfl⟩, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨y, rfl⟩ := hΩθ hw
    exact ⟨⟨y, hw⟩, Subtype.ext rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hw
    exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩
  have hker : f.ker = g.ker := by
    ext x
    have e1 : f x = 1 ↔ θ (x : ↥Y) = 1 := ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have e2 : g x = 1 ↔ q (((x : ↥Y)) : X) = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, e1, e2, hθ, hqdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hq3 : IsQuasisimple ↥(Ω₂.map q) :=
    isQuasisimple_of_surjective_of_ker_eq f g hf hg hker hq
  have hp2 : IsPComponent 2 (Ω₂.map q) :=
    CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad.isPComponent_two_of_isComponent ⟨hq3, hΩ₃subn⟩
  have hle : Ω₂.map q ≤ (pLayer X 2).map q := by
    rw [hqdef, CFSG.GH74.GLS.Stage2.Final.ModelLQ.pLayer_map_quotient_of_odd M hM]
    exact le_sSup hp2
  intro ω hω
  obtain ⟨y, hy⟩ := hf ⟨ω, hω⟩
  have hθy : θ (y : ↥Y) = ω := congrArg Subtype.val hy
  obtain ⟨l, hl, hlq⟩ := Subgroup.mem_map.1 (hle (g y).2)
  have hm : l⁻¹ * ((y : ↥Y) : X) ∈ M := QuotientGroup.eq.1 hlq
  have hy' : (y : ↥Y) = (⟨l, hL hl⟩ : ↥Y) * (⟨l⁻¹ * ((y : ↥Y) : X), hMY hm⟩ : ↥Y) :=
    Subtype.ext (by simp)
  refine ⟨⟨l, hL hl⟩, Subgroup.mem_subgroupOf.2 hl, ?_⟩
  rw [← hθy, hy', map_mul, (hθ ⟨l⁻¹ * ((y : ↥Y) : X), hMY hm⟩).2 hm, mul_one]

end CFSG.GH74.GLS.Stage2.Local.P27.QId
