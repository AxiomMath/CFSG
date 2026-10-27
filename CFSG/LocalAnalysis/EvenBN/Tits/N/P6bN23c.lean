module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bDict
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bRk

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup Module CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open
  CFSG.LocalAnalysis.EvenBN.Tits.I21L

section ModGen

theorem not_comm_A6 : ¬ (∀ a b : alternatingGroup (Fin 6), a * b = b * a) := fun h => by
  have := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 6)).1 ⟨⟨h⟩⟩
  simp at this

section Lift

variable {V : Type*} [CommGroup V] [Finite V] [Fact (∀ a : V, a * a = 1)]
variable {Z : Subgroup V} {B : Subgroup (MulAut V)} {hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z}

theorem liftAdd_map_quotRep (σ : ↥B) (U : Submodule (ZMod 2) (Additive (V ⧸ Z))) :
    liftAdd Z (U.map (quotRep Z B hB σ : Additive (V ⧸ Z) →ₗ[ZMod 2] Additive (V ⧸ Z))).toAddSubgroup =
      (liftAdd Z U.toAddSubgroup).map ((σ : MulAut V) : V →* V) := by
  have hBmem : ∀ τ ∈ B, ∀ z' ∈ Z, (τ : MulAut V) z' ∈ Z := fun τ hτ z' hz' =>
    (hB τ hτ) ▸ ⟨z', hz', rfl⟩
  ext v
  simp only [Subgroup.mem_map, MonoidHom.coe_coe, mem_liftAdd, Submodule.mem_toAddSubgroup,
    Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, hut⟩
    obtain ⟨v₀, rfl⟩ := cls_surjective Z u
    have h1 : quotRep Z B hB σ (cls Z v₀) = cls Z v := hut
    rw [quotRep_cls] at h1
    have hz' : ((σ : MulAut V) v₀)⁻¹ * v ∈ Z := (cls_eq_iff Z _ _).1 h1
    have hzz := hBmem ((σ⁻¹ : ↥B) : MulAut V) (σ⁻¹).2 _ hz'
    refine ⟨v₀ * ((σ⁻¹ : ↥B) : MulAut V) (((σ : MulAut V) v₀)⁻¹ * v), ?_, ?_⟩
    · rw [cls_mul, (cls_eq_zero_iff Z _).2 hzz, add_zero]; exact hu
    · have hinv : ∀ w : V, (σ : MulAut V) (((σ⁻¹ : ↥B) : MulAut V) w) = w := fun w => by
        have := congrArg (fun τ : ↥B => (τ : MulAut V) w) (mul_inv_cancel σ)
        simpa using this
      rw [map_mul, hinv]; group
  · rintro ⟨v', hv', rfl⟩
    refine ⟨cls Z v', hv', ?_⟩
    show quotRep Z B hB σ (cls Z v') = cls Z _
    rw [quotRep_cls]

end Lift

section JbarComm

theorem jbar_comm {Γ : Type*} [Group Γ] {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    (ρ : Γ →* (Q ≃ₗ[ZMod 2] Q)) (Jb Wb : Subgroup Γ) [Wb.Normal]
    (hWtriv : ∀ w ∈ Wb, ρ w = 1)
    (e : ↥Jb ⧸ Wb.subgroupOf Jb ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) :
    ∀ a ∈ Jb.map ρ, ∀ b ∈ Jb.map ρ, a * b = b * a := by
  have hq : ∀ x y : ↥Jb ⧸ Wb.subgroupOf Jb, x * y = y * x := fun x y =>
    e.injective (by simp only [map_mul]; exact mul_comm _ _)
  rintro _ ⟨σ₁, hσ₁, rfl⟩ _ ⟨σ₂, hσ₂, rfl⟩
  have h1 : (QuotientGroup.mk (⟨σ₁, hσ₁⟩ * ⟨σ₂, hσ₂⟩) : ↥Jb ⧸ Wb.subgroupOf Jb) =
      QuotientGroup.mk (⟨σ₂, hσ₂⟩ * ⟨σ₁, hσ₁⟩) :=
    hq (QuotientGroup.mk ⟨σ₁, hσ₁⟩) (QuotientGroup.mk ⟨σ₂, hσ₂⟩)
  have h2 : (σ₁ * σ₂)⁻¹ * (σ₂ * σ₁) ∈ Wb := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1)
  have h3 : ρ ((σ₁ * σ₂)⁻¹ * (σ₂ * σ₁)) = 1 := hWtriv _ h2
  simp only [map_mul, map_inv] at h3
  exact inv_mul_eq_one.1 h3

end JbarComm

end ModGen

section CoreStmts

@[expose] def A6CentStmt : Prop :=
  ∀ {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] {B' : Type} [Group B'] [Finite B']
    (ρ : B' →* (Q ≃ₗ[ZMod 2] Q)) {x t z h : B'}, HypM ρ x t z h →
      Nonempty ((normalClosure ({x} : Set B')).map ρ ≃* alternatingGroup (Fin 6)) →
        centralizer (((normalClosure ({x} : Set B')).map ρ : Subgroup (Q ≃ₗ[ZMod 2] Q)) :
          Set (Q ≃ₗ[ZMod 2] Q)) = ⊥

@[expose] def RankThreeStmt : Prop :=
  ∀ {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] {B' : Type} [Group B'] [Finite B']
    (ρ : B' →* (Q ≃ₗ[ZMod 2] Q)) {x t z h s : B'}, HypM ρ x t z h →
      (Nonempty ((normalClosure ({x} : Set B')).map ρ ≃* alternatingGroup (Fin 6)) ∨
        ∀ a ∈ (normalClosure ({x} : Set B')).map ρ, ∀ b ∈ (normalClosure ({x} : Set B')).map ρ,
          a * b = b * a) →
      ρ s * ρ s = 1 → rk (ρ s) = 3 →
        Nonempty ((normalClosure ({x} : Set B')).map ρ ≃* alternatingGroup (Fin 6)) ∧
          ρ s ∉ (normalClosure ({x} : Set B')).map ρ ∧
          ∃ V₁ : Submodule (ZMod 2) Q, finrank (ZMod 2) V₁ = 4 ∧
            (∀ g ∈ (normalClosure ({x} : Set B')).map ρ, Stable g V₁) ∧
            IsCompl V₁ (V₁.map (ρ t : Q →ₗ[ZMod 2] Q)) ∧ V₁.map (ρ s : Q →ₗ[ZMod 2] Q) = V₁

end CoreStmts

section Kzsec

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


variable [Fact (∀ a b : ↥d.s56V, a * b = b * a)] [Fact (∀ a : ↥d.s56V, a * a = 1)]

theorem Kz_le_Hg {c : G} (hc : c ∈ Kz d z₀) : c ∈ Hg d := hc.1

theorem starB_eq_starHom {g : G} (hg : g ∈ Hg d) : starB d g hg = starHom d ⟨g, hg⟩ :=
  Subtype.ext (starHom_val ⟨g, hg⟩).symm

theorem quotRep_starB_eq_one_of_mem_Kz (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    {c : G} (hc : c ∈ Kz d z₀) :
    quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) (starB d c (Kz_le_Hg hc)) = 1 := by
  have hcom : ∀ a b : ↥d.s56V, a * b = b * a := Fact.out
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨v, rfl⟩ := cls_surjective (Zv d z₀) q
  rw [quotRep_cls]
  show cls (Zv d z₀) _ = cls (Zv d z₀) v
  rw [cls_eq_iff]
  show ((((starB d c (Kz_le_Hg hc) : MulAut ↥d.s56V) v)⁻¹ * v : ↥d.s56V) : G) ∈ Zz d z₀
  have h1 : (((starB d c (Kz_le_Hg hc) : MulAut ↥d.s56V) v : ↥d.s56V) : G) = c * v * c⁻¹ :=
    star_apply_val (Kz_le_Hg hc) v
  have h2 := hc.2.2 (v : G) v.2
  have h3 : ((((starB d c (Kz_le_Hg hc) : MulAut ↥d.s56V) v)⁻¹ * v : ↥d.s56V) : G) =
      (c * v * c⁻¹)⁻¹ * v := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h1]
  rw [h3]
  have h4 : (c * (v : G) * c⁻¹)⁻¹ * v = (c * v * c⁻¹ * (v : G)⁻¹)⁻¹ := by
    have hmem : c * (v : G) * c⁻¹ ∈ d.s56V := by
      have := ((starB d c (Kz_le_Hg hc) : MulAut ↥d.s56V) v).2
      rwa [h1] at this
    have := congrArg (fun a : ↥d.s56V => (a : G))
      (hcom ⟨c * v * c⁻¹, hmem⟩⁻¹ v)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [this]
    group
  rw [h4]
  exact inv_mem h2

theorem mem_Kz_of_quotRep_eq_one (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    {o : G} (ho : o ∈ Hg d)
    (h1 : quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) (starB d o ho) = 1) : o ∈ Kz d z₀ := by
  have hcom : ∀ a b : ↥d.s56V, a * b = b * a := Fact.out
  refine ⟨ho, mem_normalizer_Z hZH ho, fun y hy => ?_⟩
  have h2 : quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) (starB d o ho) (cls (Zv d z₀) ⟨y, hy⟩) =
      cls (Zv d z₀) ⟨y, hy⟩ := by rw [h1]; rfl
  rw [quotRep_cls] at h2
  have h3 := (cls_eq_iff _ _ _).1 h2
  have h4 : ((((starB d o ho : MulAut ↥d.s56V) ⟨y, hy⟩)⁻¹ * ⟨y, hy⟩ : ↥d.s56V) : G) ∈ Zz d z₀ :=
    h3
  have h5 : (((starB d o ho : MulAut ↥d.s56V) ⟨y, hy⟩ : ↥d.s56V) : G) = o * y * o⁻¹ :=
    star_apply_val ho ⟨y, hy⟩
  have hmem : o * y * o⁻¹ ∈ d.s56V := by
    have := ((starB d o ho : MulAut ↥d.s56V) ⟨y, hy⟩).2
    rwa [h5] at this
  have h6 := congrArg (fun a : ↥d.s56V => (a : G)) (hcom ⟨o * y * o⁻¹, hmem⟩⁻¹ ⟨y, hy⟩)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h6
  rw [Subgroup.coe_mul, Subgroup.coe_inv, h5, h6] at h4
  have := inv_mem h4
  simpa [mul_assoc] using this

theorem jp_comap_eq (hz : d.S56Z0 z₀) (hWimg : img d (Wg d z₀) = Ws d) :
    ((Ws d).subgroupOf (img d (Jg d))).comap (jpHom d) = (Wg d z₀).subgroupOf (Jp d) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Wg_eq_pre hz hWimg]
  constructor
  · intro h
    exact (mem_preIn_iff d.s56V _).2 ⟨((mem_preIn_iff d.s56V _).1 g.2).1, h⟩
  · intro h
    exact ((mem_preIn_iff d.s56V _).1 h).2

theorem jp_quot_equiv_symm (hz : d.S56Z0 z₀) (hWimg : img d (Wg d z₀) = Ws d)
    [hN : ((Ws d).subgroupOf (img d (Jg d))).Normal]
    [N' : ((Wg d z₀).subgroupOf (Jp d)).Normal] (A : Type*) [Group A]
    (e : ↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* A) :
    Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃* A) := by
  obtain ⟨e'⟩ := nonempty_quotEquiv_comap (jpHom d) jpHom_surjective
    ((Ws d).subgroupOf (img d (Jg d)))
  exact ⟨e'.symm.trans ((QuotientGroup.quotientMulEquivOfEq (jp_comap_eq hz hWimg)).trans e)⟩

theorem node23c_a (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv)
    (hcard : Nat.card d.s56V = 2 ^ 10)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    {h₀ : G} (hh₀ : h₀ ∈ Hg d) (hh : star d (h₀ * d.t * h₀⁻¹) = star d (d.t * d.pv 2))
    (hWimg : img d (Wg d z₀) = Ws d)
    (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hWel : IsElemAbelian 2 (Ws d)) (hWJ : Ws d ≤ img d (Jg d))
    [hN : ((Ws d).subgroupOf (img d (Jg d))).Normal]
    [N' : ((Wg d z₀).subgroupOf (Jp d)).Normal]
    (e : ↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6))
    (cent : A6CentStmt) {o : G} (ho : o ∈ Hg d)
    (hoj : ∀ j ∈ Jp d, o * j * o⁻¹ * j⁻¹ ∈ Kz d z₀) : o ∈ Kz d z₀ := by
  have M := mdata_d h49 hd hz hinv hcard hh₀ hh
  haveI hWbN : ((Ws d).subgroupOf (Hs d)).Normal := Wb_normal hWnorm
  have hW2 : ∀ w ∈ (Ws d).subgroupOf (Hs d), w * w = 1 := by
    intro w hw
    have := hWel.2 (w : MulAut ↥d.s56V) (Subgroup.mem_subgroupOf.1 hw)
    exact Subtype.ext (by simpa [pow_two] using this)
  have hWJb := Wb_le_Jb h49 hd hWJ
  obtain ⟨eq⟩ := jp_quot_equiv_symm hz hWimg _ e
  obtain ⟨eb⟩ := jb_quot_equiv h49 hd hWJ _ eq
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs := eb.isSimpleGroup
  have hWtriv : ∀ w ∈ (Ws d).subgroupOf (Hs d), quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) w = 1 :=
    normal_exponent_two_acts_trivially _ M.card
      (fun U hU => M.irreducible (hB := map_Zv_eq hZH) U hU) _ hW2
  obtain ⟨er⟩ := M.range_equiv (hB := map_Zv_eq hZH) _ hWtriv hWJb _ hs eb
  have hcent := cent _ M.hypM ⟨er⟩
  have hg : quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) (starB d o ho) ∈
      centralizer (((normalClosure ({xB h49 hd} : Set ↥(Hs d))).map
        (quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH)) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨j, hj, hjH, rfl⟩ := exists_lift_Jb h49 hd hσ
    have h1 := quotRep_starB_eq_one_of_mem_Kz hZH (hoj j hj)
    have hmul : starB d (o * j * o⁻¹ * j⁻¹) (Kz_le_Hg (hoj j hj)) =
        starB d o ho * starB d j hjH * (starB d o ho)⁻¹ * (starB d j hjH)⁻¹ := by
      rw [starB_eq_starHom, starB_eq_starHom, starB_eq_starHom, ← map_inv, ← map_mul, ← map_mul,
        ← map_inv, ← map_mul]
      rfl
    rw [hmul] at h1
    simp only [map_mul, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  have hg1 : quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) (starB d o ho) ∈
      (⊥ : Subgroup (Additive (↥d.s56V ⧸ Zv d z₀) ≃ₗ[ZMod 2] Additive (↥d.s56V ⧸ Zv d z₀))) := by
    rw [← hcent]
    exact hg
  exact mem_Kz_of_quotRep_eq_one hZH ho (Subgroup.mem_bot.1 hg1)

theorem node23c_b (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv)
    (hcard : Nat.card d.s56V = 2 ^ 10)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    {h₀ : G} (hh₀ : h₀ ∈ Hg d) (hh : star d (h₀ * d.t * h₀⁻¹) = star d (d.t * d.pv 2))
    (hWimg : img d (Wg d z₀) = Ws d)
    (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hWel : IsElemAbelian 2 (Ws d)) (hWJ : Ws d ≤ img d (Jg d))
    [hN : ((Ws d).subgroupOf (img d (Jg d))).Normal]
    (hcases : Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃*
        Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))
    (r3 : RankThreeStmt) {s : G} (hs : s ∈ Hg d) (hss : s * s = 1)
    (hrk : rk (quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) (starB d s hs)) = 3) :
    (∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6))) ∧
    s ∉ Jp d ⊔ Kz d z₀ ∧
    ∃ V₁ : Subgroup G, Zz d z₀ ≤ V₁ ∧ V₁ ≤ d.s56V ∧ IsElemAbQuot V₁ (Zz d z₀) 4 ∧
      (∀ j ∈ Jp d, ∀ v ∈ V₁, j * v * j⁻¹ ∈ V₁) ∧
      V₁ ⊔ V₁.map (MulAut.conj d.t).toMonoidHom = d.s56V ∧
      V₁ ⊓ V₁.map (MulAut.conj d.t).toMonoidHom = Zz d z₀ ∧ ∀ v ∈ V₁, s * v * s⁻¹ ∈ V₁ := by
  have hcom : ∀ a b : ↥d.s56V, a * b = b * a := Fact.out
  have hsq : ∀ a : ↥d.s56V, a * a = 1 := Fact.out
  have hcG : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcom ⟨a, ha⟩ ⟨b, hb⟩)
  have hsG : ∀ a ∈ d.s56V, a * a = 1 := fun a ha => congrArg Subtype.val (hsq ⟨a, ha⟩)
  have M := mdata_d h49 hd hz hinv hcard hh₀ hh
  haveI hWbN : ((Ws d).subgroupOf (Hs d)).Normal := Wb_normal hWnorm
  have hW2 : ∀ w ∈ (Ws d).subgroupOf (Hs d), w * w = 1 := by
    intro w hw
    have := hWel.2 (w : MulAut ↥d.s56V) (Subgroup.mem_subgroupOf.1 hw)
    exact Subtype.ext (by simpa [pow_two] using this)
  have hWJb := Wb_le_Jb h49 hd hWJ
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  set ρ := quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) with hρ
  have hWtriv : ∀ w ∈ (Ws d).subgroupOf (Hs d), ρ w = 1 :=
    normal_exponent_two_acts_trivially _ M.card
      (fun U hU => M.irreducible (hB := map_Zv_eq hZH) U hU) _ hW2
  have hss' : starB d s hs * starB d s hs = 1 := Subtype.ext (by
    show star d s * star d s = 1
    rw [star, ← actFun_mul d.s56V hs hs, hss, actFun_one])
  have hs2 : ρ (starB d s hs) * ρ (starB d s hs) = 1 := by rw [← map_mul, hss', map_one]
  have hA6 : Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃*
      alternatingGroup (Fin 6)) := by
    rcases hcases with h | ⟨⟨e⟩⟩
    · exact h
    · exfalso
      obtain ⟨eb⟩ := jb_quot_equiv h49 hd hWJ _ e
      have hab := jbar_comm ρ (normalClosure ({xB h49 hd} : Set ↥(Hs d))) _ hWtriv eb
      obtain ⟨⟨eA⟩, -⟩ := r3 ρ M.hypM (Or.inr hab) hs2 hrk
      refine not_comm_A6 fun a b => ?_
      have h2 : eA.symm a * eA.symm b = eA.symm b * eA.symm a :=
        Subtype.ext (hab _ (eA.symm a).2 _ (eA.symm b).2)
      apply eA.symm.injective
      rw [map_mul, map_mul, h2]
  obtain ⟨e⟩ := hA6
  obtain ⟨eb⟩ := jb_quot_equiv h49 hd hWJ _ e
  have hs' := eb.isSimpleGroup
  obtain ⟨er⟩ := M.range_equiv (hB := map_Zv_eq hZH) _ hWtriv hWJb _ hs' eb
  obtain ⟨-, hnot, V₁, hdim, hst, hcompl, hsV⟩ := r3 ρ M.hypM (Or.inl ⟨er⟩) hs2 hrk
  have hZv := Zv_map h49 hd hz
  have htH := t_mem_H h49 hd
  set Lv := liftAdd (Zv d z₀) V₁.toAddSubgroup with hLv
  have hconj : (Lv.map d.s56V.subtype).map (MulAut.conj d.t).toMonoidHom =
      (liftAdd (Zv d z₀) (V₁.map (ρ (starB d d.t htH) :
        Additive (↥d.s56V ⧸ Zv d z₀) →ₗ[ZMod 2] Additive (↥d.s56V ⧸ Zv d z₀))).toAddSubgroup).map
        d.s56V.subtype := by
    rw [liftAdd_map_quotRep, conj_transfer htH]
  have hnot' : s ∉ Jp d ⊔ Kz d z₀ := by
    intro hmem
    let ψ : ↥(Hg d) →* (Additive (↥d.s56V ⧸ Zv d z₀) ≃ₗ[ZMod 2] Additive (↥d.s56V ⧸ Zv d z₀)) :=
      ρ.comp (starHom d)
    let T : Subgroup G :=
      (((normalClosure ({xB h49 hd} : Set ↥(Hs d))).map ρ).comap ψ).map (Hg d).subtype
    have h1 : Jp d ≤ T := by
      intro j hj
      have hjH : j ∈ Hg d := ((mem_preIn_iff d.s56V _).1 hj).1
      refine ⟨⟨j, hjH⟩, ?_, rfl⟩
      show ρ (starHom d ⟨j, hjH⟩) ∈ (normalClosure ({xB h49 hd} : Set ↥(Hs d))).map ρ
      rw [← starB_eq_starHom]
      exact Subgroup.mem_map_of_mem _ (starB_mem_Jb h49 hd hj)
    have h2 : Kz d z₀ ≤ T := by
      intro c hc
      refine ⟨⟨c, Kz_le_Hg hc⟩, ?_, rfl⟩
      show ρ (starHom d ⟨c, Kz_le_Hg hc⟩) ∈ (normalClosure ({xB h49 hd} : Set ↥(Hs d))).map ρ
      rw [← starB_eq_starHom, quotRep_starB_eq_one_of_mem_Kz hZH hc]
      exact one_mem _
    obtain ⟨⟨s', hs'⟩, hs'T, hs'eq⟩ := sup_le h1 h2 hmem
    have hss' : s' = s := hs'eq
    subst hss'
    apply hnot
    rw [starB_eq_starHom hs]
    exact hs'T
  refine ⟨jp_quot_equiv hz hWimg _ e, hnot', Lv.map d.s56V.subtype, ?_, Subgroup.map_subtype_le _, ?_,
    inv_transfer h49 hd (fun σ hσ v hv => ?_), ?_, ?_, ?_⟩
  · rw [← hZv]; exact Subgroup.map_mono (le_liftAdd _ _)
  · have := isElemAbQuot_map d.s56V hcG hsG (le_liftAdd (Zv d z₀) V₁.toAddSubgroup)
      (n := 4) (by rw [relIndex_liftAdd, card_toAddSubgroup_eq V₁ hdim])
    rwa [hZv] at this
  · show cls (Zv d z₀) ((σ : MulAut ↥d.s56V) v) ∈ V₁.toAddSubgroup
    rw [← quotRep_cls]
    exact hst (ρ σ) (Subgroup.mem_map_of_mem _ hσ) _ hv
  · rw [hconj, ← Subgroup.map_sup, ← liftAdd_sup, ← toAddSubgroup_sup, hcompl.sup_eq_top,
      Submodule.top_toAddSubgroup, liftAdd_top, Subgroup.map_top, Subgroup.range_subtype]
  · rw [hconj, ← Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _), ← liftAdd_inf,
      ← toAddSubgroup_inf, hcompl.inf_eq_bot, Submodule.bot_toAddSubgroup, liftAdd_bot, hZv]
  · rintro _ ⟨u, hu, rfl⟩
    have h1 : ρ (starB d s hs) (cls (Zv d z₀) u) ∈ V₁ := by
      have : ρ (starB d s hs) (cls (Zv d z₀) u) ∈
          V₁.map (ρ (starB d s hs) : Additive (↥d.s56V ⧸ Zv d z₀) →ₗ[ZMod 2]
            Additive (↥d.s56V ⧸ Zv d z₀)) := Submodule.mem_map_of_mem hu
      rwa [hsV] at this
    refine ⟨_, ?_, star_apply_val hs u⟩
    show cls (Zv d z₀) ((starB d s hs : MulAut ↥d.s56V) u) ∈ V₁.toAddSubgroup
    rw [← quotRep_cls]
    exact h1

end Kzsec




section Assembly23c

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem node23c_of_cores (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) (h14 : Node14 d) (_h17s : Node17s d z₀) (_h17 : Node17 d z₀)
    (h19 : Node19 d z₀) (_h20 : Node20 d z₀) (_h21 : Node21 d z₀) (h23a : Node23a d z₀)
    (_h23b : Node23b d z₀) (cent : A6CentStmt) (r3 : RankThreeStmt) : Node23c d z₀ := by
  obtain ⟨-, hVel, hcard, -⟩ := h10
  obtain ⟨-, -, -, hconj⟩ := h14
  obtain ⟨-, -, -, -, hWimg, -, hWel, -⟩ := h19
  obtain ⟨-, ⟨hWnorm, -⟩, ⟨-, hZH⟩, -, -, hWJ, hN, hcases⟩ := h23a
  have hc : ∀ a b : ↥d.s56V, a * b = b * a := fun a b => hVel.1.is_comm.comm a b
  have hs : ∀ a : ↥d.s56V, a * a = 1 := fun a => by
    have := hVel.2 a a.2
    exact Subtype.ext (by simpa [pow_two] using this)
  have hinv : d.S56Z0Inv := fun z0 hz0 => by
    have := hVel.2 z0 hz0.mem_V
    simpa [pow_two] using this
  haveI : Fact (∀ a b : ↥d.s56V, a * b = b * a) := ⟨hc⟩
  haveI : Fact (∀ a : ↥d.s56V, a * a = 1) := ⟨hs⟩
  haveI := hN
  obtain ⟨h₀, hh₀, hh⟩ := hconj
  refine ⟨fun ⟨N', ⟨e⟩⟩ o ho hoj => ?_, fun s' hs' hss hr => ?_⟩
  · haveI := N'
    exact node23c_a h49 hd hz hinv hcard hZH hh₀ hh hWimg hWnorm hWel hWJ e cent ho hoj
  · exact node23c_b h49 hd hz hinv hcard hZH hh₀ hh hWimg hWnorm hWel hWJ hcases r3 hs' hss
      (rk_quotRep_eq_three (Z_le_V h49 hd hz) hZH hs' hss hr)

end Assembly23c


end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
