module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Reduce
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Prod
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Swap

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

theorem odd_of_forall_sq_eq_one {H : Type*} [Group H] [Finite H]
    (h : ∀ x : H, x * x = 1 → x = 1) : Odd (Nat.card H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have hev : 2 ∣ Nat.card H := by
    rcases Nat.even_or_odd (Nat.card H) with h' | h'
    · exact even_iff_two_dvd.1 h'
    · exact absurd h' hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 hev
  have hsq : z * z = 1 := by
    rw [← pow_two, ← hz]
    exact pow_orderOf_eq_one z
  have := h z hsq
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

section ProdSetup

variable {B : Type} [Group B] [Finite B] {e t : B} {J₀ E₂ : Subgroup B} [(zpowers e).Normal]

structure ProdData (e t : B) (J₀ : Subgroup B) [(zpowers e).Normal]
    (D₁ D₂ : Subgroup (Xq e)) : Prop where
  simple₁ : IsSimpleGroup D₁
  nonab₁ : ∃ x y : D₁, x * y ≠ y * x
  simple₂ : IsSimpleGroup D₂
  nonab₂ : ∃ x y : D₂, x * y ≠ y * x
  sup : D₁ ⊔ D₂ = Dq e J₀
  inf : D₁ ⊓ D₂ = ⊥
  comm : ⁅D₁, D₂⁆ = ⊥
  conj : D₁.map (MulAut.conj (π₂q e t)⁻¹).toMonoidHom = D₂
  J_eq : (J₀.map (π₁q e)).map (θq e) = Dq e J₀ ⊓ centralizer ({π₂q e t} : Set (Xq e))

noncomputable abbrev fK (e : B) (J₀ : Subgroup B) [(zpowers e).Normal] : ↥(Kt J₀) →* Xq e :=
  (π₂q e).comp (Kt J₀).subtype

theorem fK_range (hL : LayerOut e t J₀) : (fK e J₀).range = Dq e J₀ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [← map_Kt_π₂ hL]
    exact ⟨x, x.2, rfl⟩
  · intro hy
    rw [← map_Kt_π₂ hL] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩

theorem fK_ker_le_center (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀) :
    (fK e J₀).ker ≤ center ↥(Kt J₀) := by
  intro x hx
  have h1 : π₂q e x = 1 := MonoidHom.mem_ker.1 hx
  have hmem : (x : B) ∈ (center ↥(Kt J₀)).map (Kt J₀).subtype := by
    rw [center_Kt_eq h hL]
    exact mem_inf.2 ⟨x.2, h1⟩
  exact (Subgroup.mem_map_iff_mem (Kt J₀).subtype_injective).1 hmem

end ProdSetup

section ProdMain

variable {B : Type} [Group B] [Finite B] {e t : B} {J₀ E₂ : Subgroup B} [(zpowers e).Normal]
  {D₁ D₂ : Subgroup (Xq e)}

noncomputable abbrev Pf (e : B) (J₀ : Subgroup B) [(zpowers e).Normal] (D' : Subgroup (Xq e)) :
    Subgroup ↥(Kt J₀) :=
  ⁅D'.comap (fK e J₀), D'.comap (fK e J₀)⁆

theorem perfect_of_simple_nonab {G : Type*} [Group G] [IsSimpleGroup G]
    (hn : ∃ x y : G, x * y ≠ y * x) : Group.IsPerfect G :=
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hn).1.1

theorem prod_factors (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)
    (hp : ProdData e t J₀ D₁ D₂) :
    (Pf e J₀ D₁).Normal ∧ (Pf e J₀ D₂).Normal ∧ ⁅Pf e J₀ D₁, Pf e J₀ D₂⁆ = ⊥ ∧
      Pf e J₀ D₁ ⊔ Pf e J₀ D₂ = ⊤ ∧ (Pf e J₀ D₁).map (fK e J₀) = D₁ ∧
      (Pf e J₀ D₂).map (fK e J₀) = D₂ ∧ Group.IsPerfect ↥(Pf e J₀ D₁) ∧
      Group.IsPerfect ↥(Pf e J₀ D₂) := by
  haveI := hp.simple₁
  haveI := hp.simple₂
  exact exists_perfect_factors (P := ↥(Kt J₀)) (X := Xq e)
    (Subgroup.isPerfect_iff.2 h.perfect_Kt) (fK e J₀) (fK_ker_le_center h hL) D₁ D₂
    (hp.sup.trans (fK_range hL).symm) hp.comm (perfect_of_simple_nonab hp.nonab₁)
    (perfect_of_simple_nonab hp.nonab₂)

noncomputable def fP (hmap : (Pf e J₀ D₁).map (fK e J₀) = D₁) :
    ↥(Pf e J₀ D₁) →* ↥D₁ :=
  ((fK e J₀).comp (Pf e J₀ D₁).subtype).codRestrict D₁ (fun x => by
    have hx : fK e J₀ (x : ↥(Kt J₀)) ∈ (Pf e J₀ D₁).map (fK e J₀) := ⟨x, x.2, rfl⟩
    rw [hmap] at hx
    exact hx)

theorem fP_surjective (hmap : (Pf e J₀ D₁).map (fK e J₀) = D₁) :
    Function.Surjective (fP hmap) := by
  intro y
  have hy : (y : Xq e) ∈ (Pf e J₀ D₁).map (fK e J₀) := by rw [hmap]; exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem fP_ker_le_center (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)
    (hmap : (Pf e J₀ D₁).map (fK e J₀) = D₁) : (fP hmap).ker ≤ center ↥(Pf e J₀ D₁) := by
  intro x hx
  have h1 : fK e J₀ (x : ↥(Kt J₀)) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have hc : (x : ↥(Kt J₀)) ∈ center ↥(Kt J₀) := fK_ker_le_center h hL (MonoidHom.mem_ker.2 h1)
  rw [mem_center_iff]
  intro y
  exact Subtype.ext ((mem_center_iff.1 hc (y : ↥(Kt J₀))))

theorem fP_injective_of_center_bot (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)
    (hmap : (Pf e J₀ D₁).map (fK e J₀) = D₁) (hz : center ↥(Pf e J₀ D₁) = ⊥) :
    Function.Injective (fP hmap) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have := fP_ker_le_center h hL hmap (MonoidHom.mem_ker.2 hx)
  rw [hz, mem_bot] at this
  exact this

theorem Pf_center_eq_bot (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀) [IsSimpleGroup D₁]
    (hnab : ∃ x y : D₁, x * y ≠ y * x) (hmap : (Pf e J₀ D₁).map (fK e J₀) = D₁)
    (hperf : Group.IsPerfect ↥(Pf e J₀ D₁))
    (hlie : CFSG.Blueprint.LieModel ↥D₁ .PSU 4 2 1) : center ↥(Pf e J₀ D₁) = ⊥ := by
  have hsurj := fP_surjective hmap
  have hker := fP_ker_le_center h hL hmap
  have key := CFSG.LocalCores.comap_center_eq_of_perfect hperf (fP hmap) hsurj hker
  have hcD : center ↥D₁ = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have hc : center ↥(Pf e J₀ D₁) = (fP hmap).ker := by
    rw [← key, hcD]
    exact MonoidHom.comap_bot _
  let eq1 : ↥(Pf e J₀ D₁) ⧸ center ↥(Pf e J₀ D₁) ≃* ↥D₁ :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective (fP hmap) hsurj)
  have hodd : Odd (Nat.card (center ↥(Pf e J₀ D₁))) := by
    apply odd_of_forall_sq_eq_one
    intro x hx
    have hxk : (x : ↥(Pf e J₀ D₁)) ∈ (fP hmap).ker := by
      rw [← hc]
      exact x.2
    have h1 : fK e J₀ ((x : ↥(Pf e J₀ D₁)) : ↥(Kt J₀)) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hxk)
    have hy : ((x : ↥(Pf e J₀ D₁)) : ↥(Kt J₀)) ∈ center ↥(Kt J₀) :=
      fK_ker_le_center h hL (MonoidHom.mem_ker.2 h1)
    have hsq : (⟨((x : ↥(Pf e J₀ D₁)) : ↥(Kt J₀)), hy⟩ : ↥(center ↥(Kt J₀))) *
        ⟨((x : ↥(Pf e J₀ D₁)) : ↥(Kt J₀)), hy⟩ = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : ↥(center ↥(Pf e J₀ D₁)) =>
        (((z : ↥(Pf e J₀ D₁)) : ↥(Kt J₀)) : ↥(Kt J₀))) hx
    have := eq_one_of_sq_eq_one_of_odd (odd_card_center_Kt h hL) hsq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(center ↥(Kt J₀)) => (z : ↥(Kt J₀))) this
  exact center_eq_bot_of_psu_four_two hGA hperf eq1 hlie hodd

theorem center_Kt_eq_bot_of_prod (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)
    (hp : ProdData e t J₀ D₁ D₂) (hz₁ : center ↥(Pf e J₀ D₁) = ⊥)
    (hz₂ : center ↥(Pf e J₀ D₂) = ⊥) : center ↥(Kt J₀) = ⊥ := by
  obtain ⟨hN₁, hN₂, hcomm, hsup, hmap₁, hmap₂, hperf₁, hperf₂⟩ := prod_factors h hL hp
  rw [eq_bot_iff]
  intro x hx
  have hxker : fK e J₀ x = 1 := by
    have : x ∈ (gKt hL).ker := by rw [ker_gKt h hL]; exact hx
    exact congrArg Subtype.val (MonoidHom.mem_ker.1 this)
  have hxs : x ∈ Pf e J₀ D₁ ⊔ Pf e J₀ D₂ := by rw [hsup]; exact mem_top x
  haveI := hN₂
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hxs
  have hfK₁ : fK e J₀ p₁ ∈ D₁ := by
    have hm : fK e J₀ p₁ ∈ (Pf e J₀ D₁).map (fK e J₀) := ⟨p₁, hp₁, rfl⟩
    rw [hmap₁] at hm
    exact hm
  have hfK₂ : fK e J₀ p₂ ∈ D₂ := by
    have hm : fK e J₀ p₂ ∈ (Pf e J₀ D₂).map (fK e J₀) := ⟨p₂, hp₂, rfl⟩
    rw [hmap₂] at hm
    exact hm
  have hmul : fK e J₀ p₁ * fK e J₀ p₂ = 1 := by rw [← map_mul]; exact hxker
  have hinv : fK e J₀ p₁ = (fK e J₀ p₂)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hmemD : fK e J₀ p₁ ∈ D₁ ⊓ D₂ := mem_inf.2 ⟨hfK₁, by rw [hinv]; exact inv_mem hfK₂⟩
  rw [hp.inf, mem_bot] at hmemD
  have hmemD₂ : fK e J₀ p₂ = 1 := by
    rw [hmemD, one_mul] at hmul
    exact hmul
  have h1 : (⟨p₁, hp₁⟩ : ↥(Pf e J₀ D₁)) = 1 := by
    have h' : (⟨p₁, hp₁⟩ : ↥(Pf e J₀ D₁)) ∈ (fP hmap₁).ker :=
      MonoidHom.mem_ker.2 (Subtype.ext hmemD)
    have h'' := fP_ker_le_center h hL hmap₁ h'
    rw [hz₁, mem_bot] at h''
    exact h''
  have h2 : (⟨p₂, hp₂⟩ : ↥(Pf e J₀ D₂)) = 1 := by
    have h' : (⟨p₂, hp₂⟩ : ↥(Pf e J₀ D₂)) ∈ (fP hmap₂).ker :=
      MonoidHom.mem_ker.2 (Subtype.ext hmemD₂)
    have h'' := fP_ker_le_center h hL hmap₂ h'
    rw [hz₂, mem_bot] at h''
    exact h''
  have e1 : p₁ = 1 := congrArg Subtype.val h1
  have e2 : p₂ = 1 := congrArg Subtype.val h2
  rw [e1, e2, mul_one]
  exact one_mem _

theorem mem_D₂_iff (h : GomiU42Setup B e t J₀ E₂) (hp : ProdData e t J₀ D₁ D₂) (y : Xq e) :
    y ∈ D₂ ↔ ∃ d ∈ D₁, π₂q e t * d * π₂q e t = y := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have ha : (π₂q e t)⁻¹ = π₂q e t := by rw [← map_inv, ht]
  have hconj : ∀ d : Xq e, (MulAut.conj (π₂q e t)⁻¹).toMonoidHom d =
      π₂q e t * d * π₂q e t := by
    intro d
    show (π₂q e t)⁻¹ * d * ((π₂q e t)⁻¹)⁻¹ = _
    rw [inv_inv, ha]
  rw [← hp.conj]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, (hconj d).symm⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, hconj d⟩

theorem map_conj_comap (h : GomiU42Setup B e t J₀ E₂) (hp : ProdData e t J₀ D₁ D₂) :
    ((D₁.comap (fK e J₀)).map (Kt J₀).subtype).map (MulAut.conj t).toMonoidHom =
      (D₂.comap (fK e J₀)).map (Kt J₀).subtype := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hN : (Kt J₀).Normal := normalClosure_normal
  have haa : π₂q e t * π₂q e t = 1 := by rw [← map_mul, h.t_sq, map_one]
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hmem : t * (x : B) * t ∈ Kt J₀ := by
      have := hN.conj_mem (x : B) x.2 t
      rwa [ht] at this
    refine ⟨⟨t * (x : B) * t, hmem⟩, ?_, ?_⟩
    · show π₂q e (t * (x : B) * t) ∈ D₂
      rw [mem_D₂_iff h hp]
      refine ⟨π₂q e (x : B), hx, ?_⟩
      rw [map_mul, map_mul]
    · simp [MulAut.conj_apply, ht]
  · rintro ⟨z, hz, rfl⟩
    have hz' : π₂q e (z : B) ∈ D₂ := hz
    rw [mem_D₂_iff h hp] at hz'
    obtain ⟨d, hd, hdz⟩ := hz'
    have hmem : t * (z : B) * t ∈ Kt J₀ := by
      have := hN.conj_mem (z : B) z.2 t
      rwa [ht] at this
    refine ⟨t * (z : B) * t, ⟨⟨t * (z : B) * t, hmem⟩, ?_, rfl⟩, ?_⟩
    · show π₂q e (t * (z : B) * t) ∈ D₁
      have : π₂q e (t * (z : B) * t) = d := by
        rw [map_mul, map_mul, ← hdz]
        calc π₂q e t * (π₂q e t * d * π₂q e t) * π₂q e t
            = (π₂q e t * π₂q e t) * d * (π₂q e t * π₂q e t) := by group
          _ = d := by rw [haa]; group
      rw [this]
      exact hd
    · show t * (t * (z : B) * t) * t⁻¹ = (z : B)
      rw [ht]
      calc t * (t * (z : B) * t) * t = (t * t) * (z : B) * (t * t) := by group
        _ = z := by rw [h.t_sq]; group

theorem swap_Pf (h : GomiU42Setup B e t J₀ E₂) (hp : ProdData e t J₀ D₁ D₂) :
    ((Pf e J₀ D₁).map (Kt J₀).subtype).map (MulAut.conj t).toMonoidHom =
      (Pf e J₀ D₂).map (Kt J₀).subtype := by
  simp only [Pf, Subgroup.map_commutator]
  rw [map_conj_comap h hp]

theorem isQuasisimple_of_equiv_simple {A D : Type} [Group A] [Group D] [IsSimpleGroup D]
    (e : A ≃* D) (hnab : ∃ x y : D, x * y ≠ y * x) : CFSG.IsQuasisimple A := by
  haveI : IsSimpleGroup A := e.isSimpleGroup
  have hnabA : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    refine ⟨e.symm x, e.symm y, fun h' => hxy ?_⟩
    have h'' := congrArg e h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h''
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabA).1

theorem layer_eq_of_factors (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)
    {P₁ P₂ : Subgroup ↥(Kt J₀)} (hN₁ : P₁.Normal) (hN₂ : P₂.Normal) (hsup : P₁ ⊔ P₂ = ⊤)
    (hq₁ : CFSG.IsQuasisimple ↥(P₁.map (Kt J₀).subtype))
    (hq₂ : CFSG.IsQuasisimple ↥(P₂.map (Kt J₀).subtype)) : CFSG.layer B = Kt J₀ := by
  apply le_antisymm (layer_le_Kt h hL)
  have hsubK : (Kt J₀).IsSubnormal := (inferInstance : (Kt J₀).Normal).isSubnormal
  have h1 : P₁.map (Kt J₀).subtype ≤ CFSG.layer B := by
    rw [CFSG.layer.eq_sSup B]
    exact le_sSup ⟨hq₁, Subgroup.IsSubnormal.trans' hN₁.isSubnormal hsubK⟩
  have h2 : P₂.map (Kt J₀).subtype ≤ CFSG.layer B := by
    rw [CFSG.layer.eq_sSup B]
    exact le_sSup ⟨hq₂, Subgroup.IsSubnormal.trans' hN₂.isSubnormal hsubK⟩
  have hK : Kt J₀ = P₁.map (Kt J₀).subtype ⊔ P₂.map (Kt J₀).subtype := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  rw [hK]
  exact sup_le h1 h2

theorem fK_mem_of_mem_Pf {D' : Subgroup (Xq e)} (hmap : (Pf e J₀ D').map (fK e J₀) = D')
    {p : ↥(Kt J₀)} (hp : p ∈ Pf e J₀ D') : fK e J₀ p ∈ D' := by
  have hm : fK e J₀ p ∈ (Pf e J₀ D').map (fK e J₀) := ⟨p, hp, rfl⟩
  rw [hmap] at hm
  exact hm

noncomputable def equivD₂ (hp : ProdData e t J₀ D₁ D₂) : ↥D₂ ≃* ↥D₁ :=
  ((Subgroup.equivMapOfInjective D₁ (MulAut.conj (π₂q e t)⁻¹).toMonoidHom
    (MulAut.conj (π₂q e t)⁻¹).injective).trans (MulEquiv.subgroupCongr hp.conj)).symm

theorem GomiU42Setup.product_branch (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀) (hp : ProdData e t J₀ D₁ D₂)
    (eD : ↥D₁ ≃* ↥((J₀.map (π₁q e)).map (θq e))) :
    CFSG.layer B ⊓ centralizer ({t} : Set B) = J₀ ∧
      ∃ K₀ : Subgroup B, CFSG.Blueprint.LieModel ↥K₀ .PSU 4 2 1 ∧
        CFSG.layer B = K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom ∧
        ⁅K₀, K₀.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
        K₀ ⊓ K₀.map (MulAut.conj t).toMonoidHom = ⊥ := by
  haveI := hp.simple₁
  haveI := hp.simple₂
  obtain ⟨hN₁, hN₂, hcomm, hsup, hmap₁, hmap₂, hperf₁, hperf₂⟩ := prod_factors h hL hp
  have hlie₁ : CFSG.Blueprint.LieModel ↥D₁ .PSU 4 2 1 :=
    lieModel_of_mulEquiv_classical eD (by decide) (lieModel_Jx h hL)
  have hlie₂ : CFSG.Blueprint.LieModel ↥D₂ .PSU 4 2 1 :=
    lieModel_of_mulEquiv_classical (equivD₂ hp) (by decide) hlie₁
  have hz₁ := Pf_center_eq_bot hGA h hL hp.nonab₁ hmap₁ hperf₁ hlie₁
  have hz₂ := Pf_center_eq_bot hGA h hL hp.nonab₂ hmap₂ hperf₂ hlie₂
  have hz := center_Kt_eq_bot_of_prod h hL hp hz₁ hz₂
  let ePD₁ : ↥(Pf e J₀ D₁) ≃* ↥D₁ := MulEquiv.ofBijective (fP hmap₁)
    ⟨fP_injective_of_center_bot h hL hmap₁ hz₁, fP_surjective hmap₁⟩
  let ePD₂ : ↥(Pf e J₀ D₂) ≃* ↥D₂ := MulEquiv.ofBijective (fP hmap₂)
    ⟨fP_injective_of_center_bot h hL hmap₂ hz₂, fP_surjective hmap₂⟩
  let eK₁ : ↥((Pf e J₀ D₁).map (Kt J₀).subtype) ≃* ↥D₁ :=
    ((Pf e J₀ D₁).equivMapOfInjective (Kt J₀).subtype (Kt J₀).subtype_injective).symm.trans ePD₁
  let eK₂ : ↥((Pf e J₀ D₂).map (Kt J₀).subtype) ≃* ↥D₂ :=
    ((Pf e J₀ D₂).equivMapOfInjective (Kt J₀).subtype (Kt J₀).subtype_injective).symm.trans ePD₂
  have hq₁ := isQuasisimple_of_equiv_simple eK₁ hp.nonab₁
  have hq₂ := isQuasisimple_of_equiv_simple eK₂ hp.nonab₂
  have hlayer : CFSG.layer B = Kt J₀ := layer_eq_of_factors h hL hN₁ hN₂ hsup hq₁ hq₂
  have hDJ : Dq e J₀ ⊓ centralizer ({π₂q e t} : Set (Xq e)) =
      (J₀.map (π₁q e)).map (θq e) := hp.J_eq.symm
  have hinf := Kt_inf_centralizer h hL hz hDJ
  refine ⟨by rw [hlayer]; exact hinf, (Pf e J₀ D₁).map (Kt J₀).subtype, ?_, ?_, ?_, ?_⟩
  · exact lieModel_of_mulEquiv_classical eK₁ (by decide) hlie₁
  · rw [hlayer, swap_Pf h hp, ← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  · rw [swap_Pf h hp, ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
  · rw [swap_Pf h hp, eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    obtain ⟨p₁, hp₁, rfl⟩ := hx1
    obtain ⟨p₂, hp₂, hp₂x⟩ := hx2
    have hpp : p₂ = p₁ := Subtype.ext hp₂x
    subst hpp
    have hf₁ := fK_mem_of_mem_Pf hmap₁ hp₁
    have hf₂ := fK_mem_of_mem_Pf hmap₂ hp₂
    have hmem : fK e J₀ p₂ ∈ D₁ ⊓ D₂ := mem_inf.2 ⟨hf₁, hf₂⟩
    rw [hp.inf, mem_bot] at hmem
    have h1 : (⟨p₂, hp₁⟩ : ↥(Pf e J₀ D₁)) = 1 := by
      have h' : (⟨p₂, hp₁⟩ : ↥(Pf e J₀ D₁)) ∈ (fP hmap₁).ker :=
        MonoidHom.mem_ker.2 (Subtype.ext hmem)
      have h'' := fP_ker_le_center h hL hmap₁ h'
      rw [hz₁, mem_bot] at h''
      exact h''
    have : p₂ = 1 := congrArg Subtype.val h1
    rw [this]
    exact one_mem _

theorem GomiU42Setup.reduction (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : GomiU42Selector fun _ _ => True) (h : GomiU42Setup B e t J₀ E₂) :
    CFSG.layer B ⊓ centralizer ({t} : Set B) = J₀ ∧
      (CFSG.Blueprint.LieModel ↥(CFSG.layer B) .PSL 4 2 2 ∨
        ∃ K₀ : Subgroup B, CFSG.Blueprint.LieModel ↥K₀ .PSU 4 2 1 ∧
          CFSG.layer B = K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom ∧
          ⁅K₀, K₀.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
          K₀ ⊓ K₀.map (MulAut.conj t).toMonoidHom = ⊥) := by
  have hL := h.layerOut
  obtain ⟨-, -, -, -, hcent, halt, -⟩ := hL.conclusion
  rcases halt with ⟨⟨hsimple, hnab, hlt, -⟩, -⟩ | ⟨⟨D₁, D₂, -, -, -, hs₁, hn₁, hs₂, hn₂, hsup, hinf,
      hcomm, hconj, hJ, -⟩, -⟩
  · obtain ⟨h1, h2⟩ := h.simple_branch hL hGA hS hsimple hnab hlt hcent
    exact ⟨h1, Or.inl h2⟩
  · have hp : ProdData e t J₀ D₁ D₂ :=
      { simple₁ := hs₁, nonab₁ := hn₁, simple₂ := hs₂, nonab₂ := hn₂, sup := hsup, inf := hinf,
        comm := hcomm, conj := hconj, J_eq := hJ }
    have ha : π₂q e t * π₂q e t = 1 := by rw [← map_mul, h.t_sq, map_one]
    obtain ⟨φ, -⟩ := exists_mulEquiv_inf_centralizer ha hcomm hinf hconj
    have hEq : (D₁ ⊔ D₂) ⊓ centralizer ({π₂q e t} : Set (Xq e)) =
        (J₀.map (π₁q e)).map (θq e) := by
      rw [hsup]
      exact hJ.symm
    let eD : ↥D₁ ≃* ↥((J₀.map (π₁q e)).map (θq e)) :=
      φ.trans (MulEquiv.subgroupCongr hEq)
    obtain ⟨h1, h2⟩ := h.product_branch hGA hL hp eD
    exact ⟨h1, Or.inr h2⟩

end ProdMain

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
