module

public import CFSG.GH74.Generic.S45.LEvenClassical
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Schreier.TitsComponent
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem map_centralizer_mulEquiv' {X Γ : Type*} [Group X] [Group Γ] (e : X ≃* Γ) (x : X) :
    (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Γ) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

@[expose] noncomputable def centralizerEquiv' {X Γ : Type*} [Group X] [Group Γ] (e : X ≃* Γ)
    (x : X) : ↥(Subgroup.centralizer ({x} : Set X)) ≃* ↥(Subgroup.centralizer ({e x} : Set Γ)) :=
  ((Subgroup.centralizer ({x} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_mulEquiv' e x))

theorem false_of_inner_qdata {S Γ : Type} [Group S] [Group Γ] (hZ : Subgroup.center S = ⊥)
    (e : S ≃* Γ) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q)
    (hfree : ∀ y : Γ, orderOf y = 2 →
      ∀ B : Subgroup ↥(Subgroup.centralizer ({y} : Set Γ)), ¬ CFSG.IsComponent B)
    (hin : ya ∈ inner S) : False := by
  classical
  obtain ⟨x, hx⟩ := hin
  have hxx : x * x = 1 := by
    have h1 : MulAut.conj (x * x) = 1 := by
      rw [map_mul]
      have : (MulAut.conj x : MulAut S) = ya := hx
      rw [this]
      exact hQ.sq
    exact conj_inj_of_center_bot hZ (by rw [h1, map_one])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hQ.ne (by rw [← hx, map_one])
  have hfixeq : autFixed ya = Subgroup.centralizer ({x} : Set S) := by
    have hx' : (MulAut.conj x : MulAut S) = ya := hx
    ext s
    rw [mem_autFixed_iff, ← hx', Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro h
      calc s * x = (x * s * x⁻¹) * x := by rw [h]
        _ = x * s := by group
    · intro h
      calc x * s * x⁻¹ = (s * x) * x⁻¹ := by rw [← h]
        _ = s := by group
  have hLbF : Lb ≤ Subgroup.centralizer ({x} : Set S) := hfixeq ▸ hQ.le
  have hsub : (Lb.subgroupOf (Subgroup.centralizer ({x} : Set S))).IsSubnormal := by
    have := hQ.sub
    rwa [hfixeq] at this
  have hB : CFSG.IsComponent (Lb.subgroupOf (Subgroup.centralizer ({x} : Set S))) := by
    refine ⟨?_, hsub⟩
    have hq : CFSG.IsQuasisimple ↥Lb := isQuasisimple_of_simple_nonab hQ.simple hQ.nonab
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hLbF)).2 hq
  have hB' := CFSG.LocalCores.isComponent_map_mulEquiv (centralizerEquiv' e x) hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (e x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, hxx, map_one]
    · intro h
      exact hx1 (e.injective (by rw [h, map_one]))
  exact hfree (e x) hord _ hB'

theorem even_twistedF4_false
    {S : Type} [Group S] (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) {f : ℕ} (hmodel : ReeTitsModel S .twistedF4 2 f)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) : False := by
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hSs hSnab
  obtain ⟨-, -, -, -, -, hinner, hiso⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions
      S 2 f hmodel
  obtain ⟨⟨-, -, -, -, -, hf3⟩, a, hfa, hmodel'⟩ := hmodel
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hmodel'
  have : Fintype F := Fintype.ofFinite F
  have : CharP F CFSG.LieType.Ree.ReeTag.F4.prime :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF]; rfl)
  obtain ⟨⟨E⟩, -⟩ := hiso a F hfa hF ⟨e₀⟩
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := hfa ▸ hF
  have ha : 1 ≤ a := by omega
  exact false_of_inner_qdata hZ E hQ (fun y hy B =>
    (CFSG.LieType.Ree.LargeReeInvolution.large_Ree_involution_centralizers_component_free a ha F
      hF').1 y hy B) (hinner _ (by rw [pow_two]; exact hQ.sq))

theorem titsD_involutory_aut_inner'
    (α : MulAut CFSG.Sporadic.Schreier.Tits.titsD) (hα : α * α = 1) :
    α ∈ inner CFSG.Sporadic.Schreier.Tits.titsD := by
  obtain ⟨hbij, -, hmap, -⟩ :=
    CFSG.Sporadic.Schreier.Tits.CTUC_Tits_derived_full_automorphism_realization
  obtain ⟨a, rfl⟩ := hbij.2 α
  have haa : a * a = 1 := hbij.1 (by rw [map_mul, hα, map_one])
  by_cases ha1 : a = 1
  · rw [ha1, map_one]
    exact Subgroup.one_mem _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (a : Equiv.Perm (Fin 1755)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
    have hD := CFSG.Sporadic.Schreier.Tits.titsA_involution_mem_D a.2 hord
    rw [← hmap]
    exact ⟨a, Subgroup.mem_subgroupOf.mpr hD, rfl⟩

theorem even_tits_false
    {S : Type} [Group S] (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) {f : ℕ}
    (hmodel : ReeTitsModel S .Tits 2 f) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : False := by
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hSs hSnab
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 f hmodel
  have hββ : MulAut.congr e ya * MulAut.congr e ya = 1 := by
    rw [← map_mul, hQ.sq, map_one]
  have hin' := titsD_involutory_aut_inner' (MulAut.congr e ya) hββ
  have hin : ya ∈ inner S := by
    have hmem : MulAut.congr e ya ∈ (inner S).map (MulAut.congr e).toMonoidHom := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
      exact hin'
    obtain ⟨x, hx, hxy⟩ := hmem
    have hxya : x = ya := (MulAut.congr e).injective hxy
    exact hxya ▸ hx
  exact false_of_inner_qdata hZ e hQ (fun y hy B =>
    CFSG.Sporadic.Schreier.Tits.titsD_involution_centralizer_component_free y hy B) hin

end CFSG.GH74.Generic.S45
