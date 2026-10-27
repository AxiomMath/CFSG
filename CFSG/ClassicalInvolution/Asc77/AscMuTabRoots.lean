module

public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD

namespace MuTab

variable {K : Type} [Group K]

@[expose] def ThreeOrth (D : UniversalRootDatum K) : Prop :=
  ∃ γ δ ε : Fin D.rank → ℤ, ModelFacts.IsLongestRoot D γ ∧ ModelFacts.IsLongestRoot D δ ∧
    ModelFacts.IsLongestRoot D ε ∧ form D.isFiniteType (toRat γ) (toRat δ) = 0 ∧
    form D.isFiniteType (toRat γ) (toRat ε) = 0 ∧ form D.isFiniteType (toRat δ) (toRat ε) = 0

theorem threeOrth_of_nodes (D : UniversalRootDatum K) {a b c : Fin D.rank}
    (ha : ModelFacts.IsLongestRoot D (Pi.single a 1))
    (hb : ModelFacts.IsLongestRoot D (Pi.single b 1))
    (hc : ModelFacts.IsLongestRoot D (Pi.single c 1))
    (hab : D.cartan a b = 0) (hac : D.cartan a c = 0) (hbc : D.cartan b c = 0) :
    ThreeOrth D :=
  ⟨_, _, _, ha, hb, hc, form_single_eq_zero_of_cartan D hab, form_single_eq_zero_of_cartan D hac,
    form_single_eq_zero_of_cartan D hbc⟩

theorem threeOrth_tail (D : UniversalRootDatum K) {a b c : Fin D.rank}
    (hl : ModelFacts.IsLongestRoot D (Pi.single c 1))
    (hcc : D.cartan c c = 2) (hcb : D.cartan c b = -1) (hca : D.cartan c a = 0)
    (hbc : D.cartan b c = -2) (hbb : D.cartan b b = 2) (hba : D.cartan b a = -1)
    (hac : D.cartan a c = 0) (hab : D.cartan a b = -1) : ThreeOrth D := by
  set S := fun j => (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j with hS
  have hδ : weylAction D.isFiniteType (S b) (Pi.single c 1) =
      Pi.single c 1 + (2 : ℤ) • Pi.single b 1 := by
    rw [hS, weylAction_simple, reflection_apply_coroot D.cartan b, coroot_single, hbc]
    module
  have hε : weylAction D.isFiniteType (S a * S b) (Pi.single c 1) =
      Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1 := by
    rw [weylAction_mul_apply, hδ, hS, weylAction_simple, reflection_apply_coroot D.cartan a]
    simp only [map_add, map_zsmul, coroot_single, hac, hab, smul_eq_mul]
    module
  have hcorc : coroot D.cartan c (Pi.single c 1 + (2 : ℤ) • Pi.single b 1 +
      (2 : ℤ) • Pi.single a 1) = 0 := by
    simp only [map_add, map_zsmul, coroot_single, smul_eq_mul, hcc, hcb, hca]
    norm_num
  have hcorb : coroot D.cartan b (Pi.single c 1 + (2 : ℤ) • Pi.single b 1 +
      (2 : ℤ) • Pi.single a 1) = 0 := by
    simp only [map_add, map_zsmul, coroot_single, smul_eq_mul, hbc, hbb, hba]
    norm_num
  have hcord : coroot D.cartan c (Pi.single c 1 + (2 : ℤ) • Pi.single b 1) = 0 := by
    simp only [map_add, map_zsmul, coroot_single, smul_eq_mul, hcc, hcb]
    norm_num
  have hfε : form D.isFiniteType (toRat (Pi.single c 1))
      (toRat (Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1)) = 0 := by
    rw [form_comm]
    exact form_toRat_single_eq_zero D c _ hcorc
  have hbε : form D.isFiniteType (toRat (Pi.single b 1))
      (toRat (Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1)) = 0 := by
    rw [form_comm]
    exact form_toRat_single_eq_zero D b _ hcorb
  refine ⟨Pi.single c 1, weylAction D.isFiniteType (S b) (Pi.single c 1),
    weylAction D.isFiniteType (S a * S b) (Pi.single c 1), hl,
    ModelFacts.IsLongest.map_weylAction hl _, ModelFacts.IsLongest.map_weylAction hl _, ?_, ?_, ?_⟩
  · rw [hδ, form_comm]
    exact form_toRat_single_eq_zero D c _ hcord
  · rw [hε]
    exact hfε
  · rw [hδ, hε]
    generalize (Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1 :
      Fin D.rank → ℤ) = E at hfε hbε ⊢
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, hfε, hbε,
      smul_zero, add_zero]

theorem threeOrth_tailBC (D : UniversalRootDatum K) {a b c : Fin D.rank}
    (hl : ModelFacts.IsLongestRoot D (2 • Pi.single c 1))
    (hcc : D.cartan c c = 2) (hcb : D.cartan c b = -2) (hca : D.cartan c a = 0)
    (hbc : D.cartan b c = -1) (hbb : D.cartan b b = 2) (hba : D.cartan b a = -1)
    (hac : D.cartan a c = 0) (hab : D.cartan a b = -1) : ThreeOrth D := by
  set S := fun j => (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j with hS
  have hδ : weylAction D.isFiniteType (S b) (2 • Pi.single c 1) =
      2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 := by
    rw [hS, weylAction_simple, reflection_apply_coroot D.cartan b, map_nsmul, coroot_single, hbc]
    module
  have hε : weylAction D.isFiniteType (S a * S b) (2 • Pi.single c 1) =
      2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1 := by
    rw [weylAction_mul_apply, hδ, hS, weylAction_simple, reflection_apply_coroot D.cartan a]
    simp only [map_add, map_nsmul, map_zsmul, coroot_single, hac, hab, smul_eq_mul]
    module
  have hcorc : coroot D.cartan c (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 +
      (2 : ℤ) • Pi.single a 1) = 0 := by
    simp only [map_add, map_nsmul, map_zsmul, coroot_single, smul_eq_mul, hcc, hcb, hca]
    norm_num
  have hcorb : coroot D.cartan b (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 +
      (2 : ℤ) • Pi.single a 1) = 0 := by
    simp only [map_add, map_nsmul, map_zsmul, coroot_single, smul_eq_mul, hbc, hbb, hba]
    norm_num
  have hcord : coroot D.cartan c (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1) = 0 := by
    simp only [map_add, map_nsmul, map_zsmul, coroot_single, smul_eq_mul, hcc, hcb]
    norm_num
  have hfε : form D.isFiniteType (toRat (2 • Pi.single c 1))
      (toRat (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1)) = 0 := by
    have h1 : form D.isFiniteType (toRat (Pi.single c 1))
        (toRat (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1)) = 0 := by
      rw [form_comm]
      exact form_toRat_single_eq_zero D c _ hcorc
    simp only [map_nsmul, LinearMap.smul_apply, h1, smul_zero]
  have hbε : form D.isFiniteType (toRat (Pi.single b 1))
      (toRat (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1)) = 0 := by
    rw [form_comm]
    exact form_toRat_single_eq_zero D b _ hcorb
  have hcε : form D.isFiniteType (toRat (Pi.single c 1))
      (toRat (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1)) = 0 := by
    rw [form_comm]
    exact form_toRat_single_eq_zero D c _ hcorc
  refine ⟨2 • Pi.single c 1, weylAction D.isFiniteType (S b) (2 • Pi.single c 1),
    weylAction D.isFiniteType (S a * S b) (2 • Pi.single c 1), hl,
    ModelFacts.IsLongest.map_weylAction hl _, ModelFacts.IsLongest.map_weylAction hl _, ?_, ?_, ?_⟩
  · rw [hδ]
    have h1 : form D.isFiniteType (toRat (Pi.single c 1))
        (toRat (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1)) = 0 := by
      rw [form_comm]
      exact form_toRat_single_eq_zero D c _ hcord
    simp only [map_nsmul, LinearMap.smul_apply, h1, smul_zero]
  · rw [hε]
    exact hfε
  · rw [hδ, hε]
    generalize (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1 :
      Fin D.rank → ℤ) = E at hcε hbε ⊢
    simp only [map_add, map_nsmul, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, hcε,
      hbε, smul_zero, add_zero]

theorem threeOrth_B (D : UniversalRootDatum K) {x y z : Fin D.rank}
    (hx : ModelFacts.IsLongestRoot D (Pi.single x 1))
    (hy : ModelFacts.IsLongestRoot D (Pi.single y 1))
    (hxy : D.cartan x y = 0) (hxz : D.cartan x z = 0) (hyy : D.cartan y y = 2)
    (hyz : D.cartan y z = -1) (hzy : D.cartan z y = -2) : ThreeOrth D := by
  set S := fun j => (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j with hS
  have hδ : weylAction D.isFiniteType (S z) (Pi.single y 1) =
      Pi.single y 1 + (2 : ℤ) • Pi.single z 1 := by
    rw [hS, weylAction_simple, reflection_apply_coroot D.cartan z, coroot_single, hzy]
    module
  have hcx : coroot D.cartan x (Pi.single y 1 + (2 : ℤ) • Pi.single z 1) = 0 := by
    simp only [map_add, map_zsmul, coroot_single, smul_eq_mul, hxy, hxz]
    norm_num
  have hcy : coroot D.cartan y (Pi.single y 1 + (2 : ℤ) • Pi.single z 1) = 0 := by
    simp only [map_add, map_zsmul, coroot_single, smul_eq_mul, hyy, hyz]
    norm_num
  refine ⟨Pi.single x 1, Pi.single y 1, weylAction D.isFiniteType (S z) (Pi.single y 1), hx, hy,
    ModelFacts.IsLongest.map_weylAction hy _, form_single_eq_zero_of_cartan D hxy, ?_, ?_⟩
  · rw [hδ, form_comm]
    exact form_toRat_single_eq_zero D x _ hcx
  · rw [hδ, form_comm]
    exact form_toRat_single_eq_zero D y _ hcy

end MuTab

end CFSG.ClassicalInvolution.Asc77
