module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleRoots
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleStar
public import CFSG.ClassicalInvolution.RouteD.TypeEModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.ModelFacts (lenSq lenSq_weylAction)

variable {K : Type} [Group K] {D : UniversalRootDatum K} {nW : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem modelStar_of_f4Nodes {t : StatedLieTag} {F : Type} [Field F]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nW H)
    (hext : SteinbergExtras D nW H) (hsc : FundamentalSingleClass t D)
    (i0 i1 i2 i3 : Fin D.rank) (hl0 : IsLongestRoot D (Pi.single i0 1))
    (hl1 : IsLongestRoot D (Pi.single i1 1))
    (a11 : D.cartan i1 i1 = 2) (a12 : D.cartan i1 i2 = -1) (a21 : D.cartan i2 i1 = -2)
    (a22 : D.cartan i2 i2 = 2) (a23 : D.cartan i2 i3 = -1) (a32 : D.cartan i3 i2 = -1)
    (a13 : D.cartan i1 i3 = 0) (a31 : D.cartan i3 i1 = 0) (a02 : D.cartan i0 i2 = 0)
    (a03 : D.cartan i0 i3 = 0)
    (hW : ∃ W, LinearBlockStandardPair F W (rankOne D.rootGroup i1) (rankOne D.rootGroup i0)) :
    ModelStar F (fundamentalSubgroups t D) := by
  let cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
  let ρ := weylAction D.isFiniteType
  let ε₂ : Fin D.rank → ℤ := ρ (cs.simple i2) (Pi.single i1 1)
  let ε₃ : Fin D.rank → ℤ := ρ (cs.simple i3) ε₂
  have hε₂r : ε₂ ∈ D.roots := Or.inl ⟨cs.simple i2, i1, rfl⟩
  have hε₃r : ε₃ ∈ D.roots :=
    Or.inl ⟨cs.simple i3 * cs.simple i2, i1, by rw [weylAction_mul_apply]⟩
  have hε₂ : ε₂ = Pi.single i1 1 - coroot D.cartan i2 (Pi.single i1 1) • Pi.single i2 1 := by
    show ρ (cs.simple i2) (Pi.single i1 1) = _
    rw [weylAction_simple, reflection_apply_coroot]
  have hε₃ : ε₃ = ε₂ - coroot D.cartan i3 ε₂ • Pi.single i3 1 := by
    show ρ (cs.simple i3) ε₂ = _
    rw [weylAction_simple, reflection_apply_coroot]
  have cr : ∀ (m i : Fin D.rank) (v : Fin D.rank → ℤ),
      coroot D.cartan m (v - coroot D.cartan i v • Pi.single i 1) =
        coroot D.cartan m v - coroot D.cartan i v * D.cartan m i := by
    intro m i v
    rw [map_sub, map_zsmul, coroot_single, smul_eq_mul]
  have k12 : coroot D.cartan i1 ε₂ = 0 := by
    rw [hε₂, cr, coroot_single, coroot_single, a11, a12, a21]
    norm_num
  have k32 : coroot D.cartan i3 ε₂ = -2 := by
    rw [hε₂, cr, coroot_single, coroot_single, a31, a32, a21]
    norm_num
  have k22 : coroot D.cartan i2 ε₂ = 2 := by
    rw [hε₂, cr, coroot_single, a21, a22]
    norm_num
  have k13 : coroot D.cartan i1 ε₃ = 0 := by
    rw [hε₃, cr, k12, k32, a13]
    simp
  have k23 : coroot D.cartan i2 ε₃ = 0 := by
    rw [hε₃, cr, k22, k32, a23]
    simp
  have o1 : form D.isFiniteType (toRat (Pi.single i1 1)) (toRat ε₂) = 0 := by
    rw [form_comm]
    exact form_toRat_single_eq_zero D i1 ε₂ k12
  have o2 : form D.isFiniteType (toRat (Pi.single i1 1)) (toRat ε₃) = 0 := by
    rw [form_comm]
    exact form_toRat_single_eq_zero D i1 ε₃ k13
  have o3 : form D.isFiniteType (toRat ε₂) (toRat ε₃) = 0 := by
    have e1 := form_toRat_single_eq_zero D i1 ε₃ k13
    have e2 := form_toRat_single_eq_zero D i2 ε₃ k23
    rw [form_comm, hε₂, map_sub, map_zsmul, map_sub, map_zsmul, e1, e2]
    simp
  have hmax1 : ∀ δ ∈ D.roots, lenSq D.isFiniteType δ ≤ lenSq D.isFiniteType (Pi.single i1 1) :=
    hl1.2
  have hlen₂ : lenSq D.isFiniteType ε₂ = lenSq D.isFiniteType (Pi.single i1 1) :=
    lenSq_weylAction D.isFiniteType (cs.simple i2) (Pi.single i1 1)
  have hmax₂ : ∀ δ ∈ D.roots, lenSq D.isFiniteType δ ≤ lenSq D.isFiniteType ε₂ := by
    intro δ hδ
    rw [hlen₂]
    exact hmax1 δ hδ
  have hmax0 : ∀ δ ∈ D.roots, lenSq D.isFiniteType δ ≤ lenSq D.isFiniteType (Pi.single i0 1) :=
    hl0.2
  let R₁ : Subgroup K := rankOne D.rootGroup i1
  let L₂ : Subgroup K := conjSub (nW i2) R₁
  let L₃ : Subgroup K := conjSub (nW i3 * nW i2) R₁
  have hS₂ : L₂ ≤ D.rootGroup ε₂ ⊔ D.rootGroup (-ε₂) :=
    conjSub_rootPair_le hct i2 (single_mem_roots D i1)
  have hS₃ : L₃ ≤ D.rootGroup ε₃ ⊔ D.rootGroup (-ε₃) := by
    rw [show L₃ = conjSub (nW i3) L₂ from conjSub_mul _ _ _]
    exact (conjSub_mono hS₂).trans (conjSub_rootPair_le hct i3 hε₂r)
  have c01 : Commutes R₁ L₂ :=
    commutes_mono (commutes_fund_of_orthogonal_of_longest D hext (single_mem_roots D i1) hε₂r
      hmax1 o1) le_rfl hS₂
  have c02 : Commutes R₁ L₃ :=
    commutes_mono (commutes_fund_of_orthogonal_of_longest D hext (single_mem_roots D i1) hε₃r
      hmax1 o2) le_rfl hS₃
  have c12 : Commutes L₂ L₃ :=
    commutes_mono (commutes_fund_of_orthogonal_of_longest D hext hε₂r hε₃r hmax₂ o3) hS₂ hS₃
  let Rc : Subgroup K := rankOne D.rootGroup i0
  have h20 : Commutes (rankOne D.rootGroup i2) Rc :=
    (commutes_rankOne_of_cartan_eq_zero_of_longest D hext hmax0 a02).symm
  have h30 : Commutes (rankOne D.rootGroup i3) Rc :=
    (commutes_rankOne_of_cartan_eq_zero_of_longest D hext hmax0 a03).symm
  have e2 : conjSub (nW i2) Rc = Rc := conjSub_eq_of_commutes_mem (hct.n_mem i2) h20
  have e3 : conjSub (nW i3) Rc = Rc := conjSub_eq_of_commutes_mem (hct.n_mem i3) h30
  have p1 : ∃ W, LinearBlockStandardPair F W L₂ Rc := by
    obtain ⟨W, hW⟩ := hW
    have := ModelFacts.linearBlockStandardPair_map_conj hW (nW i2)
    change LinearBlockStandardPair F _ (conjSub (nW i2) R₁) (conjSub (nW i2) Rc) at this
    rw [e2] at this
    exact ⟨_, this⟩
  have e32 : conjSub (nW i3 * nW i2) Rc = Rc := by rw [conjSub_mul, e2, e3]
  have p2 : ∃ W, LinearBlockStandardPair F W L₃ Rc := by
    obtain ⟨W, hW⟩ := hW
    have := ModelFacts.linearBlockStandardPair_map_conj hW (nW i3 * nW i2)
    change LinearBlockStandardPair F _ (conjSub (nW i3 * nW i2) R₁)
      (conjSub (nW i3 * nW i2) Rc) at this
    rw [e32] at this
    exact ⟨_, this⟩
  have hR₁f : R₁ ∈ fundamentalSubgroups t D := rankOne_mem_fundamental D hl1
  exact ModelStar.of_node_star hsc hR₁f (conjSub_mem_fundamentalSubgroups hR₁f _)
    (conjSub_mem_fundamentalSubgroups hR₁f _) (rankOne_mem_fundamental D hl0) c01 c02 c12 hW p1 p2

end CFSG.ClassicalInvolution.RouteD.Exotic
