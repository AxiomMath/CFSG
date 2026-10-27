module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Shift
public import CFSG.LieType.AlgebraicGroups.KernelRootGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Std

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.RankThree.PartOne.Q1327T
open CFSG.HardMathSupport.Timmesfeld.Torality
  (isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)

set_option maxRecDepth 100000

section Group

variable {G : Type*} [Group G] {M : Subgroup G}

theorem e6d4t2_conj_mem_of_normalizer {a x : G} (ha : a ∈ Subgroup.normalizer (M : Set G))
    (hx : x ∈ M) : a * x * a⁻¹ ∈ M :=
  (Subgroup.mem_normalizer_iff.1 ha x).1 hx

theorem e6d4t2_conj_inv_mem_of_normalizer {a x : G} (ha : a ∈ Subgroup.normalizer (M : Set G))
    (hx : x ∈ M) : a⁻¹ * x * a ∈ M := by
  have h := e6d4t2_conj_mem_of_normalizer (inv_mem ha) hx
  rwa [inv_inv] at h

theorem e6d4t2_coset_comm {a b z m : G} (ha : a ∈ Subgroup.normalizer (M : Set G))
    (hb : b ∈ Subgroup.normalizer (M : Set G)) (hz : z ∈ M) (hm : m ∈ M)
    (hab : a * b * a⁻¹ * b ∈ M) : (z * a) * (b * m) * (z * a)⁻¹ * (b * m) ∈ M := by
  have e : (z * a) * (b * m) * (z * a)⁻¹ * (b * m) =
      z * (a * b * a⁻¹ * b) * (b⁻¹ * (a * m * a⁻¹ * z⁻¹) * b) * m := by group
  rw [e]
  refine mul_mem (mul_mem (mul_mem hz hab) ?_) hm
  exact e6d4t2_conj_inv_mem_of_normalizer hb
    (mul_mem (e6d4t2_conj_mem_of_normalizer ha hm) (inv_mem hz))

theorem e6d4t2_cube_coset {b m : G} (hb : b ∈ Subgroup.normalizer (M : Set G)) (hm : m ∈ M)
    (hb3 : b ^ 3 ∈ M) : (b * m) ^ 3 ∈ M := by
  have e : (b * m) ^ 3 = b ^ 3 * (b⁻¹ * (b⁻¹ * m * b) * b) * (b⁻¹ * m * b) * m := by
    rw [pow_three']
    group
  rw [e]
  have h1 := e6d4t2_conj_inv_mem_of_normalizer hb hm
  exact mul_mem (mul_mem (mul_mem hb3 (e6d4t2_conj_inv_mem_of_normalizer hb h1)) h1) hm

end Group

section Finite

theorem e6d4t2_inv_mem_of_mapsTo {Sg : Set (Fin Tag.E6.rank → ℤ)} (hfin : Sg.Finite)
    {u : WeylGroup Tag.E6} (hu : ∀ γ ∈ Sg, u • γ ∈ Sg) {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ Sg) :
    u⁻¹ • γ ∈ Sg := by
  have hinj : Set.InjOn (fun x : Fin Tag.E6.rank → ℤ => u • x) Sg := fun x _ y _ h =>
    smul_left_cancel u h
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (f := fun x : Fin Tag.E6.rank → ℤ => u • x)
    (fun x hx => hu x hx)).1 hinj
  obtain ⟨δ, hδ, hδγ⟩ := hbij.surjOn hγ
  have : u⁻¹ • γ = δ := by
    rw [← hδγ]
    simp
  rw [this]
  exact hδ

end Finite

section Normalizer

theorem e6d4t2_canonicalRep_mem_normalizer_M
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {t : WeylGroup Tag.E6}
    (ht : ∀ γ ∈ kernelRoots (rootCharHom a), t • γ ∈ kernelRoots (rootCharHom a))
    (ht' : ∀ γ ∈ kernelRoots (rootCharHom a), t⁻¹ • γ ∈ kernelRoots (rootCharHom a)) :
    canonicalRep (coxeterSystem Tag.E6) L t ∈ Subgroup.normalizer
      ((torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
        Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) := by
  have hT := CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer
    (canonicalRep_mem_normalizer (R := L) t)
  have hset : (fun α => t • α) '' kernelRoots (rootCharHom a) = kernelRoots (rootCharHom a) := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact ht α hα
    · intro hβ
      exact ⟨t⁻¹ • β, ht' β hβ, smul_inv_smul t β⟩
  have hS := (canonical_weyl_root_transport Tag.E6 L).1 t (kernelRoots (rootCharHom a))
    fun α hα => hα.1
  rw [hset] at hS
  have hmap : (torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L t)).toMonoidHom =
        torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    rw [Subgroup.map_sup, hT, hS]
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe hmap
  rw [Subgroup.coe_map] at h
  exact h

theorem e6d4t2_canonicalRep_map_rootSpan
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {t : WeylGroup Tag.E6}
    (ht : ∀ γ ∈ kernelRoots (rootCharHom a), t • γ ∈ kernelRoots (rootCharHom a))
    (ht' : ∀ γ ∈ kernelRoots (rootCharHom a), t⁻¹ • γ ∈ kernelRoots (rootCharHom a)) :
    (rootSpan Tag.E6 L (kernelRoots (rootCharHom a))).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L t)).toMonoidHom =
        rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
  have hset : (fun α => t • α) '' kernelRoots (rootCharHom a) = kernelRoots (rootCharHom a) := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact ht α hα
    · intro hβ
      exact ⟨t⁻¹ • β, ht' β hβ, smul_inv_smul t β⟩
  have hS := (canonical_weyl_root_transport Tag.E6 L).1 t (kernelRoots (rootCharHom a))
    fun α hα => hα.1
  rw [hset] at hS
  exact hS

end Normalizer

section Y

theorem e6d4t2_Y_mem
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} {S : LangSetup Tag.E6 L p₀}
    {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)} (std : E6D4T2Std S a i)
    {t w' : WeylGroup Tag.E6} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = ε • (w' • γ))
    (ht : ∀ γ ∈ kernelRoots (rootCharHom a), t • γ ∈ kernelRoots (rootCharHom a))
    (ht' : ∀ γ ∈ kernelRoots (rootCharHom a), t⁻¹ • γ ∈ kernelRoots (rootCharHom a))
    (hin : twistInner (componentRoots (rootCharHom a) i) ⇑S.ρ) :
    t⁻¹ * (w' * t * w'⁻¹) ∈ e6d4t2WSig a := by
  classical
  obtain ⟨x, hx, hxρ⟩ := hin
  have hker := std.hker
  have hε2 : ∀ z : Fin Tag.E6.rank → ℤ, ε • ε • z = z := by
    intro z
    rcases hε with rfl | rfl <;> simp
  have hxW : x ∈ e6d4t2WSig a := by
    have hset : {s : WeylGroup Tag.E6 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} = (fun α => rootReflection α) '' kernelRoots (rootCharHom a) := by
      ext s
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ, hker ▸ hγ, rfl⟩
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ, hker ▸ hγ, rfl⟩
    rw [hset] at hx
    exact hx
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  have hxK : ∀ γ ∈ kernelRoots (rootCharHom a), x • γ ∈ kernelRoots (rootCharHom a) := by
    intro γ hγ
    have h1 := std.hρ γ (hker ▸ hγ)
    rw [hxρ γ (hker ▸ hγ)] at h1
    exact hker ▸ h1
  have hxK' : ∀ γ ∈ kernelRoots (rootCharHom a), x⁻¹ • γ ∈ kernelRoots (rootCharHom a) :=
    fun γ hγ => e6d4t2_inv_mem_of_mapsTo hfin hxK hγ
  have hagree : ∀ γ ∈ kernelRoots (rootCharHom a),
      (w' * t * w'⁻¹) • γ = (x * t * x⁻¹) • γ := by
    intro γ hγ
    set δ := x⁻¹ • γ with hδ
    have hδK : δ ∈ kernelRoots (rootCharHom a) := hxK' γ hγ
    have hxδ : x • δ = γ := by rw [hδ, smul_inv_smul]
    have hρδ : S.ρ δ = γ := by rw [hxρ δ (hker ▸ hδK), hxδ]
    have hw1 : w' • δ = ε • γ := by
      have := hρ δ hδK.1
      rw [hρδ] at this
      rw [this, hε2]
    have hw2 : w'⁻¹ • γ = ε • δ := by
      have h1 : w'⁻¹ • (ε • γ) = δ := by rw [← hw1, inv_smul_smul]
      rw [smul_comm] at h1
      rw [← h1, hε2]
    have htδ : t • δ ∈ kernelRoots (rootCharHom a) := ht δ hδK
    calc (w' * t * w'⁻¹) • γ = w' • (t • (w'⁻¹ • γ)) := by simp only [mul_smul]
      _ = w' • (t • (ε • δ)) := by rw [hw2]
      _ = ε • (w' • (t • δ)) := by rw [smul_comm t ε δ, smul_comm w' ε (t • δ)]
      _ = S.ρ (t • δ) := (hρ (t • δ) htδ.1).symm
      _ = x • (t • δ) := hxρ _ (hker ▸ htδ)
      _ = (x * t * x⁻¹) • γ := by simp only [mul_smul, hδ]
  have hY1 : t⁻¹ * (x * t * x⁻¹) ∈ e6d4t2WSig a := by
    have e : t⁻¹ * (x * t * x⁻¹) = (t⁻¹ * x * t⁻¹⁻¹) * x⁻¹ := by group
    rw [e]
    exact mul_mem (e6d4t2_conj_mem ht' hxW) (inv_mem hxW)
  have hZ1 : (t⁻¹ * (x * t * x⁻¹))⁻¹ * (t⁻¹ * (w' * t * w'⁻¹)) = 1 := by
    refine e6d4t2_centralizer_kernel std fun γ hγ => ?_
    have h0 : (t⁻¹ * (w' * t * w'⁻¹)) • γ = (t⁻¹ * (x * t * x⁻¹)) • γ := by
      rw [mul_smul t⁻¹ (w' * t * w'⁻¹) γ, hagree γ hγ, ← mul_smul]
    rw [mul_smul, h0, inv_smul_smul]
  rw [← inv_mul_eq_one.1 hZ1]
  exact hY1

end Y

section Fixed

theorem e6d4t2_inverting_inv {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {t : WeylGroup Tag.E6}
    (ht : ∀ x, rootChar a (t • x) = (rootChar a x)⁻¹) (x : Fin Tag.E6.rank → ℤ) :
    rootChar a (t⁻¹ • x) = (rootChar a x)⁻¹ := by
  have h := ht (t⁻¹ • x)
  rw [smul_inv_smul] at h
  rw [h, inv_inv]

theorem e6d4t2_mem_kernel_of_inverting
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {t : WeylGroup Tag.E6}
    (ht : ∀ x, rootChar a (t • x) = (rootChar a x)⁻¹) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ kernelRoots (rootCharHom a)) : t • γ ∈ kernelRoots (rootCharHom a) := by
  refine ⟨(isRoot_smul_iff t).2 hγ.1, ?_⟩
  show rootChar a (t • γ) = 1
  have h1 : rootChar a γ = 1 := hγ.2
  rw [ht, h1, inv_one]

theorem e6d4t2_exists_g
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hS : E6ShapeSetup S) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (hk24 : (kernelRoots (rootCharHom a)).ncard = 24)
    {i : KernelComponent (rootCharHom a)}
    (hin : twistInner (componentRoots (rootCharHom a) i) ⇑S.ρ) :
    ∃ (t : WeylGroup Tag.E6) (z0 : ModGL Tag.E6 L),
      (∀ x, rootChar a (t • x) = (rootChar a x)⁻¹) ∧
      z0 ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ∧
      S.D.step (z0 * canonicalRep (coxeterSystem Tag.E6) L t) =
        z0 * canonicalRep (coxeterSystem Tag.E6) L t := by
  classical
  obtain ⟨std⟩ := e6d4t2_exists_std S hT hap hk24 i
  obtain ⟨z, -, -, hz⟩ := e6d4t2_rootChar_std hap std
  set t := std.v * e6d4t2W0 * std.v⁻¹ with htdef
  have ht : ∀ x, rootChar a (t • x) = (rootChar a x)⁻¹ := e6d4t2_rootChar_t std hz
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  have htK : ∀ γ ∈ kernelRoots (rootCharHom a), t • γ ∈ kernelRoots (rootCharHom a) :=
    fun γ hγ => e6d4t2_mem_kernel_of_inverting ht hγ
  have ht'K : ∀ γ ∈ kernelRoots (rootCharHom a), t⁻¹ • γ ∈ kernelRoots (rootCharHom a) :=
    fun γ hγ => e6d4t2_mem_kernel_of_inverting (e6d4t2_inverting_inv ht) hγ
  obtain ⟨w', ε, hε, hρw, hstepw⟩ := e6d4t2_shape_weyl S hS
  have hY := e6d4t2_Y_mem std hε hρw htK ht'K hin
  set nt := canonicalRep (coxeterSystem Tag.E6) L t with hnt
  set nY := canonicalRep (coxeterSystem Tag.E6) L (t⁻¹ * (w' * t * w'⁻¹)) with hnY
  have hFnt : S.D.step nt = nt * nY := by
    rw [hnt, hstepw t, hnY, ← canonicalRep_mul_charTwo]
    congr 1
    group
  have hnYM : nY ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    canonicalRep_mem_torus_sup_rootSpan_kernelRoots hY
  have hnorm := e6d4t2_canonicalRep_mem_normalizer_M (L := L) htK ht'K
  have hc : nt * (S.D.step nt)⁻¹ ∈
      torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    rw [hFnt]
    have e : nt * (nt * nY)⁻¹ = nt * nY⁻¹ * nt⁻¹ := by group
    rw [e]
    exact e6d4t2_conj_mem_of_normalizer hnorm (inv_mem hnYM)
  obtain ⟨e, Q, he, -, hstepQ⟩ := e6d4t2_step_eq_frobTwist S hS
  have hconn := isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (τ := Tag.E6) (k := L)
    (rootCharHom a)
  have hst : ∀ g ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)),
      frobTwistGL Tag.E6 L 2 e Q g ∈
        torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := fun g hg => by
    rw [← hstepQ]
    exact e6d4t2_step_mem_M S hS hT hg
  obtain ⟨σ, -, -, hlang⟩ := exists_frobTwist_restriction 2 hconn he Q hst
  obtain ⟨zL, hzLM, hzL⟩ := hlang _ hc
  rw [← hstepQ] at hzL
  refine ⟨t, zL, ht, hzLM, ?_⟩
  have hstepz : S.D.step zL = zL * (nt * (S.D.step nt)⁻¹) := by
    rw [← hzL]
    group
  rw [map_mul, hstepz]
  change zL * (nt * (S.D.step nt)⁻¹) * S.D.step nt = zL * nt
  group

end Fixed

section Coset

theorem e6d4t2_y_decomp
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {y : ModGL Tag.E6 L}
    (hyC : y ∈ toralCentralizer Tag.E6 L a) :
    ∃ w ∈ rootCharStabilizerSubgroup a,
      ∃ m ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)),
        y = canonicalRep (coxeterSystem Tag.E6) L w * m := by
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 L a).1 y hyC
  have hbw : canonicalRep (coxeterSystem Tag.E6) L w ∈ Subgroup.normalizer
      ((torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
        Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer_toralRootGroup hw
  have hhM : h ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_left hh
  have huM : u ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)
  have hvM : v ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  refine ⟨w, hw, (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * (h * u) *
    canonicalRep (coxeterSystem Tag.E6) L w * v, ?_, by group⟩
  exact mul_mem (e6d4t2_conj_inv_mem_of_normalizer hbw (mul_mem hhM huM)) hvM

theorem e6d4t2_g_conj_mem
    {L : Type} [Field L] [CharP L 2] {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    {t : WeylGroup Tag.E6} (ht : ∀ x, rootChar a (t • x) = (rootChar a x)⁻¹)
    {z0 : ModGL Tag.E6 L}
    (hz0 : z0 ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)))
    {y : ModGL Tag.E6 L} (hyC : y ∈ toralCentralizer Tag.E6 L a) :
    (z0 * canonicalRep (coxeterSystem Tag.E6) L t) * y *
        (z0 * canonicalRep (coxeterSystem Tag.E6) L t)⁻¹ * y ∈
      torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
  obtain ⟨w, hw, m, hm, rfl⟩ := e6d4t2_y_decomp hyC
  have htK : ∀ γ ∈ kernelRoots (rootCharHom a), t • γ ∈ kernelRoots (rootCharHom a) :=
    fun γ hγ => e6d4t2_mem_kernel_of_inverting ht hγ
  have ht'K : ∀ γ ∈ kernelRoots (rootCharHom a), t⁻¹ • γ ∈ kernelRoots (rootCharHom a) :=
    fun γ hγ => e6d4t2_mem_kernel_of_inverting (e6d4t2_inverting_inv ht) hγ
  have hat := e6d4t2_canonicalRep_mem_normalizer_M (L := L) htK ht'K
  have hbw : canonicalRep (coxeterSystem Tag.E6) L w ∈ Subgroup.normalizer
      ((torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
        Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer_toralRootGroup hw
  have hab : canonicalRep (coxeterSystem Tag.E6) L t * canonicalRep (coxeterSystem Tag.E6) L w *
      (canonicalRep (coxeterSystem Tag.E6) L t)⁻¹ * canonicalRep (coxeterSystem Tag.E6) L w ∈
        torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    have e : canonicalRep (coxeterSystem Tag.E6) L (t * w * t⁻¹ * w) =
        canonicalRep (coxeterSystem Tag.E6) L t * canonicalRep (coxeterSystem Tag.E6) L w *
          (canonicalRep (coxeterSystem Tag.E6) L t)⁻¹ *
            canonicalRep (coxeterSystem Tag.E6) L w := by
      rw [canonicalRep_mul_charTwo, e6d4t2_canonicalRep_conj]
    rw [← e]
    exact canonicalRep_mem_torus_sup_rootSpan_kernelRoots
      (e6d4t2_kernelReflectionGroup_le a (e6d4t2_shift_conj hap ht hw))
  exact e6d4t2_coset_comm hat hbw hz0 hm hab

theorem e6d4t2_cube_mem_M
    {L : Type} [Field L] [CharP L 2] {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    {y : ModGL Tag.E6 L} (hyC : y ∈ toralCentralizer Tag.E6 L a) :
    y ^ 3 ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
  obtain ⟨w, hw, m, hm, rfl⟩ := e6d4t2_y_decomp hyC
  have hbw : canonicalRep (coxeterSystem Tag.E6) L w ∈ Subgroup.normalizer
      ((torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
        Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer_toralRootGroup hw
  have hb3 : canonicalRep (coxeterSystem Tag.E6) L w ^ 3 ∈
      torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    have e : canonicalRep (coxeterSystem Tag.E6) L w ^ 3 =
        canonicalRep (coxeterSystem Tag.E6) L (w ^ 3) := by
      rw [pow_three', pow_three', canonicalRep_mul_charTwo, canonicalRep_mul_charTwo]
    rw [e]
    exact canonicalRep_mem_torus_sup_rootSpan_kernelRoots
      (e6d4t2_kernelReflectionGroup_le a (e6d4t2_cube_mem hap hw))
  exact e6d4t2_cube_coset hbw hm hb3

end Coset

section Stabilizer

theorem e6d4t2_map_conj_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj x).toMonoidHom = H := by
  have h := Subgroup.mem_normalizer_iff_conj_image_eq.1 hx
  apply SetLike.coe_injective
  rw [Subgroup.coe_map]
  exact h

theorem e6d4t2_mem_normalizer_of_map_eq {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (h : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h' := congrArg SetLike.coe h
  rw [Subgroup.coe_map] at h'
  exact h'

theorem e6d4t2_map_rootSpan_g
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {t : WeylGroup Tag.E6}
    (ht : ∀ γ ∈ kernelRoots (rootCharHom a), t • γ ∈ kernelRoots (rootCharHom a))
    (ht' : ∀ γ ∈ kernelRoots (rootCharHom a), t⁻¹ • γ ∈ kernelRoots (rootCharHom a))
    {z0 : ModGL Tag.E6 L}
    (hz0 : z0 ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))) :
    (rootSpan Tag.E6 L (kernelRoots (rootCharHom a))).map
      (MulAut.conj (z0 * canonicalRep (coxeterSystem Tag.E6) L t)).toMonoidHom =
        rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
  refine e6d4t2_map_conj_of_mem_normalizer (mul_mem ?_ ?_)
  · have hle : torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ≤
        Subgroup.normalizer (rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
          Set (ModGL Tag.E6 L)) :=
      sup_le (torusGroup_le_normalizer_rootSpan fun α hα => hα.1) Subgroup.le_normalizer
    exact hle hz0
  · exact e6d4t2_mem_normalizer_of_map_eq (e6d4t2_canonicalRep_map_rootSpan ht ht')

theorem e6d4t2_conj_stab_R
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)} (std : E6D4T2Std S a i)
    {g : ModGL Tag.E6 L} (hg : g ∈ S.D.model)
    (hgA : (rootSpan Tag.E6 L (kernelRoots (rootCharHom a))).map (MulAut.conj g).toMonoidHom =
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a))) :
    MulAut.conj g ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have horbit : rationalRoots S.ρ (rootCharHom a) i = kernelRoots (rootCharHom a) := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      rw [← std.hker]
      induction k generalizing δ with
      | zero => exact hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply]
        exact ih _ (std.hρ δ hδ)
    · intro hγ
      exact ⟨0, γ, std.hker ▸ hγ, rfl⟩
  have hmodel : S.D.model.map (MulAut.conj g).toMonoidHom = S.D.model :=
    e6d4t2_map_conj_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hΓ : S.Γ.map (MulAut.conj g).toMonoidHom = S.Γ := by
    change ⁅S.D.model, S.D.model⁆.map (MulAut.conj g).toMonoidHom = ⁅S.D.model, S.D.model⁆
    rw [Subgroup.map_commutator, hmodel]
  have hP : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj g).toMonoidHom =
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalSpan
    rw [Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom hinj, horbit, hgA, hΓ]
  change (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj g).toMonoidHom =
    rationalComponent S.ρ S.Γ (rootCharHom a) i
  unfold rationalComponent
  rw [Subgroup.map_commutator, hP]

end Stabilizer

end CFSG.LocalAnalysis.GLTheoremA.T158

end
