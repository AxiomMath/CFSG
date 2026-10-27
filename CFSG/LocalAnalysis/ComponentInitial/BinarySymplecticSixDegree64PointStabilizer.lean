module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64PointFusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type*} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₁₀" =>
  (normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G)

theorem zmod_two_eq_zero_or_eq_one : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

include he hnd hzC hsup hinf hz in
theorem mem_ptSub_of_forall_conj {m : G}
    (h : ∀ v : 𝔼 × ZMod 2, m * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) * m) :
    m ∈ ptSub φ z hb e := by
  have h1 : ∀ v : 𝔼 × ZMod 2,
      ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) ∈ centralizer ({m} : Set G) :=
    fun v => mem_centralizer_singleton_iff.2 (h v).symm
  have hC : ∀ x : Multiplicative ((𝔼 × ZMod 2) × ZMod 2),
      ptHom he hb φ hzC hz x ∈ centralizer ({m} : Set G) := by
    intro x
    obtain ⟨⟨v, ε⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = x := ⟨Multiplicative.toAdd x, rfl⟩
    rcases zmod_two_eq_zero_or_eq_one ε with rfl | rfl
    · have hv : Multiplicative.ofAdd (v, (0 : ZMod 2)) =
          Multiplicative.ofAdd (v, (1 : ZMod 2)) * Multiplicative.ofAdd ((0 : 𝔼 × ZMod 2), 1) := by
        rw [← ofAdd_add, Prod.mk_add_mk, add_zero]
        rfl
      rw [hv, map_mul]
      exact mul_mem (h1 v) (h1 0)
    · exact h1 v
  rw [← centralizer_ptSub he hb hnd φ hzC hsup hinf hz, mem_centralizer_iff]
  intro x hx
  have hx' : x ∈ (ptHom he hb φ hzC hz).range := by
    rw [range_ptHom he hb φ hzC hz]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  exact mem_centralizer_singleton_iff.1 (hC y)

theorem zmod_two_add_add_add_add' : ∀ a c c' d : ZMod 2, a + c + c' + c' + d = a + c + d := by
  decide

omit he hb hnd in
theorem hV_mul_apply {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {β : BilinForm (ZMod 2) E}
    {Q : QuadraticForm (ZMod 2) E} (hQ : QuadraticMap.polarBilin Q = β)
    (s t : bilinIsometryGroup β) (v : E × ZMod 2) :
    OddQuadraticFive.hV hQ (s * t) v = OddQuadraticFive.hV hQ s (OddQuadraticFive.hV hQ t v) := by
  rw [OddQuadraticFive.hV_apply, OddQuadraticFive.hV_apply, OddQuadraticFive.hV_apply]
  simp only [OddQuadraticFive.sE_mul]
  rw [zmod_two_add_add_add_add']

omit he hb hnd in
theorem hV_one_apply {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {β : BilinForm (ZMod 2) E}
    {Q : QuadraticForm (ZMod 2) E} (hQ : QuadraticMap.polarBilin Q = β) (v : E × ZMod 2) :
    OddQuadraticFive.hV hQ 1 v = v :=
  OddQuadraticFive.hV_eq_self hQ 1 (OddQuadraticFive.sE_one _)

omit hb hnd in
theorem hV_ext {s s' : bilinIsometryGroup (b.restrict 𝔼)}
    (h : ∀ v : 𝔼 × ZMod 2, OddQuadraticFive.hV (polarBilin_ptQuad he) s v =
      OddQuadraticFive.hV (polarBilin_ptQuad he) s' v) : s = s' :=
  Subtype.ext (Units.ext (LinearMap.ext fun w => congrArg Prod.fst (h (w, 0))))

include he hnd hsup hinf in
theorem exists_ptStab (n : 𝒩₁₀) :
    ∃ s : bilinIsometryGroup (b.restrict 𝔼), ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      (n : G) * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * (n : G)⁻¹ =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, ε)) :=
  exists_hV_of_mem_stab he hb hnd φ hzC hsup hinf hz (mem_inf.1 n.2).1
    (mem_centralizer_singleton_iff.1 (mem_inf.1 n.2).2)

@[expose] def ptStabFun (n : 𝒩₁₀) : bilinIsometryGroup (b.restrict 𝔼) :=
  Classical.choose (exists_ptStab he hb hnd φ hzC hsup hinf hz n)

theorem ptStabFun_spec (n : 𝒩₁₀) (v : 𝔼 × ZMod 2) (ε : ZMod 2) :
    (n : G) * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * (n : G)⁻¹ =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd
        (OddQuadraticFive.hV (polarBilin_ptQuad he) (ptStabFun he hb hnd φ hzC hsup hinf hz n) v,
          ε)) :=
  Classical.choose_spec (exists_ptStab he hb hnd φ hzC hsup hinf hz n) v ε

theorem ptStabFun_eq {n : 𝒩₁₀} {s : bilinIsometryGroup (b.restrict 𝔼)}
    (hs : ∀ v : 𝔼 × ZMod 2,
      (n : G) * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 0)) * (n : G)⁻¹ =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, 0))) :
    ptStabFun he hb hnd φ hzC hsup hinf hz n = s :=
  hV_ext he fun v => by
    have h := (ptStabFun_spec he hb hnd φ hzC hsup hinf hz n v 0).symm.trans (hs v)
    exact congrArg Prod.fst (Multiplicative.ofAdd.injective (ptHom_injective he hb φ hzC hz hinf h))

@[expose] def ptStab : 𝒩₁₀ →* bilinIsometryGroup (b.restrict 𝔼) where
  toFun := ptStabFun he hb hnd φ hzC hsup hinf hz
  map_one' := ptStabFun_eq he hb hnd φ hzC hsup hinf hz fun v => by
    rw [OneMemClass.coe_one, one_mul, inv_one, mul_one, hV_one_apply]
  map_mul' n m := ptStabFun_eq he hb hnd φ hzC hsup hinf hz fun v => by
    rw [hV_mul_apply, ← ptStabFun_spec he hb hnd φ hzC hsup hinf hz n,
      ← ptStabFun_spec he hb hnd φ hzC hsup hinf hz m, Subgroup.coe_mul]
    group

theorem ptStab_spec (n : 𝒩₁₀) (v : 𝔼 × ZMod 2) (ε : ZMod 2) :
    (n : G) * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * (n : G)⁻¹ =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd
        (OddQuadraticFive.hV (polarBilin_ptQuad he) (ptStab he hb hnd φ hzC hsup hinf hz n) v,
          ε)) :=
  ptStabFun_spec he hb hnd φ hzC hsup hinf hz n v ε

theorem ptStab_eq {n : 𝒩₁₀} {s : bilinIsometryGroup (b.restrict 𝔼)}
    (hs : ∀ v : 𝔼 × ZMod 2,
      (n : G) * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 0)) * (n : G)⁻¹ =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, 0))) :
    ptStab he hb hnd φ hzC hsup hinf hz n = s :=
  ptStabFun_eq he hb hnd φ hzC hsup hinf hz hs

omit hnd hsup hinf in
theorem ptHom_pointElt (w : 𝔼) (c ε : ZMod 2) :
    ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, c + ptQuad e w), ε)) =
      ((φ.symm (pointElt hb (mem_pairOrth_left w.2) c) : L) : G) * zPow z ε := by
  have hX : ptElt hb ((w, c + ptQuad e w) : 𝔼 × ZMod 2) =
      pointElt hb (mem_pairOrth_left w.2) c := by
    rw [ptElt_eq]
    apply pointElt_ext
    change pointMap b (e (Sum.inl 0)) (w : V) (c + ptQuad e w + ptQuad e w) =
      pointMap b (e (Sum.inl 0)) (w : V) c
    rw [add_assoc, zmod_two_add_self_eq_zero, add_zero]
  rw [ptHom_apply, ptHomV_apply, hX]

theorem ptStab_conj_pointElt (n : 𝒩₁₀) (w : 𝔼) (c : ZMod 2) :
    (n : G) * ((φ.symm (pointElt hb (mem_pairOrth_left w.2) c) : L) : G) * (n : G)⁻¹ =
      ((φ.symm (pointElt hb (mem_pairOrth_left
        (OddQuadraticFive.sE (ptStab he hb hnd φ hzC hsup hinf hz n) w).2) c) : L) : G) := by
  set s := ptStab he hb hnd φ hzC hsup hinf hz n with hs
  have h := ptStab_spec he hb hnd φ hzC hsup hinf hz n (w, c + ptQuad e w) 0
  have h1 : OddQuadraticFive.hV (polarBilin_ptQuad he) s (w, c + ptQuad e w) =
      (OddQuadraticFive.sE s w, c + ptQuad e (OddQuadraticFive.sE s w)) := by
    rw [OddQuadraticFive.hV_apply]
    change (OddQuadraticFive.sE s w,
      c + ptQuad e w + ptQuad e w + ptQuad e (OddQuadraticFive.sE s w)) = _
    rw [add_assoc c, zmod_two_add_self_eq_zero, add_zero]
  rw [← hs, h1, ptHom_pointElt, ptHom_pointElt, zPow_zero, mul_one, mul_one] at h
  exact h

include hzC hz in
theorem ptLevi_mem_ptStabSub [Finite G] (s : bilinIsometryGroup (b.restrict 𝔼)) :
    ptLevi he hb φ s ∈ 𝒩₁₀ :=
  mem_inf.2 ⟨ptLevi_mem_normalizer he hb φ hzC hz s,
    mem_centralizer_singleton_iff.2 (ptLevi_mul_z he hb φ hzC s)⟩

theorem ptStab_ptLevi [Finite G] (s : bilinIsometryGroup (b.restrict 𝔼)) :
    ptStab he hb hnd φ hzC hsup hinf hz
      ⟨ptLevi he hb φ s, ptLevi_mem_ptStabSub he hb φ hzC hz s⟩ = s :=
  ptStab_eq he hb hnd φ hzC hsup hinf hz fun v => ptLevi_conj_ptHom he hb φ hzC hz s v 0

theorem ptStab_surjective [Finite G] :
    Function.Surjective (ptStab he hb hnd φ hzC hsup hinf hz) :=
  fun s => ⟨_, ptStab_ptLevi he hb hnd φ hzC hsup hinf hz s⟩

theorem ker_ptStab :
    (ptStab he hb hnd φ hzC hsup hinf hz).ker = (ptSub φ z hb e).subgroupOf 𝒩₁₀ := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    refine mem_ptSub_of_forall_conj he hb hnd φ hzC hsup hinf hz fun v => ?_
    have h1 := ptStab_spec he hb hnd φ hzC hsup hinf hz n v 1
    rw [h, hV_one_apply, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · intro h
    obtain ⟨-, hBe, -, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
    refine ptStab_eq he hb hnd φ hzC hsup hinf hz fun v => ?_
    rw [hV_one_apply]
    have hx : ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 0)) ∈ ptSub φ z hb e := by
      rw [← range_ptHom he hb φ hzC hz]
      exact ⟨_, rfl⟩
    rw [mul_comm_of_isElementaryAbelian hBe h hx, mul_inv_cancel_right]

omit he hnd in
theorem stabilizer_conjClass_ptSub :
    MulAction.stabilizer 𝒩₁ (⟨z, self_mem_conjClass 𝒩₁ z⟩ : conjClass 𝒩₁ z) =
      Subgroup.subgroupOf 𝒩₁₀ 𝒩₁ := by
  rw [stabilizer_conjClass]
  ext n
  rw [mem_subgroupOf, mem_subgroupOf, mem_inf]
  exact ⟨fun h => ⟨n.2, h⟩, fun h => h.2⟩

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))

include he hnd hzC hsup hinf hz in
theorem ker_toPermHom_conjClass_ptSub (hfull₁ : conjClass 𝒩₁ z = z • (𝒜₁ : Set G)) :
    (MulAction.toPermHom 𝒩₁ (conjClass 𝒩₁ z)).ker = (ptSub φ z hb e).subgroupOf 𝒩₁ := by
  obtain ⟨-, hBe, -, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  ext m
  rw [mem_ker_toPermHom_conjClass, mem_subgroupOf]
  constructor
  · intro h
    refine mem_ptSub_of_forall_conj he hb hnd φ hzC hsup hinf hz fun v => ?_
    have hx : ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) ∈ conjClass 𝒩₁ z := by
      rw [hfull₁]
      exact (mem_smul_ptA_iff he hb φ hzC hz).2 ⟨v, rfl⟩
    have h1 := h _ hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · rintro hm x ⟨g, hg, rfl⟩
    have hxB : g * z * g⁻¹ ∈ ptSub φ z hb e :=
      (mem_normalizer_iff.1 hg z).1 (mem_sup_right (mem_zpowers z))
    rw [mul_comm_of_isElementaryAbelian hBe hm hxB, mul_inv_cancel_right]

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
