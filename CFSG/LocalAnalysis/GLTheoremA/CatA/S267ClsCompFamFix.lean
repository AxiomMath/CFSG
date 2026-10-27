module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamOut
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Matrix Module CFSG.GroupTheory.SteinbergBK

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

section Ext

variable {F : Subfield K} {E : Type*} [AddCommGroup E] [Module K E] {E₀ : Submodule F E}
  {m : ℕ} (b : Basis (Fin m) K E) (b₀ : Basis (Fin m) F E₀) (hb : ∀ i, (b₀ i : E) = b i)

@[expose] noncomputable def extLin (g : E₀ →ₗ[F] E₀) : E →ₗ[K] E :=
  b.constr K fun i => (g (b₀ i) : E)

theorem extLin_apply_basis (g : E₀ →ₗ[F] E₀) (i : Fin m) : extLin b b₀ g (b i) = g (b₀ i) :=
  b.constr_basis K _ i

include hb in
theorem extLin_apply_mem (g : E₀ →ₗ[F] E₀) (x : E₀) : extLin b b₀ g x = g x := by
  have hx : (x : E) = ∑ i, ((b₀.repr x i : F) : K) • b i := by
    conv_lhs => rw [← b₀.sum_repr x]
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, Subfield.smul_def, hb]
  have hgx : (g x : E) = ∑ i, ((b₀.repr x i : F) : K) • (g (b₀ i) : E) := by
    conv_lhs => rw [← b₀.sum_repr x]
    rw [map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul, Subfield.smul_def]
  rw [hx, hgx, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, extLin_apply_basis]

@[expose] noncomputable def extEquiv (g : E₀ ≃ₗ[F] E₀) : E ≃ₗ[K] E :=
  LinearEquiv.ofLinear (extLin b b₀ g.toLinearMap) (extLin b b₀ g.symm.toLinearMap)
    (b.ext fun i => by
      rw [LinearMap.comp_apply, extLin_apply_basis, extLin_apply_mem b b₀ hb, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply, hb])
    (b.ext fun i => by
      rw [LinearMap.comp_apply, extLin_apply_basis, extLin_apply_mem b b₀ hb, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.id_apply, hb])

theorem extEquiv_apply_mem (g : E₀ ≃ₗ[F] E₀) (x : E₀) : extEquiv b b₀ hb g x = g x :=
  extLin_apply_mem b b₀ hb g.toLinearMap x

theorem extEquiv_apply_basis (g : E₀ ≃ₗ[F] E₀) (i : Fin m) : extEquiv b b₀ hb g (b i) = g (b₀ i) :=
  extLin_apply_basis b b₀ g.toLinearMap i

@[expose] noncomputable def extHom' : (E₀ ≃ₗ[F] E₀) →* (E ≃ₗ[K] E) where
  toFun := extEquiv b b₀ hb
  map_one' := LinearEquiv.toLinearMap_injective (b.ext fun i => by
    rw [LinearEquiv.coe_coe, extEquiv_apply_basis, LinearEquiv.coe_coe, LinearEquiv.coe_one,
      id, hb]
    rfl)
  map_mul' g g' := LinearEquiv.toLinearMap_injective (b.ext fun i => by
    rw [LinearEquiv.coe_coe, extEquiv_apply_basis, LinearEquiv.coe_coe, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, extEquiv_apply_basis, ← extEquiv_apply_mem b b₀ hb g (g' (b₀ i))])

theorem extHom'_apply (g : E₀ ≃ₗ[F] E₀) : extHom' b b₀ hb g = extEquiv b b₀ hb g :=
  rfl

theorem extHom'_injective : Function.Injective (extHom' b b₀ hb) := fun g g' h =>
  LinearEquiv.ext fun x => Subtype.ext (by
    rw [← extEquiv_apply_mem b b₀ hb g x, ← extEquiv_apply_mem b b₀ hb g' x]
    exact congrArg (fun e : E ≃ₗ[K] E => e (x : E)) h)

@[expose] noncomputable def resFix (e : E ≃ₗ[K] E) (he : ∀ x ∈ E₀, e x ∈ E₀)
    (he' : ∀ x ∈ E₀, e.symm x ∈ E₀) : E₀ ≃ₗ[F] E₀ where
  toFun x := ⟨e x, he x x.2⟩
  invFun x := ⟨e.symm x, he' x x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by
    simp only [Submodule.coe_smul, Subfield.smul_def, map_smul, RingHom.id_apply])
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)

theorem coe_resFix_apply (e : E ≃ₗ[K] E) (he : ∀ x ∈ E₀, e x ∈ E₀)
    (he' : ∀ x ∈ E₀, e.symm x ∈ E₀) (x : E₀) : (resFix e he he' x : E) = e x :=
  rfl

theorem extEquiv_resFix (e : E ≃ₗ[K] E) (he : ∀ x ∈ E₀, e x ∈ E₀)
    (he' : ∀ x ∈ E₀, e.symm x ∈ E₀) : extEquiv b b₀ hb (resFix e he he') = e :=
  LinearEquiv.toLinearMap_injective (b.ext fun i => by
    rw [LinearEquiv.coe_coe, extEquiv_apply_basis, coe_resFix_apply, LinearEquiv.coe_coe, hb])

theorem extEquiv_comm {σ : K →+* K} (a : E ≃+ E) (ha : ∀ (c : K) (v : E), a (c • v) = σ c • a v)
    (hfix : ∀ x : E₀, a x = x) (g : E₀ ≃ₗ[F] E₀) (v : E) :
    a (extEquiv b b₀ hb g v) = extEquiv b b₀ hb g (a v) := by
  have hab : ∀ i, a (b i) = b i := fun i => by rw [← hb]; exact hfix (b₀ i)
  conv_lhs => rw [← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, ha, extEquiv_apply_basis, hab, hfix]

end Ext

section Fix

variable (A : GL ι K) (σ : K ≃+* K) (U : Submodule K (ι → K))

@[expose] def fixU : Submodule (semilinearFixedSubfield σ) U where
  carrier := {u | ModelGen.semiMap A σ (u : ι → K) = u}
  add_mem' {u v} hu hv := by
    change ModelGen.semiMap A σ ((u : ι → K) + v) = (u : ι → K) + v
    rw [map_add, hu, hv]
  zero_mem' := by
    change ModelGen.semiMap A σ (0 : ι → K) = 0
    exact map_zero _
  smul_mem' c u hu := by
    have hc : σ (c : K) = c := RingHom.mem_eqLocusField.1 c.2
    change ModelGen.semiMap A σ ((c : K) • (u : ι → K)) = (c : K) • (u : ι → K)
    rw [ModelGen.semiMap_smul, hu, hc]

theorem mem_fixU {u : U} : u ∈ fixU A σ U ↔ ModelGen.semiMap A σ (u : ι → K) = u :=
  Iff.rfl

variable {τ : K →+* K}

@[expose] def isomU₀ (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K) {F : Subfield K}
    (U₀ : Submodule F U) : Subgroup (U₀ ≃ₗ[F] U₀) where
  carrier := {g | ∀ x y : U₀, β ((g x : U) : ι → K) ((g y : U) : ι → K) = β ((x : U) : ι → K)
    ((y : U) : ι → K)}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x y := (hg _ _).trans (hh x y)
  inv_mem' {g} hg x y := by
    have h := hg (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem mem_isomU₀ {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} {F : Subfield K} {U₀ : Submodule F U}
    {g : U₀ ≃ₗ[F] U₀} : g ∈ isomU₀ U β U₀ ↔
      ∀ x y : U₀, β ((g x : U) : ι → K) ((g y : U) : ι → K) =
        β ((x : U) : ι → K) ((y : U) : ι → K) :=
  Iff.rfl

end Fix

section Basis

@[expose] noncomputable def semiU (A : GL ι K) (σ : K ≃+* K) {p : ℕ} (hp : 0 < p)
    (hσp : σ ^ p = 1) (U : Submodule K (ι → K)) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) :
    U ≃+ U where
  toFun u := ⟨ModelGen.semiMap A σ u, hU u u.2⟩
  invFun u := ⟨(ModelGen.semiMap A σ)^[p - 1] u, semiMap_iterate_mem hU (p - 1) u.2⟩
  left_inv u := Subtype.ext (by
    show (ModelGen.semiMap A σ)^[p - 1] (ModelGen.semiMap A σ u) = u
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
      ModelGen.semiMap_iterate_eq_self A hσp])
  right_inv u := Subtype.ext (by
    show ModelGen.semiMap A σ ((ModelGen.semiMap A σ)^[p - 1] u) = u
    rw [show ModelGen.semiMap A σ ((ModelGen.semiMap A σ)^[p - 1] (u : ι → K)) =
        (ModelGen.semiMap A σ)^[p - 1 + 1] u from (Function.iterate_succ_apply' _ _ _).symm,
      Nat.sub_add_cancel hp, ModelGen.semiMap_iterate_eq_self A hσp])
  map_add' u v := Subtype.ext (map_add (ModelGen.semiMap A σ) (u : ι → K) v)

variable {A : GL ι K} {σ : K ≃+* K} {p : ℕ} (hp : 0 < p) (hσp : σ ^ p = 1)
  {U : Submodule K (ι → K)} (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)

theorem semiU_smul (c : K) (u : U) :
    semiU A σ hp hσp U hU (c • u) = σ c • semiU A σ hp hσp U hU u :=
  Subtype.ext (ModelGen.semiMap_smul A σ c u)

theorem coe_semiU_iterate (n : ℕ) (u : U) :
    (((⇑(semiU A σ hp hσp U hU))^[n] u : U) : ι → K) = (ModelGen.semiMap A σ)^[n] u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

theorem fixU_eq : fixU A σ U =
    semilinearFixedSubmodule σ (semiU A σ hp hσp U hU) (semiU_smul hp hσp hU) := by
  ext u
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

include hp hσp hU in
theorem exists_fixBasis [Finite K] (hσ : orderOf σ = p) :
    ∃ (b : Basis (Fin (finrank K U)) K U)
      (b₀ : Basis (Fin (finrank K U)) (semilinearFixedSubfield σ) (fixU A σ U)),
      ∀ i, (b₀ i : U) = b i := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨r, -, n, hr, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = r ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨-, -, b, b₀, -, hb, -, -⟩ := coprime_finite_field_semilinear_fixed_basis hr n.pos hK σ hσ
    rfl (semiU A σ hp hσp U hU) (semiU_smul hp hσp hU) fun v => Subtype.ext (by
      rw [coe_semiU_iterate, ModelGen.semiMap_iterate_eq_self A hσp])
  exact ⟨b, b₀.map (LinearEquiv.ofEq _ _ (fixU_eq hp hσp hU).symm), fun i => by
    rw [Basis.map_apply]
    exact hb i⟩

end Basis

section Layer

variable {τ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

theorem extEquiv_mem_isomU {U : Submodule K (ι → K)} {F : Subfield K} {U₀ : Submodule F U}
    {m : ℕ} (b : Basis (Fin m) K U) (b₀ : Basis (Fin m) F U₀) (hb : ∀ i, (b₀ i : U) = b i)
    {g : U₀ ≃ₗ[F] U₀} (hg : g ∈ isomU₀ U β U₀) : extEquiv b b₀ hb g ∈ isomU β U := by
  intro x y
  have key := LinearMap.ext_basis b b
    (B := (β.comp (U.subtype ∘ₗ (extEquiv b b₀ hb g).toLinearMap)).compl₂
      (U.subtype ∘ₗ (extEquiv b b₀ hb g).toLinearMap))
    (B' := (β.comp U.subtype).compl₂ U.subtype) fun i j => by
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe]
      rw [← hb i, ← hb j, extEquiv_apply_mem, extEquiv_apply_mem]
      exact hg (b₀ i) (b₀ j)
  exact congrArg (fun B : U →ₗ[K] U →ₛₗ[τ] K => B x y) key

theorem conj_mem_commutator_self {G : Type*} [Group G] {H : Subgroup G} {x c : G} (hx : x ∈ H)
    (hc : c ∈ ⁅H, H⁆) : x * c * x⁻¹ ∈ ⁅H, H⁆ := by
  have hN := Subgroup.normal_subgroupOf_commutator_sup H H
  have hxs : x ∈ H ⊔ H := Subgroup.mem_sup_left hx
  have hcs : c ∈ H ⊔ H := Subgroup.mem_sup_left (Subgroup.commutator_le_self H hc)
  have h := hN.conj_mem ⟨c, hcs⟩ (Subgroup.mem_subgroupOf.2 hc) ⟨x, hxs⟩
  exact Subgroup.mem_subgroupOf.1 h

variable {U W : Submodule K (ι → K)}

theorem glEquiv_eq_extU (hUW : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0)
    {h : GL ι K} (hh : h ∈ blkSub β U W) :
    glEquiv h = extU hUW ((blkSubEquiv hUW horth ⟨h, hh⟩ : isomU β U) : U ≃ₗ[K] U) :=
  linearEquiv_ext_of_isCompl hUW
    (fun u hu => by rw [extU_apply_mem hUW _ ⟨u, hu⟩, coe_blkSubEquiv_apply])
    (fun w hw => by rw [extU_apply_mem_right hUW _ ⟨w, hw⟩, hh.2.2 w hw])

theorem extU_comm_semiMap (hUW : IsCompl U W) {A : GL ι K} {σ : K ≃+* K}
    (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) (hW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W)
    {e : U ≃ₗ[K] U} (he : ∀ u : U, ModelGen.semiMap A σ (e u : ι → K) = e ⟨_, hU u u.2⟩)
    (v : ι → K) : extU hUW e (ModelGen.semiMap A σ v) = ModelGen.semiMap A σ (extU hUW e v) := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1
    (show v ∈ U ⊔ W by rw [hUW.sup_eq_top]; trivial)
  rw [map_add, (extU hUW e).map_add, (extU hUW e).map_add, extU_apply_mem hUW e ⟨u, hu⟩,
    extU_apply_mem hUW e ⟨_, hU u hu⟩, extU_apply_mem_right hUW e ⟨w, hw⟩,
    extU_apply_mem_right hUW e ⟨_, hW w hw⟩, map_add, he ⟨u, hu⟩]

theorem glaPLayer_ne_bot_of_fix [Finite K] (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) {A : GL ι K} {σ : K ≃+* K} {p : ℕ}
    (hp : p.Prime) (hσ : orderOf σ = p) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    (hW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W)
    (hq : CFSG.Open.IsQuasisimple ↥⁅isomU₀ U β (fixU A σ U), isomU₀ U β (fixU A σ U)⁆)
    (hdvd : p ∣ Nat.card ↥⁅isomU₀ U β (fixU A σ U), isomU₀ U β (fixU A σ U)⁆) :
    CFSG.Open.GLAPLayer p (blkI β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥ := by
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨b, b₀, hb⟩ := exists_fixBasis hp.pos hσp hU hσ
  set G₀ := isomU₀ U β (fixU A σ U) with hG₀
  set φ : ((fixU A σ U) ≃ₗ[semilinearFixedSubfield σ] (fixU A σ U)) →* GL ι K :=
    glEquiv.symm.toMonoidHom.comp ((extHom hUW).comp (extHom' b b₀ hb)) with hφ
  have hφapp : ∀ g, glEquiv (φ g) = extU hUW (extEquiv b b₀ hb g) := fun g =>
    MulEquiv.apply_symm_apply _ _
  have hφinj : Function.Injective φ := by
    intro g g' h
    apply extHom'_injective b b₀ hb
    rw [extHom'_apply, extHom'_apply]
    have h1 := congrArg glEquiv h
    rw [hφapp, hφapp] at h1
    exact LinearEquiv.ext fun u => Subtype.ext (by
      have := congrArg (fun e : (ι → K) ≃ₗ[K] (ι → K) => e (u : ι → K)) h1
      simpa only [extU_apply_mem hUW] using this)
  have hfix : ∀ x : fixU A σ U, semiU A σ hp.pos hσp U hU x = x := fun x => Subtype.ext x.2
  have hcomm : ∀ (g : (fixU A σ U) ≃ₗ[semilinearFixedSubfield σ] (fixU A σ U)) (u : U),
      ModelGen.semiMap A σ (extEquiv b b₀ hb g u : ι → K) =
        extEquiv b b₀ hb g ⟨_, hU u u.2⟩ := fun g u => by
    have h := extEquiv_comm b b₀ hb (σ := (σ : K →+* K)) (semiU A σ hp.pos hσp U hU)
      (semiU_smul hp.pos hσp hU) hfix g u
    exact congrArg Subtype.val h
  have hφC : ∀ g, φ g ∈ centGL {(ModelGen.semiMap A σ).toAddMonoidHom} := by
    intro g
    rw [mem_centGL]
    rintro s rfl v
    rw [hφapp]
    exact extU_comm_semiMap hUW hU hW (hcomm g) v
  have hφG : G₀.map φ ≤ blkSub β U W := by
    rintro _ ⟨g, hg, rfl⟩
    have h := extU_mem_blkSub hUW horth (extEquiv_mem_isomU b b₀ hb hg)
    rwa [show glEquiv.symm (extU hUW (extEquiv b b₀ hb g)) = φ g from rfl] at h
  set H := blkI β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom} with hH
  set L := (⁅G₀, G₀⁆ : Subgroup _).map φ with hL
  have hLH : L ≤ H := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨?_, hφC g⟩
    have h := Subgroup.mem_map_of_mem φ hg
    rw [Subgroup.map_commutator] at h
    exact Subgroup.commutator_mono hφG hφG h
  have hLn : (L.subgroupOf H).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨g₀, hg₀, hgn⟩ := hn
    have hxS : (x : GL ι K) ∈ blkSub β U W := blkI_le_blkSub β U W x.2.1
    set e : U ≃ₗ[K] U := ((blkSubEquiv hUW horth ⟨(x : GL ι K), hxS⟩ : isomU β U) : U ≃ₗ[K] U)
      with he
    have hxe : glEquiv (x : GL ι K) = extU hUW e := glEquiv_eq_extU hUW horth hxS
    have hxa : ∀ v, glEquiv (x : GL ι K) (ModelGen.semiMap A σ v) =
        ModelGen.semiMap A σ (glEquiv (x : GL ι K) v) := fun v =>
      (mem_centGL.1 x.2.2) _ rfl v
    have heU : ∀ u : U, (e u : ι → K) = glEquiv (x : GL ι K) u := fun u => rfl
    have he0 : ∀ y ∈ fixU A σ U, e y ∈ fixU A σ U := fun y hy => by
      rw [mem_fixU, heU, ← hxa, hy]
    have he0' : ∀ y ∈ fixU A σ U, e.symm y ∈ fixU A σ U := fun y hy => by
      rw [mem_fixU]
      apply (glEquiv (x : GL ι K)).injective
      rw [← heU, LinearEquiv.apply_symm_apply, hxa, ← heU, LinearEquiv.apply_symm_apply]
      exact hy.symm ▸ rfl
    set r := resFix e he0 he0' with hr
    have hrG : r ∈ G₀ := fun y y' => by
      rw [coe_resFix_apply, coe_resFix_apply]
      exact (blkSubEquiv hUW horth ⟨(x : GL ι K), hxS⟩).2 y y'
    have hre : extEquiv b b₀ hb r = e := extEquiv_resFix b b₀ hb e he0 he0'
    refine ⟨r * g₀ * r⁻¹, conj_mem_commutator_self hrG hg₀, ?_⟩
    apply glEquiv.injective
    rw [hφapp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgn, map_mul, map_mul,
      map_inv, hxe, hφapp]
    rw [show extEquiv b b₀ hb (r * g₀ * r⁻¹) =
      extEquiv b b₀ hb r * extEquiv b b₀ hb g₀ * (extEquiv b b₀ hb r)⁻¹ by
        rw [← extHom'_apply, map_mul, map_mul, map_inv]; rfl, hre]
    rw [show extU hUW (e * extEquiv b b₀ hb g₀ * e⁻¹) =
      extU hUW e * extU hUW (extEquiv b b₀ hb g₀) * (extU hUW e)⁻¹ by
        rw [show extU hUW (e * extEquiv b b₀ hb g₀ * e⁻¹) =
          extHom hUW (e * extEquiv b b₀ hb g₀ * e⁻¹) from rfl, map_mul, map_mul, map_inv]
        rfl]
  have e := Subgroup.equivMapOfInjective (⁅G₀, G₀⁆ : Subgroup _) φ hφinj
  have hLq : CFSG.Open.IsQuasisimple ↥L := CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq
  have hLp : p ∣ Nat.card ↥L := by
    rw [← Nat.card_congr e.toEquiv]
    exact hdvd
  have hcomp := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hLq hLp hLH hLn
  intro hbot
  have hle : L ≤ CFSG.Open.GLAPLayer p H := le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hcomp hle

end Layer

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
