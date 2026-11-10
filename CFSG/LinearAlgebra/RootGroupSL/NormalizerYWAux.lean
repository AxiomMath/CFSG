module

public import CFSG.LinearAlgebra.RootGroupSL.Normalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LinearAlgebra.RootGroupSL.NormalizerYWAux

open CFSG.Open

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

@[expose] def yMap (g : DSpace E X ≃ₗ[k] DSpace E X) : E →ₗ[k] E where
  toFun b := (g (0, 0, b)).2.2
  map_add' b b' := by
    have h : ((0 : E), (0 : X), b + b') =
        ((0 : E), (0 : X), b) + ((0 : E), (0 : X), b') := by ext <;> simp
    rw [h, map_add]; rfl
  map_smul' c b := by
    have h : ((0 : E), (0 : X), c • b) =
        c • (((0 : E), (0 : X), b) : DSpace E X) := by ext <;> simp
    rw [h, map_smul]; rfl

@[expose] def wMap (g : DSpace E X ≃ₗ[k] DSpace E X) : E →ₗ[k] E where
  toFun e := (g (e, 0, 0)).1
  map_add' e e' := by
    have h : (e + e', (0 : X), (0 : E)) =
        ((e, (0 : X), (0 : E)) : DSpace E X) + (e', 0, 0) := by ext <;> simp
    rw [h, map_add]; rfl
  map_smul' c e := by
    have h : (c • e, (0 : X), (0 : E)) =
        c • (((e, (0 : X), (0 : E)) : DSpace E X)) := by ext <;> simp
    rw [h, map_smul]; rfl

theorem mem_flagK_iff {v : DSpace E X} : v ∈ flagK k E X ↔ v.2.2 = 0 :=
  Iff.rfl

theorem mem_flagW_iff {v : DSpace E X} : v ∈ flagW k E X ↔ v.2 = 0 :=
  Iff.rfl

@[simp] theorem yMap_apply (g : DSpace E X ≃ₗ[k] DSpace E X) (b : E) :
    yMap g b = (g (0, 0, b)).2.2 := rfl

@[simp] theorem wMap_apply (g : DSpace E X ≃ₗ[k] DSpace E X) (e : E) :
    wMap g e = (g (e, 0, 0)).1 := rfl

theorem yMap_one : yMap (1 : DSpace E X ≃ₗ[k] DSpace E X) = LinearMap.id := by
  ext b; simp

theorem wMap_one : wMap (1 : DSpace E X ≃ₗ[k] DSpace E X) = LinearMap.id := by
  ext e; simp

theorem yMap_mul {u v : DSpace E X ≃ₗ[k] DSpace E X}
    (hu : ∀ w : DSpace E X, w.2.2 = 0 → (u w).2.2 = 0) :
    yMap (u * v) = (yMap u).comp (yMap v) := by
  ext b
  have hz : (v (0, 0, b) - (0, 0, (v (0, 0, b)).2.2)).2.2 = 0 := by simp
  have h := hu _ hz
  have hdec : v (0, 0, b) = (0, 0, (v (0, 0, b)).2.2) +
      (v (0, 0, b) - (0, 0, (v (0, 0, b)).2.2)) := by abel
  calc yMap (u * v) b = (u (v (0, 0, b))).2.2 := rfl
    _ = (u ((0, 0, (v (0, 0, b)).2.2) +
          (v (0, 0, b) - (0, 0, (v (0, 0, b)).2.2)))).2.2 := by rw [← hdec]
    _ = (u (0, 0, (v (0, 0, b)).2.2) +
          u (v (0, 0, b) - (0, 0, (v (0, 0, b)).2.2))).2.2 := by rw [map_add]
    _ = (u (0, 0, (v (0, 0, b)).2.2)).2.2 +
          (u (v (0, 0, b) - (0, 0, (v (0, 0, b)).2.2))).2.2 := rfl
    _ = (u (0, 0, (v (0, 0, b)).2.2)).2.2 + 0 := by rw [h]
    _ = ((yMap u).comp (yMap v)) b := by simp [LinearMap.comp_apply]

theorem wMap_mul {u v : DSpace E X ≃ₗ[k] DSpace E X}
    (hv : ∀ w : DSpace E X, w ∈ flagW k E X → v w ∈ flagW k E X) :
    wMap (u * v) = (wMap u).comp (wMap v) := by
  ext e
  have hin : ((e, 0, 0) : DSpace E X) ∈ flagW k E X := by rw [mem_flagW_iff]; rfl
  have hmem : v (e, 0, 0) ∈ flagW k E X := hv _ hin
  have h2 : (v (e, 0, 0)).2 = 0 := by rwa [mem_flagW_iff] at hmem
  have h : v (e, 0, 0) = ((v (e, 0, 0)).1, (0 : X), (0 : E)) := by
    rw [← Prod.mk.eta (p := v (e, 0, 0)), h2]
    rfl
  calc wMap (u * v) e = (u (v (e, 0, 0))).1 := rfl
    _ = (u ((v (e, 0, 0)).1, 0, 0)).1 := by rw [h]
    _ = ((wMap u).comp (wMap v)) e := by simp [LinearMap.comp_apply]

@[expose] def PreservesK (u : DSpace E X ≃ₗ[k] DSpace E X) : Prop :=
  ∀ w : DSpace E X, w ∈ flagK k E X → u w ∈ flagK k E X

theorem preservesK_coord {u : DSpace E X ≃ₗ[k] DSpace E X} (hu : PreservesK u) :
    ∀ w : DSpace E X, w.2.2 = 0 → (u w).2.2 = 0 := fun w hw =>
  mem_flagK_iff.mp (hu w (mem_flagK_iff.mpr hw))

theorem preservesK_of_mem_normalizer {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))) :
    PreservesK g.toLinearEquiv := fun v hv =>
  (mem_flagK_iff_of_mem_normalizer hg v).mpr hv

theorem preservesW_of_mem_normalizer {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))) : ∀ w : DSpace E X, w ∈ flagW k E X → g.toLinearEquiv w ∈ flagW k E X :=
  fun v hv =>
  (mem_flagW_iff_of_mem_normalizer hg v).mpr hv

theorem rootEquiv_sub (t : E) (w : DSpace E X) :
    rootEquiv k X t w - w = (t * w.2.2, 0, 0) := by
  ext <;> simp [rootEquiv, shearE, LinearMap.mulLeft_apply]

theorem exists_linearEquiv_det_eq [Finite k] (hX : 0 < Module.finrank k X) (u : kˣ) :
    ∃ g : X ≃ₗ[k] X, LinearEquiv.det g = u := by
  classical
  let b := Module.Basis.ofVectorSpace k X
  let ι := Module.Basis.ofVectorSpaceIndex k X
  have hcard : 0 < Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b]; exact hX
  haveI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  let i₀ : ι := Classical.arbitrary ι
  let w : ι → kˣ := fun i => if i = i₀ then u else 1
  refine ⟨b.equiv (b.unitsSMul w) (Equiv.refl ι), ?_⟩
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hmat : LinearMap.toMatrix b b
      ((b.equiv (b.unitsSMul w) (Equiv.refl ι) : X ≃ₗ[k] X) : X →ₗ[k] X) =
      Matrix.diagonal (fun i => (w i : k)) := by
    rw [LinearMap.toMatrix_eq_basisToMatrix]
    have hfun : ((b.equiv (b.unitsSMul w) (Equiv.refl ι) : X ≃ₗ[k] X) : X →ₗ[k] X) ∘ b =
        b.unitsSMul w := by
      funext j
      simp only [Function.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      rfl
    rw [hfun, Module.Basis.toMatrix_unitsSMul]
    rfl
  rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal]
  have hprod : (∏ i : ι, (w i : k)) = (u : k) := by
    have h := Finset.prod_eq_single (s := Finset.univ) i₀
      (fun b _ hb => by
        change (((if b = i₀ then u else 1 : kˣ)) : k) = 1
        rw [if_neg hb]
        rfl)
      (fun h => absurd (Finset.mem_univ i₀) h)
    simpa [w] using h
  exact hprod

abbrev NN : Subgroup (SpecialLinearGroup k (DSpace E X)) :=
  Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))

theorem pCoreOf_le_ambient (p : ℕ) (H : Subgroup (SpecialLinearGroup k (DSpace E X))) :
    pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

theorem le_normalizer_pCoreOf (p : ℕ)
    (H : Subgroup (SpecialLinearGroup k (DSpace E X))) :
    H ≤ Subgroup.normalizer (pCoreOf p H : Set (SpecialLinearGroup k (DSpace E X))) := by
  have hforward : ∀ g ∈ H, ∀ x ∈ pCoreOf p H, g * x * g⁻¹ ∈ pCoreOf p H := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
      (CFSG.pCore_normal (p := p) (G := ↥H)).conj_mem y hy ⟨g, hg⟩, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hforward g hg x, fun hx => by
    have h := hforward g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x from by group] at h⟩

theorem eq_one_of_pow_two_pow_eq_one [CharP E 2] {x : E} {n : ℕ}
    (h : x ^ 2 ^ n = 1) : x = 1 := by
  have h2 : (x + 1) ^ 2 ^ n = 0 := by
    rw [add_pow_char_pow (R := E) (p := 2) (n := n) (x := x) (y := 1), h, one_pow]
    exact CharTwo.add_self_eq_zero 1
  have h3 : x + 1 = 0 := eq_zero_of_pow_eq_zero h2
  rw [← CharTwo.add_self_eq_zero (1 : E)] at h3
  exact add_right_cancel h3

theorem yMap_mul_mem {u v : SpecialLinearGroup k (DSpace E X)}
    (hu : u ∈ NN) (hv : v ∈ NN) :
    yMap (u.toLinearEquiv * v.toLinearEquiv) =
      (yMap u.toLinearEquiv).comp (yMap v.toLinearEquiv) :=
  yMap_mul (hu := preservesK_coord (preservesK_of_mem_normalizer hu))

theorem wMap_mul_mem {u v : SpecialLinearGroup k (DSpace E X)}
    (hu : u ∈ NN) (hv : v ∈ NN) :
    wMap (u.toLinearEquiv * v.toLinearEquiv) =
      (wMap u.toLinearEquiv).comp (wMap v.toLinearEquiv) :=
  wMap_mul (hv := preservesW_of_mem_normalizer hv)

theorem yMap_pow_mem {u : SpecialLinearGroup k (DSpace E X)} (hu : u ∈ NN) (n : ℕ) :
    yMap ((u ^ n).toLinearEquiv) = (yMap u.toLinearEquiv) ^ n := by
  induction n with
  | zero => rw [pow_zero, map_one, yMap_one, pow_zero]; rfl
  | succ n ih =>
      rw [pow_succ', map_mul, yMap_mul_mem hu (Subgroup.pow_mem _ hu n), ih, pow_succ']
      rfl

theorem wMap_pow_mem {u : SpecialLinearGroup k (DSpace E X)} (hu : u ∈ NN) (n : ℕ) :
    wMap ((u ^ n).toLinearEquiv) = (wMap u.toLinearEquiv) ^ n := by
  induction n with
  | zero => rw [pow_zero, map_one, wMap_one, pow_zero]; rfl
  | succ n ih =>
      rw [pow_succ', map_mul, wMap_mul_mem hu (Subgroup.pow_mem _ hu n), ih, pow_succ']
      rfl

theorem mulLeft_one' : LinearMap.mulLeft k (1 : E) = LinearMap.id := by
  ext x; simp [LinearMap.mulLeft_apply]

theorem mulLeft_pow (s : E) (n : ℕ) :
    (LinearMap.mulLeft k s) ^ n = LinearMap.mulLeft k (s ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mulLeft_one']; rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', ih, LinearMap.mulLeft_mul]
      rfl

theorem wMap_conj_yMap {g : SpecialLinearGroup k (DSpace E X)} (hg : g ∈ NN) (t : E) :
    ∃ s : E, wMap g.toLinearEquiv ∘ₗ LinearMap.mulLeft k t ∘ₗ
      yMap ((g⁻¹ : SpecialLinearGroup k (DSpace E X)).toLinearEquiv) = LinearMap.mulLeft k s := by
  have hmem : g * rootElt k X t * g⁻¹ ∈ rootSL k E X :=
    (Subgroup.mem_normalizer_iff.mp hg (rootElt k X t)).mp (rootElt_mem_rootSL t)
  obtain ⟨t', ht'⟩ := mem_rootSL_iff.mp hmem
  refine ⟨t', ?_⟩
  ext b
  let e : DSpace E X ≃ₗ[k] DSpace E X := g * rootElt k X t * g⁻¹
  have h1 : e ((0, 0, b) : DSpace E X) = rootEquiv k X t' ((0, 0, b) : DSpace E X) := by
    have hfun : ⇑e = ⇑(rootEquiv k X t') := by
      change ⇑(g * rootElt k X t * g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) = ⇑(rootEquiv k X t')
      rw [show (g * rootElt k X t * g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) =
        rootEquiv k X t' from ht']
    exact congrFun hfun (0, 0, b)
  have h2 : e ((0, 0, b) : DSpace E X) =
      (g : DSpace E X ≃ₗ[k] DSpace E X)
        (rootEquiv k X t ((g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) ((0, 0, b) : DSpace E X))) := by
    change (g * rootElt k X t * g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) ((0, 0, b) : DSpace E X) = _
    simp [map_mul, rootElt]
  rw [h2] at h1
  have happ : (g : DSpace E X ≃ₗ[k] DSpace E X)
      ((g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) ((0, 0, b) : DSpace E X)) =
      ((0, 0, b) : DSpace E X) := by
    have h : (g : DSpace E X ≃ₗ[k] DSpace E X) *
        (g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) = 1 := by
      simpa using mul_inv_cancel (g : DSpace E X ≃ₗ[k] DSpace E X)
    have := congrArg (fun f : DSpace E X ≃ₗ[k] DSpace E X =>
      f ((0, 0, b) : DSpace E X)) h
    simpa using this
  have h3 : (g : DSpace E X ≃ₗ[k] DSpace E X)
      ((rootEquiv k X t ((g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) ((0, 0, b) : DSpace E X))) -
        (g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) ((0, 0, b) : DSpace E X)) =
      rootEquiv k X t' ((0, 0, b) : DSpace E X) - ((0, 0, b) : DSpace E X) := by
    rw [map_sub, h1, happ]
  rw [rootEquiv_sub t ((g⁻¹ : DSpace E X ≃ₗ[k] DSpace E X) ((0, 0, b) : DSpace E X)),
    rootEquiv_sub t' ((0, 0, b) : DSpace E X)] at h3
  have h4 := congrArg Prod.fst h3
  simpa [wMap, yMap, LinearMap.mulLeft_apply] using h4

theorem yMap_conj {g : SpecialLinearGroup k (DSpace E X)} (hg : g ∈ NN) (t : E) :
    ∃ s : E, yMap g.toLinearEquiv ∘ₗ LinearMap.mulLeft k t ∘ₗ
      yMap ((g⁻¹ : SpecialLinearGroup k (DSpace E X)).toLinearEquiv) = LinearMap.mulLeft k s := by
  obtain ⟨t', ht'⟩ := wMap_conj_yMap hg t
  obtain ⟨s0, hs0⟩ := wMap_conj_yMap hg 1
  have hs0' : wMap g.toLinearEquiv ∘ₗ yMap ((g⁻¹).toLinearEquiv) =
      LinearMap.mulLeft k s0 := by
    simpa [mulLeft_one'] using hs0
  have hy_left : (yMap g.toLinearEquiv).comp (yMap ((g⁻¹).toLinearEquiv)) = LinearMap.id := by
    have h := yMap_mul_mem (u := g) (v := g⁻¹) hg (Subgroup.inv_mem _ hg)
    rw [show g.toLinearEquiv * (g⁻¹).toLinearEquiv = 1 by
      rw [← map_mul, mul_inv_cancel, map_one], yMap_one] at h
    exact h.symm
  have hy_right : (yMap ((g⁻¹).toLinearEquiv)).comp (yMap g.toLinearEquiv) = LinearMap.id := by
    have h := yMap_mul_mem (u := g⁻¹) (v := g) (Subgroup.inv_mem _ hg) hg
    rw [show (g⁻¹).toLinearEquiv * g.toLinearEquiv = 1 by
      rw [← map_mul, inv_mul_cancel, map_one], yMap_one] at h
    exact h.symm
  have hw_left : (wMap ((g⁻¹).toLinearEquiv)).comp (wMap g.toLinearEquiv) = LinearMap.id := by
    have h := wMap_mul_mem (u := g⁻¹) (v := g) (Subgroup.inv_mem _ hg) hg
    rw [show (g⁻¹).toLinearEquiv * g.toLinearEquiv = 1 by
      rw [← map_mul, inv_mul_cancel, map_one], wMap_one] at h
    exact h.symm
  have hy_left_apply : ∀ x : E, yMap g.toLinearEquiv (yMap ((g⁻¹).toLinearEquiv) x) = x := by
    intro x
    have := congrArg (fun f : E →ₗ[k] E => f x) hy_left
    simpa [LinearMap.comp_apply] using this
  have hw_left_apply : ∀ x : E, wMap ((g⁻¹).toLinearEquiv) (wMap g.toLinearEquiv x) = x := by
    intro x
    have := congrArg (fun f : E →ₗ[k] E => f x) hw_left
    simpa [LinearMap.comp_apply] using this
  have hyinj : Function.Injective (yMap ((g⁻¹).toLinearEquiv)) := by
    intro a b hab
    have h := congrArg (fun x => yMap g.toLinearEquiv x) hab
    rw [hy_left_apply a, hy_left_apply b] at h
    exact h
  have hwinj : Function.Injective (wMap g.toLinearEquiv) := by
    intro a b hab
    have h := congrArg (fun x => wMap ((g⁻¹).toLinearEquiv) x) hab
    rw [hw_left_apply a, hw_left_apply b] at h
    exact h
  have h1val : wMap g.toLinearEquiv (yMap ((g⁻¹).toLinearEquiv) (1 : E)) = s0 := by
    have h := congrArg (fun f : E →ₗ[k] E => f 1) hs0'
    simpa [LinearMap.comp_apply, LinearMap.mulLeft_apply] using h
  have h0val : wMap g.toLinearEquiv (yMap ((g⁻¹).toLinearEquiv) 0) = 0 := by
    have h := congrArg (fun f : E →ₗ[k] E => f 0) hs0'
    simpa [LinearMap.comp_apply, LinearMap.mulLeft_apply] using h
  have hs0ne : s0 ≠ 0 := by
    intro h0
    have hz : yMap ((g⁻¹).toLinearEquiv) (1 : E) = yMap ((g⁻¹).toLinearEquiv) 0 := by
      apply hwinj
      rw [h1val, h0val, h0]
    exact one_ne_zero (hyinj hz)
  have hwdecomp : wMap g.toLinearEquiv =
      (LinearMap.mulLeft k s0).comp (yMap g.toLinearEquiv) := by
    rw [← hs0', LinearMap.comp_assoc, hy_right, LinearMap.comp_id]
  have hm : (LinearMap.mulLeft k s0).comp ((yMap g.toLinearEquiv).comp
      ((LinearMap.mulLeft k t).comp (yMap ((g⁻¹).toLinearEquiv)))) =
      LinearMap.mulLeft k t' := by
    rw [← LinearMap.comp_assoc, ← hwdecomp]
    simpa [LinearMap.comp_assoc] using ht'
  refine ⟨s0⁻¹ * t', ?_⟩
  ext x
  have hx := congrArg (fun f : E →ₗ[k] E => f x) hm
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at hx ⊢
  have key : yMap g.toLinearEquiv (t * yMap ((g⁻¹).toLinearEquiv) x) = s0⁻¹ * (t' * x) := by
    have hcancel := inv_mul_cancel_left₀ hs0ne
      (yMap g.toLinearEquiv (t * yMap ((g⁻¹).toLinearEquiv) x))
    rw [← hcancel, hx]
  rw [key, ← mul_assoc]

end CFSG.LinearAlgebra.RootGroupSL.NormalizerYWAux
