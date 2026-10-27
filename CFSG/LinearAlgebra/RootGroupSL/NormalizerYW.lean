module

public import CFSG.LinearAlgebra.RootGroupSL.NormalizerYWAux
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open NormalizerYWAux

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

theorem exists_mul_algEquiv_of_normalizes_mulLeft (b : E ≃ₗ[k] E)
    (hb : ∀ t : E, ∃ s : E,
      b.toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ b.symm.toLinearMap = LinearMap.mulLeft k s) :
    ∃ (c : Eˣ) (τ : E ≃ₐ[k] E), ∀ x : E, b x = (c : E) * τ x := by
  classical
  choose s hs using hb
  have hkey : ∀ t x : E, b (t * x) = s t * b x := by
    intro t x
    have h := congrArg (fun f : E →ₗ[k] E => f (b x)) (hs t)
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at h
    exact h
  have hbc : ∀ t : E, b t = s t * b 1 := by
    intro t
    simpa using hkey t 1
  have hc0 : b 1 ≠ 0 := by
    intro h
    have hb1 : b 1 = b 0 := by simpa using h
    exact one_ne_zero (b.injective hb1)
  let c : Eˣ := Units.mk0 (b 1) hc0
  have hc : (c : E) = b 1 := rfl
  have hs_mul : ∀ x y : E, s (x * y) = s x * s y := by
    intro x y
    apply mul_right_cancel₀ hc0
    calc s (x * y) * b 1 = b (x * y) := (hbc (x * y)).symm
      _ = s x * b y := hkey x y
      _ = s x * (s y * b 1) := by rw [hbc y]
      _ = (s x * s y) * b 1 := (mul_assoc _ _ _).symm
  have hs_add : ∀ x y : E, s (x + y) = s x + s y := by
    intro x y
    apply mul_right_cancel₀ hc0
    calc s (x + y) * b 1 = b (x + y) := (hbc (x + y)).symm
      _ = b x + b y := map_add b x y
      _ = s x * b 1 + s y * b 1 := by rw [hbc x, hbc y]
      _ = (s x + s y) * b 1 := (add_mul _ _ _).symm
  have hs_one : s 1 = 1 := by
    apply mul_right_cancel₀ hc0
    calc s 1 * b 1 = b 1 := (hbc 1).symm
      _ = 1 * b 1 := (one_mul _).symm
  have hs_zero : s 0 = 0 := by
    have h : s 0 * b 1 = 0 := by
      calc s 0 * b 1 = b 0 := (hbc 0).symm
        _ = 0 := b.map_zero
    exact (mul_eq_zero.mp h).resolve_right hc0
  have hs_commutes : ∀ a : k, s (algebraMap k E a) = algebraMap k E a := by
    intro a
    have h1 : b (algebraMap k E a) = a • b 1 := by
      rw [Algebra.algebraMap_eq_smul_one (R := k) (A := E) a, map_smul]
    have h2 : a • b 1 = algebraMap k E a * b 1 := by
      rw [Algebra.smul_def]
    apply mul_right_cancel₀ hc0
    rw [← hbc (algebraMap k E a), h1, h2]
  have hs_eq : ∀ x : E, s x = (c : E)⁻¹ * b x := by
    intro x
    rw [hbc x, ← hc, mul_comm (s x) (c : E), ← mul_assoc]
    rw [inv_mul_cancel₀ (Units.ne_zero c), one_mul]
  let τ : E →ₐ[k] E :=
    { toFun := s
      map_one' := hs_one
      map_mul' := hs_mul
      map_zero' := hs_zero
      map_add' := hs_add
      commutes' := hs_commutes }
  have hbij : Function.Bijective τ := by
    constructor
    · intro x y hxy
      have hxy' : (c : E)⁻¹ * b x = (c : E)⁻¹ * b y := by
        rw [← hs_eq x, ← hs_eq y]
        exact hxy
      exact b.injective (mul_left_cancel₀ (inv_ne_zero (Units.ne_zero c)) hxy')
    · intro y
      refine ⟨b.symm ((c : E) * y), ?_⟩
      rw [show τ (b.symm ((c : E) * y)) = s (b.symm ((c : E) * y)) from rfl, hs_eq,
        b.apply_symm_apply, ← mul_assoc]
      rw [inv_mul_cancel₀ (Units.ne_zero c), one_mul]
  refine ⟨c, AlgEquiv.ofBijective τ hbij, ?_⟩
  intro x
  change b x = (c : E) * s x
  rw [hbc x, ← hc, mul_comm]

private noncomputable def detElt (hX : 0 < Module.finrank k X) (u : kˣ) : X ≃ₗ[k] X :=
  Classical.choose (exists_linearEquiv_det_eq (k := k) (X := X) hX u)

private theorem detElt_spec (hX : 0 < Module.finrank k X) (u : kˣ) :
    LinearEquiv.det (detElt (k := k) (X := X) hX u) = u :=
  Classical.choose_spec (exists_linearEquiv_det_eq (k := k) (X := X) hX u)

private noncomputable def hElt (hX : 0 < Module.finrank k X) (s : Eˣ) :
    SpecialLinearGroup k (DSpace E X) :=
  blockSL (mulLeftEquiv k s)
    (detElt (k := k) (X := X) hX ((LinearEquiv.det (mulLeftEquiv k s))⁻¹ ^ 2))
    (mulLeftEquiv k s)
    (by
      rw [detElt_spec]
      group)

private theorem hElt_mem (hX : 0 < Module.finrank k X) (s : Eˣ) :
    hElt (X := X) hX s ∈ NN := by
  rw [hElt, blockSL_mem_normalizer_iff]
  intro t
  refine ⟨t, ?_⟩
  ext x
  simp [mulLeftEquiv, LinearMap.mulLeft, LinearMap.comp_apply, mul_assoc, mul_comm, mul_left_comm]

private theorem hElt_yMap (hX : 0 < Module.finrank k X) (s : Eˣ) :
    yMap (hElt (X := X) hX s).toLinearEquiv = LinearMap.mulLeft k (s : E) := by
  ext x
  simp [hElt, yMap, blockSL, blockDiag, mulLeftEquiv, LinearMap.mulLeft]

private noncomputable def yEquivHom :
    NN (k := k) (E := E) (X := X) →* (E ≃ₗ[k] E) where
  toFun u := LinearEquiv.ofLinearMap (yMap u.1.toLinearEquiv)
    (yMap (u.1⁻¹).toLinearEquiv)
    (by
      rw [← yMap_mul_mem (u := u.1) (v := u.1⁻¹) u.2 (Subgroup.inv_mem _ u.2)]
      rw [show u.1.toLinearEquiv * (u.1⁻¹).toLinearEquiv = 1 by
        rw [← map_mul, mul_inv_cancel, map_one], yMap_one])
    (by
      rw [← yMap_mul_mem (u := u.1⁻¹) (v := u.1) (Subgroup.inv_mem _ u.2) u.2]
      rw [show (u.1⁻¹).toLinearEquiv * u.1.toLinearEquiv = 1 by
        rw [← map_mul, inv_mul_cancel, map_one], yMap_one])
  map_one' := by
    ext x; simp [yMap_one]
  map_mul' u v := by
    ext x
    have h : yMap ((u * v).1.toLinearEquiv) =
        (yMap u.1.toLinearEquiv).comp (yMap v.1.toLinearEquiv) := by
      rw [show (u * v).1 = u.1 * v.1 from rfl, map_mul]
      exact yMap_mul_mem u.2 v.2
    simpa [LinearMap.comp_apply] using congrFun (congrArg DFunLike.coe h) x

private theorem yEquivHom_apply (u : NN (k := k) (E := E) (X := X)) :
    (yEquivHom u).toLinearMap = yMap u.1.toLinearEquiv := rfl

private theorem mulLeftEquiv_symm_apply (s : Eˣ) (x : E) :
    (mulLeftEquiv k s).symm x = (s : E)⁻¹ * x := by
  change LinearMap.mulLeft k ((s⁻¹ : Eˣ) : E) x = (s : E)⁻¹ * x
  rw [LinearMap.mulLeft_apply, Units.val_inv_eq_inv_val]

theorem pCoreOf_normalizer_trivial_on_quotient (hX : 0 < Module.finrank k X)
    {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ pCoreOf 2
      (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))))
    (v : DSpace E X) : g v - v ∈ flagK k E X := by
  haveI hcharE : CharP E 2 := CharP.of_ringHom_of_ne_zero (algebraMap k E) 2 (by norm_num)
  have hgN : g ∈ NN := pCoreOf_le_ambient 2 NN hg
  have hy_left : (yMap g.toLinearEquiv).comp (yMap ((g⁻¹).toLinearEquiv)) = LinearMap.id := by
    have h := yMap_mul_mem (u := g) (v := g⁻¹) hgN (Subgroup.inv_mem _ hgN)
    rw [show g.toLinearEquiv * (g⁻¹).toLinearEquiv = 1 by
      rw [← map_mul, mul_inv_cancel, map_one], yMap_one] at h
    exact h.symm
  have hy_right : (yMap ((g⁻¹).toLinearEquiv)).comp (yMap g.toLinearEquiv) = LinearMap.id := by
    have h := yMap_mul_mem (u := g⁻¹) (v := g) (Subgroup.inv_mem _ hgN) hgN
    rw [show (g⁻¹).toLinearEquiv * g.toLinearEquiv = 1 by
      rw [← map_mul, inv_mul_cancel, map_one], yMap_one] at h
    exact h.symm
  let ye : E ≃ₗ[k] E := LinearEquiv.ofLinearMap (yMap g.toLinearEquiv)
    (yMap ((g⁻¹).toLinearEquiv)) hy_left hy_right
  have hye_to : ye.toLinearMap = yMap g.toLinearEquiv := rfl
  have hye_symm : ye.symm.toLinearMap = yMap ((g⁻¹).toLinearEquiv) := rfl
  have hrel : ∀ t : E, ∃ s : E,
      ye.toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ ye.symm.toLinearMap = LinearMap.mulLeft k s := by
    intro t
    obtain ⟨s, hs⟩ := yMap_conj hgN t
    exact ⟨s, by rw [hye_to, hye_symm]; exact hs⟩
  obtain ⟨c, τ, hcτ⟩ := exists_mul_algEquiv_of_normalizes_mulLeft ye hrel
  have hβτ : ∀ x : E, yMap g.toLinearEquiv x = (c : E) * τ x := fun x => hcτ x
  have hτ_unit : ∀ s : Eˣ, τ (s : E) = (s : E) := by
    intro s
    let hh : SpecialLinearGroup k (DSpace E X) := hElt hX s
    have hh_mem : hh ∈ NN := hElt_mem hX s
    let O : Subgroup (SpecialLinearGroup k (DSpace E X)) := pCoreOf 2 NN
    have hnormO : NN ≤ Subgroup.normalizer (O : Set (SpecialLinearGroup k (DSpace E X))) :=
      le_normalizer_pCoreOf 2 NN
    have hkO : hh * g * hh⁻¹ * g⁻¹ ∈ O := by
      refine O.mul_mem ?_ (O.inv_mem hg)
      exact (Subgroup.mem_normalizer_iff.mp (hnormO hh_mem) g).mp hg
    have hkNN : hh * g * hh⁻¹ * g⁻¹ ∈ NN := pCoreOf_le_ambient 2 NN hkO
    haveI hOpg : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2) (G := ↥NN)).map NN.subtype
    obtain ⟨n, hn⟩ := isPGroup_iff_pow_pow_eq_one.mp hOpg
      (⟨hh * g * hh⁻¹ * g⁻¹, hkO⟩ : O)
    have hkpow : (hh * g * hh⁻¹ * g⁻¹) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hhom_hh : yEquivHom (⟨hh, hh_mem⟩ : NN) = mulLeftEquiv k s := by
      apply LinearEquiv.ext
      intro x
      change yMap hh.toLinearEquiv x = (mulLeftEquiv k s) x
      rw [show yMap hh.toLinearEquiv = LinearMap.mulLeft k (s : E) from hElt_yMap hX s]
      rfl
    have hhom_g : yEquivHom (⟨g, hgN⟩ : NN) = ye := by
      apply LinearEquiv.ext
      intro x; rfl
    have hhom_comm : yEquivHom (⟨hh * g * hh⁻¹ * g⁻¹, hkNN⟩ : NN) =
        mulLeftEquiv k s * ye * (mulLeftEquiv k s)⁻¹ * ye⁻¹ := by
      rw [show (⟨hh * g * hh⁻¹ * g⁻¹, hkNN⟩ : NN) =
          (⟨hh, hh_mem⟩ : NN) * ⟨g, hgN⟩ * (⟨hh, hh_mem⟩ : NN)⁻¹ * ⟨g, hgN⟩⁻¹ by
        apply Subtype.ext; rfl]
      simp only [map_mul, map_inv, hhom_hh, hhom_g]
    have hτs_ne : τ (s : E) ≠ 0 := fun h =>
      s.ne_zero (τ.injective (by rw [h, map_zero]))
    let u : E := (s : E) * (τ (s : E))⁻¹
    have hyk : yMap ((hh * g * hh⁻¹ * g⁻¹).toLinearEquiv) = LinearMap.mulLeft k u := by
      rw [← yEquivHom_apply (⟨hh * g * hh⁻¹ * g⁻¹, hkNN⟩ : NN), hhom_comm]
      ext x
      have h2 : τ (ye.symm x) = (c : E)⁻¹ * x := by
        have hx : x = (c : E) * τ (ye.symm x) :=
          (LinearEquiv.apply_symm_apply ye x).symm.trans (hcτ (ye.symm x))
        conv_rhs => rw [hx]
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      calc (mulLeftEquiv k s * ye * (mulLeftEquiv k s)⁻¹ * ye⁻¹) x
          = (mulLeftEquiv k s) (ye ((mulLeftEquiv k s).symm (ye.symm x))) := rfl
        _ = (mulLeftEquiv k s) (ye ((s : E)⁻¹ * ye.symm x)) := by
              rw [mulLeftEquiv_symm_apply]
        _ = (mulLeftEquiv k s) ((c : E) * τ ((s : E)⁻¹ * ye.symm x)) := by rw [hcτ]
        _ = (mulLeftEquiv k s) ((c : E) * ((τ (s : E))⁻¹ * τ (ye.symm x))) := by
              rw [map_mul τ ((s : E)⁻¹) (ye.symm x), map_inv₀ τ (s : E)]
        _ = (mulLeftEquiv k s) ((c : E) * ((τ (s : E))⁻¹ * ((c : E)⁻¹ * x))) := by rw [h2]
        _ = (s : E) * ((c : E) * ((τ (s : E))⁻¹ * ((c : E)⁻¹ * x))) := by
              rw [mulLeftEquiv_apply]
        _ = LinearMap.mulLeft k u x := by
              rw [LinearMap.mulLeft_apply, show u = (s : E) * (τ (s : E))⁻¹ from rfl]
              field_simp [c.ne_zero, hτs_ne]
    have hpow : (yMap ((hh * g * hh⁻¹ * g⁻¹).toLinearEquiv)) ^ 2 ^ n = 1 := by
      rw [← yMap_pow_mem hkNN]
      rw [show (hh * g * hh⁻¹ * g⁻¹) ^ 2 ^ n = 1 from hkpow, map_one, yMap_one]
      rfl
    have hu : u ^ 2 ^ n = 1 := by
      have hmu : LinearMap.mulLeft k (u ^ 2 ^ n) = 1 := by
        rw [← mulLeft_pow u (2 ^ n), ← hyk, hpow]
      have := congrArg (fun f : E →ₗ[k] E => f 1) hmu
      simpa using this
    have hu1 : (s : E) * (τ (s : E))⁻¹ = 1 := eq_one_of_pow_two_pow_eq_one hu
    have hs_eq : τ (s : E) = (s : E) := by
      have h1 : (s : E) = τ (s : E) := by
        have := congrArg (fun y : E => y * τ (s : E)) hu1
        rw [mul_assoc, inv_mul_cancel₀ hτs_ne, mul_one, one_mul] at this
        exact this
      exact h1.symm
    exact hs_eq
  have hτ_all : ∀ x : E, τ x = x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · exact hτ_unit (Units.mk0 x hx)
  have hβc : yMap g.toLinearEquiv = LinearMap.mulLeft k (c : E) := by
    ext x
    rw [hβτ x, hτ_all x, LinearMap.mulLeft_apply]
  obtain ⟨m, hm⟩ := isPGroup_iff_pow_pow_eq_one.mp
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥NN)).map NN.subtype) (⟨g, hg⟩ : pCoreOf 2 NN)
  have hgpow : g ^ 2 ^ m = 1 := by
    change ((⟨g, hg⟩ : pCoreOf 2 NN) : SpecialLinearGroup k (DSpace E X)) ^ 2 ^ m = 1
    rw [← Subgroup.coe_pow (pCoreOf 2 NN) (⟨g, hg⟩ : pCoreOf 2 NN) (2 ^ m),
      ← Subgroup.coe_one (pCoreOf 2 NN)]
    exact congrArg Subtype.val hm
  have hcpow : (c : E) ^ 2 ^ m = 1 := by
    have hmc : (LinearMap.mulLeft k (c : E)) ^ 2 ^ m = 1 := by
      rw [← hβc, ← yMap_pow_mem hgN]
      rw [show g ^ 2 ^ m = 1 from hgpow, map_one, yMap_one]
      rfl
    have := congrArg (fun f : E →ₗ[k] E => f 1) hmc
    rw [mulLeft_pow] at this
    simpa using this
  have hc1 : (c : E) = 1 := eq_one_of_pow_two_pow_eq_one hcpow
  have hyid : yMap g.toLinearEquiv = LinearMap.id := by
    rw [hβc, hc1, mulLeft_one']
  rw [mem_flagK_iff]
  have hcoord : (g.toLinearEquiv v).2.2 = v.2.2 := by
    have hmemK : v - ((0 : E), (0 : X), v.2.2) ∈ flagK k E X := by
      rw [mem_flagK_iff]; simp
    have hgmem : g.toLinearEquiv (v - ((0 : E), (0 : X), v.2.2)) ∈ flagK k E X :=
      (preservesK_of_mem_normalizer hgN) _ hmemK
    have hzero : (g.toLinearEquiv (v - ((0 : E), (0 : X), v.2.2))).2.2 = 0 :=
      mem_flagK_iff.mp hgmem
    have hdec : v = ((0 : E), (0 : X), v.2.2) + (v - ((0 : E), (0 : X), v.2.2)) := by abel
    calc (g.toLinearEquiv v).2.2
        = (g.toLinearEquiv (((0 : E), (0 : X), v.2.2) +
            (v - ((0 : E), (0 : X), v.2.2)))).2.2 := by
            conv_lhs => rw [hdec]
      _ = (g.toLinearEquiv ((0 : E), (0 : X), v.2.2) +
            g.toLinearEquiv (v - ((0 : E), (0 : X), v.2.2))).2.2 := by
            rw [map_add]
      _ = (g.toLinearEquiv ((0 : E), (0 : X), v.2.2)).2.2 +
            (g.toLinearEquiv (v - ((0 : E), (0 : X), v.2.2))).2.2 :=
            rfl
      _ = v.2.2 + 0 := by
            rw [show (g.toLinearEquiv ((0 : E), (0 : X), v.2.2)).2.2 = v.2.2 from by
              rw [show (g.toLinearEquiv ((0 : E), (0 : X), v.2.2)).2.2 =
                yMap g.toLinearEquiv v.2.2 from rfl, hyid]; rfl, hzero]
      _ = v.2.2 := by rw [add_zero]
  rw [show (g v - v).2.2 = (g.toLinearEquiv v).2.2 - v.2.2 from rfl, hcoord, sub_self]

theorem pCoreOf_normalizer_trivial_on_flagW (hX : 0 < Module.finrank k X)
    {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ pCoreOf 2
      (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))))
    (v : DSpace E X) (hv : v ∈ flagW k E X) : g v = v := by
  haveI hcharE : CharP E 2 := CharP.of_ringHom_of_ne_zero (algebraMap k E) 2 (by norm_num)
  have hgN : g ∈ NN := pCoreOf_le_ambient 2 NN hg
  have hyid : yMap g.toLinearEquiv = LinearMap.id := by
    ext b
    have h := pCoreOf_normalizer_trivial_on_quotient (k := k) (E := E) (X := X) hX hg
      ((0 : E), (0 : X), b)
    rw [mem_flagK_iff] at h
    simpa [yMap, sub_eq_zero] using h
  have hyinv : yMap ((g⁻¹).toLinearEquiv) = LinearMap.id := by
    have hleft : (yMap g.toLinearEquiv).comp (yMap ((g⁻¹).toLinearEquiv)) = LinearMap.id := by
      have h := yMap_mul_mem (u := g) (v := g⁻¹) hgN (Subgroup.inv_mem _ hgN)
      rw [show g.toLinearEquiv * (g⁻¹).toLinearEquiv = 1 by
        rw [← map_mul, mul_inv_cancel, map_one], yMap_one] at h
      exact h.symm
    rw [hyid] at hleft
    simpa using hleft
  obtain ⟨u, hu⟩ := wMap_conj_yMap hgN 1
  have hw : wMap g.toLinearEquiv = LinearMap.mulLeft k u := by
    rw [mulLeft_one', hyinv] at hu
    simpa using hu
  obtain ⟨m, hm⟩ := isPGroup_iff_pow_pow_eq_one.mp
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥NN)).map NN.subtype) (⟨g, hg⟩ : pCoreOf 2 NN)
  have hgpow : g ^ 2 ^ m = 1 := by
    change ((⟨g, hg⟩ : pCoreOf 2 NN) : SpecialLinearGroup k (DSpace E X)) ^ 2 ^ m = 1
    rw [← Subgroup.coe_pow (pCoreOf 2 NN) (⟨g, hg⟩ : pCoreOf 2 NN) (2 ^ m),
      ← Subgroup.coe_one (pCoreOf 2 NN)]
    exact congrArg Subtype.val hm
  have hupow : u ^ 2 ^ m = 1 := by
    have hmu : (LinearMap.mulLeft k u) ^ 2 ^ m = 1 := by
      rw [← hw, ← wMap_pow_mem hgN]
      rw [show g ^ 2 ^ m = 1 from hgpow, map_one, wMap_one]
      rfl
    have := congrArg (fun f : E →ₗ[k] E => f 1) hmu
    rw [mulLeft_pow] at this
    simpa using this
  have hu1 : u = 1 := eq_one_of_pow_two_pow_eq_one hupow
  have hwid : wMap g.toLinearEquiv = LinearMap.id := by
    rw [hw, hu1, mulLeft_one']
  change g.toLinearEquiv v = v
  have hv' : v = (((v.1, (0 : X), (0 : E)) : DSpace E X)) := by
    have h2 : v.2 = 0 := mem_flagW_iff.mp hv
    rw [← Prod.mk.eta (p := v), h2]
    rfl
  have hgW : g.toLinearEquiv (v.1, (0 : X), (0 : E)) =
      (wMap g.toLinearEquiv v.1, (0 : X), (0 : E)) := by
    have hmem : g.toLinearEquiv (v.1, (0 : X), (0 : E)) ∈ flagW k E X :=
      (mem_flagW_iff_of_mem_normalizer hgN (v.1, (0 : X), (0 : E))).mpr
        (by rw [mem_flagW_iff]; rfl)
    have h2 : (g.toLinearEquiv (v.1, (0 : X), (0 : E))).2 = 0 := mem_flagW_iff.mp hmem
    rw [← Prod.mk.eta (p := g.toLinearEquiv (v.1, (0 : X), (0 : E))), h2]
    rfl
  rw [hv', hgW, hwid]
  rfl

end CFSG.LinearAlgebra.RootGroupSL
