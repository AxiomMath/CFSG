module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap
open CFSG.GroupTheory.WeirSylow

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma map_commSp_le_self {g t : OGroup Q} (htt : t * t = 1) (hgt : g * t = t * g) :
    (commSp t).map (g : V →ₗ[ZMod 3] V) ≤ commSp t := by
  intro x hx
  rw [Submodule.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  rw [mem_commSp_iff htt]
  change (t : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) w) = -((g : V ≃ₗ[ZMod 3] V) w)
  have hw' : (t : V ≃ₗ[ZMod 3] V) w = -w := (mem_commSp_iff htt).mp hw
  have hcomm : (t : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) w) =
      (g : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) w) := by
    have h := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V) w) hgt
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h
    exact h.symm
  rw [hcomm, hw', map_neg]

private lemma map_commSp_eq_self {g t : OGroup Q} (htt : t * t = 1) (hgt : g * t = t * g) :
    (commSp t).map (g : V →ₗ[ZMod 3] V) = commSp t :=
  Submodule.eq_of_le_of_finrank_eq (map_commSp_le_self htt hgt) (by
    rw [LinearEquiv.finrank_map_eq])

private lemma quaternion_aux {A : Type*} [Ring A] (h2 : (2 : A) = -1) (a b : A)
    (ha : a * a = -1) (hb : b * b = -1) (hab : b * a = -(a * b)) :
    IsIdempotentElem (-(1 + a + b)) ∧
      (a * b) * (-(1 + a + b)) = (1 - (-(1 + a + b))) * (a * b) ∧
      (a * b) * (1 - (-(1 + a + b))) = (-(1 + a + b)) * (a * b) ∧
      (a * b) * (a * b) = -1 := by
  have haab' : a * (a * b) = -b := by
    rw [← mul_assoc, ha, neg_one_mul]
  have hbab' : b * (a * b) = a := by
    rw [← mul_assoc, hab, neg_mul, mul_assoc, hb, mul_neg, mul_one, neg_neg]
  have haba : a * b * a = b := by
    rw [mul_assoc, hab, mul_neg, haab', neg_neg]
  have habb : a * b * b = -a := by
    rw [mul_assoc, hb, mul_neg, mul_one]
  have hksq : (a * b) * (a * b) = -1 := by
    rw [← mul_assoc (a * b) a b, haba, hb]
  have hL : (a * b) * (1 + a + b) = a * b + b - a := by
    rw [mul_add, mul_add, mul_one, haba, habb]
    abel
  have hL2 : (a * b) * (2 + a + b) = 2 * (a * b) + b - a := by
    rw [mul_add, mul_add, mul_two, two_mul, haba, habb]
    abel
  have hR : (2 + a + b) * (a * b) = 2 * (a * b) - b + a := by
    rw [add_mul, add_mul, haab', hbab']
    abel
  have h1e : (1 : A) + (1 + a + b) = 2 + a + b := by
    rw [show (2 : A) = 1 + 1 from one_add_one_eq_two.symm]
    abel
  have hexp : (1 + a + b) * (1 + a + b) =
      1 + a * a + b * b + (a * b + b * a) + 2 * a + 2 * b := by
    noncomm_ring
  have hba : a * b + b * a = 0 := by rw [hab]; abel
  have hsq : (1 + a + b) * (1 + a + b) = -(1 + a + b) := by
    rw [hexp, ha, hb, hba, h2]
    noncomm_ring
  refine ⟨?_, ?_, ?_, hksq⟩
  · show (-(1 + a + b)) * (-(1 + a + b)) = -(1 + a + b)
    calc (-(1 + a + b)) * (-(1 + a + b)) = (1 + a + b) * (1 + a + b) := by noncomm_ring
      _ = -(1 + a + b) := hsq
  · rw [sub_neg_eq_add, h1e, mul_neg, hL, hR, h2, neg_one_mul]
    abel
  · have hR2 : (-(1 + a + b)) * (a * b) = 2 * (a * b) + b - a := by
      rw [neg_mul]
      have h : (1 + a + b) * (a * b) = a * b - b + a := by
        rw [add_mul, add_mul, one_mul, haab', hbab']
        abel
      rw [h, h2, neg_one_mul]
      abel
    rw [sub_neg_eq_add, h1e, hL2, hR2]

theorem four_dvd_invDim_of_quaternion (hQ : Q.Nondegenerate) {q r : OGroup Q}
    (hqr : q * q = r * r) (hyy : (q * q) * (q * q) = 1) (hrq : r * q = q⁻¹ * r) :
    4 ∣ invDim (q * q) ∧ invSign (q * q) = 1 := by
  let W : Submodule (ZMod 3) V := commSp (q * q)
  have hqy : q * (q * q) = (q * q) * q := (mul_assoc q q q).symm
  have hry : r * (q * q) = (q * q) * r := by
    rw [hqr]
    exact (mul_assoc r r r).symm
  have hWq : W.map (q : V →ₗ[ZMod 3] V) = W := map_commSp_eq_self hyy hqy
  have hWr : W.map (r : V →ₗ[ZMod 3] V) = W := map_commSp_eq_self hyy hry
  let a : W ≃ₗ[ZMod 3] W := (q : V ≃ₗ[ZMod 3] V).ofSubmodules W W hWq
  let b : W ≃ₗ[ZMod 3] W := (r : V ≃ₗ[ZMod 3] V).ofSubmodules W W hWr
  have ha_apply : ∀ x : W, (a x : V) = (q : V ≃ₗ[ZMod 3] V) (x : V) :=
    fun x => LinearEquiv.ofSubmodules_apply (e := (q : V ≃ₗ[ZMod 3] V)) hWq x
  have hb_apply : ∀ x : W, (b x : V) = (r : V ≃ₗ[ZMod 3] V) (x : V) :=
    fun x => LinearEquiv.ofSubmodules_apply (e := (r : V ≃ₗ[ZMod 3] V)) hWr x
  have ha_symm_apply : ∀ x : W, (a.symm x : V) = (q : V ≃ₗ[ZMod 3] V).symm (x : V) :=
    fun x => LinearEquiv.ofSubmodules_symm_apply (e := (q : V ≃ₗ[ZMod 3] V)) hWq x
  have hb_symm_apply : ∀ x : W, (b.symm x : V) = (r : V ≃ₗ[ZMod 3] V).symm (x : V) :=
    fun x => LinearEquiv.ofSubmodules_symm_apply (e := (r : V ≃ₗ[ZMod 3] V)) hWr x
  have h2E : (2 : Module.End (ZMod 3) W) = -1 := by
    have h : (2 : Module.End (ZMod 3) W) = 1 + 1 := one_add_one_eq_two.symm
    rw [h]
    ext x
    change (x : V) + (x : V) = -(x : V)
    rw [← two_smul (ZMod 3) (x : V), show (2 : ZMod 3) = -1 by decide, neg_one_smul]
  have hcoe_q : ((q * q : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      (q : V ≃ₗ[ZMod 3] V) * (q : V ≃ₗ[ZMod 3] V) := rfl
  have hcoe_r : ((r * r : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      (r : V ≃ₗ[ZMod 3] V) * (r : V ≃ₗ[ZMod 3] V) := rfl
  have haE : (a : Module.End (ZMod 3) W) * (a : Module.End (ZMod 3) W) = -1 := by
    ext x
    change (a (a x) : V) = -(x : V)
    rw [ha_apply (a x), ha_apply x]
    change (q : V ≃ₗ[ZMod 3] V) ((q : V ≃ₗ[ZMod 3] V) (x : V)) = -(x : V)
    rw [← LinearEquiv.mul_apply, ← hcoe_q]
    exact (mem_commSp_iff hyy).mp x.2
  have hbE : (b : Module.End (ZMod 3) W) * (b : Module.End (ZMod 3) W) = -1 := by
    ext x
    change (b (b x) : V) = -(x : V)
    rw [hb_apply (b x), hb_apply x]
    change (r : V ≃ₗ[ZMod 3] V) ((r : V ≃ₗ[ZMod 3] V) (x : V)) = -(x : V)
    rw [← LinearEquiv.mul_apply, ← hcoe_r, ← hqr]
    exact (mem_commSp_iff hyy).mp x.2
  have hcoe_neg_a : ((a.symm : W ≃ₗ[ZMod 3] W) : Module.End (ZMod 3) W)
      = -(a : Module.End (ZMod 3) W) := by
    apply LinearMap.ext
    intro x
    have hxx : a (a x) = -x := by
      have h := congrArg (fun f : Module.End (ZMod 3) W => f x) haE
      simpa [Module.End.mul_apply, LinearMap.neg_apply] using h
    change a.symm x = -(a x)
    rw [a.symm_apply_eq, map_neg, hxx, neg_neg]
  have hrqE : (b : Module.End (ZMod 3) W) * (a : Module.End (ZMod 3) W)
      = -((a : Module.End (ZMod 3) W) * (b : Module.End (ZMod 3) W)) := by
    have h1 : (b : Module.End (ZMod 3) W) * (a : Module.End (ZMod 3) W)
        = (a.symm : Module.End (ZMod 3) W) * (b : Module.End (ZMod 3) W) := by
      ext x
      change (b (a x) : V) = (a.symm (b x) : V)
      rw [hb_apply (a x), ha_apply x, ha_symm_apply (b x), hb_apply x]
      have h := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V) (x : V)) hrq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply] at h
      simpa using h
    rw [h1, hcoe_neg_a]
    exact neg_mul (a : Module.End (ZMod 3) W) (b : Module.End (ZMod 3) W)
  obtain ⟨he_idem, hke, hke', hkk⟩ :=
    quaternion_aux h2E (a : Module.End (ZMod 3) W) (b : Module.End (ZMod 3) W) haE hbE hrqE
  let e : Module.End (ZMod 3) W :=
    -(1 + (a : Module.End (ZMod 3) W) + (b : Module.End (ZMod 3) W))
  have he_idem' : IsIdempotentElem e := he_idem
  have he_sq : e * e = e := he_idem
  have hone_sub_mul : (1 - e) * e = 0 := by
    rw [sub_mul, one_mul, he_sq, sub_self]
  have he_mul_sub : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, he_sq, sub_self]
  have hone_sub_sq : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he_sq]
    abel
  let k : W ≃ₗ[ZMod 3] W := a * b
  let kE : Module.End (ZMod 3) W := (a : Module.End (ZMod 3) W) * (b : Module.End (ZMod 3) W)
  have hkE : (k : Module.End (ZMod 3) W) = kE := rfl
  have hke_k : kE * e = (1 - e) * kE := hke
  have hke_k' : kE * (1 - e) = e * kE := hke'
  have hkk' : kE * kE = -1 := hkk
  let M : Submodule (ZMod 3) W := LinearMap.range e
  let N : Submodule (ZMod 3) W := LinearMap.range (1 - e)
  have hcompl : IsCompl M N := by
    dsimp only [M, N]
    rw [← LinearMap.IsIdempotentElem.ker_eq_range_one_sub he_idem']
    exact LinearMap.IsIdempotentElem.isCompl he_idem'
  have hmap_le : M.map kE ≤ N := by
    intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := hx
    refine ⟨kE v, ?_⟩
    have h := congrArg (fun f : Module.End (ZMod 3) W => f v) hke_k
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hmap_ge : N ≤ M.map kE := by
    intro y hy
    obtain ⟨w, hw⟩ := hy
    refine Submodule.mem_map.mpr ⟨-(kE y), ?_, ?_⟩
    · refine M.neg_mem ?_
      have h := congrArg (fun f : Module.End (ZMod 3) W => f w) hke_k'
      simp only [Module.End.mul_apply] at h
      rw [hw] at h
      exact ⟨kE w, h.symm⟩
    · have h1 : kE (kE y) = -y := by
        rw [show kE (kE y) = (kE * kE) y from rfl, hkk', LinearMap.neg_apply,
          Module.End.one_apply]
      rw [map_neg, h1, neg_neg]
  have hmap : M.map kE = N := le_antisymm hmap_le hmap_ge
  have hdimMN : Module.finrank (ZMod 3) M = Module.finrank (ZMod 3) N := by
    rw [← hmap, ← hkE, LinearEquiv.finrank_map_eq]
  let B := (Q.restrict W).polarBilin
  have hBapply : ∀ x y : W, B x y = QuadraticMap.polar Q (x : V) (y : V) := by
    intro x y
    simp only [B, QuadraticMap.polarBilin_restrict, LinearMap.domRestrict₁₂_apply,
      QuadraticMap.polarBilin_apply_apply]
  have hBsym : ∀ x y : W, B x y = B y x := fun x y => QuadraticMap.polar_comm Q (x : V) (y : V)
  have hBnd : B.Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff).mpr (nondegenerate_restrict_commSp hQ hyy)
  have haIso : ∀ x y : W,
      B ((a : Module.End (ZMod 3) W) x) ((a : Module.End (ZMod 3) W) y) = B x y := by
    intro x y
    rw [hBapply, hBapply]
    change QuadraticMap.polar Q ((a x : W) : V) ((a y : W) : V) =
      QuadraticMap.polar Q (x : V) (y : V)
    rw [ha_apply x, ha_apply y]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup q.2 (x : V) (y : V)
  have hbIso : ∀ x y : W,
      B ((b : Module.End (ZMod 3) W) x) ((b : Module.End (ZMod 3) W) y) = B x y := by
    intro x y
    rw [hBapply, hBapply]
    change QuadraticMap.polar Q ((b x : W) : V) ((b y : W) : V) =
      QuadraticMap.polar Q (x : V) (y : V)
    rw [hb_apply x, hb_apply y]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup r.2 (x : V) (y : V)
  have hkiso : ∀ x y : W, B (kE x) (kE y) = B x y := by
    intro x y
    have hx : kE x = (a : Module.End (ZMod 3) W) ((b : Module.End (ZMod 3) W) x) := by
      rfl
    have hy : kE y = (a : Module.End (ZMod 3) W) ((b : Module.End (ZMod 3) W) y) := by
      rfl
    rw [hx, hy, haIso, hbIso]
  have hadj_a : ∀ x y : W, B ((a : Module.End (ZMod 3) W) x) y =
      - B x ((a : Module.End (ZMod 3) W) y) := by
    intro x y
    have h := haIso x ((a : Module.End (ZMod 3) W) y)
    rw [← Module.End.mul_apply, haE, LinearMap.neg_apply, map_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have hadj_b : ∀ x y : W, B ((b : Module.End (ZMod 3) W) x) y =
      - B x ((b : Module.End (ZMod 3) W) y) := by
    intro x y
    have h := hbIso x ((b : Module.End (ZMod 3) W) y)
    rw [← Module.End.mul_apply, hbE, LinearMap.neg_apply, map_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have hadj_k : ∀ x y : W, B (kE x) y = - B x (kE y) := by
    intro x y
    have h := hkiso x (kE y)
    rw [show kE (kE y) = -y by
          rw [← Module.End.mul_apply, hkk', LinearMap.neg_apply, Module.End.one_apply],
        map_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have h1e_apply : ∀ y : W, (1 - e) y = -(y - (a : Module.End (ZMod 3) W) y
      - (b : Module.End (ZMod 3) W) y) := by
    intro y
    have hsub : (1 : Module.End (ZMod 3) W) - e = 2 + (a : Module.End (ZMod 3) W)
        + (b : Module.End (ZMod 3) W) := by
      rw [show e = -(1 + (a : Module.End (ZMod 3) W) + (b : Module.End (ZMod 3) W)) from rfl,
        sub_neg_eq_add, one_add_one_eq_two.symm]
      abel
    rw [hsub, LinearMap.add_apply, LinearMap.add_apply, h2E, LinearMap.neg_apply,
      Module.End.one_apply]
    abel
  have hadj_e : ∀ x y : W, B (e x) y = B x ((1 - e) y) := by
    intro x y
    have hex : e x = -(x + (a : Module.End (ZMod 3) W) x
        + (b : Module.End (ZMod 3) W) x) := by
      simp only [e, LinearMap.neg_apply, LinearMap.add_apply, Module.End.one_apply]
    calc B (e x) y
        = B (-(x + (a : Module.End (ZMod 3) W) x + (b : Module.End (ZMod 3) W) x)) y := by
          rw [hex]
      _ = - B (x + (a : Module.End (ZMod 3) W) x + (b : Module.End (ZMod 3) W) x) y := by
          rw [map_neg, LinearMap.neg_apply]
      _ = -(B x y + B ((a : Module.End (ZMod 3) W) x) y
            + B ((b : Module.End (ZMod 3) W) x) y) := by
          rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
      _ = -(B x y + (-B x ((a : Module.End (ZMod 3) W) y))
            + (-B x ((b : Module.End (ZMod 3) W) y))) := by rw [hadj_a, hadj_b]
      _ = B x (-(y - (a : Module.End (ZMod 3) W) y - (b : Module.End (ZMod 3) W) y)) := by
          rw [map_neg, map_sub, map_sub]
          abel
      _ = B x ((1 - e) y) := by rw [h1e_apply y]
  have hBMM : ∀ x ∈ M, ∀ y ∈ M, B x y = 0 := by
    intro x hx y hy
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    calc B (e v) (e w) = B v ((1 - e) (e w)) := hadj_e v (e w)
      _ = B v (((1 - e) * e) w) := by rw [← Module.End.mul_apply]
      _ = B v 0 := by rw [hone_sub_mul, LinearMap.zero_apply]
      _ = 0 := by rw [map_zero]
  have hBNN : ∀ x ∈ N, ∀ y ∈ N, B x y = 0 := by
    intro x hx y hy
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    have h := hadj_e ((1 - e) v) ((1 - e) w)
    rw [show e ((1 - e) v) = 0 by
          rw [← Module.End.mul_apply, he_mul_sub, LinearMap.zero_apply],
        show (1 - e) ((1 - e) w) = (1 - e) w by
          rw [← Module.End.mul_apply, hone_sub_sq]] at h
    rw [map_zero, LinearMap.zero_apply] at h
    exact h.symm
  have hQWs : (Q.restrict W).Nondegenerate := nondegenerate_restrict_commSp hQ hyy
  have hMsing : ∀ x ∈ M, (Q.restrict W) x = 0 := by
    intro x hx
    have hBxx : B x x = 0 := hBMM x hx x hx
    have hpol : B x x = 2 * (Q.restrict W) x := by
      rw [hBapply x x, QuadraticMap.polar_self]
      rw [QuadraticMap.restrict_apply, nsmul_eq_mul]
      norm_num
    rw [hpol] at hBxx
    exact (mul_eq_zero.mp hBxx).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
  have hdimW : Module.finrank (ZMod 3) W = 2 * Module.finrank (ZMod 3) M := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  have hIsPlus : IsPlusType (Q.restrict W) := by
    refine ⟨M, by omega, hMsing⟩
  have hInvSign : invSign (q * q) = 1 := by
    have hiff := isPlusType_iff_quadSign_eq_one hQWs hdimW
    change quadSign (Q.restrict W) = 1
    exact hiff.mp hIsPlus
  let β : LinearMap.BilinForm (ZMod 3) M := B.compl₁₂ M.subtype (kE.comp M.subtype)
  have hβalt : β.IsAlt := by
    intro v
    change B (v : W) (kE (v : W)) = 0
    have h : B (v : W) (kE (v : W)) = - B (v : W) (kE (v : W)) :=
      (hBsym _ _).trans (hadj_k (v : W) (v : W))
    have h2 : (2 : ZMod 3) * B (v : W) (kE (v : W)) = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h
    exact (mul_eq_zero.mp h2).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
  have hβnd : β.Nondegenerate := by
    constructor
    · intro v hv
      have hBv : ∀ w : W, B (v : W) w = 0 := by
        intro w
        have hw : w ∈ M ⊔ N := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
        obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hw
        rw [map_add]
        have h1 : B (v : W) m = 0 := hBMM (v : W) v.2 m hm
        have h2 : B (v : W) n = 0 := by
          have hn' : n ∈ M.map kE := by rwa [hmap]
          obtain ⟨w', hw', hw'k⟩ := Submodule.mem_map.mp hn'
          rw [← hw'k]
          exact hv ⟨w', hw'⟩
        rw [h1, h2, add_zero]
      exact Subtype.ext (hBnd.1 (v : W) hBv)
    · intro w hw
      have hkw : kE (w : W) ∈ N := hmap_le (Submodule.mem_map.mpr ⟨w, w.2, rfl⟩)
      have hBw : ∀ x : W, B x (kE (w : W)) = 0 := by
        intro x
        have hx : x ∈ M ⊔ N := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
        obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hx
        rw [map_add, LinearMap.add_apply]
        have h1 : B m (kE (w : W)) = 0 := hw ⟨m, hm⟩
        have h2 : B n (kE (w : W)) = 0 := hBNN n hn (kE (w : W)) hkw
        rw [h1, h2, add_zero]
      have hzero : kE (w : W) = 0 := hBnd.2 (kE (w : W)) hBw
      have h1 : kE (kE (w : W)) = 0 := by rw [hzero, map_zero]
      rw [← Module.End.mul_apply, hkk', LinearMap.neg_apply, Module.End.one_apply] at h1
      exact Subtype.ext (neg_eq_zero.mp h1)
  have hβeven : Even (Module.finrank (ZMod 3) M) := hβalt.even_finrank hβnd
  refine ⟨?_, hInvSign⟩
  change 4 ∣ Module.finrank (ZMod 3) W
  obtain ⟨m, hm⟩ := hβeven
  refine ⟨m, ?_⟩
  rw [hdimW, hm]
  ring

end CFSG.OddStandard.SmallF3.Omega

end
