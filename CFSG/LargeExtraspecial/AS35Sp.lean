module

public import CFSG.LargeExtraspecial.AS35Fis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open Matrix CFSG.Fischer.Classification
open CFSG.Fischer.Classification.Recognition.SpU.Sp (add_self_zmod2 add_self_vec
  eq_one_of_ne_zero_zmod2 b_symm exists_b_eq_one)

namespace AS35Sp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}

abbrev Sp (b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)) : Subgroup (GL ι (ZMod 2)) :=
  fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y

noncomputable def ac (g : Sp b) (x : ι → ZMod 2) : ι → ZMod 2 :=
  ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x

theorem ac_mul (g h : Sp b) (x : ι → ZMod 2) : ac (g * h) x = ac g (ac h x) := by
  simp only [ac, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem ac_one (x : ι → ZMod 2) : ac (1 : Sp b) x = x := by
  simp only [ac, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]

theorem ac_add (g : Sp b) (x y : ι → ZMod 2) : ac g (x + y) = ac g x + ac g y :=
  Matrix.mulVec_add _ _ _

theorem ac_smul (g : Sp b) (c : ZMod 2) (x : ι → ZMod 2) : ac g (c • x) = c • ac g x :=
  Matrix.mulVec_smul _ _ _

theorem ac_zero (g : Sp b) : ac g 0 = 0 := Matrix.mulVec_zero _

theorem ac_inv_ac (g : Sp b) (x : ι → ZMod 2) : ac g⁻¹ (ac g x) = x := by
  rw [← ac_mul, inv_mul_cancel, ac_one]

theorem ac_ac_inv (g : Sp b) (x : ι → ZMod 2) : ac g (ac g⁻¹ x) = x := by
  rw [← ac_mul, mul_inv_cancel, ac_one]

theorem ac_ext {g h : Sp b} (e : ∀ x, ac g x = ac h x) : g = h :=
  Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun _ => e _))

theorem b_ac_ac (g : Sp b) (x y : ι → ZMod 2) : b (ac g x) (ac g y) = b x y :=
  (mem_fischerMatrixGroup_bilin_iff b g).1 g.2 x y

theorem b_ac_left {g : Sp b} {v : ι → ZMod 2} (hg : ac g v = v) (x : ι → ZMod 2) :
    b (ac g x) v = b x v := by
  conv_lhs => rw [← hg]
  exact b_ac_ac g x v

variable (b) in
noncomputable def R (v : ι → ZMod 2) : Subgroup (Sp b) where
  carrier := {g | ac g v = v ∧ ∀ y, b y v = 0 → ∃ c : ZMod 2, ac g y = y + c • v}
  one_mem' := ⟨ac_one v, fun y _ => ⟨0, by rw [ac_one, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro g h ⟨hgv, hg⟩ ⟨hhv, hh⟩
    refine ⟨by rw [ac_mul, hhv, hgv], fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hh y hy
    obtain ⟨c', hc'⟩ := hg y hy
    exact ⟨c' + c, by rw [ac_mul, hc, ac_add, ac_smul, hgv, hc', add_smul, add_assoc]⟩
  inv_mem' := by
    rintro g ⟨hgv, hg⟩
    have hv' : ac g⁻¹ v = v := by
      conv_lhs => rw [← hgv]
      exact ac_inv_ac g v
    refine ⟨hv', fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hg (ac g⁻¹ y) (by rw [b_ac_left hv', hy])
    rw [ac_ac_inv] at hc
    refine ⟨c, ?_⟩
    calc ac g⁻¹ y = ac g⁻¹ y + c • v + c • v := by rw [add_assoc, add_self_vec, add_zero]
      _ = y + c • v := by rw [← hc]

noncomputable def tr (halt : ∀ x, b x x = 0) (w : ι → ZMod 2) : Sp b :=
  ⟨sympTransvectionGL b halt w, sympTransvectionGL_mem_fischerMatrixGroup w⟩

theorem ac_tr (halt : ∀ x, b x x = 0) (w x : ι → ZMod 2) : ac (tr halt w) x = x + b x w • w :=
  sympTransvectionGL_mulVec w x

theorem ac_tr_mul_tr (halt : ∀ x, b x x = 0) {v w : ι → ZMod 2} (hw : b w v = 0)
    {y : ι → ZMod 2} (hy : b y v = 0) :
    ac (tr halt w * tr halt (w + v)) y = y + b y w • v := by
  have hww : b (w + v) w = 0 := by
    rw [map_add, LinearMap.add_apply, halt w, b_symm halt v w, hw, add_zero]
  rw [ac_mul, ac_tr, ac_tr, map_add, hy, add_zero, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, hww, smul_zero, add_zero]
  calc y + b y w • (w + v) + b y w • w = y + b y w • v + (b y w • w + b y w • w) := by
        rw [smul_add]; abel
    _ = y + b y w • v := by rw [add_self_vec, add_zero]

theorem tr_mul_tr_mem_R (halt : ∀ x, b x x = 0) {v w : ι → ZMod 2} (hw : b w v = 0) :
    tr halt w * tr halt (w + v) ∈ R b v := by
  refine ⟨?_, fun y hy => ⟨b y w, ac_tr_mul_tr halt hw hy⟩⟩
  have hvv : b v (w + v) = 0 := by
    rw [map_add, b_symm halt v w, hw, halt v, add_zero]
  rw [ac_mul, ac_tr halt (w + v) v, hvv, zero_smul, add_zero, ac_tr, b_symm halt v w, hw,
    zero_smul, add_zero]

section Centralizer

variable (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
  {t : Sp b} {v : ι → ZMod 2} (hv : v ≠ 0) (ht : ∀ x, ac t x = x + b x v • v)

include halt hnd hv ht in
theorem ac_eq_of_mem_centralizer {c : Sp b} (hc : c ∈ centralizer {t}) : ac c v = v := by
  obtain ⟨y₀, hy₀⟩ := exists_b_eq_one halt hnd hv
  have e := congrArg (fun g => ac g y₀) (Subgroup.mem_centralizer_singleton_iff.1 hc)
  simp only [ac_mul, ht, hy₀, one_smul, ac_add] at e
  have e' : ac c v = b (ac c y₀) v • v := add_left_cancel e
  rcases eq_or_ne (b (ac c y₀) v) 0 with h0 | h1
  · exfalso
    apply hv
    rw [h0, zero_smul] at e'
    rw [← ac_inv_ac c v, e', ac_zero]
  · rw [e', eq_one_of_ne_zero_zmod2 h1, one_smul]

include ht in
theorem R_le_centralizer : R b v ≤ centralizer {t} := by
  rintro g ⟨hgv, -⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 (ac_ext fun x => ?_)
  rw [ac_mul, ac_mul, ht, ht, ac_add, ac_smul, hgv, b_ac_left hgv]

include halt hnd hv ht in
theorem conj_mem_R {c g : Sp b} (hc : c ∈ centralizer {t}) (hg : g ∈ R b v) :
    c * g * c⁻¹ ∈ R b v := by
  have hcv := ac_eq_of_mem_centralizer halt hnd hv ht hc
  have hcv' : ac c⁻¹ v = v := by
    conv_lhs => rw [← hcv]
    exact ac_inv_ac c v
  obtain ⟨hgv, hg⟩ := hg
  refine ⟨by rw [ac_mul, ac_mul, hcv', hgv, hcv], fun y hy => ?_⟩
  obtain ⟨e, he⟩ := hg (ac c⁻¹ y) (by rw [b_ac_left hcv', hy])
  exact ⟨e, by rw [ac_mul, ac_mul, he, ac_add, ac_smul, ac_ac_inv, hcv]⟩

end Centralizer

theorem b_delta_v {g : Sp b} {v : ι → ZMod 2} (hgv : ac g v = v) (x : ι → ZMod 2) :
    b (ac g x + x) v = 0 := by
  rw [map_add, LinearMap.add_apply, b_ac_left hgv, add_self_zmod2]

theorem b_delta {v : ι → ZMod 2} {g : Sp b} (hg : g ∈ R b v) {y : ι → ZMod 2} (hy : b y v = 0)
    (x : ι → ZMod 2) : b y (ac g x + x) = b (ac g y + y) x := by
  obtain ⟨hgv, hgy⟩ := hg
  obtain ⟨c, hc⟩ := hgy y hy
  have hiso := b_ac_ac g y x
  have hvx : b v (ac g x) = b v x := by
    conv_lhs => rw [← hgv]
    exact b_ac_ac g v x
  rw [hc, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hvx, smul_eq_mul] at hiso
  rw [hc, add_comm y, add_assoc, add_self_vec, add_zero, map_smul, LinearMap.smul_apply,
    smul_eq_mul, map_add]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination hiso + (b y x - c * b v x) * h2

theorem delta_eq_smul (halt : ∀ x, b x x = 0) {v : ι → ZMod 2} {g : Sp b} (hg : g ∈ R b v)
    {y₀ : ι → ZMod 2} (hy₀ : b y₀ v = 1) {y : ι → ZMod 2} (hy : b y v = 0) :
    ac g y + y = b y (ac g y₀ + y₀) • v := by
  rw [b_delta hg hy y₀]
  obtain ⟨c, hc⟩ := hg.2 y hy
  rw [hc, add_comm y, add_assoc, add_self_vec, add_zero, map_smul, LinearMap.smul_apply,
    smul_eq_mul, b_symm halt v y₀, hy₀, mul_one]

theorem mul_self_eq_one (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    {v : ι → ZMod 2} (hv : v ≠ 0) {g : Sp b} (hg : g ∈ R b v) : g * g = 1 := by
  obtain ⟨y₀, hy₀⟩ := exists_b_eq_one halt hnd hv
  have hδδ : ∀ x, ac g (ac g x + x) = ac g x + x := by
    intro x
    have h1 : b (ac g y₀ + y₀) (ac g x + x) = 0 := by
      rw [b_delta hg (b_delta_v hg.1 y₀) x, delta_eq_smul halt hg hy₀ (b_delta_v hg.1 y₀),
        halt, zero_smul, map_zero, LinearMap.zero_apply]
    have h2 : ac g (ac g x + x) + (ac g x + x) = 0 := by
      rw [delta_eq_smul halt hg hy₀ (b_delta_v hg.1 x), b_symm halt, h1, zero_smul]
    calc ac g (ac g x + x) = ac g (ac g x + x) + (ac g x + x) + (ac g x + x) := by
          rw [add_assoc, add_self_vec, add_zero]
      _ = ac g x + x := by rw [h2, zero_add]
  refine ac_ext fun x => ?_
  rw [ac_mul, ac_one]
  have e := hδδ x
  rw [ac_add] at e
  calc ac g (ac g x) = ac g (ac g x) + ac g x + ac g x := by
        rw [add_assoc, add_self_vec, add_zero]
    _ = x := by rw [e, add_comm (ac g x) x, add_assoc, add_self_vec, add_zero]

theorem mem_R_of_commutator (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    {t : Sp b} {v : ι → ZMod 2} (hv : v ≠ 0) (ht : ∀ x, ac t x = x + b x v • v) {c : Sp b}
    (hc : c ∈ centralizer {t})
    (hcQ : ∀ x ∈ R b v, c * x * c⁻¹ * x⁻¹ = 1 ∨ c * x * c⁻¹ * x⁻¹ = t) : c ∈ R b v := by
  have hcv := ac_eq_of_mem_centralizer halt hnd hv ht hc
  have key : ∀ x ∈ R b v, ∀ y, b y v = 0 → ac (c * x) y = ac (x * c) y := by
    intro x hx y hy
    have hcx : c * x = c * x * c⁻¹ * x⁻¹ * (x * c) := by group
    rcases hcQ x hx with h | h
    · rw [hcx, h, one_mul]
    · rw [hcx, h, ac_mul t, ht, ac_mul, b_ac_left hx.1, b_ac_left hcv, hy, zero_smul, add_zero]
  refine ⟨hcv, fun y hy => ?_⟩
  set z := ac c y + y with hz
  have hzu : ∀ u, b u v = 0 → b z u = 0 := by
    intro u hu
    have e := key _ (tr_mul_tr_mem_R halt hu) y hy
    simp only [ac_mul] at e
    rw [← ac_mul (tr halt u), ac_tr_mul_tr halt hu hy, ac_add, ac_smul, hcv,
      ← ac_mul (tr halt u), ac_tr_mul_tr halt hu (by rw [b_ac_left hcv, hy]),
      add_right_inj] at e
    have e' : b y u = b (ac c y) u := smul_left_injective (ZMod 2) hv e
    rw [hz, map_add, LinearMap.add_apply, ← e', add_self_zmod2]
  obtain ⟨y₀, hy₀⟩ := exists_b_eq_one halt hnd hv
  refine ⟨b z y₀, ?_⟩
  have hzv : z + b z y₀ • v = 0 := by
    refine hnd _ fun x => ?_
    have hx : b (x + b x v • y₀) v = 0 := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hy₀, smul_eq_mul,
        mul_one, add_self_zmod2]
    have h := hzu _ hx
    rw [map_add, map_smul, smul_eq_mul] at h
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      b_symm halt v x]
    linear_combination h
  have hz' : z = b z y₀ • v := by
    calc z = z + b z y₀ • v + b z y₀ • v := by rw [add_assoc, add_self_vec, add_zero]
      _ = b z y₀ • v := by rw [hzv, zero_add]
  calc ac c y = z + y := by rw [hz, add_assoc, add_self_vec, add_zero]
    _ = y + b z y₀ • v := by
      conv_lhs => rw [hz']
      rw [add_comm]

end AS35Sp

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

theorem false_of_case2 {m : ℕ} {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (h : fischerLinearModel {g : G | IsConj S.z g}
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) : False := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨v, hv, htv⟩ := (hφ S.z).mp (IsConj.refl _)
  have ht : ∀ x, AS35Sp.ac (φ S.z) x = x + b x v • v := htv
  set S' := S.map φ with hS'
  have hle : AS35Sp.R b v ≤ S'.M := AS35Sp.R_le_centralizer ht
  have hRQ : AS35Sp.R b v ≤ S'.QG := by
    have hn : ((AS35Sp.R b v).subgroupOf S'.M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle]
      exact fun x k hx hk => AS35Sp.conj_mem_R halt hnd hv ht hk hx
    have h2 : IsPGroup 2 ((AS35Sp.R b v).subgroupOf S'.M) := fun g =>
      ⟨1, Subtype.ext (Subtype.ext (by
        simpa [pow_two] using AS35Sp.mul_self_eq_one halt hnd hv (g.2 : _)))⟩
    have hP := S'.le_of_normal _ hn h2
    exact fun x hx => ⟨⟨x, hle hx⟩, hP hx, rfl⟩
  have hQR : S'.QG ≤ AS35Sp.R b v := fun c hc =>
    AS35Sp.mem_R_of_commutator halt hnd hv ht (S'.QG_le_M hc)
      fun x hx => S'.commutator_eq_one_or_z hc (hRQ hx)
  obtain ⟨x, hx, y, hy, hxy⟩ := S'.exists_mem_QG_mul_ne
  have h1 := AS35Sp.mul_self_eq_one halt hnd hv (hQR hx)
  have h2 := AS35Sp.mul_self_eq_one halt hnd hv (hQR hy)
  have h3 := AS35Sp.mul_self_eq_one halt hnd hv (mul_mem (hQR hx) (hQR hy))
  apply hxy
  calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h3
    _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [inv_eq_of_mul_eq_one_left h2, inv_eq_of_mul_eq_one_left h1]

end Setting

end CFSG.LargeExtraspecial
