module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Field.ZMod
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.CGT.T75JM

open CFSG CFSG.GroupTheory Module
open scoped IsMulCommutative MatrixGroups Matrix

abbrev V3 : Type := Fin 3 → ZMod 2

@[expose] def glAct (M : GL (Fin 3) (ZMod 2)) (c : V3) : V3 :=
  (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ c

theorem glAct_mul (M N : GL (Fin 3) (ZMod 2)) (c : V3) :
    glAct (M * N) c = glAct M (glAct N c) := by
  simp [glAct, Matrix.mulVec_mulVec]

theorem glAct_one (c : V3) : glAct (1 : GL (Fin 3) (ZMod 2)) c = c := by
  simp [glAct]

theorem glAct_inv_left (M : GL (Fin 3) (ZMod 2)) (c : V3) : glAct M⁻¹ (glAct M c) = c := by
  rw [← glAct_mul, inv_mul_cancel, glAct_one]

theorem glAct_inv_right (M : GL (Fin 3) (ZMod 2)) (c : V3) : glAct M (glAct M⁻¹ c) = c := by
  rw [← glAct_mul, mul_inv_cancel, glAct_one]

@[expose] def affPerm (M : GL (Fin 3) (ZMod 2)) (t : V3) : Equiv.Perm V3 where
  toFun c := glAct M c + t
  invFun c := glAct M⁻¹ (c - t)
  left_inv c := by simp [glAct_inv_left]
  right_inv c := by simp [glAct_inv_right]

@[expose] def translate (t : V3) : Equiv.Perm V3 := affPerm 1 t

theorem translate_apply (t c : V3) : translate t c = c + t := by
  simp [translate, affPerm, glAct_one]

@[expose] def evalWord3 {H : Type*} [Group H] (x : Fin 3 → H) (w : List (Fin 3 × Bool)) : H :=
  (w.map fun p => if p.2 then x p.1 else (x p.1)⁻¹).prod

theorem evalWord3_append {H : Type*} [Group H] (x : Fin 3 → H) (w w' : List (Fin 3 × Bool)) :
    evalWord3 x (w ++ w') = evalWord3 x w * evalWord3 x w' := by
  simp [evalWord3, List.prod_append]

theorem evalWord3_map {H H' : Type*} [Group H] [Group H'] (f : H →* H') (x : Fin 3 → H)
    (w : List (Fin 3 × Bool)) : f (evalWord3 x w) = evalWord3 (fun i => f (x i)) w := by
  induction w with
  | nil => simp [evalWord3]
  | cons p w ih =>
    have h1 : evalWord3 x (p :: w) = (if p.2 then x p.1 else (x p.1)⁻¹) * evalWord3 x w := by
      simp [evalWord3]
    have h2 : evalWord3 (fun i => f (x i)) (p :: w) =
        (if p.2 then f (x p.1) else (f (x p.1))⁻¹) * evalWord3 (fun i => f (x i)) w := by
      simp [evalWord3]
    rw [h1, map_mul, ih, h2]
    by_cases hp : p.2 <;> simp [hp]

@[expose] def vecIdx (c : V3) : Fin 8 :=
  ⟨(c 0).val + 2 * (c 1).val + 4 * (c 2).val, by
    have h0 : (c 0).val < 2 := ZMod.val_lt _
    have h1 : (c 1).val < 2 := ZMod.val_lt _
    have h2 : (c 2).val < 2 := ZMod.val_lt _
    omega⟩

@[expose] def idxVec (i : Fin 8) : V3 :=
  ![((i.val % 2 : ℕ) : ZMod 2), ((i.val / 2 % 2 : ℕ) : ZMod 2), ((i.val / 4 % 2 : ℕ) : ZMod 2)]

theorem idxVec_vecIdx : ∀ c : V3, idxVec (vecIdx c) = c := by decide

theorem vecIdx_idxVec : ∀ i : Fin 8, vecIdx (idxVec i) = i := by decide

@[expose] def vecEquiv : V3 ≃ Fin 8 := ⟨vecIdx, idxVec, idxVec_vecIdx, vecIdx_idxVec⟩

@[expose] def affPerm8 (M : GL (Fin 3) (ZMod 2)) (t : V3) : Equiv.Perm (Fin 8) :=
  vecEquiv.permCongrHom (affPerm M t)

@[expose] def translate8 (t : V3) : Equiv.Perm (Fin 8) := vecEquiv.permCongrHom (translate t)

@[expose] def FinCheck (Ms : Fin 3 → GL (Fin 3) (ZMod 2))
    (Rs : List (List (Fin 3 × Bool) × List (Fin 3 × Bool))) (Ew : Fin 3 → List (Fin 3 × Bool))
    (P : List (List (Fin 3 × Bool))) : Prop :=
  ∀ t : Fin 3 → V3,
    (∀ r ∈ Rs, evalWord3 (fun k => affPerm8 (Ms k) (t k)) r.1 =
      evalWord3 (fun k => affPerm8 (Ms k) (t k)) r.2) →
    (∀ j, evalWord3 (fun k => affPerm8 (Ms k) (t k)) (Ew j) = translate8 (Pi.single j 1)) →
    ∀ w ∈ P, evalWord3 (fun k => affPerm8 (Ms k) (t k)) w = 1

instance finCheckDecidable (Ms : Fin 3 → GL (Fin 3) (ZMod 2))
    (Rs : List (List (Fin 3 × Bool) × List (Fin 3 × Bool))) (Ew : Fin 3 → List (Fin 3 × Bool))
    (P : List (List (Fin 3 × Bool))) : Decidable (FinCheck Ms Rs Ew P) := by
  unfold FinCheck
  infer_instance

section ConjLinear

variable {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

@[expose] noncomputable def conjLinear : G →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun g := (MulEquiv.toAdditive (MulAut.conjNormal g)).toLinearEquiv (ZMod.map_smul _)
  map_one' := LinearEquiv.ext fun e => Additive.toMul.injective (Subtype.ext (by
    change ((MulAut.conjNormal (1 : G) (Additive.toMul e) : V) : G) = ((Additive.toMul e : V) : G)
    rw [MulAut.conjNormal_apply]
    group))
  map_mul' g h := LinearEquiv.ext fun e => Additive.toMul.injective (Subtype.ext (by
    change ((MulAut.conjNormal (g * h) (Additive.toMul e) : V) : G) =
      ((MulAut.conjNormal g (MulAut.conjNormal h (Additive.toMul e)) : V) : G)
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    group))

theorem coe_conjLinear_apply (g : G) (e : Additive V) :
    ((Additive.toMul (conjLinear V g e) : V) : G) = g * ((Additive.toMul e : V) : G) * g⁻¹ :=
  MulAut.conjNormal_apply g (Additive.toMul e)

theorem conjLinear_eq_one_iff (hC : Subgroup.centralizer (V : Set G) ≤ V) (g : G) :
    conjLinear V g = 1 ↔ ∃ e : Additive V, ((Additive.toMul e : V) : G) = g := by
  constructor
  · intro h
    refine ⟨Additive.ofMul ⟨g, hC (Subgroup.mem_centralizer_iff.2 fun v hv => ?_)⟩, rfl⟩
    have h1 := congrArg (fun φ : Additive V ≃ₗ[ZMod 2] Additive V =>
      ((Additive.toMul (φ (Additive.ofMul ⟨v, hv⟩)) : V) : G)) h
    simp only [coe_conjLinear_apply] at h1
    change g * v * g⁻¹ = v at h1
    calc v * g = g * v * g⁻¹ * g := by rw [h1]
      _ = g * v := by group
  · rintro ⟨e, rfl⟩
    refine LinearEquiv.ext fun x => Additive.toMul.injective (Subtype.ext ?_)
    rw [coe_conjLinear_apply]
    have := mul_comm (Additive.toMul e) (Additive.toMul x)
    rw [← Subtype.coe_inj, Subgroup.coe_mul, Subgroup.coe_mul] at this
    rw [this, mul_inv_cancel_right]
    rfl

end ConjLinear

theorem card_linearEquiv_eq {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {n : ℕ} (hn : finrank (ZMod 2) E = n) :
    Nat.card (E ≃ₗ[ZMod 2] E) = Nat.card (GL (Fin n) (ZMod 2)) := by
  let b := (Module.finBasisOfFinrankEq (ZMod 2) E hn).equivFun
  let e₁ : (E ≃ₗ[ZMod 2] E) ≃ ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    { toFun := fun f => b.symm.trans (f.trans b)
      invFun := fun g => b.trans (g.trans b.symm)
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  rw [Nat.card_congr e₁]
  exact Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv)

theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem card_V3 : Nat.card (Multiplicative V3) = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem sq_eq_one_V3 (c : Multiplicative V3) : c ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  funext i
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  simpa using h2 (Multiplicative.toAdd c i)

variable {K : Type} [Group K]

theorem eps_comm' (ε : Multiplicative V3 →* K) (c d : Multiplicative V3) :
    ε c * ε d = ε d * ε c := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem isElemAb_range (ε : Multiplicative V3 →* K) : IsElementaryAbelian 2 ε.range where
  toIsMulCommutative := ⟨⟨fun x y => by
    obtain ⟨c, hc⟩ := x.2
    obtain ⟨d, hd⟩ := y.2
    apply Subtype.ext
    show (x : K) * y = y * x
    rw [← hc, ← hd, eps_comm']⟩⟩
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨c, hc⟩ := x.2
    apply Subtype.ext
    show (x : K) ^ 2 = 1
    rw [← hc, ← map_pow, sq_eq_one_V3, map_one]

structure AffHyp (ε : Multiplicative V3 →* K) (a : Fin 3 → K)
    (M : Fin 3 → GL (Fin 3) (ZMod 2)) : Prop where
  gen : Subgroup.closure (Set.range a) = ⊤
  inj : Function.Injective ε
  norm : ∀ (k : Fin 3) (c : V3),
    a k * ε (Multiplicative.ofAdd c) * (a k)⁻¹ = ε (Multiplicative.ofAdd (glAct (M k) c))
  cent : ∀ x : K, (∀ c, x * ε c = ε c * x) → x ∈ ε.range

namespace AffHyp

variable {ε : Multiplicative V3 →* K} {a : Fin 3 → K} {M : Fin 3 → GL (Fin 3) (ZMod 2)}
  (h : AffHyp ε a M)

include h

theorem a_mem_normalizer (k : Fin 3) : a k ∈ Subgroup.normalizer (ε.range : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd (glAct (M k) c.toAdd), ?_⟩
    rw [← h.norm k c.toAdd]
    rfl
  · rintro ⟨c', hc'⟩
    refine ⟨Multiplicative.ofAdd (glAct (M k)⁻¹ c'.toAdd), ?_⟩
    have h1 := h.norm k (glAct (M k)⁻¹ c'.toAdd)
    rw [glAct_inv_right] at h1
    have h2 : a k * x * (a k)⁻¹ = ε c' := hc'.symm
    have h4 : ε c' = a k * ε (Multiplicative.ofAdd (glAct (M k)⁻¹ c'.toAdd)) * (a k)⁻¹ := h1.symm
    have : x = (a k)⁻¹ * (a k * x * (a k)⁻¹) * a k := by group
    rw [this, h2, h4]
    group

theorem normalizer_eq_top : Subgroup.normalizer (ε.range : Set K) = ⊤ := by
  rw [eq_top_iff, ← h.gen]
  exact (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact h.a_mem_normalizer k)

theorem range_normal : ε.range.Normal := Subgroup.normalizer_eq_top_iff.1 h.normalizer_eq_top

theorem card_E : Nat.card ε.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective h.inj).toEquiv]
  exact card_V3

theorem centralizer_le : Subgroup.centralizer (ε.range : Set K) ≤ ε.range := fun x hx =>
  h.cent x fun c => (Subgroup.mem_centralizer_iff.1 hx _ (MonoidHom.mem_range.2 ⟨c, rfl⟩)).symm

theorem card_dvd [Finite K] : Nat.card K ∣ 1344 := by
  classical
  have := h.range_normal
  have := isElemAb_range ε
  have hE := h.card_E
  have : Finite (Additive ε.range) := inferInstanceAs (Finite ε.range)
  have : FiniteDimensional (ZMod 2) (Additive ε.range) := Module.Finite.of_finite
  have hrank : finrank (ZMod 2) (Additive ε.range) = 3 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ε.range)
    rw [Nat.card_zmod, show Nat.card (Additive ε.range) = Nat.card ε.range from rfl, hE] at h1
    have h2 : 2 ^ finrank (ZMod 2) (Additive ε.range) = 2 ^ 3 := h1.symm.trans (by norm_num)
    exact Nat.pow_right_injective le_rfl h2
  have hGL : Nat.card (Additive ε.range ≃ₗ[ZMod 2] Additive ε.range) = 168 := by
    rw [card_linearEquiv_eq hrank, card_GL_three_two]
  have hker : (conjLinear ε.range).ker = ε.range := by
    ext g
    rw [MonoidHom.mem_ker, conjLinear_eq_one_iff _ h.centralizer_le]
    exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hg => ⟨Additive.ofMul ⟨g, hg⟩, rfl⟩⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (conjLinear ε.range).ker
  have h2 : Nat.card (K ⧸ (conjLinear ε.range).ker) = Nat.card (conjLinear ε.range).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  have h3 : Nat.card (conjLinear ε.range).range ∣ 168 := by
    rw [← hGL]
    exact Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card (conjLinear ε.range).ker = 8 := by rw [hker, hE]
  rw [h2, h4] at h1
  obtain ⟨m, hm⟩ := h3
  refine ⟨m, ?_⟩
  calc 1344 = 168 * 8 := by norm_num
    _ = (Nat.card (conjLinear ε.range).range * m) * 8 := by rw [← hm]
    _ = (Nat.card (conjLinear ε.range).range * 8) * m := by ring
    _ = Nat.card K * m := by rw [h1]

end AffHyp

@[expose] def powZ4 (ρ : K) (i : ZMod 4) : K := ρ ^ i.val

theorem pow_mod4 {ρ : K} (hρ : ρ ^ 4 = 1) (n : ℕ) : ρ ^ (n % 4) = ρ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hρ, one_pow, mul_one]

theorem powZ4_add {ρ : K} (hρ : ρ ^ 4 = 1) (i j : ZMod 4) :
    powZ4 ρ (i + j) = powZ4 ρ i * powZ4 ρ j := by
  unfold powZ4
  rw [ZMod.val_add, pow_mod4 hρ, pow_add]

theorem powZ4_zero (ρ : K) : powZ4 ρ 0 = 1 := by simp [powZ4]

theorem powZ4_neg {ρ : K} (hρ : ρ ^ 4 = 1) (i : ZMod 4) : powZ4 ρ (-i) = (powZ4 ρ i)⁻¹ := by
  have := powZ4_add hρ i (-i)
  rw [add_neg_cancel, powZ4_zero] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem powZ4_conj {s ρ : K} (hs : s * s = 1) (hsρ : s * ρ * s = ρ⁻¹)
    (i : ZMod 4) : s * powZ4 ρ i * s = (powZ4 ρ i)⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  unfold powZ4
  have h1 : s * ρ ^ i.val * s = (s * ρ * s) ^ i.val := by
    have := conj_pow (a := s) (b := ρ) (i := i.val)
    rw [hs'] at this
    exact this.symm
  rw [h1, hsρ, inv_pow]

@[expose] def dihHom (s ρ : K) (hs : s * s = 1) (hρ : ρ ^ 4 = 1) (hsρ : s * ρ * s = ρ⁻¹) :
    DihedralGroup 4 →* K where
  toFun x := match x with
    | DihedralGroup.r i => powZ4 ρ i
    | DihedralGroup.sr i => s * powZ4 ρ i
  map_one' := by
    show powZ4 ρ 0 = 1
    exact powZ4_zero ρ
  map_mul' x y := by
    have hc := powZ4_conj hs hsρ
    rcases x with i | i <;> rcases y with j | j
    · rw [DihedralGroup.r_mul_r]
      exact powZ4_add hρ i j
    · rw [DihedralGroup.r_mul_sr]
      show s * powZ4 ρ (j - i) = powZ4 ρ i * (s * powZ4 ρ j)
      have h1 : powZ4 ρ i * s = s * (powZ4 ρ i)⁻¹ := by
        have := hc i
        calc powZ4 ρ i * s = s * (s * powZ4 ρ i * s) := by
              rw [← mul_assoc, ← mul_assoc, hs, one_mul]
          _ = s * (powZ4 ρ i)⁻¹ := by rw [this]
      rw [← mul_assoc, h1, mul_assoc, ← powZ4_neg hρ, ← powZ4_add hρ, sub_eq_neg_add]
    · rw [DihedralGroup.sr_mul_r]
      show s * powZ4 ρ (i + j) = s * powZ4 ρ i * powZ4 ρ j
      rw [powZ4_add hρ, mul_assoc]
    · rw [DihedralGroup.sr_mul_sr]
      show powZ4 ρ (j - i) = s * powZ4 ρ i * (s * powZ4 ρ j)
      have := hc i
      calc powZ4 ρ (j - i) = (powZ4 ρ i)⁻¹ * powZ4 ρ j := by
            rw [sub_eq_neg_add, powZ4_add hρ, powZ4_neg hρ]
        _ = s * powZ4 ρ i * s * powZ4 ρ j := by rw [this]
        _ = s * powZ4 ρ i * (s * powZ4 ρ j) := by rw [mul_assoc (s * powZ4 ρ i) s]

@[expose] def matD (S R : GL (Fin 3) (ZMod 2)) : DihedralGroup 4 → GL (Fin 3) (ZMod 2)
  | DihedralGroup.r i => R ^ i.val
  | DihedralGroup.sr i => S * R ^ i.val

structure D8Hyp (ε : Multiplicative V3 →* K) (s ρ : K) (S R : GL (Fin 3) (ZMod 2)) : Prop where
  sq : s * s = 1
  four : ρ ^ 4 = 1
  conj : s * ρ * s = ρ⁻¹
  norm_s : ∀ c : V3, s * ε (Multiplicative.ofAdd c) * s⁻¹ =
    ε (Multiplicative.ofAdd (glAct S c))
  norm_ρ : ∀ c : V3, ρ * ε (Multiplicative.ofAdd c) * ρ⁻¹ =
    ε (Multiplicative.ofAdd (glAct R c))
  dist : ∀ d : DihedralGroup 4, (∀ c, glAct (matD S R d) c = c) → d = 1

namespace D8Hyp

variable {ε : Multiplicative V3 →* K} {s ρ : K} {S R : GL (Fin 3) (ZMod 2)}
  (hd : D8Hyp ε s ρ S R)

include hd

theorem norm_pow (n : ℕ) (c : V3) :
    ρ ^ n * ε (Multiplicative.ofAdd c) * (ρ ^ n)⁻¹ =
      ε (Multiplicative.ofAdd (glAct (R ^ n) c)) := by
  induction n generalizing c with
  | zero => simp [glAct_one]
  | succ n ih =>
    have h1 : ρ ^ (n + 1) * ε (Multiplicative.ofAdd c) * (ρ ^ (n + 1))⁻¹ =
        ρ * (ρ ^ n * ε (Multiplicative.ofAdd c) * (ρ ^ n)⁻¹) * ρ⁻¹ := by
      rw [pow_succ']
      group
    rw [h1, ih, hd.norm_ρ, pow_succ', glAct_mul]

theorem norm_dih (d : DihedralGroup 4) (c : V3) :
    dihHom s ρ hd.sq hd.four hd.conj d * ε (Multiplicative.ofAdd c) *
        (dihHom s ρ hd.sq hd.four hd.conj d)⁻¹ =
      ε (Multiplicative.ofAdd (glAct (matD S R d) c)) := by
  rcases d with i | i
  · show powZ4 ρ i * ε (Multiplicative.ofAdd c) * (powZ4 ρ i)⁻¹ = _
    exact hd.norm_pow i.val c
  · show s * powZ4 ρ i * ε (Multiplicative.ofAdd c) * (s * powZ4 ρ i)⁻¹ =
      ε (Multiplicative.ofAdd (glAct (S * R ^ i.val) c))
    have h1 : s * powZ4 ρ i * ε (Multiplicative.ofAdd c) * (s * powZ4 ρ i)⁻¹ =
        s * (powZ4 ρ i * ε (Multiplicative.ofAdd c) * (powZ4 ρ i)⁻¹) * s⁻¹ := by group
    rw [h1]
    show s * (ρ ^ i.val * ε (Multiplicative.ofAdd c) * (ρ ^ i.val)⁻¹) * s⁻¹ = _
    rw [hd.norm_pow, hd.norm_s, glAct_mul]

theorem f_injective (hinj : Function.Injective ε) :
    Function.Injective (dihHom s ρ hd.sq hd.four hd.conj) := by
  rw [injective_iff_map_eq_one]
  intro d hd1
  apply hd.dist d
  intro c
  have h1 := hd.norm_dih d c
  rw [hd1] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  exact (Multiplicative.ofAdd.injective (hinj h1)).symm

theorem inf_range_eq_bot (hinj : Function.Injective ε) :
    (dihHom s ρ hd.sq hd.four hd.conj).range ⊓ ε.range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨d, hdx⟩, ⟨c₀, hc₀⟩⟩ := Subgroup.mem_inf.1 hx
  have hfix : ∀ c : V3, glAct (matD S R d) c = c := by
    intro c
    have h1 := hd.norm_dih d c
    rw [hdx, ← hc₀, eps_comm' ε c₀ (Multiplicative.ofAdd c), mul_assoc, mul_inv_cancel,
      mul_one] at h1
    exact (Multiplicative.ofAdd.injective (hinj h1)).symm
  have hd1 : d = 1 := hd.dist d hfix
  rw [← hdx, hd1, map_one]
  exact Subgroup.one_mem _

end D8Hyp

structure Cplt (ε : Multiplicative V3 →* K) (D : Subgroup K) : Prop where
  inj : Function.Injective ε
  normal : ε.range.Normal
  cent : ∀ x : K, (∀ c, x * ε c = ε c * x) → x ∈ ε.range
  inf_eq : ε.range ⊓ D = ⊥
  sup_eq : ε.range ⊔ D = ⊤

namespace AffHyp

variable {ε : Multiplicative V3 →* K} {a : Fin 3 → K} {M : Fin 3 → GL (Fin 3) (ZMod 2)}
  {s ρ : K} {S R : GL (Fin 3) (ZMod 2)}

theorem exists_complement [Finite K] (h : AffHyp ε a M) (hd : D8Hyp ε s ρ S R) :
    ∃ D : Subgroup K, ε.range ⊓ D = ⊥ ∧ ε.range ⊔ D = ⊤ := by
  classical
  have := h.range_normal
  have := isElemAb_range ε
  have hQE := hd.inf_range_eq_bot h.inj
  have hEQ : ε.range ⊓ (dihHom s ρ hd.sq hd.four hd.conj).range = ⊥ := by
    rw [inf_comm]
    exact hQE
  have hQcard : Nat.card (dihHom s ρ hd.sq hd.four hd.conj).range = 8 := by
    have := Nat.card_congr (MonoidHom.ofInjective (hd.f_injective h.inj)).toEquiv
    rw [DihedralGroup.nat_card] at this
    exact this.symm
  have hsup : Nat.card (ε.range ⊔ (dihHom s ρ hd.sq hd.four hd.conj).range : Subgroup K) = 64 := by
    have := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer ε.range _
      (by rw [h.normalizer_eq_top]; exact le_top) (disjoint_iff.2 hEQ)
    rw [h.card_E, hQcard] at this
    exact this
  have hidx := Subgroup.card_mul_index (ε.range ⊔ (dihHom s ρ hd.sq hd.four hd.conj).range)
  rw [hsup] at hidx
  have h1 : 64 * (ε.range ⊔ (dihHom s ρ hd.sq hd.four hd.conj).range).index ∣ 64 * 21 := by
    rw [hidx]
    exact h.card_dvd
  have h2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hcop : Nat.Coprime (ε.range ⊔ (dihHom s ρ hd.sq hd.four hd.conj).range).index
      (Nat.card ε.range) := by
    rw [h.card_E]
    exact Nat.Coprime.coprime_dvd_left h2 (by decide)
  obtain ⟨D, -, hD1, hD2⟩ := abelian_normal_coprime_index_complement_lifting ε.range _
    (dihHom s ρ hd.sq hd.four hd.conj).range hcop hEQ rfl
  exact ⟨D, hD1, hD2⟩

theorem cplt (h : AffHyp ε a M) {D : Subgroup K} (h1 : ε.range ⊓ D = ⊥) (h2 : ε.range ⊔ D = ⊤) :
    Cplt ε D :=
  ⟨h.inj, h.range_normal, h.cent, h1, h2⟩

end AffHyp

namespace Cplt

variable {ε : Multiplicative V3 →* K} {D : Subgroup K} (c : Cplt ε D)

@[expose] noncomputable def partE (g : K) : ε.range :=
  have := c.normal
  ComplementLifting.part c.inf_eq c.sup_eq g

theorem partE_spec (g : K) : ((c.partE g : ε.range) : K)⁻¹ * g ∈ D := by
  have := c.normal
  exact ComplementLifting.part_spec c.inf_eq c.sup_eq (Subgroup.mem_top g)

theorem partE_eq {g : K} {n : ε.range} (hn : (n : K)⁻¹ * g ∈ D) : c.partE g = n := by
  have := c.normal
  exact ComplementLifting.part_eq c.inf_eq c.sup_eq (Subgroup.mem_top g) hn

@[expose] noncomputable def cpart (g : K) : V3 :=
  ((MonoidHom.ofInjective c.inj).symm (c.partE g)).toAdd

theorem eps_cpart (g : K) :
    ε (Multiplicative.ofAdd (c.cpart g)) = ((c.partE g : ε.range) : K) := by
  unfold cpart
  rw [ofAdd_toAdd]
  exact MonoidHom.apply_ofInjective_symm c.inj _

theorem cpart_spec (g : K) : (ε (Multiplicative.ofAdd (c.cpart g)))⁻¹ * g ∈ D := by
  rw [c.eps_cpart g]
  exact c.partE_spec g

theorem cpart_eq {g : K} {x : V3} (hx : (ε (Multiplicative.ofAdd x))⁻¹ * g ∈ D) :
    c.cpart g = x := by
  have h1 : c.partE g = MonoidHom.ofInjective c.inj (Multiplicative.ofAdd x) := c.partE_eq hx
  unfold cpart
  rw [h1, MulEquiv.symm_apply_apply, toAdd_ofAdd]

theorem cpart_eps (x : V3) : c.cpart (ε (Multiplicative.ofAdd x)) = x := by
  apply c.cpart_eq
  rw [inv_mul_cancel]
  exact D.one_mem

theorem cpart_mul_right {g l : K} (hl : l ∈ D) : c.cpart (g * l) = c.cpart g := by
  apply c.cpart_eq
  have := D.mul_mem (c.cpart_spec g) hl
  simpa [mul_assoc] using this

theorem cpart_mul_left (x : V3) (g : K) :
    c.cpart (ε (Multiplicative.ofAdd x) * g) = x + c.cpart g := by
  apply c.cpart_eq
  have h1 := c.cpart_spec g
  have : (ε (Multiplicative.ofAdd (x + c.cpart g)))⁻¹ * (ε (Multiplicative.ofAdd x) * g) =
      (ε (Multiplicative.ofAdd (c.cpart g)))⁻¹ * g := by
    rw [ofAdd_add, map_mul]
    group
  rw [this]
  exact h1

@[expose] noncomputable def act (k : K) (x : V3) : V3 := c.cpart (k * ε (Multiplicative.ofAdd x))

theorem act_one (x : V3) : c.act 1 x = x := by
  unfold act
  rw [one_mul]
  exact c.cpart_eps x

theorem act_mul (k k' : K) (x : V3) : c.act (k * k') x = c.act k (c.act k' x) := by
  unfold act
  have hℓ := c.cpart_spec (k' * ε (Multiplicative.ofAdd x))
  set y := c.cpart (k' * ε (Multiplicative.ofAdd x)) with hy
  have : k * k' * ε (Multiplicative.ofAdd x) = (k * ε (Multiplicative.ofAdd y)) *
      ((ε (Multiplicative.ofAdd y))⁻¹ * (k' * ε (Multiplicative.ofAdd x))) := by group
  rw [this]
  exact c.cpart_mul_right hℓ

@[expose] noncomputable def piHom : K →* Equiv.Perm V3 where
  toFun k :=
    { toFun := c.act k
      invFun := c.act k⁻¹
      left_inv := fun x => by rw [← c.act_mul, inv_mul_cancel, c.act_one]
      right_inv := fun x => by rw [← c.act_mul, mul_inv_cancel, c.act_one] }
  map_one' := Equiv.ext fun x => c.act_one x
  map_mul' k k' := Equiv.ext fun x => c.act_mul k k' x

theorem piHom_apply (k : K) (x : V3) : c.piHom k x = c.act k x := rfl

theorem piHom_eps (x : V3) : c.piHom (ε (Multiplicative.ofAdd x)) = translate x := by
  ext y
  rw [piHom_apply, translate_apply, act, ← map_mul, ← ofAdd_add, c.cpart_eps, add_comm]

theorem piHom_a {a : Fin 3 → K} {M : Fin 3 → GL (Fin 3) (ZMod 2)} (h : AffHyp ε a M) (k : Fin 3) :
    c.piHom (a k) = affPerm (M k) (c.cpart (a k)) := by
  ext x
  rw [piHom_apply, act]
  have h1 : a k * ε (Multiplicative.ofAdd x) = ε (Multiplicative.ofAdd (glAct (M k) x)) * a k := by
    have := h.norm k x
    calc a k * ε (Multiplicative.ofAdd x)
        = a k * ε (Multiplicative.ofAdd x) * (a k)⁻¹ * a k := by group
      _ = ε (Multiplicative.ofAdd (glAct (M k) x)) * a k := by rw [this]
  have h2 : (affPerm (M k) (c.cpart (a k))) x = glAct (M k) x + c.cpart (a k) := rfl
  rw [h2, h1, c.cpart_mul_left]

theorem piHom_injective : Function.Injective c.piHom := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hx : ∀ x : V3, c.cpart (k * ε (Multiplicative.ofAdd x)) = x := fun x => by
    have h1 : c.piHom k x = (1 : Equiv.Perm V3) x := by rw [hk]
    exact h1
  have hkD : k ∈ D := by
    have h0 := hx 0
    rw [ofAdd_zero, map_one, mul_one] at h0
    have := c.cpart_spec k
    rw [h0, ofAdd_zero, map_one, inv_one, one_mul] at this
    exact this
  have hcomm : ∀ x : V3, k * ε (Multiplicative.ofAdd x) = ε (Multiplicative.ofAdd x) * k := by
    intro x
    have h1 : (ε (Multiplicative.ofAdd x))⁻¹ * (k * ε (Multiplicative.ofAdd x)) ∈ D := by
      have := c.cpart_spec (k * ε (Multiplicative.ofAdd x))
      rwa [hx x] at this
    have h2 : k⁻¹ * ((ε (Multiplicative.ofAdd x))⁻¹ * (k * ε (Multiplicative.ofAdd x))) ∈ D :=
      D.mul_mem (D.inv_mem hkD) h1
    have hu : ε (Multiplicative.ofAdd x) ∈ ε.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
    have h3 : k⁻¹ * ((ε (Multiplicative.ofAdd x))⁻¹ * (k * ε (Multiplicative.ofAdd x))) ∈
        ε.range := by
      have h4 := c.normal.conj_mem _ (ε.range.inv_mem hu) k⁻¹
      have h5 := ε.range.mul_mem h4 hu
      have e : k⁻¹ * ((ε (Multiplicative.ofAdd x))⁻¹ * (k * ε (Multiplicative.ofAdd x))) =
          k⁻¹ * (ε (Multiplicative.ofAdd x))⁻¹ * k⁻¹⁻¹ * ε (Multiplicative.ofAdd x) := by group
      rw [e]
      exact h5
    have h6 : k⁻¹ * ((ε (Multiplicative.ofAdd x))⁻¹ * (k * ε (Multiplicative.ofAdd x))) ∈
        ε.range ⊓ D := ⟨h3, h2⟩
    rw [c.inf_eq, Subgroup.mem_bot] at h6
    have h7 := inv_mul_eq_one.1 h6
    calc k * ε (Multiplicative.ofAdd x)
        = ε (Multiplicative.ofAdd x) * ((ε (Multiplicative.ofAdd x))⁻¹ *
            (k * ε (Multiplicative.ofAdd x))) := by group
      _ = ε (Multiplicative.ofAdd x) * k := by rw [← h7]
  have hkE : k ∈ ε.range := c.cent k fun y => by simpa using hcomm y.toAdd
  have : k ∈ ε.range ⊓ D := ⟨hkE, hkD⟩
  rw [c.inf_eq, Subgroup.mem_bot] at this
  exact this

end Cplt

theorem rels_of_finCheck {ε : Multiplicative V3 →* K} {a : Fin 3 → K}
    {M : Fin 3 → GL (Fin 3) (ZMod 2)} {s ρ : K} {S R : GL (Fin 3) (ZMod 2)} [Finite K]
    (h : AffHyp ε a M) (hd : D8Hyp ε s ρ S R)
    {Rs : List (List (Fin 3 × Bool) × List (Fin 3 × Bool))} {Ew : Fin 3 → List (Fin 3 × Bool)}
    {P : List (List (Fin 3 × Bool))} (hfc : FinCheck M Rs Ew P)
    (hrel : ∀ r ∈ Rs, evalWord3 a r.1 = evalWord3 a r.2)
    (hEw : ∀ j, evalWord3 a (Ew j) = ε (Multiplicative.ofAdd (Pi.single j 1))) :
    ∀ w ∈ P, evalWord3 a w = 1 := by
  obtain ⟨D, hD1, hD2⟩ := h.exists_complement hd
  have c := h.cplt hD1 hD2
  let π8 : K →* Equiv.Perm (Fin 8) := vecEquiv.permCongrHom.toMonoidHom.comp c.piHom
  have hπ : ∀ w, π8 (evalWord3 a w) =
      evalWord3 (fun k => affPerm8 (M k) (c.cpart (a k))) w := by
    intro w
    rw [evalWord3_map π8 a w]
    congr 1
    funext k
    exact congrArg vecEquiv.permCongrHom (c.piHom_a h k)
  have hπinj : Function.Injective π8 := vecEquiv.permCongrHom.injective.comp c.piHom_injective
  intro w hw
  apply hπinj
  rw [hπ, map_one]
  refine hfc (fun k => c.cpart (a k)) (fun r hr => ?_) (fun j => ?_) w hw
  · rw [← hπ, ← hπ, hrel r hr]
  · rw [← hπ, hEw j]
    exact congrArg vecEquiv.permCongrHom (c.piHom_eps _)

end CFSG.CGT.T75JM
