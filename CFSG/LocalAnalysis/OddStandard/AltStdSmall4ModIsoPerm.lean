module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructPerm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.ModIso

open Equiv Subgroup Matrix
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

variable {n : ℕ}

section Bits

@[expose] def bitsFun (i : Fin 8) : Fin 3 → ZMod 2 :=
  ![((i.val % 2 : ℕ) : ZMod 2), ((i.val / 2 % 2 : ℕ) : ZMod 2), ((i.val / 4 % 2 : ℕ) : ZMod 2)]

@[expose] def unbits (v : Fin 3 → ZMod 2) : Fin 8 :=
  ⟨(v 0).val + 2 * (v 1).val + 4 * (v 2).val, by
    have h0 := ZMod.val_lt (v 0)
    have h1 := ZMod.val_lt (v 1)
    have h2 := ZMod.val_lt (v 2)
    omega⟩

theorem unbits_bitsFun : ∀ i : Fin 8, unbits (bitsFun i) = i := by decide +kernel

theorem bitsFun_unbits : ∀ v : Fin 3 → ZMod 2, bitsFun (unbits v) = v := by decide +kernel

@[expose] def bits : Fin 8 ≃ (Fin 3 → ZMod 2) where
  toFun := bitsFun
  invFun := unbits
  left_inv := unbits_bitsFun
  right_inv := bitsFun_unbits

theorem bitsFun_xr : ∀ i j : Fin 8, bitsFun (xr i j) = bitsFun i + bitsFun j := by
  decide +kernel

theorem bits_xr (i j : Fin 8) : bits (xr i j) = bits i + bits j := bitsFun_xr i j

theorem bits_zero : bits 0 = 0 := by decide +kernel

theorem bits_symm_add (v w : Fin 3 → ZMod 2) :
    bits.symm (v + w) = xr (bits.symm v) (bits.symm w) := by
  apply bits.injective
  rw [bits_xr, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem bits_symm_zero : bits.symm 0 = 0 := by
  rw [Equiv.symm_apply_eq, bits_zero]

end Bits

section Xor

theorem xr_self (v : Fin 8) : xr v v = 0 := Fin.ext (Nat.xor_self v.val)

theorem xor_xor_cancel (a b : ℕ) : a ^^^ b ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_linear (x y c : ℕ) : x ^^^ y ^^^ c ^^^ c = (x ^^^ c) ^^^ (y ^^^ c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases c.testBit i <;> rfl

end Xor

section Lin

@[expose] def glPerm (A : GL (Fin 3) (ZMod 2)) : Perm (Fin 3 → ZMod 2) where
  toFun v := (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v
  invFun v := ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v
  left_inv v := by
    simp only
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv v := by
    simp only
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

@[expose] def glPermHom : GL (Fin 3) (ZMod 2) →* Perm (Fin 3 → ZMod 2) where
  toFun := glPerm
  map_one' := Equiv.ext fun v => by
    show ((1 : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v
    rw [Units.val_one, one_mulVec]
  map_mul' A B := Equiv.ext fun v => by
    show ((A * B : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v =
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
    rw [Units.val_mul, mulVec_mulVec]

@[expose] def linPerm8 : GL (Fin 3) (ZMod 2) →* Perm (Fin 8) :=
  (bits.symm.permCongrHom).toMonoidHom.comp glPermHom

theorem linPerm8_apply (A : GL (Fin 3) (ZMod 2)) (i : Fin 8) :
    linPerm8 A i = bits.symm ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ bits i) := rfl

theorem bits_linPerm8 (A : GL (Fin 3) (ZMod 2)) (i : Fin 8) :
    bits (linPerm8 A i) = (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ bits i := by
  rw [linPerm8_apply, Equiv.apply_symm_apply]

theorem linPerm8_xr (A : GL (Fin 3) (ZMod 2)) (i j : Fin 8) :
    linPerm8 A (xr i j) = xr (linPerm8 A i) (linPerm8 A j) := by
  apply bits.injective
  rw [bits_linPerm8, bits_xr, bits_xr, bits_linPerm8, bits_linPerm8, mulVec_add]

theorem linPerm8_zero (A : GL (Fin 3) (ZMod 2)) : linPerm8 A 0 = 0 := by
  rw [linPerm8_apply, bits_zero, mulVec_zero, bits_symm_zero]

theorem sign_linPerm8 (A : GL (Fin 3) (ZMod 2)) : Perm.sign (linPerm8 A) = 1 := by
  have hf := eq_lin8 (f := linPerm8 A) (linPerm8_xr A)
  have hinj : Function.Injective (lin8 (linPerm8 A 1) (linPerm8 A 2) (linPerm8 A 4)) := by
    rw [← hf]
    exact (linPerm8 A).injective
  have h := sign_lin8 _ _ _ hinj
  convert h using 2
  exact Equiv.ext fun x => congrFun hf x

theorem linPerm8_injective : Function.Injective linPerm8 := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h : ∀ v, (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v := fun v => by
    have h1 := congrArg (fun σ : Perm (Fin 8) => bits (σ (bits.symm v))) hA
    simp only [bits_linPerm8, Equiv.apply_symm_apply, Perm.one_apply] at h1
    exact h1
  apply Units.ext
  rw [Units.val_one]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, one_mulVec]

theorem isXorAdd_linPerm8 (A : GL (Fin 3) (ZMod 2)) : N0.IsXorAdd (linPerm8 A) := fun i j => by
  rw [← N0.xr_eq_xor, linPerm8_xr, N0.xr_eq_xor]

@[expose] def linPerm (hn : 8 ≤ n) : GL (Fin 3) (ZMod 2) →* Perm (Fin n) :=
  (N0.ext8Hom hn).comp linPerm8

theorem linPerm_eq_ext8 (hn : 8 ≤ n) (A : GL (Fin 3) (ZMod 2)) :
    linPerm hn A = N0.ext8 hn (linPerm8 A) := rfl

theorem val_linPerm_of_lt (hn : 8 ≤ n) (A : GL (Fin 3) (ZMod 2)) {i : Fin n} (hi : i.val < 8) :
    (linPerm hn A i).val = (linPerm8 A ⟨i.val, hi⟩).val :=
  congrArg Fin.val (N0.ext8_apply_lt hn (linPerm8 A) ⟨i.val, hi⟩)

theorem linPerm_of_ge (hn : 8 ≤ n) (A : GL (Fin 3) (ZMod 2)) {i : Fin n} (hi : 8 ≤ i.val) :
    linPerm hn A i = i :=
  N0.ext8_apply_ge hn (linPerm8 A) hi

theorem linPerm_pt_zero (hn : 8 ≤ n) (A : GL (Fin 3) (ZMod 2)) : linPerm hn A (pt hn 0) = pt hn 0 :=
  Fin.ext (by
    rw [val_linPerm_of_lt hn A (i := pt hn 0) (show (0 : ℕ) < 8 by norm_num)]
    exact congrArg Fin.val (linPerm8_zero A))

theorem linPerm_mem_alternatingGroup (hn : 8 ≤ n) (A : GL (Fin 3) (ZMod 2)) :
    linPerm hn A ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, linPerm_eq_ext8, N0.sign_ext8, sign_linPerm8]

theorem linPerm_injective (hn : 8 ≤ n) : Function.Injective (linPerm (n := n) hn) :=
  (N0.ext8_injective hn).comp linPerm8_injective

theorem linPerm_mul_tr (hn : 8 ≤ n) (A : GL (Fin 3) (ZMod 2)) (v : Fin 8) :
    linPerm hn A * tr hn v = tr hn (linPerm8 A v) * linPerm hn A := by
  rw [linPerm_eq_ext8, ← N0.ext8_conj_tr hn (isXorAdd_linPerm8 A) v, inv_mul_cancel_right]

@[expose] def lin (hn : 8 ≤ n) : GL (Fin 3) (ZMod 2) →* alternatingGroup (Fin n) :=
  (linPerm hn).codRestrict _ (linPerm_mem_alternatingGroup hn)

theorem coe_lin (hn : 8 ≤ n) (A : GL (Fin 3) (ZMod 2)) :
    ((lin hn A : alternatingGroup (Fin n)) : Perm (Fin n)) = linPerm hn A := rfl

theorem lin_injective (hn : 8 ≤ n) : Function.Injective (lin (n := n) hn) := fun A B h =>
  linPerm_injective hn (congrArg Subtype.val h)

end Lin

section AGL

theorem eq_of_tr_mul_linPerm (hn : 8 ≤ n) {b b' : Fin 8} {A A' : GL (Fin 3) (ZMod 2)}
    (h : tr hn b * linPerm hn A = tr hn b' * linPerm hn A') : b = b' ∧ A = A' := by
  have h0 := congrArg (fun σ : Perm (Fin n) => (σ (pt hn 0)).val) h
  simp only [Perm.mul_apply, linPerm_pt_zero, val_tr_pt_zero] at h0
  have hb : b = b' := Fin.ext h0
  subst hb
  exact ⟨rfl, linPerm_injective hn (mul_left_cancel h)⟩

@[expose] def AGL (hn : 8 ≤ n) : Subgroup (alternatingGroup (Fin n)) where
  carrier := {σ | ∃ (b : Fin 8) (A : GL (Fin 3) (ZMod 2)),
    (σ : Perm (Fin n)) = tr hn b * linPerm hn A}
  mul_mem' := by
    rintro σ τ ⟨b, A, hσ⟩ ⟨b', A', hτ⟩
    refine ⟨xr b (linPerm8 A b'), A * A', ?_⟩
    rw [Subgroup.coe_mul, hσ, hτ, map_mul, ← tr_mul_tr, mul_assoc, ← mul_assoc (linPerm hn A),
      linPerm_mul_tr, mul_assoc, mul_assoc]
  one_mem' := ⟨0, 1, by rw [Subgroup.coe_one, tr_zero, map_one, one_mul]⟩
  inv_mem' := by
    rintro σ ⟨b, A, hσ⟩
    refine ⟨linPerm8 A⁻¹ b, A⁻¹, ?_⟩
    rw [Subgroup.coe_inv, hσ, _root_.mul_inv_rev, tr_inv, ← map_inv, linPerm_mul_tr]

noncomputable def linPartFun (hn : 8 ≤ n) (σ : AGL hn) : GL (Fin 3) (ZMod 2) :=
  σ.2.choose_spec.choose

theorem coe_eq_tr_mul_linPartFun (hn : 8 ≤ n) (σ : AGL hn) :
    ((σ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      tr hn σ.2.choose * linPerm hn (linPartFun hn σ) :=
  σ.2.choose_spec.choose_spec

theorem exists_eq_tr_mul_linPartFun (hn : 8 ≤ n) (σ : AGL hn) :
    ∃ b : Fin 8, ((σ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      tr hn b * linPerm hn (linPartFun hn σ) :=
  ⟨_, coe_eq_tr_mul_linPartFun hn σ⟩

theorem linPartFun_eq (hn : 8 ≤ n) {σ : AGL hn} {b : Fin 8} {A : GL (Fin 3) (ZMod 2)}
    (h : ((σ : alternatingGroup (Fin n)) : Perm (Fin n)) = tr hn b * linPerm hn A) :
    linPartFun hn σ = A :=
  (eq_of_tr_mul_linPerm hn ((coe_eq_tr_mul_linPartFun hn σ).symm.trans h)).2

noncomputable def linPart (hn : 8 ≤ n) : AGL hn →* GL (Fin 3) (ZMod 2) where
  toFun := linPartFun hn
  map_one' := linPartFun_eq hn (b := 0) (A := 1) (by
    rw [OneMemClass.coe_one, Subgroup.coe_one, tr_zero, map_one, one_mul])
  map_mul' σ τ := by
    obtain ⟨b₁, h₁⟩ := exists_eq_tr_mul_linPartFun hn σ
    obtain ⟨b₂, h₂⟩ := exists_eq_tr_mul_linPartFun hn τ
    apply linPartFun_eq hn (b := xr b₁ (linPerm8 (linPartFun hn σ) b₂))
    rw [MulMemClass.coe_mul, Subgroup.coe_mul, h₁, h₂, map_mul, ← tr_mul_tr, mul_assoc,
      ← mul_assoc (linPerm hn (linPartFun hn σ)), linPerm_mul_tr, mul_assoc, mul_assoc]

theorem exists_eq_tr_mul_linPart (hn : 8 ≤ n) (σ : AGL hn) :
    ∃ b : Fin 8, ((σ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      tr hn b * linPerm hn (linPart hn σ) :=
  exists_eq_tr_mul_linPartFun hn σ

end AGL

section Decomp

theorem exists_GL_of_xr {f : Fin 8 → Fin 8} (hf : ∀ i j, f (xr i j) = xr (f i) (f j))
    (hinj : Function.Injective f) : ∃ A : GL (Fin 3) (ZMod 2), ∀ k, linPerm8 A k = f k := by
  have hf0 : f 0 = 0 := by
    have h := hf 0 0
    rw [xr_self, xr_self] at h
    exact h
  let g : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun v => bits (f (bits.symm v))
      map_zero' := by
        show bits (f (bits.symm 0)) = 0
        rw [bits_symm_zero, hf0, bits_zero]
      map_add' := fun v w => by
        show bits (f (bits.symm (v + w))) = bits (f (bits.symm v)) + bits (f (bits.symm w))
        rw [bits_symm_add, hf, bits_xr] }
  let M := LinearMap.toMatrix' (AddMonoidHom.toZModLinearMap 2 g)
  have hM : ∀ v, M *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hMinj : Function.Injective M.mulVec := by
    intro v w h
    have h1 : g v = g w := by rw [← hM, ← hM]; exact h
    have h2 := bits.injective h1
    exact bits.symm.injective (hinj h2)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.1 hMinj
  refine ⟨hu.unit, fun k => ?_⟩
  rw [linPerm8_apply, IsUnit.unit_spec, hM]
  show bits.symm (bits (f (bits.symm (bits k)))) = f k
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem mem_AGL (hn : 8 ≤ n) (hn11 : n ≤ 11) {σ : alternatingGroup (Fin n)}
    (hσ : ∀ e ∈ eBar hn, ∃ e' ∈ eBar hn,
      (σ : Perm (Fin n)) * (e : Perm (Fin n)) * (σ : Perm (Fin n))⁻¹ = e')
    {k : ℕ} (hk : σ ^ 2 ^ k = 1) : σ ∈ AGL hn := by
  set s : Perm (Fin n) := (σ : Perm (Fin n)) with hs
  have hlt : ∀ i : Fin n, i.val < 8 → (s i).val < 8 := fun i hi =>
    lt_eight_of_normalizes_eBar hn hσ hi
  obtain ⟨b, hb⟩ : ∃ b : Fin 8, b.val = (s (pt hn 0)).val :=
    ⟨⟨_, hlt _ (show (0 : ℕ) < 8 by norm_num)⟩, rfl⟩
  let f : Fin 8 → Fin 8 := fun k =>
    ⟨(s ⟨k.val, by omega⟩).val ^^^ b.val, xor_lt_eight (hlt _ k.2) b.2⟩
  have hfv : ∀ k : Fin 8, (f k).val = (s ⟨k.val, by omega⟩).val ^^^ b.val := fun _ => rfl
  have hf : ∀ i j, f (xr i j) = xr (f i) (f j) := by
    intro i j
    apply Fin.ext
    show (s ⟨i.val ^^^ j.val, _⟩).val ^^^ b.val = (f i).val ^^^ (f j).val
    rw [hfv, hfv, affine_of_normalizes_eBar hn hσ (i := ⟨i.val, by omega⟩)
      (j := ⟨j.val, by omega⟩) i.2 j.2 rfl, ← hb]
    exact xor_linear _ _ _
  have hfinj : Function.Injective f := by
    intro i j h
    have h1 := congrArg (fun x : Fin 8 => x.val ^^^ b.val) h
    simp only [hfv, xor_xor_cancel] at h1
    have h2 := s.injective (Fin.ext h1)
    have h3 := congrArg Fin.val h2
    exact Fin.ext h3
  obtain ⟨A, hA⟩ := exists_GL_of_xr hf hfinj
  set ν : Perm (Fin n) := tr hn b * linPerm hn A with hνdef
  have hν : ∀ i : Fin n, i.val < 8 → ν i = s i := by
    intro i hi
    have h8 : (linPerm hn A i).val < 8 := by
      rw [val_linPerm_of_lt hn A hi]
      exact (linPerm8 A _).2
    apply Fin.ext
    rw [hνdef, Perm.mul_apply, val_tr_of_lt hn b h8, val_linPerm_of_lt hn A hi, hA, hfv]
    exact xor_xor_cancel _ _
  have hν8 : ∀ i : Fin n, 8 ≤ i.val → ν i = i := by
    intro i hi
    rw [hνdef, Perm.mul_apply, linPerm_of_ge hn A hi, tr_of_ge hn b hi]
  set τ : Perm (Fin n) := ν⁻¹ * s with hτdef
  have hτ : ∀ i : Fin n, i.val < 8 → τ i = i := by
    intro i hi
    rw [hτdef, Perm.mul_apply, Perm.inv_eq_iff_eq]
    exact (hν i hi).symm
  have hdisj : ν.Disjoint τ := fun i => by
    by_cases hi : i.val < 8
    · exact Or.inr (hτ i hi)
    · exact Or.inl (hν8 i (by omega))
  have hsν : s = ν * τ := by rw [hτdef, mul_inv_cancel_left]
  have hτk : τ ^ 2 ^ k = 1 := by
    have h1 : s ^ 2 ^ k = 1 := by
      rw [hs, ← Subgroup.coe_pow, hk, Subgroup.coe_one]
    rw [hsν, hdisj.commute.mul_pow] at h1
    exact ((hdisj.pow_disjoint_pow _ _).mul_eq_one_iff.1 h1).2
  have hτA : τ ∈ alternatingGroup (Fin n) :=
    mul_mem (inv_mem (mul_mem (tr_mem_alternatingGroup hn b) (linPerm_mem_alternatingGroup hn A)))
      σ.2
  have hτc : ∀ e ∈ eBar hn, τ * (e : Perm (Fin n)) = e * τ := by
    intro e he
    obtain ⟨v, hv⟩ := (mem_eBar_iff hn).1 he
    rw [hv]
    have hd : (tr hn v).Disjoint τ := fun i => by
      by_cases hi : i.val < 8
      · exact Or.inr (hτ i hi)
      · exact Or.inl (tr_of_ge hn v (by omega))
    exact hd.commute.symm.eq
  obtain ⟨e, he, hτe⟩ := exists_eBar_eq_of_comm hn hn11 hτc hτk (Or.inr hτA)
  obtain ⟨v, hv⟩ := (mem_eBar_iff hn).1 he
  have hv0 : v = 0 := by
    have h1 : tr hn v (pt hn 0) = pt hn 0 := by
      rw [← hv, hτe]
      exact hτ _ (show (0 : ℕ) < 8 by norm_num)
    have h2 := congrArg Fin.val h1
    rw [val_tr_pt_zero] at h2
    exact Fin.ext h2
  have hτ1 : τ = 1 := by rw [← hτe, hv, hv0, tr_zero]
  exact ⟨b, A, by rw [← hs, hsν, hτ1, mul_one]⟩

end Decomp

section Card

theorem card_le_eight {K : Subgroup (GL (Fin 3) (ZMod 2))} (hK : IsPGroup 2 K) :
    Nat.card K ≤ 8 := by
  obtain ⟨g, hg⟩ := FixedCodim.exists_conj_le_sylowT hK
  have hle : K.map (MulAut.conj g⁻¹).toMonoidHom ≤ sylowT := by
    rintro _ ⟨k, hk, rfl⟩
    have h := hg k hk
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have h := Subgroup.card_le_of_le hle
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective, card_sylowT] at h

end Card

end CFSG.OddStandard.AltStdSmall4.ModIso
