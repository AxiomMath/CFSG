module

public import CFSG.ClassicalInvolution.RouteD.GapsD4ABasic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LinearAut

open Matrix.SpecialLinearGroup (transvection)
open CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] {n : ℕ}

theorem transvection_apply_self {i j : Fin n} (hij : i ≠ j) (c : F) :
    ((transvection hij c : SL(n, F)) : Matrix (Fin n) (Fin n) F) i j = c := by
  rw [coe_transvection_eq]
  simp [hij]

theorem transvection_injective {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (fun c : F => (transvection hij c : SL(n, F))) := by
  intro c d h
  have := congrArg (fun g : SL(n, F) => (g : Matrix (Fin n) (Fin n) F) i j) h
  simpa only [transvection_apply_self] using this

section Abstract

variable [Finite F]

theorem exists_third (hn : 3 ≤ n) (a b : Fin n) : ∃ k : Fin n, k ≠ a ∧ k ≠ b := by
  by_cases h0 : a.val ≠ 0 ∧ b.val ≠ 0
  · exact ⟨⟨0, by omega⟩, fun e => h0.1 (by rw [← e]), fun e => h0.2 (by rw [← e])⟩
  · by_cases h1 : a.val ≠ 1 ∧ b.val ≠ 1
    · exact ⟨⟨1, by omega⟩, fun e => h1.1 (by rw [← e]), fun e => h1.2 (by rw [← e])⟩
    · refine ⟨⟨2, by omega⟩, fun e => ?_, fun e => ?_⟩
      · have := congrArg Fin.val e
        simp only at this
        omega
      · have := congrArg Fin.val e
        simp only at this
        omega

theorem exists_phi_d (hn : 3 ≤ n) (f : ∀ i j : Fin n, i ≠ j → F → F)
    (hadd : ∀ i j (h : i ≠ j) s s', f i j h (s + s') = f i j h s + f i j h s')
    (hinj : ∀ i j (h : i ≠ j), Function.Injective (f i j h))
    (hmul : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s t,
      f i k hik (s * t) = f i j hij s * f j k hjk t) :
    ∃ (φ : F ≃+* F) (d : Fin n → Fˣ), ∀ i j (h : i ≠ j) s,
      f i j h s = (d i : F) * φ s * (((d j)⁻¹ : Fˣ) : F) := by
  have f_zero : ∀ i j (h : i ≠ j), f i j h 0 = 0 := fun i j h => by
    have := hadd i j h 0 0
    simpa using this
  have c_ne : ∀ i j (h : i ≠ j), f i j h 1 ≠ 0 := fun i j h e =>
    one_ne_zero (hinj i j h (e.trans (f_zero i j h).symm))
  have hA : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s,
      f i k hik s = f i j hij s * f j k hjk 1 := fun i j k hij hjk hik s => by
    simpa using hmul i j k hij hjk hik s 1
  have hB : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) t,
      f i k hik t = f i j hij 1 * f j k hjk t := fun i j k hij hjk hik t => by
    simpa using hmul i j k hij hjk hik 1 t
  have hC : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      f i k hik 1 = f i j hij 1 * f j k hjk 1 := fun i j k hij hjk hik => by
    simpa using hmul i j k hij hjk hik 1 1
  let ψ : ∀ i j : Fin n, i ≠ j → F → F := fun i j h s => f i j h s / f i j h 1
  have Ψ1 : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s,
      ψ i j hij s = ψ i k hik s := by
    intro i j k hij hjk hik s
    simp only [ψ]
    rw [hA i j k hij hjk hik s, hC i j k hij hjk hik]
    have h1 := c_ne i j hij
    have h2 := c_ne j k hjk
    field_simp
  have Ψ2 : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) t,
      ψ i k hik t = ψ j k hjk t := by
    intro i j k hij hjk hik t
    simp only [ψ]
    rw [hB i j k hij hjk hik t, hC i j k hij hjk hik]
    have h1 := c_ne i j hij
    have h2 := c_ne j k hjk
    field_simp
  have move2 : ∀ i j k (hij : i ≠ j) (hik : i ≠ k) s, ψ i j hij s = ψ i k hik s := by
    intro i j k hij hik s
    by_cases hjk : j = k
    · subst hjk
      rfl
    · exact Ψ1 i j k hij hjk hik s
  have move1 : ∀ i l k (hik : i ≠ k) (hlk : l ≠ k) s, ψ i k hik s = ψ l k hlk s := by
    intro i l k hik hlk s
    by_cases hil : i = l
    · subst hil
      rfl
    · exact Ψ2 i l k hil hlk hik s
  have sym : ∀ a b (hab : a ≠ b) s, ψ a b hab s = ψ b a hab.symm s := by
    intro a b hab s
    obtain ⟨k, hka, hkb⟩ := exists_third hn a b
    calc ψ a b hab s = ψ a k hka.symm s := Ψ1 a b k hab hkb.symm hka.symm s
      _ = ψ b k hkb.symm s := Ψ2 a b k hab hkb.symm hka.symm s
      _ = ψ b a hab.symm s := Ψ1 b k a hkb.symm hka hab.symm s
  have hall : ∀ a b (hab : a ≠ b) c d (hcd : c ≠ d) s, ψ a b hab s = ψ c d hcd s := by
    intro a b hab c d hcd s
    by_cases had : a = d
    · subst had
      calc ψ a b hab s = ψ a c hcd.symm s := move2 a b c hab hcd.symm s
        _ = ψ c a hcd s := sym a c hcd.symm s
    · calc ψ a b hab s = ψ a d had s := move2 a b d hab had s
        _ = ψ c d hcd s := move1 a c d had hcd s
  let r1 : Fin n := ⟨0, by omega⟩
  let r2 : Fin n := ⟨1, by omega⟩
  let r3 : Fin n := ⟨2, by omega⟩
  have h12 : r1 ≠ r2 := fun e => by have := congrArg Fin.val e; simp [r1, r2] at this
  have h23 : r2 ≠ r3 := fun e => by have := congrArg Fin.val e; simp [r2, r3] at this
  have h13 : r1 ≠ r3 := fun e => by have := congrArg Fin.val e; simp [r1, r3] at this
  let φf : F → F := ψ r1 r2 h12
  have φf_eq : ∀ i j (h : i ≠ j) s, ψ i j h s = φf s := fun i j h s => hall i j h r1 r2 h12 s
  have φf_one : φf 1 = 1 := div_self (c_ne r1 r2 h12)
  have φf_add : ∀ s s', φf (s + s') = φf s + φf s' := by
    intro s s'
    simp only [φf, ψ]
    rw [hadd, add_div]
  have φf_zero : φf 0 = 0 := by
    have := φf_add 0 0
    simpa using this
  have φf_mul : ∀ s t, φf (s * t) = φf s * φf t := by
    intro s t
    have e1 : ψ r1 r3 h13 (s * t) = ψ r1 r2 h12 s * ψ r2 r3 h23 t := by
      simp only [ψ]
      rw [hmul r1 r2 r3 h12 h23 h13 s t, hC r1 r2 r3 h12 h23 h13]
      have := c_ne r1 r2 h12
      have := c_ne r2 r3 h23
      field_simp
    rw [φf_eq r1 r3 h13, φf_eq r2 r3 h23] at e1
    exact e1
  have φf_inj : Function.Injective φf := by
    intro s s' h
    exact hinj r1 r2 h12 ((div_left_inj' (c_ne r1 r2 h12)).mp h)
  let φr : F →+* F :=
    { toFun := φf, map_one' := φf_one, map_mul' := φf_mul, map_zero' := φf_zero,
      map_add' := φf_add }
  let φ : F ≃+* F := RingEquiv.ofBijective φr ⟨φf_inj, Finite.injective_iff_surjective.mp φf_inj⟩
  have hφ : ∀ s, φ s = φf s := fun s => rfl
  let cc : Fin n → Fin n → F := fun i j => if h : i = j then 1 else f i j h 1
  have cc_ne : ∀ i j, cc i j ≠ 0 := by
    intro i j
    by_cases h : i = j
    · simp [cc, h]
    · simp only [cc, h, dite_false]
      exact c_ne i j h
  have cc_of_ne : ∀ i j (h : i ≠ j), cc i j = f i j h 1 := by
    intro i j h
    simp [cc, h]
  have cc_self : ∀ i, cc i i = 1 := by
    intro i
    simp [cc]
  have hkey : ∀ i j, cc i j = cc r1 j / cc r1 i := by
    intro i j
    by_cases hij : i = j
    · rw [hij, cc_self, div_self (cc_ne r1 j)]
    by_cases hir : i = r1
    · rw [hir, cc_self, div_one]
    by_cases hjr : j = r1
    · rw [hjr, cc_self]
      obtain ⟨k, hki, hkr⟩ := exists_third hn i r1
      have e1 := hC i r1 k hir hkr.symm hki.symm
      have e2 := hC r1 i k (Ne.symm hir) hki.symm hkr.symm
      rw [cc_of_ne i r1 hir, cc_of_ne r1 i (Ne.symm hir)]
      rw [e2] at e1
      have hP := c_ne i k hki.symm
      have hab : f i r1 hir 1 * f r1 i (Ne.symm hir) 1 = 1 := by
        apply mul_right_cancel₀ hP
        linear_combination (-1 : F) * e1
      exact eq_one_div_of_mul_eq_one_left hab
    · rw [cc_of_ne i j hij, cc_of_ne r1 j (Ne.symm hjr), cc_of_ne r1 i (Ne.symm hir)]
      have e := hC r1 i j (Ne.symm hir) hij (Ne.symm hjr)
      have h2 := c_ne r1 i (Ne.symm hir)
      field_simp
      rw [e]
      ring
  refine ⟨φ, fun i => Units.mk0 (cc r1 i)⁻¹ (inv_ne_zero (cc_ne r1 i)), ?_⟩
  intro i j h s
  have hf : f i j h s = f i j h 1 * ψ i j h s := by
    simp only [ψ]
    field_simp [c_ne i j h]
  rw [hf, φf_eq i j h s, ← hφ, ← cc_of_ne i j h, hkey i j]
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val, inv_inv]
  field_simp

end Abstract

section Main

theorem slConjugation_map_transvection {i j : Fin n} (hij : i ≠ j) (d : Fin n → Fˣ) (φ : F ≃+* F)
    (c : F) :
    slConjugation n F (diagGL d)
        (Matrix.SpecialLinearGroup.map φ.toRingHom (transvection hij c)) =
      transvection hij ((d i : F) * φ c * (((d j)⁻¹ : Fˣ) : F)) := by
  refine Subtype.ext (Matrix.ext fun a b => ?_)
  rw [slConjugation_diagGL_apply, Matrix.SpecialLinearGroup.map_apply_coe, coe_transvection_eq hij,
    show (φ.toRingHom.mapMatrix (1 + Matrix.single i j c) : Matrix (Fin n) (Fin n) F) =
      φ.mapMatrix (1 + Matrix.single i j c) from rfl,
    mapMatrix_one_add_single, coe_transvection_eq hij]
  by_cases hc : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hc
    simp [Matrix.add_apply, Matrix.one_apply_ne hij]
  · by_cases hab : a = b
    · subst hab
      simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, hc, ↓reduceIte,
        add_zero]
      rw [mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · simp only [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, hc, ↓reduceIte,
        add_zero, mul_zero, zero_mul]

variable [Finite F]

theorem exists_conj_mapMatrix_of_root_stable (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hα : Function.Injective α)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j) (s : F),
      ∃ t, α (transvection hij s) = transvection hij t) :
    ∃ (D : GL (Fin n) F) (φ : F ≃+* F), ∀ x : SL(n, F),
      ((α x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
        (D : Matrix (Fin n) (Fin n) F) * φ.mapMatrix (x : Matrix (Fin n) (Fin n) F) *
          ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  choose f hf using hroot
  have hadd : ∀ i j (h : i ≠ j) s s', f i j h (s + s') = f i j h s + f i j h s' := by
    intro i j h s s'
    apply transvection_injective h
    show transvection h (f i j h (s + s')) = transvection h (f i j h s + f i j h s')
    rw [← hf i j h (s + s'), Matrix.SpecialLinearGroup.transvection_add, map_mul, hf, hf,
      ← Matrix.SpecialLinearGroup.transvection_add]
  have hinj : ∀ i j (h : i ≠ j), Function.Injective (f i j h) := by
    intro i j h s s' e
    apply transvection_injective h
    apply hα
    show α (transvection h s) = α (transvection h s')
    rw [hf, hf, e]
  have hmul : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s t,
      f i k hik (s * t) = f i j hij s * f j k hjk t := by
    intro i j k hij hjk hik s t
    apply transvection_injective hik
    show transvection hik (f i k hik (s * t)) = transvection hik (f i j hij s * f j k hjk t)
    rw [← hf i k hik (s * t), ← Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik,
      map_commutatorElement, hf, hf, Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik]
  obtain ⟨φ, d, hd⟩ := exists_phi_d hn f hadd hinj hmul
  refine ⟨diagGL d, φ, fun x => ?_⟩
  set β : SL(n, F) →* SL(n, F) :=
    (slConjugation n F (diagGL d)).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map φ.toRingHom) with hβ
  have hαβ : α = β := by
    have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin n) F → SL(n, F))) ≤ MonoidHom.eqLocus α β := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, rfl⟩
      show α t.toSpecialLinearGroup = β t.toSpecialLinearGroup
      rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def, hf, hβ, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, slConjugation_map_transvection, hd]
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ MonoidHom.eqLocus α β := by
      apply hle
      rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
      exact Subgroup.mem_top x
    exact hx
  rw [hαβ]
  show (((slConjugation n F (diagGL d)) (Matrix.SpecialLinearGroup.map φ.toRingHom x) :
    SL(n, F)) : Matrix (Fin n) (Fin n) F) = _
  rw [slConjugation_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

end Main

end CFSG.ClassicalInvolution.ModelFacts.LinearAut
