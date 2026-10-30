module

public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescLinRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open Polynomial Module Matrix
open CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Timmesfeld.CrossChar

section Coprime

variable {S : Type} [Group S] [Finite S]

private def restrictToStable (D : Subgroup (MulAut S)) (T : Subgroup S)
    (h : ∀ β ∈ D, ∀ x ∈ T, β x ∈ T) : D →* MulAut T where
  toFun β :=
    { toFun := fun x => ⟨(β : MulAut S) x, h β β.2 x x.2⟩
      invFun := fun x => ⟨(β : MulAut S)⁻¹ x, h _ (D.inv_mem β.2) x x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul (β : MulAut S) (x : S) (y : S)) }
  map_one' := by
    ext x
    rfl
  map_mul' β γ := by
    ext x
    rfl

theorem exists_ne_one_fix_involution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D) (hD2 : Nat.card D = p ^ 2)
    {T : Subgroup S} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hDT : ∀ α ∈ D, T.map α.toMonoidHom = T) :
    ∃ e ∈ D, e ≠ 1 ∧ ∃ t ∈ T, orderOf t = 2 ∧ e t = t := by
  classical
  have hmem : ∀ β ∈ D, ∀ x ∈ T, β x ∈ T := fun β hβ x hx => by
    rw [← hDT β hβ]
    exact Subgroup.mem_map_of_mem _ hx
  haveI : IsMulCommutative D := hD.1
  let _ : CommGroup D := IsMulCommutative.instCommGroup
  haveI : CFSG.IsElementaryAbelian p D :=
    { toIsMulCommutative := hD.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hD.2 x x.2) }
  let α := restrictToStable D T hmem
  have hcop : ¬ p ∣ Nat.card T := by
    intro h
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have htop := CFSG.SolvableSignalizer.iSup_fixedSubgroup_eq_top p hp α (by rw [hD2]) hcop
  by_contra hno
  push Not at hno
  have hbot : ∀ a : D, a ≠ 1 → CFSG.SolvableSignalizer.fixedSubgroup α a = ⊥ := by
    intro a ha
    by_contra hne
    set F := CFSG.SolvableSignalizer.fixedSubgroup α a with hF
    have hF2 : IsPGroup 2 F := (hT2.to_subgroup F)
    haveI : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hne
    have h2F : 2 ∣ Nat.card F := by
      obtain ⟨n, hn⟩ := hF2.exists_card_eq
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hn] at h1 ⊢
      have : n ≠ 0 := by rintro rfl; simp at h1
      exact dvd_pow_self 2 this
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2F
    have hxfix : α a (x : T) = (x : T) := x.2
    have ho : orderOf ((x : T) : S) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have ha1 : (a : MulAut S) ≠ 1 := fun h => ha (Subtype.ext h)
    exact hno a a.2 ha1 ((x : T) : S) (x : T).2 ho (congrArg Subtype.val hxfix)
  have hall : (⨆ (a : D) (_ : a ≠ 1), CFSG.SolvableSignalizer.fixedSubgroup α a) = ⊥ := by
    refine iSup₂_eq_bot.2 ?_
    intro a ha
    exact hbot a ha
  rw [hall] at htop
  apply hT
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : T) ∈ (⊥ : Subgroup T) := by rw [htop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

end Coprime

section Abstract

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem finrank_range_eq_one_of_mul_self_eq_zero (hV : finrank k V = 3) {N : Module.End k V}
    (hN : N ≠ 0) (hN2 : N * N = 0) : finrank k (LinearMap.range N) = 1 := by
  have h1 : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    show N (N v) = 0
    rw [← Module.End.mul_apply, hN2, LinearMap.zero_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  have hle := Submodule.finrank_mono h1
  have hpos : 0 < finrank k (LinearMap.range N) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    exact hN
  omega

end Abstract

section Matrix

variable {k : Type} [Field k]

theorem eq_one_of_commute_diagonal_of_mul_self_eq_one [CharP k 2] {n : ℕ} {d : Fin n → k}
    (hd : Function.Injective d) {U : Matrix (Fin n) (Fin n) k}
    (hU : diagonal d * U = U * diagonal d) (hU2 : U * U = 1) : U = 1 := by
  have hoff : ∀ i j, i ≠ j → U i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hU i) j
    rw [diagonal_mul, mul_diagonal] at h
    have h' : (d i - d j) * U i j = 0 := by
      rw [sub_mul, h, mul_comm (d j)]
      exact sub_self _
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact absurd (hd (sub_eq_zero.1 h1)) hij
    · exact h1
  have hdiag : U = diagonal (fun i => U i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, hoff i j hij]
  have hii : ∀ i, U i i = 1 := by
    intro i
    have h := congrFun (congrFun hU2 i) i
    rw [hdiag, diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have h3 : (U i i - 1) * (U i i - 1) = 0 := by linear_combination h + (1 - U i i) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h3)
  rw [hdiag]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, hii, one_apply_eq]
  · rw [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem exists_perfect_fixSubgroup_of_commute_of_mul_self_eq_one [Finite k] [CharP k 2]
    (h3 : 3 ∣ Nat.card k - 1) {M U : GL (Fin 3) k} (hM : M ^ 3 = 1) (hU : U ≠ 1)
    (hU2 : U * U = 1) (hMU : M * U = U * M) :
    ∃ Q : Subgroup (projectiveSL 3 k), Q ≤ fixSubgroup (LinearFlag.conjAut 3 k M) ∧
      ⁅Q, Q⁆ = Q ∧ 3 ∣ Nat.card Q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd Nat.prime_three h3
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (n := 3) (p := 3) ⟨ζ, hζ⟩
    (Subgroup.zpowers M) (by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm])
    (by
      intro x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hM, _root_.one_zpow])
  have hPM := hP M (Subgroup.mem_zpowers M)
  set d : Fin 3 → k := fun l =>
    ((P * M * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) l l with hddef
  have hd : ((P * M * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal d :=
    glConj_eq_diagonal hPM
  by_cases hinj : Function.Injective d
  · exfalso
    apply hU
    have hcomm : diagonal d * ((P * U * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        ((P * U * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
      rw [← hd, ← Units.val_mul, ← Units.val_mul]
      congr 1
      calc P * M * P⁻¹ * (P * U * P⁻¹) = P * (M * U) * P⁻¹ := by group
        _ = P * (U * M) * P⁻¹ := by rw [hMU]
        _ = P * U * P⁻¹ * (P * M * P⁻¹) := by group
    have hsq : ((P * U * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        ((P * U * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
      rw [← Units.val_mul]
      have : P * U * P⁻¹ * (P * U * P⁻¹) = 1 := by
        calc P * U * P⁻¹ * (P * U * P⁻¹) = P * (U * U) * P⁻¹ := by group
          _ = 1 := by rw [hU2]; group
      rw [this, Units.val_one]
    have h1 := eq_one_of_commute_diagonal_of_mul_self_eq_one hinj hcomm hsq
    have h1' : P * U * P⁻¹ = 1 := Units.ext h1
    calc U = P⁻¹ * (P * U * P⁻¹) * P := by group
      _ = 1 := by rw [h1']; group
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    exact exists_perfect_fixSubgroup_of_diagonal_eq (P := P) Nat.prime_three (by norm_num) h3 hM
      (fun r s hrs => by rw [hd]; exact Matrix.diagonal_apply_ne d hrs) hne hij

theorem exists_cube_root_of_commute [CharP k 2] {M U : GL (Fin 3) k} {a : kˣ}
    (hMa : M ^ 3 = GeneralLinearGroup.scalar (Fin 3) a) (hU : U ≠ 1) (hU2 : U * U = 1)
    (hMU : M * U = U * M) : ∃ μ : kˣ, μ ^ 3 = a := by
  classical
  set N : Matrix (Fin 3) (Fin 3) k := (U : Matrix (Fin 3) (Fin 3) k) - 1 with hN
  have hN0 : Matrix.toLin' N ≠ 0 := by
    intro h
    apply hU
    have : N = 0 := Matrix.toLin'.injective (by rw [h, map_zero])
    exact Units.ext (sub_eq_zero.1 this)
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h2M : (2 : Matrix (Fin 3) (Fin 3) k) = 0 := by
    rw [← map_ofNat (Matrix.scalar (Fin 3)) 2, h2, map_zero]
  have hU2' : (U : Matrix (Fin 3) (Fin 3) k) * U = 1 := by
    rw [← Units.val_mul, hU2, Units.val_one]
  have hNN : N * N = 0 := by
    have : N * N = (U : Matrix (Fin 3) (Fin 3) k) * U - 1 - 2 * N := by
      rw [hN]
      noncomm_ring
    rw [this, h2M, zero_mul, sub_zero, hU2', sub_self]
  have hN2 : Matrix.toLin' N * Matrix.toLin' N = 0 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hNN, map_zero]
  have hR1 := finrank_range_eq_one_of_mul_self_eq_zero (Module.finrank_fin_fun k) hN0 hN2
  obtain ⟨⟨v, hvR⟩, hv0, hall⟩ := finrank_eq_one_iff'.1 hR1
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hMN : (M : Matrix (Fin 3) (Fin 3) k) * N = N * M := by
    rw [hN, mul_sub, sub_mul, mul_one, one_mul, ← Units.val_mul, hMU, Units.val_mul]
  have hMvR : (M : Matrix (Fin 3) (Fin 3) k) *ᵥ v ∈ LinearMap.range (Matrix.toLin' N) := by
    obtain ⟨w, hw⟩ := hvR
    refine ⟨(M : Matrix (Fin 3) (Fin 3) k) *ᵥ w, ?_⟩
    rw [Matrix.toLin'_apply] at hw ⊢
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMN]
  obtain ⟨c, hc⟩ := hall ⟨_, hMvR⟩
  have hc' : (M : Matrix (Fin 3) (Fin 3) k) *ᵥ v = c • v := (congrArg Subtype.val hc).symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc'
    apply hv0'
    have : ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
        ((M : Matrix (Fin 3) (Fin 3) k) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this, hc', Matrix.mulVec_zero]
  refine ⟨Units.mk0 c hc0, ?_⟩
  have h3v : ((M ^ 3 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v = c ^ 3 • v := by
    have e3 : ((M ^ 3 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (M : Matrix (Fin 3) (Fin 3) k) * ((M : Matrix (Fin 3) (Fin 3) k) * M) := by
      rw [pow_succ', pow_succ', pow_one, Units.val_mul, Units.val_mul]
    rw [e3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [hc', Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  rw [hMa, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mulVec, Matrix.one_mulVec] at h3v
  have hav : (a : k) • v = c ^ 3 • v := h3v
  have : (a : k) = c ^ 3 := by
    by_contra hne
    have h0 : ((a : k) - c ^ 3) • v = 0 := by rw [sub_smul, hav, sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact hne (sub_eq_zero.1 h)
    · exact hv0' h
  ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, this]

theorem exists_lift_of_sq_eq_one {t : projectiveSL 3 k} (ht : t ^ 2 = 1) :
    ∃ U : SpecialLinearGroup (Fin 3) k, proj 3 k U = t ∧ U ^ 2 = 1 := by
  obtain ⟨U₀, rfl⟩ := proj_surjective 3 k t
  have hs : U₀ ^ 2 ∈ scalars 3 k := by
    rw [← proj_eq_one_iff, map_pow, ht]
  obtain ⟨c, hc3, hcU⟩ := mem_scalars.1 hs
  refine ⟨U₀ ^ 3, ?_, ?_⟩
  · rw [map_pow, pow_succ, ht, one_mul]
  · have h : ((U₀ ^ 2) ^ 3 : SpecialLinearGroup (Fin 3) k) = 1 := by
      have hm : ((U₀ ^ 2) ^ 3 : SpecialLinearGroup (Fin 3) k).1 =
          (1 : SpecialLinearGroup (Fin 3) k).1 := by
        calc ((U₀ ^ 2) ^ 3 : SpecialLinearGroup (Fin 3) k).1
            = ((U₀ ^ 2 : SpecialLinearGroup (Fin 3) k).1) ^ 3 := by
              exact Matrix.SpecialLinearGroup.coe_pow _ _
          _ = (scalar (Fin 3) (c : k)) ^ 3 := by rw [← hcU]
          _ = 1 := by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc3, Units.val_one, map_one]
          _ = (1 : SpecialLinearGroup (Fin 3) k).1 := by
              exact Matrix.SpecialLinearGroup.coe_one.symm
      exact Subtype.ext hm
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, h]

theorem mul_comm_of_conjAut_proj_eq {M : GL (Fin 3) k} {U : SpecialLinearGroup (Fin 3) k}
    (hU2 : U ^ 2 = 1) (hfix : LinearFlag.conjAut 3 k M (proj 3 k U) = proj 3 k U) :
    M * Matrix.SpecialLinearGroup.toGL U = Matrix.SpecialLinearGroup.toGL U * M := by
  rw [conjAut_proj, proj_eq_proj_iff] at hfix
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 hfix
  set W := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k M U with hW
  have hWm : Matrix.SpecialLinearGroup.toGL W = M * Matrix.SpecialLinearGroup.toGL U * M⁻¹ := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hW, coe_slConjugation, Units.val_mul, Units.val_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hWU : Matrix.SpecialLinearGroup.toGL (W⁻¹ * U) = GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc, GeneralLinearGroup.coe_scalar]
  set u := Matrix.SpecialLinearGroup.toGL U with hu
  set s := GeneralLinearGroup.scalar (Fin 3) c with hs
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, ← sq, hU2, map_one]
  have hUWs : u = M * u * M⁻¹ * s := by
    rw [← hWU, map_mul, map_inv, ← hWm, mul_inv_cancel_left]
  have hsc : ∀ g : GL (Fin 3) k, s * g = g * s := fun g => GeneralLinearGroup.scalar_commute c g
  have hs2 : s * s = 1 := by
    have h1 : u * u = (M * u * M⁻¹) * (M * u * M⁻¹) * (s * s) := by
      conv_lhs => rw [hUWs]
      rw [show M * u * M⁻¹ * s * (M * u * M⁻¹ * s) = M * u * M⁻¹ * (s * (M * u * M⁻¹)) * s by
        group]
      rw [hsc (M * u * M⁻¹)]
      group
    have h2 : (M * u * M⁻¹) * (M * u * M⁻¹) = 1 := by
      calc (M * u * M⁻¹) * (M * u * M⁻¹) = M * (u * u) * M⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [h2, one_mul, hu2] at h1
    exact h1.symm
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← map_pow, hc3, map_one]
  have hs1 : s = 1 := by
    calc s = s ^ 3 * (s * s)⁻¹ := by group
      _ = 1 := by rw [hs3, hs2]; group
  rw [hs1, mul_one] at hUWs
  calc M * u = M * u * M⁻¹ * M := by group
    _ = u * M := by rw [← hUWs]

end Matrix

section SLevel

@[expose] def NoGoodTwoLocal (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 → D ≤ innAutDerived S →
    (¬ ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup S, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P) →
    ∀ T : Subgroup S, IsPGroup 2 T → T ≠ ⊥ → (∀ α ∈ D, T.map α.toMonoidHom = T) → False

theorem NoGoodTwoLocal.of_mulEquiv {p : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : NoGoodTwoLocal p S) : NoGoodTwoLocal p S' := by
  intro D' hD' hcard hle hno T' hT2 hT hDT
  let c : MulAut S ≃* MulAut S' := MulAut.congr e
  let D : Subgroup (MulAut S) := D'.map (c.symm : MulAut S' →* MulAut S)
  have hmemD : ∀ x : MulAut S', c.symm x ∈ D ↔ x ∈ D' := fun x =>
    Subgroup.mem_map_equiv.trans (by simp)
  have hinn : ∀ x : MulAut S', c.symm x ∈ innAutDerived S ↔ x ∈ innAutDerived S' := fun x => by
    rw [← mem_innAutDerived_congr e]
    exact Iff.of_eq (congrArg (· ∈ innAutDerived S') (c.apply_symm_apply x))
  have hDel : IsElemAbelian p D := hD'.map _
  have hDcard : Nat.card D = p ^ 2 := by
    rw [← hcard]
    exact Subgroup.card_map_of_injective c.symm.injective
  have hDle : D ≤ innAutDerived S := by
    intro x hx
    rw [← c.symm_apply_apply x] at hx ⊢
    exact (hinn _).2 (hle ((hmemD _).1 hx))
  have hnoD : ¬ ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup S, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧
      p ∣ Nat.card P := by
    rintro ⟨β, hβD, hβ1, P, hPfix, hPperf, hPdvd⟩
    refine hno ⟨c β, ?_, fun h1 => hβ1 (c.injective (h1.trans (map_one c).symm)),
      P.map (e : S →* S'), ?_, ?_, ?_⟩
    · rw [← c.symm_apply_apply β] at hβD
      exact (hmemD _).1 hβD
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_fixSubgroup]
      have hy' : β y = y := hPfix hy
      change e (β (e.symm (e y))) = e y
      rw [e.symm_apply_apply, hy']
    · rw [← Subgroup.map_commutator, hPperf]
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hPdvd
  let T : Subgroup S := T'.map (e.symm : S' →* S)
  have hT2' : IsPGroup 2 T := hT2.map _
  have hT' : T ≠ ⊥ := by
    intro hbot
    apply hT
    exact (Subgroup.map_eq_bot_iff_of_injective T' e.symm.injective).1 hbot
  have hDT' : ∀ α ∈ D, T.map α.toMonoidHom = T := by
    rintro _ ⟨α', hα', rfl⟩
    have hcomp : (((c.symm α' : MulAut S) : S ≃* S).toMonoidHom.comp (e.symm : S' →* S)) =
        (e.symm : S' →* S).comp α'.toMonoidHom := by
      ext g
      change e.symm (α' (e (e.symm g))) = e.symm (α' g)
      rw [e.apply_symm_apply]
    change (T'.map (e.symm : S' →* S)).map (c.symm α').toMonoidHom = T'.map (e.symm : S' →* S)
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hDT α' hα']
  exact h D hDel hDcard hDle hnoD T hT2' hT' hDT'

end SLevel

section Model

variable {k : Type} [Field k] [Finite k]

theorem noGoodTwoLocal_projectiveSL_three [CharP k 2] (h3 : 3 ∣ Nat.card k - 1) :
    NoGoodTwoLocal 3 (projectiveSL 3 k) := by
  intro D hD hD2 hDinn hno T hT2 hT hDT
  obtain ⟨e, heD, he1, t, htT, ht2, het⟩ :=
    exists_ne_one_fix_involution Nat.prime_three (by norm_num) hD hD2 hT2 hT hDT
  obtain ⟨M, rfl⟩ := mem_linearAutGroup_iff.1
    (innAutDerived_projectiveSL_le_linearAutGroup (by norm_num) (hDinn heD))
  have he3 : LinearFlag.conjAut 3 k (M ^ 3) = 1 := by
    rw [map_pow]
    exact hD.2 _ heD
  obtain ⟨a, ha⟩ := exists_eq_scalar_of_conjAut_eq_one (by norm_num) he3
  have ht2' : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  obtain ⟨U, hUt, hU2⟩ := exists_lift_of_sq_eq_one ht2'
  have hU1 : Matrix.SpecialLinearGroup.toGL U ≠ 1 := by
    intro h
    have hU : U = 1 := Matrix.SpecialLinearGroup.toGL_injective (by rw [h, map_one])
    rw [hU, map_one] at hUt
    rw [← hUt, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hU2' : Matrix.SpecialLinearGroup.toGL U * Matrix.SpecialLinearGroup.toGL U = 1 := by
    rw [← map_mul, ← sq, hU2, map_one]
  have hMU := mul_comm_of_conjAut_proj_eq hU2 (by rw [hUt]; exact het)
  obtain ⟨μ, hμ⟩ := exists_cube_root_of_commute ha hU1 hU2' hMU
  have hM'3 : (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * M) ^ 3 = 1 := by
    rw [scalar_mul_pow, ha, ← map_mul, inv_pow, hμ, inv_mul_cancel, map_one]
  have hM'U : GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * M * Matrix.SpecialLinearGroup.toGL U =
      Matrix.SpecialLinearGroup.toGL U * (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * M) := by
    rw [mul_assoc, hMU, ← mul_assoc, ← mul_assoc, GeneralLinearGroup.scalar_commute]
  obtain ⟨Q, hQ, hQperf, hQ3⟩ :=
    exists_perfect_fixSubgroup_of_commute_of_mul_self_eq_one h3 hM'3 hU1 hU2' hM'U
  rw [conjAut_scalar_mul] at hQ
  exact hno ⟨LinearFlag.conjAut 3 k M, heD, he1, Q, hQ, hQperf, hQ3⟩

end Model

theorem lpEpsNoGoodTwoLocal_linear (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.p = 2) :
    HDesc.LpEpsNoGoodTwoLocal 3 ⟨.A 2 q, hv⟩ := by
  intro hlp D hD hD2 hDinn _ hno T hT2 hT hDT
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let k := GaloisField q.p q.exponent
  have hcard : Nat.card k = q.card := by
    dsimp only [k]
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
    exact (TauCeti.PrimePower.card_def q).symm
  haveI : CharP k 2 := CharP.congr q.p hq
  have h3 : 3 ∣ Nat.card k - 1 := by
    obtain ⟨q', ⟨hq', h⟩ | ⟨hq', -⟩⟩ := hlp
    · injection hq' with h1 h2
      subst h2
      rwa [hcard]
    · exact absurd hq' (by simp)
  let eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩).Group ≃*
      LinearFlag.projectiveSL 3 k :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k)
  exact NoGoodTwoLocal.of_mulEquiv eModel.symm (noGoodTwoLocal_projectiveSL_three h3) D hD hD2
    hDinn hno T hT2 hT hDT

end CFSG.LocalAnalysis.GLTheoremA.HDescLinRes

end
