module

public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.Twist
public import CFSG.GH74.GLS.IVK.L2.FieldProj
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.GH74.GLS.IVK.L2.DihedralAux
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section K

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

theorem card_le_four_of_le_inf (hF : L2Field F) (T : Sylow 2 (MulAut K)) (X : Subgroup (MulAut K))
    (hT : X ≤ (T : Subgroup (MulAut K))) (hG : X ≤ innDiagSub e)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hsq : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 4 := by
  obtain ⟨m, hm, ⟨φ⟩⟩ := dihedral_of_sylow_inf_innDiag e hF T
  set M : Subgroup (MulAut K) := (T : Subgroup (MulAut K)) ⊓ innDiagSub e with hM
  have hXM : X ≤ M := le_inf hT hG
  have hne : NeZero (2 ^ m) := ⟨by positivity⟩
  let X' : Subgroup ↥M := X.subgroupOf M
  have hcard1 : Nat.card X' = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  let X'' : Subgroup (DihedralGroup (2 ^ m)) := X'.map φ.toMonoidHom
  have hcard2 : Nat.card X'' = Nat.card X' := Subgroup.card_map_of_injective φ.injective
  have hb : Nat.card X'' ≤ 4 := by
    apply DihedralAux.card_le_four_of_elemAbelian
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (hsq a ha)
      rw [this, map_one]
  omega

include e in
theorem card_le_eight_of_elemAbelian (hF : L2Field F) (A : Subgroup (MulAut K))
    (hA : IsElementaryAbelian 2 ↥A) : Nat.card ↥A ≤ 8 := by
  have := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ a : ↥A, a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 ↥A)
  have hsq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hx
    rwa [pow_two] at this
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hA2 : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨T', hT'⟩ := hA2.exists_le_sylow
  set φ : ↥A →* (F ≃+* F) := (fieldProj e).comp A.subtype with hφ
  have hker : Nat.card φ.ker ≤ 4 := by
    set X : Subgroup (MulAut K) := φ.ker.map A.subtype with hX
    have hXA : X ≤ A := by
      rintro _ ⟨a, _, rfl⟩
      exact a.2
    have hXG : X ≤ innDiagSub e := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mem_innDiagSub_iff e _).mpr (MonoidHom.mem_ker.mp ha)
    have hcard : Nat.card X = Nat.card φ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have := card_le_four_of_le_inf e hF T' X (hXA.trans hT') hXG
      (fun x hx y hy => hcomm x (hXA hx) y (hXA hy)) (fun x hx => hsq x (hXA hx))
    omega
  have hrange : Nat.card φ.range ≤ 2 := by
    have := ringAut_isCyclic F
    have : IsCyclic φ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent φ.range ∣ 2 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      show φ a ^ 2 = 1
      rw [← map_pow, hpow a, map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have := Subgroup.card_ker_mul_card_range φ
  nlinarith

theorem ivk_1_2k_a : IVK_1_2k_a := by
  intro F _ _ hF K _ _ e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set ℕ := {r | ∃ A : Subgroup (MulAut K), IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r}
    with hS
  have hupper : ∀ r ∈ S, r ≤ 3 := by
    rintro r ⟨A, hA, hr⟩
    have h8 := card_le_eight_of_elemAbelian e hF A hA
    rw [hr] at h8
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  have hmem2 : 2 ∈ S := by
    obtain ⟨T', -⟩ := (IsPGroup.of_bot (p := 2) (G := MulAut K)).exists_le_sylow
    obtain ⟨m, hm, ⟨d⟩⟩ := dihedral_of_sylow_inf_innAut e hF T'
    obtain ⟨V, -, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv _ hm d
    refine ⟨V, ?_, by simp⟩
    exact
      { toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by rw [hV.exponent_two] }
  have hbdd : BddAbove S := ⟨3, hupper⟩
  have h2 : 2 ≤ sSup S := le_csSup hbdd hmem2
  have h3 : sSup S ≤ 3 := csSup_le ⟨2, hmem2⟩ hupper
  show sSup S = 2 ∨ sSup S = 3
  omega

theorem ivk_1_2k_b : IVK_1_2k_b := by
  intro F _ _ hF K _ _ e E hE hE8
  have := hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
    rwa [pow_two] at this
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  obtain ⟨T', hT'⟩ := hE2.exists_le_sylow
  have hnot : ¬ E ≤ innDiagSub e := by
    intro hsub
    have := card_le_four_of_le_inf e hF T' E hT' hsub hcomm hsq
    omega
  obtain ⟨y, hyE, hyG⟩ := Set.not_subset.mp hnot
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyG (innDiagSub e).one_mem
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq y hyE) hy1
  refine ⟨y, hyE, hy2, ?_⟩
  have hproj : fieldProj e y ≠ 1 := fun h => hyG ((mem_innDiagSub_iff e y).mpr h)
  have hord : orderOf (thetaAut e y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hy2
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e y) hord
    (by rw [← fieldProj_apply]; exact hproj)
  set σ := (thetaAut e y).right with hσ
  have hΘφ : thetaAut e (fieldAutHom e σ) = SemidirectProduct.inr σ := thetaAut_fieldAutHom e σ
  set a : MulAut K := innDiagHom e C with ha
  have hΘa : thetaAut e a = SemidirectProduct.inl C := thetaAut_innDiagHom e C
  have hconj : a⁻¹ * y * a = fieldAutHom e σ := by
    apply (thetaAut e).injective
    rw [map_mul, map_mul, map_inv, hΘa, hΘφ]
    exact hC
  have hy : y = a * fieldAutHom e σ * a⁻¹ := by
    rw [← hconj]; group
  refine ⟨F, inferInstance, inferInstance, twistEquiv e a⁻¹, σ, ?_⟩
  rw [fieldAutHom_twist, inv_inv, hy]

end K

end CFSG.GH74.GLS.IVK
