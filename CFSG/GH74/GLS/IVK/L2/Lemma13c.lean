module

public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerNormalizer

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter
open scoped Pointwise

section Quadratic

theorem isSquare_mul_of_not_isSquare {F : Type*} [Field F] [Fintype F] {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ IsSquare.zero)
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul, h1, h2]
  norm_num

theorem exists_quadratic_overfield (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (ι : F →+* E),
      Odd (Nat.card E) ∧ ∀ a : F, IsSquare (ι a) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    have h2 := FiniteField.even_card_of_char_two h
    rw [← Nat.card_eq_fintype_card] at h2
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hchar
  have : Fact (¬ IsSquare c) := ⟨hc⟩
  refine ⟨QuadraticAlgebra F c 0, inferInstance, ?_, algebraMap F (QuadraticAlgebra F c 0), ?_, ?_⟩
  · exact Finite.of_surjective (fun p : F × F => (⟨p.1, p.2⟩ : QuadraticAlgebra F c 0))
      (fun z => ⟨(z.re, z.im), rfl⟩)
  · have h : Nat.card (QuadraticAlgebra F c 0) = Nat.card F * Nat.card F := by
      rw [← Nat.card_prod]
      exact Nat.card_congr ⟨fun z => (z.re, z.im), fun p => ⟨p.1, p.2⟩, fun z => rfl, fun p => rfl⟩
    rw [h]
    exact hodd.mul hodd
  · intro a
    by_cases ha : IsSquare a
    · obtain ⟨r, hr⟩ := ha
      exact ⟨algebraMap _ _ r, by rw [hr, map_mul]⟩
    · obtain ⟨r, hr⟩ := isSquare_mul_of_not_isSquare ha hc
      have hω : (QuadraticAlgebra.omega : QuadraticAlgebra F c 0) * QuadraticAlgebra.omega =
          algebraMap F (QuadraticAlgebra F c 0) c := by
        rw [QuadraticAlgebra.omega_mul_omega_eq_mk, QuadraticAlgebra.algebraMap_eq]
      have hω0 : (QuadraticAlgebra.omega : QuadraticAlgebra F c 0) ≠ 0 := by
        intro h
        have := congrArg QuadraticAlgebra.im h
        simp [QuadraticAlgebra.omega] at this
      refine ⟨algebraMap F (QuadraticAlgebra F c 0) r * QuadraticAlgebra.omega⁻¹, ?_⟩
      have h1 : algebraMap F (QuadraticAlgebra F c 0) a *
          algebraMap F (QuadraticAlgebra F c 0) c =
          algebraMap F (QuadraticAlgebra F c 0) r * algebraMap F (QuadraticAlgebra F c 0) r := by
        rw [← map_mul, ← map_mul, hr]
      rw [← hω] at h1
      field_simp
      linear_combination h1

end Quadratic

section Embedding

theorem exists_pgl2_psl2_embedding (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (Ψ : PGL2 F →* PSL2 E),
      Odd (Nat.card E) ∧ Function.Injective Ψ := by
  obtain ⟨E, hE, hfin, ι, hEodd, hsq⟩ := exists_quadratic_overfield F hodd
  let Φ : PGL2 F →* PGL2 E := Matrix.ProjGenLinGroup.map ι
  have hΦ : Function.Injective Φ := CFSG.Semidihedral.FixedFieldCentralizer.pgl_map_injective ι
  have hrange : ∀ g : PGL2 F, Φ g ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := E)).range := by
    intro g
    induction g using Matrix.ProjGenLinGroup.induction_on with
    | mk M =>
      show Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map ι M) ∈ _
      rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.map_det,
        Units.coe_map]
      exact hsq _
  let Ψ : PGL2 F →* PSL2 E :=
    ((MonoidHom.ofInjective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (n := Fin 2) (R := E))).symm : _ ≃* _).toMonoidHom.comp
      (MonoidHom.codRestrict Φ _ hrange)
  refine ⟨E, hE, hfin, Ψ, hEodd, ?_⟩
  intro x y hxy
  apply hΦ
  have := (MonoidHom.ofInjective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (n := Fin 2) (R := E))).symm.injective hxy
  exact congrArg Subtype.val this

end Embedding


section Normalizer

variable {M : Type*} [Group M]

theorem mem_normalizer_subgroupOf_iff (D X : Subgroup M) (hXD : X ≤ D) (g : D) :
    (g : M) ∈ normalizer (X : Set M) ↔ g ∈ normalizer ((X.subgroupOf D : Subgroup D) : Set D) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := X) (f := D.subtype) (by
    intro x hx
    exact ⟨⟨x, hXD hx⟩, rfl⟩)
  have h2 : g ∈ (normalizer (X : Set M)).comap D.subtype ↔ (g : M) ∈ normalizer (X : Set M) :=
    Iff.rfl
  rw [← h2, h]
  rfl

theorem mem_normalizer_map_iff {G H : Type*} [Group G] [Group H] (Ψ : G →* H)
    (hΨ : Function.Injective Ψ) (Y : Subgroup G) (g : G) :
    g ∈ normalizer (Y : Set G) ↔ Ψ g ∈ normalizer ((Y.map Ψ : Subgroup H) : Set H) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := Y.map Ψ) (f := Ψ) (by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩)
  rw [Subgroup.comap_map_eq_self_of_injective hΨ] at h
  have h2 : g ∈ (normalizer ((Y.map Ψ : Subgroup H) : Set H)).comap Ψ ↔
      Ψ g ∈ normalizer ((Y.map Ψ : Subgroup H) : Set H) := Iff.rfl
  rw [← h2, h]

theorem normalizer_inf_eq_centralizer_inf {E : Type} [Field E] [Finite E]
    (hE : IsOddPrimePower (Nat.card E)) (D : Subgroup M) (Ψ : D →* PSL2 E)
    (hΨ : Function.Injective Ψ) {A : M} (hAD : A ∈ D) (hA : orderOf A = 2)
    (X : Subgroup M) (hXD : X ≤ D) (hX : X ≠ ⊥) (hXodd : ∀ x ∈ X, Odd (orderOf x))
    (hXc : X ≤ centralizer ({A} : Set M)) :
    normalizer (X : Set M) ⊓ D = centralizer ({A} : Set M) ⊓ D := by
  set A' : D := ⟨A, hAD⟩ with hA'
  set X' : Subgroup D := X.subgroupOf D with hX'
  have hA'ord : orderOf A' = 2 := by
    rw [← hA]
    exact Subgroup.orderOf_mk A hAD
  have hinv : BenderSuzuki.PFAppendixIII.IsInvolution (Ψ A') := by
    refine ⟨?_, ?_⟩
    · intro h1
      have : A' = 1 := hΨ (by rw [h1, map_one])
      rw [this, orderOf_one] at hA'ord
      omega
    · rw [← map_pow]
      have : A' ^ 2 = 1 := by
        rw [← hA'ord]
        exact pow_orderOf_eq_one A'
      rw [this, map_one]
  have hX'ne : X' ≠ ⊥ := by
    intro hbot
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXD hx⟩ : D) ∈ X' := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hYne : X'.map Ψ ≠ ⊥ := by
    intro hbot
    apply hX'ne
    rw [eq_bot_iff]
    intro x hx
    have : Ψ x ∈ X'.map Ψ := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (hΨ (this.trans (map_one Ψ).symm))
  have hYodd : ∀ y ∈ X'.map Ψ, Odd (orderOf y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [orderOf_injective Ψ hΨ x]
    have : (x : M) ∈ X := hx
    rw [← Subgroup.orderOf_coe]
    exact hXodd _ this
  have hYc : X'.map Ψ ≤ centralizer ({Ψ A'} : Set (PSL2 E)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hx' : (x : M) ∈ X := hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hXc hx')
  have hlib := psl2_odd_centralizer_normalizer hE hinv (X'.map Ψ) hYne hYodd hYc
  ext g
  constructor
  · rintro ⟨hgN, hgD⟩
    refine ⟨?_, hgD⟩
    have h1 : (⟨g, hgD⟩ : D) ∈ normalizer (X' : Set D) :=
      (mem_normalizer_subgroupOf_iff D X hXD ⟨g, hgD⟩).mp hgN
    have h2 : Ψ ⟨g, hgD⟩ ∈ normalizer ((X'.map Ψ : Subgroup (PSL2 E)) : Set (PSL2 E)) :=
      (mem_normalizer_map_iff Ψ hΨ X' _).mp h1
    rw [hlib] at h2
    have h3 := Subgroup.mem_centralizer_singleton_iff.mp h2
    have h4 : ⟨g, hgD⟩ * A' = A' * ⟨g, hgD⟩ := hΨ (by rw [map_mul, map_mul]; exact h3)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h4)
  · rintro ⟨hgC, hgD⟩
    refine ⟨?_, hgD⟩
    have h3 : Ψ ⟨g, hgD⟩ * Ψ A' = Ψ A' * Ψ ⟨g, hgD⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)
    have h2 : Ψ ⟨g, hgD⟩ ∈ centralizer ({Ψ A'} : Set (PSL2 E)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr h3
    rw [← hlib] at h2
    have h1 := (mem_normalizer_map_iff Ψ hΨ X' _).mpr h2
    exact (mem_normalizer_subgroupOf_iff D X hXD ⟨g, hgD⟩).mpr h1

end Normalizer

section Main

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mem_stabilizer_subgroup_iff (α : MulAut K) (W : Subgroup K) :
    α ∈ MulAction.stabilizer (MulAut K) W ↔ ∀ k, α k ∈ W ↔ k ∈ W := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h k
    have := SetLike.ext_iff.1 h (α k)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa using this.symm
  · intro h
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have := h (α⁻¹ • x)
    simpa using this.symm

omit [Finite K] in
theorem mem_normalizer_map_conj_iff (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (g : MulAut K) (X : Subgroup K) :
    g ∈ normalizer ((X.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K)) ↔ g ∈ MulAction.stabilizer (MulAut K) X := by
  rw [Subgroup.mem_normalizer_iff, mem_stabilizer_subgroup_iff]
  have key : ∀ (h : MulAut K) (k : K), h * MulAut.conj k * h⁻¹ = MulAut.conj (h k) :=
    fun h k => mul_conj_mul_inv_eq_conj_apply h k
  have hmem : ∀ k : K, MulAut.conj k ∈ X.map (MulAut.conj : K →* MulAut K) ↔ k ∈ X :=
    fun k => Subgroup.mem_map_iff_mem hinj
  constructor
  · intro h k
    calc g k ∈ X ↔ MulAut.conj (g k) ∈ X.map (MulAut.conj : K →* MulAut K) := (hmem _).symm
      _ ↔ g * MulAut.conj k * g⁻¹ ∈ X.map (MulAut.conj : K →* MulAut K) := by rw [key]
      _ ↔ MulAut.conj k ∈ X.map (MulAut.conj : K →* MulAut K) := (h _).symm
      _ ↔ k ∈ X := hmem _
  · intro h y
    constructor
    · rintro ⟨k, hk, rfl⟩
      show g * MulAut.conj k * g⁻¹ ∈ _
      rw [key]
      exact (hmem _).mpr ((h k).mpr hk)
    · intro hy
      obtain ⟨k', hk', hk'eq⟩ := hy
      have hy' : y = MulAut.conj (g⁻¹ k') := by
        rw [← key g⁻¹ k']
        have : (MulAut.conj k') = g * y * g⁻¹ := hk'eq
        rw [this]
        group
      rw [hy']
      refine (hmem _).mpr ?_
      have := (h (g⁻¹ k')).mp (by simpa using hk')
      exact this

theorem ivk_1_3c : IVK_1_3c := by
  intro F _ _ hF K _ _ e u hu hu2 X hX1 hXu
  obtain ⟨E, hE, hfin, Ψ0, hEodd, hΨ0⟩ := exists_pgl2_psl2_embedding F hF.1
  let Ψ : ↥(innDiagSub e) →* PSL2 E := Ψ0.comp (innDiagEquiv e).toMonoidHom
  have hΨ : Function.Injective Ψ := hΨ0.comp (innDiagEquiv e).injective
  have hconj := conj_injective_of_L2 e
  set Xi : Subgroup (MulAut K) := X.map (MulAut.conj : K →* MulAut K) with hXi
  have hXiD : Xi ≤ innDiagSub e := by
    rintro _ ⟨k, -, rfl⟩
    exact innAut_le_innDiagSub e ⟨k, rfl⟩
  have hXine : Xi ≠ ⊥ := by
    intro hbot
    apply hX1
    rw [eq_bot_iff]
    intro k hk
    have : MulAut.conj k ∈ Xi := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (hconj (this.trans (map_one _).symm))
  have hXfix : ∀ k ∈ X, u k = k := by
    intro k hk
    obtain ⟨k', -, rfl⟩ := hXu hk
    exact k'.2
  have hXodd : ∀ k ∈ X, Odd (orderOf k) := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := hXu hk
    have hdvd : orderOf (⟨k', hk'⟩ : pPrimeCore 2 ↥(fixedSubgroup K u)) ∣
        Nat.card (pPrimeCore 2 ↥(fixedSubgroup K u)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    have h1 : orderOf ((fixedSubgroup K u).subtype k') = orderOf k' := Subgroup.orderOf_coe k'
    rw [h1]
    exact Nat.coprime_two_left.mp
      (Nat.Coprime.of_dvd_right hdvd (pPrimeCore_coprime_card (p := 2) (G := ↥(fixedSubgroup K u))))
  have hXiodd : ∀ x ∈ Xi, Odd (orderOf x) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [orderOf_injective (MulAut.conj : K →* MulAut K) hconj k]
    exact hXodd k hk
  have hXic : Xi ≤ centralizer ({u} : Set (MulAut K)) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := mul_conj_mul_inv_eq_conj_apply u k
    rw [hXfix k hk] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have key := normalizer_inf_eq_centralizer_inf (isOddPrimePower_of_odd_card hEodd) (innDiagSub e) Ψ hΨ
    hu hu2 Xi hXiD hXine hXiodd hXic
  ext g
  show g ∈ autNormalizer (innDiagSub e) X ↔ g ∈ centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e
  unfold autNormalizer
  rw [← key, Subgroup.mem_inf, Subgroup.mem_inf, mem_normalizer_map_conj_iff hconj]
  exact and_comm

end Main

end CFSG.GH74.GLS.IVK
