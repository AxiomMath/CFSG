module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL4Comm
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL4Form
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClBridge
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraphField
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowS
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSymplectic

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint Subgroup Matrix CFSG.GH74.Uniqueness.Bender
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem l4_type {A : Type} [Group A] [Finite A] {K : Subgroup A} {p ℓ e : ℕ} {k : Type}
    [Field k] [Finite k] (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hk : Nat.card k = ℓ ^ e)
    (hp2 : p ≠ 2) {f : ℕ}
    (hsrc : StatedClassicalModel (K ⧸ center K) .PSL 2 p f ∨
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (K ⧸ center K) .PSL 3 2 2)
    (hodd : Odd (Nat.card (center K)))
    {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    {x : A} (hx : orderOf x = 2)
    (hL₁ : CFSG.Assembly.IsComponentOf (K.map ρ)
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 4 k) ⊓
        centralizer {ρ x})) :
    (∃ (B : GL (Fin 4) k) (μ : kˣ), ρ x = conjAut 4 k B ∧ ¬ IsSquare (μ : k) ∧
        B ^ 2 = GeneralLinearGroup.scalar (Fin 4) μ) ∨
      ∃ B : GL (Fin 4) k, ρ x = conjAut 4 k B * dualAut 4 k ∧
        (B : Matrix (Fin 4) (Fin 4) k)ᵀ = (B : Matrix (Fin 4) (Fin 4) k) := by
  classical
  have hm3 : 3 ≤ 4 := by norm_num
  have hm4 : 4 ≤ 4 := le_refl 4
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ x)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨μ, hμ, hsq, -⟩ :=
        inner_case_reduction hx hm4 hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc (fun _ => Or.inr hodd)
      exact Or.inl ⟨B, μ, hρa, hμ, hsq⟩
    · exact (field_case_false hx hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc).elim
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut 4 k B * dualAut 4 k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← hx, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · exact Or.inr ⟨B, hρa, hB⟩
      · exact (symplectic_case_false hm4 hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc).elim
    · exact (graph_field_case_false hx hm4 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc).elim

section Algebra

variable {k : Type} [Field k] [Finite k]

omit [Finite k] in
theorem scalar_comm' {n : ℕ} (c : kˣ) (g : GL (Fin n) k) :
    GeneralLinearGroup.scalar (Fin n) c * g = g * GeneralLinearGroup.scalar (Fin n) c := by
  have h : GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) k) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact (Subgroup.mem_center_iff.1 h g).symm

theorem exists_scalar_of_conjAut_comm {m : ℕ} (hm : 3 ≤ m) (B X : GL (Fin m) k)
    (h : conjAut m k B * conjAut m k X = conjAut m k X * conjAut m k B) :
    ∃ c : kˣ, B * X = GeneralLinearGroup.scalar (Fin m) c * X * B := by
  have h1 : conjAut m k (B * X * B⁻¹ * X⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h]
    group
  have h2 := ker_conjAut_le_center hm (MonoidHom.mem_ker.2 h1)
  rw [GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  refine ⟨c, ?_⟩
  calc B * X = (B * X * B⁻¹ * X⁻¹) * X * B := by group
    _ = GeneralLinearGroup.scalar (Fin m) c * X * B := by rw [← hc]

theorem exists_scalar_of_graph_comm {m : ℕ} (hm : 3 ≤ m) (B X : GL (Fin m) k)
    (h : Commute (conjAut m k X) (conjAut m k B * dualAut m k)) :
    ∃ c : kˣ, B * GeneralLinearGroup.inverseTranspose X * B⁻¹ =
      GeneralLinearGroup.scalar (Fin m) c * X := by
  have h0 := (commute_conjAut_pureGraph_iff B X).1 h
  have h1 : conjAut m k ((X * B)⁻¹ * (B * GeneralLinearGroup.inverseTranspose X)) = 1 := by
    simp only [map_mul, map_inv]
    rw [← h0]
    group
  have h2 := ker_conjAut_le_center hm (MonoidHom.mem_ker.2 h1)
  rw [GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  refine ⟨c, ?_⟩
  have h3 : B * GeneralLinearGroup.inverseTranspose X =
      X * B * GeneralLinearGroup.scalar (Fin m) c := by
    rw [hc]
    group
  calc B * GeneralLinearGroup.inverseTranspose X * B⁻¹
      = X * B * GeneralLinearGroup.scalar (Fin m) c * B⁻¹ := by rw [h3]
    _ = X * (B * GeneralLinearGroup.scalar (Fin m) c * B⁻¹) := by group
    _ = X * GeneralLinearGroup.scalar (Fin m) c := by
        rw [← scalar_comm' c B]; group
    _ = GeneralLinearGroup.scalar (Fin m) c * X := (scalar_comm' c X).symm

end Algebra




theorem l4_pair {A : Type} [Group A] [Finite A] {W K : Subgroup A} {p ℓ e f : ℕ} {k : Type}
    [Field k] [Finite k] (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hk : Nat.card k = ℓ ^ e)
    (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (K ⧸ center K) .PSL 2 p f ∨
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (K ⧸ center K) .PSL 3 2 2)
    (hodd : Odd (Nat.card (center K)))
    {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    {a b : A} (hb : orderOf b = 2) (hab : a ≠ b)
    (hbK : b ∈ centralizer (K : Set A))
    (hCAa : (centralizer {a}).map ρ = ρ.range ⊓ centralizer {ρ a})
    (hCWa : (W ⊓ centralizer {a}).map ρ = inner (projectiveSL 4 k) ⊓ centralizer {ρ a})
    (hL₁a : CFSG.Assembly.IsComponentOf (K.map ρ)
      (inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    (hL₁b : CFSG.Assembly.IsComponentOf (K.map ρ)
      (inner (projectiveSL 4 k) ⊓ centralizer {ρ b}))
    {B : GL (Fin 4) k} {μ : kˣ} (hρa : ρ a = conjAut 4 k B) (hμ : ¬ IsSquare (μ : k))
    (hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin 4) μ) : False := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨hS, -⟩ := selectorRowS_of_inner htwo hinj hCAa hCWa hL₁a hρa hμ hsq
  obtain ⟨ν, hν, Ψ, C, -, h2, -, -, -, -, -, -, h9, -, -, -, -, -⟩ := hS
  have hcent : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)),
      ρ b * conjAut 4 k (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) =
        conjAut 4 k (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) * ρ b := by
    intro g
    have hmem : (MulAut.conj (conjAut 4 k C))
        (conjAut 4 k (rowSPi ν Ψ (SpecialLinearGroup.toGL g))) ∈ K.map ρ := by
      rw [h9]
      exact ⟨conjAut 4 k (rowSPi ν Ψ (SpecialLinearGroup.toGL g)), ⟨g, rfl⟩, rfl⟩
    obtain ⟨x, hxK, hx⟩ := hmem
    have h1 : x * b = b * x := Subgroup.mem_centralizer_iff.1 hbK x hxK
    have h2' : ρ x * ρ b = ρ b * ρ x := by rw [← map_mul, ← map_mul, h1]
    rw [hx] at h2'
    simp only [MulAut.conj_apply, map_mul, map_inv] at h2' ⊢
    exact h2'.symm
  have hsc : ∀ (c : kˣ) (Y Z : GL (Fin 4) k),
      Y * (GeneralLinearGroup.scalar (Fin 4) c * Z) =
        GeneralLinearGroup.scalar (Fin 4) c * (Y * Z) := fun c Y Z => by
    rw [← mul_assoc, ← scalar_comm' c Y, mul_assoc]
  rcases l4_type hℓ hℓ2 he hk hp2 hsrc hodd hinj hb hL₁b with
    ⟨Bb, μb, hρb, -, hsqb⟩ | ⟨Bb, hρb, hBs⟩
  ·
    have hlin : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)), ∃ c : kˣ,
        (C⁻¹ * Bb * C) * rowSPi ν Ψ (SpecialLinearGroup.toGL g) =
          GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g) *
            (C⁻¹ * Bb * C) := by
      intro g
      have hc := hcent g
      rw [hρb] at hc
      obtain ⟨c, hc'⟩ := exists_scalar_of_conjAut_comm (by norm_num) Bb
        (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) hc
      refine ⟨c, ?_⟩
      calc (C⁻¹ * Bb * C) * rowSPi ν Ψ (SpecialLinearGroup.toGL g)
          = C⁻¹ * (Bb * (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹)) * C := by group
        _ = C⁻¹ * (GeneralLinearGroup.scalar (Fin 4) c *
              (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) * Bb) * C := by rw [hc']
        _ = GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g) *
              (C⁻¹ * Bb * C) := by
            rw [mul_assoc (GeneralLinearGroup.scalar (Fin 4) c), hsc]
            group
    have hsq0 : ∃ c : kˣ, (C⁻¹ * Bb * C) ^ 2 = GeneralLinearGroup.scalar (Fin 4) c := by
      refine ⟨μb, ?_⟩
      calc (C⁻¹ * Bb * C) ^ 2 = C⁻¹ * Bb ^ 2 * C := by rw [pow_two, pow_two]; group
        _ = C⁻¹ * GeneralLinearGroup.scalar (Fin 4) μb * C := by rw [hsqb]
        _ = GeneralLinearGroup.scalar (Fin 4) μb := by
            rw [← scalar_comm' μb C⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    obtain ⟨c, hc | hc⟩ := rowS_commutant ν Ψ hν htwo (C⁻¹ * Bb * C) hlin hsq0
    · have hBb : Bb = GeneralLinearGroup.scalar (Fin 4) c := by
        calc Bb = C * (C⁻¹ * Bb * C) * C⁻¹ := by group
          _ = C * GeneralLinearGroup.scalar (Fin 4) c * C⁻¹ := by rw [hc]
          _ = GeneralLinearGroup.scalar (Fin 4) c := by rw [← scalar_comm' c C]; group
      have h1 : ρ b = 1 := by rw [hρb, hBb, conjAut_scalar]
      have : b = 1 := hinj (by rw [h1, map_one])
      rw [this, orderOf_one] at hb
      omega
    · have hBb : Bb = GeneralLinearGroup.scalar (Fin 4) c * (C * rowSU ν Ψ * C⁻¹) := by
        calc Bb = C * (C⁻¹ * Bb * C) * C⁻¹ := by group
          _ = C * (GeneralLinearGroup.scalar (Fin 4) c * rowSU ν Ψ) * C⁻¹ := by rw [hc]
          _ = GeneralLinearGroup.scalar (Fin 4) c * (C * rowSU ν Ψ * C⁻¹) := by
              rw [hsc, mul_assoc]
      have h1 : ρ b = ρ a := by
        rw [hρb, hBb, map_mul, conjAut_scalar, one_mul, h2]
        simp only [map_mul, map_inv]
      exact hab (hinj h1).symm
  ·
    have hgr : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)), ∃ c : kˣ,
        (C⁻¹ * Bb * GeneralLinearGroup.inverseTranspose C) *
            GeneralLinearGroup.inverseTranspose (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) *
            (C⁻¹ * Bb * GeneralLinearGroup.inverseTranspose C)⁻¹ =
          GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g) := by
      intro g
      have hc : Commute (conjAut 4 k (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹))
          (conjAut 4 k Bb * dualAut 4 k) := by
        have := hcent g
        rw [hρb] at this
        exact this.symm
      obtain ⟨c, hc'⟩ := exists_scalar_of_graph_comm (by norm_num) Bb
        (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) hc
      refine ⟨c, ?_⟩
      have h5 : (C⁻¹ * Bb * GeneralLinearGroup.inverseTranspose C) *
            GeneralLinearGroup.inverseTranspose (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) *
            (C⁻¹ * Bb * GeneralLinearGroup.inverseTranspose C)⁻¹ =
          C⁻¹ * (Bb * GeneralLinearGroup.inverseTranspose
            (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) * Bb⁻¹) * C := by
        simp only [map_mul, map_inv]
        group
      rw [h5, hc', hsc]
      group
    have hsym : ((C⁻¹ * Bb * GeneralLinearGroup.inverseTranspose C : GL (Fin 4) k) :
        Matrix (Fin 4) (Fin 4) k)ᵀ =
        ((C⁻¹ * Bb * GeneralLinearGroup.inverseTranspose C : GL (Fin 4) k) :
          Matrix (Fin 4) (Fin 4) k) := by
      simp only [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, Matrix.transpose_mul,
        Matrix.transpose_transpose, hBs, Matrix.mul_assoc]
    exact rowS_no_symmetric_invariant ν Ψ hν htwo _ hsym hgr


theorem l4_core {A : Type} [Group A] [Finite A] {W K : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) (hKW : K ≤ W) {p ℓ e f : ℕ} {k : Type}
    [Field k] [Finite k] (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hk : Nat.card k = ℓ ^ e)
    (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (K ⧸ center K) .PSL 2 p f ∨
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (K ⧸ center K) .PSL 3 2 2)
    (hodd : Odd (Nat.card (center K))) (φ : W ≃* projectiveSL 4 k)
    {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) (hcomm : x * y = y * x)
    (hxK : x ∈ centralizer (K : Set A)) (hyK : y ∈ centralizer (K : Set A))
    (hterm : ∀ u : A, orderOf u = 2 → u ∈ centralizer (K : Set A) →
      CFSG.Assembly.IsComponentOf K (centralizer ({u} : Set A))) : False := by
  classical
  have hZ := center_projectiveSL_eq_bot (k := k) (show 3 ≤ 4 by norm_num)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW φ hZ
  have hz1 : x * y ≠ 1 := by
    intro h1
    have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hxx : x⁻¹ = x := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx]
      exact pow_orderOf_eq_one x
    exact hxy (this.trans hxx).symm
  have hz2 : orderOf (x * y) = 2 := by
    refine orderOf_eq_prime ?_ hz1
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
    have hy2 : y * y = 1 := by rw [← pow_two, ← hy]; exact pow_orderOf_eq_one y
    calc (x * y) ^ 2 = x * y * (x * y) := pow_two _
      _ = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, mul_one]
  have hzK : x * y ∈ centralizer (K : Set A) := Subgroup.mul_mem _ hxK hyK
  have hKx := hterm x hx hxK
  have hKy := hterm y hy hyK
  have hKz := hterm (x * y) hz2 hzK
  have himg : ∀ {u : A}, CFSG.Assembly.IsComponentOf K (centralizer ({u} : Set A)) →
      (centralizer {u}).map ρ = ρ.range ⊓ centralizer {ρ u} ∧
      (W ⊓ centralizer {u}).map ρ = inner (projectiveSL 4 k) ⊓ centralizer {ρ u} ∧
      CFSG.Assembly.IsComponentOf (K.map ρ) (inner (projectiveSL 4 k) ⊓ centralizer {ρ u}) :=
    fun {u} hKu => by
      obtain ⟨-, hCA, hCW', hL₁⟩ := socle_images φ hinj hρW hKW hKu
      exact ⟨hCA, hCW', hL₁⟩
  obtain ⟨hCAx, hCWx, hL₁x⟩ := himg hKx
  obtain ⟨hCAy, hCWy, hL₁y⟩ := himg hKy
  obtain ⟨hCAz, hCWz, hL₁z⟩ := himg hKz
  have hxz : x ≠ x * y := by
    intro h1
    have : y = 1 := by
      have := congrArg (fun t => x⁻¹ * t) h1
      simpa using this.symm
    rw [this, orderOf_one] at hy
    omega
  rcases l4_type hℓ hℓ2 he hk hp2 hsrc hodd hinj hx hL₁x with
    ⟨Bx, μx, hρx, hμx, hsqx⟩ | ⟨Bx, hρx, hBxs⟩
  · exact l4_pair hℓ hℓ2 he hk hp2 hsrc hodd hinj hy hxy hyK hCAx hCWx hL₁x hL₁y hρx hμx hsqx
  rcases l4_type hℓ hℓ2 he hk hp2 hsrc hodd hinj hy hL₁y with
    ⟨By, μy, hρy, hμy, hsqy⟩ | ⟨By, hρy, hBys⟩
  · exact l4_pair hℓ hℓ2 he hk hp2 hsrc hodd hinj hx hxy.symm hxK hCAy hCWy hL₁y hL₁x hρy hμy
      hsqy
  have htrans := standard_automorphism_transport (n := 4) (K := k)
  have hρz : ρ (x * y) = conjAut 4 k (Bx * GeneralLinearGroup.inverseTranspose By) := by
    rw [map_mul, hρx, hρy, map_mul]
    calc conjAut 4 k Bx * dualAut 4 k * (conjAut 4 k By * dualAut 4 k)
        = conjAut 4 k Bx * (dualAut 4 k * conjAut 4 k By * dualAut 4 k) := by group
      _ = _ := by rw [htrans.2.2.2.2.1]
  rcases l4_type hℓ hℓ2 he hk hp2 hsrc hodd hinj hz2 hL₁z with
    ⟨Bz, μz, hρz', hμz, hsqz⟩ | ⟨Bz, hρz', hBzs⟩
  · exact l4_pair hℓ hℓ2 he hk hp2 hsrc hodd hinj hx hxz.symm hxK hCAz hCWz hL₁z hL₁x hρz' hμz hsqz
  · exfalso
    have h1 : conjAut 4 k Bz * dualAut 4 k =
        conjAut 4 k (Bx * GeneralLinearGroup.inverseTranspose By) := hρz'.symm.trans hρz
    have h2 : dualAut 4 k = conjAut 4 k (Bz⁻¹ * (Bx * GeneralLinearGroup.inverseTranspose By)) := by
      rw [map_mul, map_inv, ← h1]
      group
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := k) (n := 4) (by norm_num)
    rw [h2]
    exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem ivk73_l4 (p f : ℕ)
    (_hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f) (_hmod : p ^ f % 8 ≠ 1) :
    Ivk73Empty (fun X _ => LieModel X .PSL 4 p f) := by
  intro N _ _ L K Q h hm
  obtain ⟨x, hxQ, y, hyQ, hx, hy, hxy, hcomm⟩ :=
    C3.Layer1.U1a.exists_commuting_involutions h.Q_rank
  have := h.normal
  obtain ⟨p', f', hp2', hsrc⟩ := h.exists_hsrc
  obtain ⟨⟨hr, hf', -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := Generic.S45.LQ.stated_of_lieModel_PSL hm
  let φ : ↥L ≃* projectiveSL 4 F :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F))
  exact l4_core (W := L) h.centralizer_eq_bot h.K_le hr hp2 hf' hF hp2' hsrc
    (odd_center_K h.kbar_cases) φ hx hy hxy hcomm (h.Q_sylow.le hxQ) (h.Q_sylow.le hyQ)
    (fun u hu hc => h.isComponentOf_centralizer hu hc)

end CFSG.GH74.GLS.IVK
