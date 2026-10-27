module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsS6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv

theorem card_alt6' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

@[expose] def tMulC : List Nat := [0, 4, 8, 5, 6, 1, 7, 2, 3, 9]

@[expose] def tMulInvC : List Nat := [0, 5, 7, 8, 1, 3, 4, 6, 2, 9]

theorem tMul_code : code A6Models.tMul = tMulC := by decide +kernel

theorem tMulInv_code : code A6Models.tMul⁻¹ = tMulInvC := by decide +kernel

theorem tMul_mem : A6Models.tMul ∈ A6Models.autA6 := by
  unfold A6Models.autA6
  exact Subgroup.subset_closure (by simp)

theorem swap_class_check : Core.autL.all (fun a =>
    Core.cmul a a != Core.cid || a == Core.cid || (Core.cpslList a).length % 12 != 0 ||
    Core.pslLit.any (fun y => Core.cmul a y == Core.cmul y Core.tFrobC) ||
    Core.pslLit.any (fun y =>
      Core.cmul (Core.cmul (Core.cmul tMulC a) tMulInvC) y == Core.cmul y Core.tFrobC)) = true := by
  decide +kernel

theorem exists_swap_class {a : P10} (ha : a ∈ A6Models.autA6) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (h12 : 12 ∣ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10))) :
    (∃ y ∈ A6Models.psl29, a * y = y * A6Models.tFrob) ∨
      ∃ y ∈ A6Models.psl29, (A6Models.tMul * a * A6Models.tMul⁻¹) * y = y * A6Models.tFrob := by
  have hall := swap_class_check
  rw [List.all_eq_true] at hall
  have h1 := hall (code a) (code_mem_autL ha)
  rw [card_psl29_centralizer] at h12
  have e1 : (Core.cmul (code a) (code a) != Core.cid) = false := by
    rw [← code_mul, ha2, code_one]
    simp
  have e2 : (code a == Core.cid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [← code_one]
    intro hc
    exact ha1 (code_injective hc)
  have e3 : ((Core.cpslList (code a)).length % 12 != 0) = false := by
    simp [Nat.mod_eq_zero_of_dvd h12]
  rw [e1, e2, e3] at h1
  simp only [Bool.false_or, Bool.or_eq_true, List.any_eq_true] at h1
  rcases h1 with ⟨c, hc, hmem⟩ | ⟨c, hc, hmem⟩
  · left
    obtain ⟨y, hy, rfl⟩ := exists_psl29_of_code hc
    refine ⟨y, hy, code_injective ?_⟩
    simp only [beq_iff_eq] at hmem
    rw [code_mul, code_mul, tFrob_code]
    exact hmem
  · right
    obtain ⟨y, hy, rfl⟩ := exists_psl29_of_code hc
    refine ⟨y, hy, code_injective ?_⟩
    simp only [beq_iff_eq] at hmem
    rw [code_mul, code_mul, code_mul, code_mul, tFrob_code, tMul_code, tMulInv_code]
    exact hmem

theorem exists_psl_equiv : ∃ ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6),
    ∀ (x : P10) (hx : x ∈ A6Models.psl29),
      ∃ hy : A6Models.tFrob * x * A6Models.tFrob⁻¹ ∈ A6Models.psl29,
        ((ψ ⟨_, hy⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          tau * ((ψ ⟨x, hx⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * tau⁻¹ := by
  obtain ⟨ψ, hinj, hev, hconj⟩ := exists_psl_hom
  let ψ₁ : ↥A6Models.psl29 →* alternatingGroup (Fin 6) := ψ.codRestrict _ hev
  have hψ₁inj : Function.Injective ψ₁ := fun a b h => hinj (congrArg Subtype.val h)
  have hbij : Function.Bijective ψ₁ :=
    hψ₁inj.bijective_of_nat_card_le (by rw [card_psl29, card_alt6'])
  exact ⟨MulEquiv.ofBijective ψ₁ hbij, fun x hx => hconj x hx⟩

@[expose] def conjAut (a : ↥A6Models.autA6) : MulAut ↥A6Models.psl29 where
  toFun x := ⟨(a : P10) * (x : P10) * (a : P10)⁻¹, psl29_normal _ a.2 _ x.2⟩
  invFun x := ⟨(a : P10)⁻¹ * (x : P10) * (a : P10), by
    have h := psl29_normal _ (A6Models.autA6.inv_mem a.2) _ x.2
    simpa using h⟩
  left_inv x := by
    apply Subtype.ext
    show (a : P10)⁻¹ * ((a : P10) * (x : P10) * (a : P10)⁻¹) * (a : P10) = x
    group
  right_inv x := by
    apply Subtype.ext
    show (a : P10) * ((a : P10)⁻¹ * (x : P10) * (a : P10)) * (a : P10)⁻¹ = x
    group
  map_mul' x y := by
    apply Subtype.ext
    show (a : P10) * ((x : P10) * (y : P10)) * (a : P10)⁻¹ =
      ((a : P10) * (x : P10) * (a : P10)⁻¹) * ((a : P10) * (y : P10) * (a : P10)⁻¹)
    group

theorem conjAut_apply (a : ↥A6Models.autA6) (x : ↥A6Models.psl29) :
    ((conjAut a x : ↥A6Models.psl29) : P10) = (a : P10) * (x : P10) * (a : P10)⁻¹ := rfl

theorem conjAut_mk_apply (a : P10) (ha : a ∈ A6Models.autA6) (x : ↥A6Models.psl29) :
    ((conjAut ⟨a, ha⟩ x : ↥A6Models.psl29) : P10) = a * (x : P10) * a⁻¹ := rfl

theorem conjAut_injective : Function.Injective conjAut := by
  intro a b h
  have hcomm : ∀ x ∈ A6Models.psl29, ((a : P10)⁻¹ * (b : P10)) * x = x * ((a : P10)⁻¹ * (b : P10)) := by
    intro x hx
    have hx' := congrArg (fun f : MulAut ↥A6Models.psl29 => ((f ⟨x, hx⟩ : ↥A6Models.psl29) : P10)) h
    simp only [conjAut_apply] at hx'
    calc (a : P10)⁻¹ * (b : P10) * x = (a : P10)⁻¹ * ((b : P10) * x * (b : P10)⁻¹) * (b : P10) := by
          group
      _ = (a : P10)⁻¹ * ((a : P10) * x * (a : P10)⁻¹) * (b : P10) := by rw [hx']
      _ = x * ((a : P10)⁻¹ * (b : P10)) := by group
  have hmem : (a : P10)⁻¹ * (b : P10) ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.inv_mem a.2) b.2
  have h1 := centralizer_psl29 hmem hcomm
  apply Subtype.ext
  calc (a : P10) = (a : P10) * ((a : P10)⁻¹ * (b : P10)) := by rw [h1, mul_one]
    _ = (b : P10) := by group

theorem conjAut_surjective : Function.Surjective conjAut := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  have hcard : Nat.card (MulAut ↥A6Models.psl29) ≤ 1440 := by
    have h := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    rwa [← Nat.card_congr (MulAut.congr ψ).toEquiv] at h
  have : Finite (MulAut ↥A6Models.psl29) :=
    Finite.of_injective (fun f : MulAut ↥A6Models.psl29 => (f : ↥A6Models.psl29 → ↥A6Models.psl29))
      DFunLike.coe_injective
  exact (conjAut_injective.bijective_of_nat_card_le (by rw [card_autA6]; exact hcard)).2

theorem tau_eq_swap : tau = swap 0 1 := by decide +kernel

theorem tau_isSwap : tau.IsSwap := ⟨0, 1, by decide, tau_eq_swap⟩

section Finish

variable {K : Type*} [Group K]

theorem finish_swap_model (α : MulAut K) (φ : K ≃* ↥A6Models.psl29) (a : P10)
    (hφ : ∀ k : K, ((φ (α k) : ↥A6Models.psl29) : P10) = a * ((φ k : ↥A6Models.psl29) : P10) * a⁻¹)
    {y : P10} (hy : y ∈ A6Models.psl29) (hay : a * y = y * A6Models.tFrob) :
    ∃ φ' : K ≃* ↥A6Models.psl29, ∀ k : K, ((φ' (α k) : ↥A6Models.psl29) : P10) =
      A6Models.tFrob * ((φ' k : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹ := by
  let yy : ↥A6Models.psl29 := ⟨y, hy⟩
  let φ' : K ≃* ↥A6Models.psl29 := φ.trans (MulAut.conj yy⁻¹)
  refine ⟨φ', fun k => ?_⟩
  have hφ' : ∀ k : K, ((φ' k : ↥A6Models.psl29) : P10) = y⁻¹ * ((φ k : ↥A6Models.psl29) : P10) * y := by
    intro k
    show ((yy⁻¹ * φ k * yy⁻¹⁻¹ : ↥A6Models.psl29) : P10) = _
    simp [yy]
  rw [hφ', hφ', hφ k]
  have h1 : a = y * A6Models.tFrob * y⁻¹ := by
    calc a = a * y * y⁻¹ := by group
      _ = y * A6Models.tFrob * y⁻¹ := by rw [hay]
  rw [h1]
  group

theorem iso_swap_of_model (ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6))
    (hψ : ∀ (x : P10) (hx : x ∈ A6Models.psl29),
      ∃ hy : A6Models.tFrob * x * A6Models.tFrob⁻¹ ∈ A6Models.psl29,
        ((ψ ⟨_, hy⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          tau * ((ψ ⟨x, hx⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * tau⁻¹)
    (α : MulAut K) (φ : K ≃* ↥A6Models.psl29)
    (hφ : ∀ k : K, ((φ (α k) : ↥A6Models.psl29) : P10) =
      A6Models.tFrob * ((φ k : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹) :
    ∀ k : K, ((ψ (φ (α k)) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      tau⁻¹ * ((ψ (φ k) : alternatingGroup (Fin 6)) : Perm (Fin 6)) * tau := by
  intro k
  obtain ⟨hmem, hrel⟩ := hψ ((φ k : ↥A6Models.psl29) : P10) (φ k).2
  have heq : φ (α k) = ⟨_, hmem⟩ := Subtype.ext (hφ k)
  rw [heq, hrel, tau_inv]

end Finish

theorem exists_aut_model {K : Type*} [Group K] (φ : K ≃* ↥A6Models.psl29) (γ : MulAut K) :
    ∃ b : P10, b ∈ A6Models.autA6 ∧ ∀ k : K, ((φ (γ k) : ↥A6Models.psl29) : P10) =
      b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹ := by
  let β : MulAut ↥A6Models.psl29 := (φ.symm.trans γ).trans φ
  obtain ⟨⟨b, hbA⟩, hb⟩ := conjAut_surjective β
  refine ⟨b, hbA, fun k => ?_⟩
  have h := congrArg (fun f : MulAut ↥A6Models.psl29 => ((f (φ k) : ↥A6Models.psl29) : P10)) hb
  simp only [conjAut_mk_apply] at h
  rw [h]
  simp [β]

theorem exists_swap_model {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6))
    (α : MulAut K) (hα2 : ∀ k, α (α k) = k) (hα1 : ∃ k, α k ≠ k)
    (L : Subgroup K) (hL : Nat.card L = 12) (hαL : ∀ l ∈ L, α l = l) :
    ∃ φ : K ≃* ↥A6Models.psl29, ∀ k : K, ((φ (α k) : ↥A6Models.psl29) : P10) =
      A6Models.tFrob * ((φ k : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹ := by
  obtain ⟨ψ, hψ⟩ := exists_psl_equiv
  let φ : K ≃* ↥A6Models.psl29 := e₀.trans ψ.symm
  obtain ⟨a, haA, hβa⟩ := exists_aut_model φ α
  have ha2 : a * a = 1 := by
    have hc : a * a ∈ A6Models.autA6 := A6Models.autA6.mul_mem haA haA
    refine centralizer_psl29 hc fun x hx => ?_
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have h1 := hβa k
    have h2 := hβa (α k)
    rw [hα2 k, h1, hk] at h2
    calc a * a * x = (a * (a * x * a⁻¹) * a⁻¹) * (a * a) := by group
      _ = x * (a * a) := by rw [← h2]
  have ha1 : a ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := hα1
    apply hk
    apply φ.injective
    apply Subtype.ext
    rw [hβa k, h1]
    simp
  have hdvd : 12 ∣ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10)) := by
    let f : K →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
    have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
    have hle : L.map f ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10) := by
      rintro _ ⟨l, hl, rfl⟩
      refine ⟨(φ l).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h := hβa l
      rw [hαL l hl] at h
      show ((φ l : ↥A6Models.psl29) : P10) * a = a * ((φ l : ↥A6Models.psl29) : P10)
      calc ((φ l : ↥A6Models.psl29) : P10) * a
          = (a * ((φ l : ↥A6Models.psl29) : P10) * a⁻¹) * a := by rw [← h]
        _ = a * ((φ l : ↥A6Models.psl29) : P10) := by group
    have hcard : Nat.card (L.map f) = 12 := by
      rw [Subgroup.card_map_of_injective hfinj]
      exact hL
    exact hcard ▸ Subgroup.card_dvd_of_le hle
  rcases exists_swap_class haA ha2 ha1 hdvd with ⟨y, hy, hay⟩ | ⟨y, hy, hay⟩
  · exact finish_swap_model α φ a hβa hy hay
  ·
    let g₀ : ↥A6Models.autA6 := ⟨A6Models.tMul, tMul_mem⟩
    let φ₂ : K ≃* ↥A6Models.psl29 := φ.trans (conjAut g₀)
    refine finish_swap_model α φ₂ (A6Models.tMul * a * A6Models.tMul⁻¹) ?_ hy hay
    intro k
    show A6Models.tMul * ((φ (α k) : ↥A6Models.psl29) : P10) * A6Models.tMul⁻¹ = _
    rw [hβa k]
    show _ = (A6Models.tMul * a * A6Models.tMul⁻¹) *
      (A6Models.tMul * ((φ k : ↥A6Models.psl29) : P10) * A6Models.tMul⁻¹) *
        (A6Models.tMul * a * A6Models.tMul⁻¹)⁻¹
    group

theorem exists_iso_swap {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6))
    (α : MulAut K) (hα2 : ∀ k, α (α k) = k) (hα1 : ∃ k, α k ≠ k)
    (L : Subgroup K) (hL : Nat.card L = 12) (hαL : ∀ l ∈ L, α l = l) :
    ∃ e : K ≃* alternatingGroup (Fin 6), ∀ k : K,
      ((e (α k) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        tau⁻¹ * ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6)) * tau := by
  obtain ⟨ψ, hψ⟩ := exists_psl_equiv
  obtain ⟨φ, hφ⟩ := exists_swap_model e₀ α hα2 hα1 L hL hαL
  exact ⟨φ.trans ψ, iso_swap_of_model ψ hψ α φ hφ⟩

end CFSG.QuasithinUnique.DoubleA3
