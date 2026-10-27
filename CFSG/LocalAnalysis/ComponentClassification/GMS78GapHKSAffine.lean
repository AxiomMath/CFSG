module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.GMS78

@[expose] def HKSRegularNormalAffine : Prop :=
  ∀ (R : Type) [Field R] [Finite R] (M : Type) [AddCommGroup M] [Module R M] [Finite M],
    4 ≤ Nat.card R → 3 ≤ Module.finrank R M → ∀ X : Subgroup (Equiv.Perm M),
    (∀ x ∈ X, ∃ φ : M ≃ₗ[R] M, ∃ b : M, ∀ m, x m = φ m + b) →
    (∀ a b c d : M, a ≠ b → c ≠ d → ∃ x ∈ X, x a = c ∧ x b = d) →
    ∀ C : Subgroup (Equiv.Perm M), C ≤ X → (∀ c ∈ C, c 0 = 0) → IsCyclic C →
      (∀ x ∈ X, x 0 = 0 → ∀ c ∈ C, x * c * x⁻¹ ∈ C) →
      (∀ β γ : M, β ≠ 0 → γ ≠ 0 → ∃! c, c ∈ C ∧ c β = γ) →
      ∃ E : Subgroup (Equiv.Perm M), E ≤ X ∧ (∀ x ∈ X, ∀ r ∈ E, x * r * x⁻¹ ∈ E) ∧
        ∀ β γ : M, ∃! r, r ∈ E ∧ r β = γ

namespace Affine

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M] [Module R M]

@[expose] def linPart (x : Equiv.Perm M) (m : M) : M := x m - x 0

theorem linPart_eq {x : Equiv.Perm M} {φ : M ≃ₗ[R] M} {b : M} (h : ∀ m, x m = φ m + b) :
    linPart x = φ := by
  funext m
  simp [linPart, h]

theorem linPart_zero (x : Equiv.Perm M) : linPart x 0 = 0 := sub_self _

theorem linPart_mul {x y : Equiv.Perm M} {φ : M ≃ₗ[R] M} {b : M} (hx : ∀ m, x m = φ m + b) :
    linPart (x * y) = linPart x ∘ linPart y := by
  funext m
  simp only [linPart, Function.comp_apply, Equiv.Perm.mul_apply, hx, map_sub, map_zero]
  abel

theorem linPart_one : linPart (1 : Equiv.Perm M) = id := by
  funext m
  simp [linPart]

theorem eq_add_of_linPart_eq_id {x : Equiv.Perm M} (h : linPart x = id) (m : M) :
    x m = m + x 0 := by
  have := congrFun h m
  simp only [linPart, id] at this
  exact eq_add_of_sub_eq this

variable (X : Subgroup (Equiv.Perm M))

@[expose] noncomputable def linHom (haff : ∀ x ∈ X, ∃ φ : M ≃ₗ[R] M, ∃ b : M, ∀ m, x m = φ m + b) :
    X →* Equiv.Perm M where
  toFun x := Equiv.ofBijective (linPart (x : Equiv.Perm M)) (by
    obtain ⟨φ, b, h⟩ := haff x x.2
    rw [linPart_eq h]
    exact φ.bijective)
  map_one' := by
    ext m
    simp [linPart]
  map_mul' x y := by
    obtain ⟨φ, b, h⟩ := haff x x.2
    ext m
    simp only [Subgroup.coe_mul, Equiv.ofBijective_apply, Equiv.Perm.mul_apply]
    rw [linPart_mul h]
    rfl

variable {X}

theorem linHom_apply (haff : ∀ x ∈ X, ∃ φ : M ≃ₗ[R] M, ∃ b : M, ∀ m, x m = φ m + b) (x : X)
    (m : M) : linHom X haff x m = linPart (x : Equiv.Perm M) m := rfl

theorem exists_translation_of_finrank_le_two [Finite R] [Finite M] [Nontrivial M]
    (hd : Module.finrank R M ≤ 2)
    (haff : ∀ x ∈ X, ∃ φ : M ≃ₗ[R] M, ∃ b : M, ∀ m, x m = φ m + b)
    (h2 : ∀ a b c d : M, a ≠ b → c ≠ d → ∃ x ∈ X, x a = c ∧ x b = d) :
    ∃ x ∈ X, ∃ b : M, b ≠ 0 ∧ ∀ m, x m = m + b := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have : Fintype M := Fintype.ofFinite M
  have : Module.Finite R M := Module.Finite.of_finite
  by_contra hno
  push Not at hno
  have hinj : ∀ x ∈ X, ∀ y ∈ X, linPart x = linPart y → x = y := by
    intro x hx y hy hxy
    obtain ⟨φ, b, h⟩ := haff x⁻¹ (inv_mem hx)
    have hid : linPart (x⁻¹ * y) = id := by
      rw [linPart_mul h, ← hxy, ← linPart_mul h, inv_mul_cancel, linPart_one]
    have htr := eq_add_of_linPart_eq_id hid
    have h0 : (x⁻¹ * y) 0 = 0 := by
      by_contra hne
      obtain ⟨m, hm⟩ := hno _ (mul_mem (inv_mem hx) hy) _ hne
      exact hm (htr m)
    have h1 : x⁻¹ * y = 1 := by
      ext m
      rw [htr m, h0, add_zero]
      rfl
    rw [← mul_inv_cancel_left x y, h1, mul_one]
  set n := Module.finrank R M with hn
  set bas := Module.finBasis R M
  let F : X → {s : Fin n → M // LinearIndependent R s} := fun x =>
    ⟨linPart (x : Equiv.Perm M) ∘ bas, by
      obtain ⟨φ, b, h⟩ := haff x x.2
      rw [linPart_eq h]
      exact bas.linearIndependent.map' φ.toLinearMap (LinearEquiv.ker φ)⟩
  have hF : Function.Injective F := by
    intro x y hxy
    obtain ⟨φ, b, h⟩ := haff x x.2
    obtain ⟨ψ, c, h'⟩ := haff y y.2
    have h1 : (φ : M →ₗ[R] M) = ψ := bas.ext fun i => by
      have := congrFun (congrArg Subtype.val hxy) i
      simpa [F, linPart_eq h, linPart_eq h'] using this
    have h2 : linPart (x : Equiv.Perm M) = linPart (y : Equiv.Perm M) := by
      rw [linPart_eq h, linPart_eq h']
      exact funext fun m => by simpa using LinearMap.congr_fun h1 m
    exact Subtype.ext (hinj x x.2 y y.2 h2)
  have hup := Nat.card_le_card_of_injective F hF
  rw [card_linearIndependent le_rfl] at hup
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hchoose : ∀ p : M × {m : M // m ≠ 0}, ∃ x ∈ X, x 0 = p.1 ∧ x m₀ = p.1 + p.2 := by
    rintro ⟨a, c, hc⟩
    obtain ⟨x, hx, h1, h2⟩ := h2 0 m₀ a (a + c) hm₀.symm (by simpa using hc)
    exact ⟨x, hx, h1, h2⟩
  choose G hG using hchoose
  let G' : M × {m : M // m ≠ 0} → X := fun p => ⟨G p, (hG p).1⟩
  have hG' : Function.Injective G' := by
    intro p p' hpp'
    have h1 : G p = G p' := congrArg Subtype.val hpp'
    have ha : p.1 = p'.1 := by rw [← (hG p).2.1, ← (hG p').2.1, h1]
    have hc : (p.2 : M) = p'.2 := by
      have := (hG p).2.2
      rw [h1, (hG p').2.2, ha] at this
      exact (add_left_cancel this).symm
    exact Prod.ext ha (Subtype.ext hc)
  have hlow := Nat.card_le_card_of_injective G' hG'
  rw [Nat.card_prod] at hlow
  have hne : Nat.card {m : M // m ≠ 0} = Nat.card M - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Nat.card_eq_fintype_card]
  rw [hne, Module.natCard_eq_pow_finrank (K := R), Nat.card_eq_fintype_card (α := R)] at hlow
  set q := Fintype.card R
  have hq : 2 ≤ q := by
    have := Fintype.one_lt_card (α := R)
    omega
  have hn1 : 1 ≤ n := Module.finrank_pos_iff.mpr inferInstance
  rw [← hn] at hup hlow
  rcases (show n = 1 ∨ n = 2 by omega) with h | h
  · rw [h] at hup hlow
    simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one] at hup hlow
    have : q * (q - 1) ≤ q - 1 := hlow.trans hup
    have h3 : 1 * (q - 1) < q * (q - 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  · rw [h] at hup hlow
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hup
    have h3 : q ^ 2 - q < q ^ 2 := by
      have : 0 < q := by omega
      have : q ≤ q ^ 2 := by nlinarith
      omega
    have h4 : 0 < q ^ 2 - 1 := by
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    have : q ^ 2 * (q ^ 2 - 1) ≤ (q ^ 2 - 1) * (q ^ 2 - q) := hlow.trans hup
    have h5 : (q ^ 2 - 1) * (q ^ 2 - q) < (q ^ 2 - 1) * q ^ 2 :=
      Nat.mul_lt_mul_of_pos_left h3 h4
    rw [mul_comm (q ^ 2 - 1) (q ^ 2)] at h5
    omega

theorem eq_add_of_mem_regular [Finite R] [Finite M] [Nontrivial M]
    (haff : ∀ x ∈ X, ∃ φ : M ≃ₗ[R] M, ∃ b : M, ∀ m, x m = φ m + b)
    {C : Subgroup (Equiv.Perm M)} (hCX : C ≤ X) (hC0 : ∀ c ∈ C, c 0 = 0)
    (htr : ∀ β γ : M, β ≠ 0 → γ ≠ 0 → ∃ c ∈ C, c β = γ) {E : Subgroup (Equiv.Perm M)}
    (hEX : E ≤ X) (hEn : ∀ x ∈ X, ∀ r ∈ E, x * r * x⁻¹ ∈ E)
    (hEreg : ∀ β γ : M, ∃! r, r ∈ E ∧ r β = γ) {r : Equiv.Perm M} (hr : r ∈ E) (m : M) :
    r m = m + r 0 := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have : Module.Finite R M := Module.Finite.of_finite
  set p := ringChar R
  have : CharP R p := ringChar.charP R
  obtain ⟨k, hp, hk⟩ := FiniteField.card R p
  have : Fact p.Prime := ⟨hp⟩
  have hEc : Nat.card E = Nat.card M := by
    let ev : E → M := fun r => (r : Equiv.Perm M) 0
    refine Nat.card_eq_of_bijective ev ⟨fun r r' h => ?_, fun γ => ?_⟩
    · obtain ⟨r₀, -, huniq⟩ := hEreg 0 (ev r)
      exact Subtype.ext ((huniq _ ⟨r.2, rfl⟩).trans (huniq _ ⟨r'.2, h.symm⟩).symm)
    · obtain ⟨r₀, ⟨hr₀, hr₀γ⟩, -⟩ := hEreg 0 γ
      exact ⟨⟨r₀, hr₀⟩, hr₀γ⟩
  have hMc : Nat.card M = p ^ (k * Module.finrank R M) := by
    rw [Module.natCard_eq_pow_finrank (K := R), Nat.card_eq_fintype_card (α := R), hk, pow_mul]
  have hEp : IsPGroup p E := IsPGroup.of_card (hEc.trans hMc)
  set E' := (E.subgroupOf X).map (linHom X haff) with hE'
  have hE'p : IsPGroup p E' :=
    (hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEX).symm).map _
  have hmod := hE'p.card_modEq_card_fixedPoints M
  have hn1 : 1 ≤ Module.finrank R M := Module.finrank_pos_iff.mpr inferInstance
  have hk1 : 1 ≤ k * Module.finrank R M :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero k.ne_zero (by omega))
  have h0 : Nat.card M ≡ 0 [MOD p] := by
    rw [hMc]
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by omega))
  have hfix : p ∣ Nat.card (MulAction.fixedPoints E' M) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h0)
  have h0mem : (0 : M) ∈ MulAction.fixedPoints E' M := by
    rintro ⟨s, x, -, rfl⟩
    change linHom X haff x 0 = 0
    rw [linHom_apply]
    exact linPart_zero _
  obtain ⟨m₁, hm₁, hm₁0⟩ : ∃ m₁ ∈ MulAction.fixedPoints E' M, m₁ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : MulAction.fixedPoints E' M ⊆ {0} := fun x hx => hall x hx
    have hle : Nat.card (MulAction.fixedPoints E' M) ≤ 1 := by
      calc Nat.card (MulAction.fixedPoints E' M) ≤ Nat.card ({0} : Set M) :=
            Nat.card_mono (Set.toFinite _) hsub
        _ = 1 := by simp
    have hpos : 0 < Nat.card (MulAction.fixedPoints E' M) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, h0mem⟩⟩, inferInstance⟩
    have := Nat.le_of_dvd hpos hfix
    have := hp.two_le
    omega
  have hfixE : ∀ s ∈ E, linPart s m₁ = m₁ := by
    intro s hs
    have := hm₁ ⟨linHom X haff ⟨s, hEX hs⟩, ⟨⟨s, hEX hs⟩, hs, rfl⟩⟩
    exact this
  have hlinC : ∀ c ∈ C, linPart c = c := fun c hc => funext fun m => by
    simp [linPart, hC0 c hc]
  have hlin : linPart r = id := by
    funext m
    by_cases hm : m = 0
    · rw [hm, linPart_zero]
      rfl
    obtain ⟨c, hc, hcm⟩ := htr m₁ m hm₁0 hm
    have hc' : c⁻¹ * r * c ∈ E := by
      have := hEn c⁻¹ (inv_mem (hCX hc)) r hr
      simpa using this
    have h1 := hfixE _ hc'
    obtain ⟨φ, b, hφ⟩ := haff c⁻¹ (inv_mem (hCX hc))
    obtain ⟨ψ, b', hψ⟩ := haff (c⁻¹ * r) (mul_mem (inv_mem (hCX hc)) (hEX hr))
    rw [linPart_mul hψ, linPart_mul hφ, hlinC c hc, hlinC c⁻¹ (inv_mem hc)] at h1
    simp only [Function.comp_apply] at h1
    have h2 := congrArg c h1
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h2
    rw [← hcm]
    exact h2
  exact eq_add_of_linPart_eq_id hlin m

theorem exists_translation (hHKS : HKSRegularNormalAffine) {R M : Type} [Field R] [Finite R]
    [AddCommGroup M] [Module R M] [Finite M] [Nontrivial M] (hR : 4 ≤ Nat.card R)
    {X : Subgroup (Equiv.Perm M)}
    (haff : ∀ x ∈ X, ∃ φ : M ≃ₗ[R] M, ∃ b : M, ∀ m, x m = φ m + b)
    (h2 : ∀ a b c d : M, a ≠ b → c ≠ d → ∃ x ∈ X, x a = c ∧ x b = d)
    {C : Subgroup (Equiv.Perm M)} (hCX : C ≤ X) (hC0 : ∀ c ∈ C, c 0 = 0) (hcyc : IsCyclic C)
    (hnorm : ∀ x ∈ X, x 0 = 0 → ∀ c ∈ C, x * c * x⁻¹ ∈ C)
    (hreg : ∀ β γ : M, β ≠ 0 → γ ≠ 0 → ∃! c, c ∈ C ∧ c β = γ) :
    ∃ x ∈ X, ∃ b : M, b ≠ 0 ∧ ∀ m, x m = m + b := by
  by_cases hd : 3 ≤ Module.finrank R M
  · obtain ⟨E, hEX, hEn, hEreg⟩ := hHKS R M hR hd X haff h2 C hCX hC0 hcyc hnorm hreg
    obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
    obtain ⟨r, ⟨hr, hr0⟩, -⟩ := hEreg 0 m₀
    refine ⟨r, hEX hr, m₀, hm₀, fun m => ?_⟩
    rw [eq_add_of_mem_regular haff hCX hC0 (fun β γ hβ hγ => (hreg β γ hβ hγ).exists) hEX hEn
      hEreg hr m, hr0]
  · exact exists_translation_of_finrank_le_two (by omega) haff h2

end Affine

end CFSG.ComponentClassification.GMS78
