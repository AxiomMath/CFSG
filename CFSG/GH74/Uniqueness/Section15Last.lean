module

public import CFSG.GH74.Uniqueness.Section15GL32
public import CFSG.GH74.Uniqueness.Section15LastField
public import CFSG.GH74.Uniqueness.Section15HeringStmt

public section

namespace CFSG.GH74.Uniqueness

open Subgroup MulAction

namespace Section15Last

variable {X : Type} [Group X] [Finite X] {M V R₀ Mo D K : Subgroup X} {u : X} {n : ℕ}

theorem final_main (h : FinalHyp M V R₀ Mo D K u n) (hHer : Hering32Stmt) :
    n = 3 ∧ ∃ x ∈ M, x * x ∈ V ∧ x * x ∉ R₀ := by
  let _ : MulAction ↥M ↥Mo := h.pointAct
  obtain ⟨F, _, _, e, hcardF, he1, hunits, hsemi⟩ := h.fieldData
  let ρ₀ : ↥M →* Equiv.Perm ↥Mo := MulAction.toPermHom ↥M ↥Mo
  let G : Subgroup (Equiv.Perm ↥Mo) := ρ₀.range
  let ρ : ↥M →* ↥G := ρ₀.rangeRestrict
  have hρsurj : Function.Surjective ρ := ρ₀.rangeRestrict_surjective
  have hfaith : FaithfulSMul ↥G ↥Mo :=
    ⟨fun {g₁ g₂} hg => Subtype.ext (Equiv.ext hg)⟩
  have hker : ∀ g : ↥M, ρ g = 1 ↔ (g : X) ∈ V := by
    intro g
    rw [← h.smulMo_trivial_iff g]
    constructor
    · intro hg y
      have h1 := congrArg (fun p : ↥G => (p : Equiv.Perm ↥Mo) y) hg
      exact h1
    · intro hg
      exact Subtype.ext (Equiv.ext fun y => hg y)
  have he0 : e.symm 0 = 1 := by
    rw [← he1]
    exact e.symm_apply_apply 1
  have h2 : IsMultiplyPretransitive ↥G ↥Mo 2 := by
    rw [is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg1, hg2⟩ := h.exists_smulMo_two hab hcd
    exact ⟨ρ g, hg1, hg2⟩
  have hH1 : ∀ g : ↥G, g • e.symm 0 = e.symm 0 →
      ∃ (a : Fˣ) (σ : F ≃+* F), ∀ x : F, e (g • e.symm x) = a * σ x := by
    intro g hg
    obtain ⟨g₀, rfl⟩ := hρsurj g
    rw [he0] at hg
    have hfix : tt u g₀ = 1 := (h.smulMo_one_eq_one_iff g₀).mp hg
    obtain ⟨a, σ, hσ⟩ := hsemi g₀ hfix
    refine ⟨a, σ, fun x => ?_⟩
    have h1 := hσ (e.symm x)
    rw [e.apply_symm_apply] at h1
    exact h1
  have hH2 : ∀ a : Fˣ, ∃ g : ↥G, g • e.symm 0 = e.symm 0 ∧ ∀ x : F, e (g • e.symm x) = a * x := by
    intro a
    obtain ⟨g₀, hfix, hg₀⟩ := hunits a
    refine ⟨ρ g₀, ?_, fun x => ?_⟩
    · rw [he0]
      exact (h.smulMo_one_eq_one_iff g₀).mpr hfix
    · have h1 := hg₀ (e.symm x)
      rw [e.apply_symm_apply] at h1
      exact h1
  rcases hHer ↥G ↥Mo n h.two_le F hcardF e h2 hH1 hH2 with ⟨N, hNn, hN⟩ | ⟨hn3, ⟨φ⟩⟩
  ·
    exfalso
    have hNcard : Nat.card N = 2 ^ n := by
      have hbij : Function.Bijective (fun m : N => (m : ↥G) • (1 : ↥Mo)) := by
        constructor
        · intro m₁ m₂ hm
          obtain ⟨m, _, hmu⟩ := hN 1 ((m₁ : ↥G) • 1)
          rw [hmu m₁ rfl, hmu m₂ hm.symm]
        · intro δ
          obtain ⟨m, hm, _⟩ := hN 1 δ
          exact ⟨m, hm⟩
      rw [Nat.card_congr (Equiv.ofBijective _ hbij), h.card_Mo]
    have hN2 : IsPGroup 2 N := IsPGroup.of_card hNcard
    have hV2 : IsPGroup 2 (V.subgroupOf M) := IsPGroup.of_card (n := 2 * n + 1) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le).toEquiv, h.card_V])
    have hkerle : ρ.ker ≤ V.subgroupOf M := fun g hg => (hker g).mp hg
    have hker2 : IsPGroup 2 ρ.ker := hV2.to_le hkerle
    have hNc2 : IsPGroup 2 (N.comap ρ) := hN2.comap_of_ker_isPGroup ρ hker2
    let Nt : Subgroup X := (N.comap ρ).map M.subtype
    have hNt2 : IsPGroup 2 Nt := hNc2.map M.subtype
    have hNtM : Nt ≤ M := Subgroup.map_subtype_le _
    have hNtn : ∀ g ∈ M, ∀ x ∈ Nt, g * x * g⁻¹ ∈ Nt := by
      intro g hg x hx
      obtain ⟨x', hx', rfl⟩ := hx
      refine ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      show ρ (⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNn.conj_mem _ hx' (ρ ⟨g, hg⟩)
    have hNtV : Nt ≤ V := h.V_max Nt hNtM hNtn hNt2
    have hNbot : ∀ m : ↥G, m ∈ N → m = 1 := by
      intro m hm
      obtain ⟨g, rfl⟩ := hρsurj m
      have hgNt : (g : X) ∈ Nt := ⟨g, hm, rfl⟩
      exact (hker g).mpr (hNtV hgNt)
    obtain ⟨y, hy⟩ : ∃ y : ↥Mo, y ≠ 1 := by
      have h1 : 1 < Nat.card ↥Mo := by
        rw [h.card_Mo]
        exact Nat.one_lt_two_pow (by have := h.two_le; omega)
      have := Finite.one_lt_card_iff_nontrivial.mp h1
      exact exists_ne (1 : ↥Mo)
    obtain ⟨m, hm, _⟩ := hN 1 y
    have hm1 : (m : ↥G) = 1 := hNbot m m.2
    rw [hm1, one_smul] at hm
    exact hy hm.symm
  ·
    refine ⟨hn3, ?_⟩
    let R' : Subgroup ↥M := R₀.subgroupOf M
    have hR'n : R'.Normal := ⟨fun x hx g => h.R₀_norm g g.2 x hx⟩
    let ρ' : ↥M →* Section15GL32.GL32 := φ.toMonoidHom.comp ρ
    have hker' : ∀ g : ↥M, ρ' g = 1 ↔ (g : X) ∈ V := by
      intro g
      rw [← hker g]
      exact map_eq_one_iff φ φ.injective
    have hR'le : R' ≤ ρ'.ker := fun g hg => (hker' g).mpr (h.R₀_le hg)
    let ρE : (↥M ⧸ R') →* Section15GL32.GL32 := QuotientGroup.lift R' ρ' hR'le
    have hρ'surj : Function.Surjective ρ' := φ.surjective.comp hρsurj
    have hρEsurj : Function.Surjective ρE := by
      intro y
      obtain ⟨g, hg⟩ := hρ'surj y
      exact ⟨QuotientGroup.mk g, hg⟩
    let z : ↥M ⧸ R' := QuotientGroup.mk ⟨u, h.u_mem_M⟩
    have hz1 : z ≠ 1 := by
      intro h1
      have h2 : (⟨u, h.u_mem_M⟩ : ↥M) ∈ R' := (QuotientGroup.eq_one_iff _).mp h1
      exact h.u_not_mem h2
    have hzρ : ρE z = 1 := (hker' ⟨u, h.u_mem_M⟩).mpr h.u_mem
    have hkerz : ∀ x : ↥M ⧸ R', ρE x = 1 → x = 1 ∨ x = z := by
      intro x hx
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have hgV : (g : X) ∈ V := (hker' g).mp hx
      by_cases hgR : (g : X) ∈ R₀
      · left
        exact (QuotientGroup.eq_one_iff g).mpr hgR
      · right
        apply QuotientGroup.eq.mpr
        have h1 : u * (g : X) ∈ R₀ := h.u_mul_mem hgV hgR
        have h2 : (g : X)⁻¹ * u = (u * (g : X))⁻¹ := by rw [mul_inv_rev, h.u_inv_eq]
        show (g : X)⁻¹ * u ∈ R₀
        rw [h2]
        exact R₀.inv_mem h1
    have hgen : ∀ T : (↥M ⧸ R') →* Multiplicative (ZMod 2),
        (∀ y, Odd (orderOf y) → T y = 1) → ∀ x, T x = 1 := by
      intro T hT x
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
      let T' : ↥M →* Multiplicative (ZMod 2) := T.comp (QuotientGroup.mk' R')
      have hodd' : ∀ y : ↥M, Odd (orderOf y) → T' y = 1 := fun y hy => by
        refine hT _ ?_
        exact Odd.of_dvd_nat hy (orderOf_map_dvd (QuotientGroup.mk' R') y)
      have hsub : {y : X | y ∈ M ∧ Odd (orderOf y)} ⊆ (T'.ker).map M.subtype := by
        rintro y ⟨hyM, hyodd⟩
        refine ⟨⟨y, hyM⟩, ?_, rfl⟩
        exact hodd' ⟨y, hyM⟩ (by rwa [Subgroup.orderOf_mk])
      have hclos : Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)} ≤
          (T'.ker).map M.subtype := (Subgroup.closure_le _).mpr hsub
      obtain ⟨x₁, hx₁, hx₁eq⟩ := hclos ((le_of_eq h.oddGen.symm) x₀.2)
      have hx₁x₀ : x₁ = x₀ := Subtype.ext hx₁eq
      subst hx₁x₀
      exact hx₁
    obtain ⟨x, hx⟩ := Section15GL32.exists_sq_eq_of_gl32 ρE hρEsurj hz1 hzρ hkerz hgen
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
    have hx' : (QuotientGroup.mk (x₀ * x₀) : ↥M ⧸ R') = QuotientGroup.mk ⟨u, h.u_mem_M⟩ := by
      rw [QuotientGroup.mk_mul]
      exact hx
    have hq := QuotientGroup.eq.mp hx'
    have hr : ((x₀ : X) * x₀)⁻¹ * u ∈ R₀ := hq
    have e1 : ∀ a v : X, a = v * (a⁻¹ * v)⁻¹ := fun a v => by group
    have e2 : ∀ a v : X, v = a * (a⁻¹ * v) := fun a v => by group
    refine ⟨(x₀ : X), x₀.2, ?_, ?_⟩
    · rw [e1 ((x₀ : X) * x₀) u]
      exact V.mul_mem h.u_mem (h.R₀_le (R₀.inv_mem hr))
    · intro hxR
      apply h.u_not_mem
      rw [e2 ((x₀ : X) * x₀) u]
      exact R₀.mul_mem hxR hr

end Section15Last

open Section15Last

theorem heringFinal :
    ∀ {X : Type} [Group X] [Finite X] (M V R₀ Mo D K : Subgroup X) (u : X) (n : ℕ),
      2 ≤ n → Mo ≤ R₀ → R₀ ≤ V → V ≤ M → D ≤ M → K ≤ D →
      (∀ g ∈ M, ∀ x ∈ V, g * x * g⁻¹ ∈ V) → (∀ g ∈ M, ∀ x ∈ R₀, g * x * g⁻¹ ∈ R₀) →
      (∀ g ∈ M, ∀ x ∈ Mo, g * x * g⁻¹ ∈ Mo) → (∀ d ∈ D, ∀ k ∈ K, d * k * d⁻¹ ∈ K) →
      Nat.card Mo = 2 ^ n → Nat.card R₀ = 2 ^ (2 * n) → Nat.card V = 2 ^ (2 * n + 1) →
      Nat.card K = 2 ^ n - 1 → Nat.card M = 2 ^ (3 * n) * Nat.card D →
      (∀ x ∈ Mo, x * x = 1) → (∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a) → (∀ x ∈ R₀, x * x ∈ Mo) →
      (∀ x ∈ R₀, x ∉ Mo → x * x ≠ 1) →
      u ∈ V → u ∉ R₀ → u * u = 1 → (∀ x ∈ R₀, u * x * u⁻¹ = x⁻¹) →
      (∀ x ∈ V, x ∉ R₀ → ∃ g ∈ M, g * u * g⁻¹ = x) →
      (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) →
      (∀ a ∈ Mo, a ≠ 1 → ∀ b ∈ Mo, b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b) →
      (∀ k ∈ K, k ≠ 1 → ∀ x ∈ Mo, k * x = x * k → x = 1) →
      (∀ d ∈ D, d * u = u * d) → (∀ d ∈ D, d ∈ V → d = 1 ∨ d = u) →
      (∀ g ∈ M, (∀ x ∈ Mo, g * x = x * g) → g ∈ V) →
      (∀ N : Subgroup X, N ≤ M → (∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → IsPGroup 2 N → N ≤ V) →
      closure {y : X | y ∈ M ∧ Odd (orderOf y)} = M →
      Hering32Stmt →
      n = 3 ∧ ∃ x ∈ M, x * x ∈ V ∧ x * x ∉ R₀ := by
  intro X _ _ M V R₀ Mo D K u n h2n hMoR hRV hVM hDM hKD hVn hRn hMon hKn hcMo hcR hcV hcK hcM
    hMosq hRcomm hRsq hRsqne huV huR husq huinv hVconj hKcomm hKtrans hKfpf hDu hDV hCMo hVmax
    hodd hHer
  exact final_main ⟨h2n, hMoR, hRV, hVM, hDM, hKD, hVn, hRn, hMon, hKn, hcMo, hcR, hcV, hcK, hcM,
    hMosq, hRcomm, hRsq, hRsqne, huV, huR, husq, huinv, hVconj, hKcomm, hKtrans, hKfpf, hDu, hDV,
    hCMo, hVmax, hodd⟩ hHer

end CFSG.GH74.Uniqueness
