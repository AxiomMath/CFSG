module

public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2KeyPSL

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped MatrixGroups commutatorElement

section CrossAbstract

variable {G : Type} [Group G] [Finite G]

theorem fixed_of_closure_eq {H : Subgroup G} (hHab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (α : MulAut G) {Y : Subgroup G} (hYH : Y ≤ H) (hYα : ∀ y ∈ Y, α y ∈ Y)
    (hYc : Subgroup.closure {y : G | ∃ x ∈ Y, y = x * (α x)⁻¹} = Y) :
    ∀ x ∈ Y, α x = x → x = 1 := by
  classical
  let S : Subgroup G :=
    { carrier := {y : G | ∃ x ∈ Y, y = x * (α x)⁻¹}
      one_mem' := ⟨1, Y.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
        refine ⟨x * x', Y.mul_mem hx hx', ?_⟩
        have h1 : (α x)⁻¹ * x' = x' * (α x)⁻¹ := by
          have := hHab x' (hYH hx') (α x)⁻¹ (H.inv_mem (hYH (hYα x hx)))
          exact this.symm
        calc x * (α x)⁻¹ * (x' * (α x')⁻¹) = x * ((α x)⁻¹ * x') * (α x')⁻¹ := by group
          _ = x * (x' * (α x)⁻¹) * (α x')⁻¹ := by rw [h1]
          _ = x * x' * ((α x)⁻¹ * (α x')⁻¹) := by group
          _ = x * x' * (α (x * x'))⁻¹ := by
            rw [map_mul, mul_inv_rev]
            have h2 : (α x')⁻¹ * (α x)⁻¹ = (α x)⁻¹ * (α x')⁻¹ :=
              hHab _ (H.inv_mem (hYH (hYα x' hx'))) _ (H.inv_mem (hYH (hYα x hx)))
            rw [h2]
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨x⁻¹, Y.inv_mem hx, ?_⟩
        have h1 : x⁻¹ * α x = α x * x⁻¹ := hHab _ (H.inv_mem (hYH hx)) _ (hYH (hYα x hx))
        rw [map_inv, inv_inv, mul_inv_rev, inv_inv, h1] }
  have hS : (S : Set G) = (Y : Set G) := by
    have : Subgroup.closure (S : Set G) = S := Subgroup.closure_eq S
    have h2 : Subgroup.closure {y : G | ∃ x ∈ Y, y = x * (α x)⁻¹} = S := this
    rw [hYc] at h2
    rw [← h2]
  have hsurj : ∀ y ∈ Y, ∃ x ∈ Y, y = x * (α x)⁻¹ := by
    intro y hy
    have : y ∈ (S : Set G) := by rw [hS]; exact hy
    exact this
  let f : Y → Y := fun x => ⟨x * (α x)⁻¹, Y.mul_mem x.2 (Y.inv_mem (hYα x x.2))⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hsurj y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy.symm⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hf
  intro x hx hαx
  have h1 : f ⟨x, hx⟩ = f 1 := by
    apply Subtype.ext
    simp [f, hαx]
  have := hinj h1
  exact congrArg Subtype.val this

theorem card_le_two_mul_inf {H C : Subgroup G} {w : G} (hN : ∀ g ∈ C, g ∈ H ∨ w⁻¹ * g ∈ H) :
    Nat.card C ≤ 2 * Nat.card ↥(C ⊓ H) := by
  classical
  by_cases hall : ∀ g ∈ C, g ∈ H
  · have : C ⊓ H = C := inf_eq_left.mpr hall
    rw [this]; omega
  · push Not at hall
    obtain ⟨c₀, hc₀C, hc₀H⟩ := hall
    have hc₀ : w⁻¹ * c₀ ∈ H := (hN c₀ hc₀C).resolve_left hc₀H
    have hmem : ∀ g : C, (g : G) ∉ H → c₀⁻¹ * (g : G) ∈ C ⊓ H := by
      intro g hg
      refine ⟨C.mul_mem (C.inv_mem hc₀C) g.2, ?_⟩
      have h1 : w⁻¹ * (g : G) ∈ H := (hN g g.2).resolve_left hg
      have := H.mul_mem (H.inv_mem hc₀) h1
      simpa [mul_assoc] using this
    let f : C → ↥(C ⊓ H) × Bool := fun g =>
      if hg : (g : G) ∈ H then (⟨g, g.2, hg⟩, false) else (⟨c₀⁻¹ * g, hmem g hg⟩, true)
    have hf : Function.Injective f := by
      intro g g' h
      by_cases hg : (g : G) ∈ H <;> by_cases hg' : (g' : G) ∈ H
      · simp only [f, hg, hg', dite_true] at h
        exact Subtype.ext (congrArg (fun z : ↥(C ⊓ H) × Bool => (z.1 : G)) h)
      · simp only [f, hg, hg', dite_true, dite_false] at h
        exact absurd (congrArg Prod.snd h) (by simp)
      · simp only [f, hg, hg', dite_true, dite_false] at h
        exact absurd (congrArg Prod.snd h) (by simp)
      · simp only [f, hg, hg', dite_false] at h
        have := congrArg (fun z : ↥(C ⊓ H) × Bool => (z.1 : G)) h
        simp only at this
        exact Subtype.ext (mul_left_cancel this)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega

omit [Finite G] in
theorem mul_map_injective {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (hAB : ∀ x, x ∈ A → x ∈ B → x = 1) :
    Function.Injective
      (fun ab : A × B => (⟨(ab.1 : G) * ab.2, H.mul_mem (hA ab.1.2) (hB ab.2.2)⟩ : H)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
  have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
    calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
      _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
      _ = b' * (b : G)⁻¹ := by group
  have hmemA : (a' : G)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem a'.2) a.2
  have hmemB : (a' : G)⁻¹ * a ∈ B := by rw [h2]; exact B.mul_mem b'.2 (B.inv_mem b.2)
  have h3 := hAB _ hmemA hmemB
  have h4 : (a : G) = a' := by
    have : (a' : G)⁻¹ * a = 1 := h3
    exact (inv_mul_eq_one.mp this).symm
  have h5 : (b : G) = b' := by
    rw [h4] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)

theorem card_mul_le_of_inf_trivial {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (hAB : ∀ x, x ∈ A → x ∈ B → x = 1) : Nat.card A * Nat.card B ≤ Nat.card H := by
  have := Nat.card_le_card_of_injective _ (mul_map_injective hA hB hAB)
  rwa [Nat.card_prod] at this

theorem exists_mul_of_card_le {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (hAB : ∀ x, x ∈ A → x ∈ B → x = 1) (hcard : Nat.card H ≤ Nat.card A * Nat.card B) :
    ∀ h ∈ H, ∃ a ∈ A, ∃ b ∈ B, h = a * b := by
  intro h hh
  have hbij := (mul_map_injective hA hB hAB).bijective_of_nat_card_le
    (by rw [Nat.card_prod]; exact hcard)
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨h, hh⟩
  exact ⟨a, a.2, b, b.2, (congrArg Subtype.val hab).symm⟩

theorem cross_abstract {H : Subgroup G} (hH : L48.IsTorus H) (α : MulAut G)
    {Y : Subgroup G} (hYH : Y ≤ H) (hYα : ∀ y ∈ Y, α y ∈ Y)
    (hYc : Subgroup.closure {y : G | ∃ x ∈ Y, y = x * (α x)⁻¹} = Y)
    {C : Subgroup G} (hCN : C ≤ normalizer (H : Set G)) (hCfix : ∀ c ∈ C, α c = c) :
    Nat.card C * Nat.card Y ≤ 2 * Nat.card H := by
  obtain ⟨w, hw, hw2, hinv, hNw⟩ := hH.exists_inv
  have hfixY := fixed_of_closure_eq hH.comm α hYH hYα hYc
  let H₁ : Subgroup G := H ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id G)
  have h1 : Nat.card H₁ * Nat.card Y ≤ Nat.card H :=
    card_mul_le_of_inf_trivial inf_le_left hYH (fun x hxH₁ hxY => hfixY x hxY hxH₁.2)
  have hCH : C ⊓ H ≤ H₁ := fun x hx => ⟨hx.2, hCfix x hx.1⟩
  have h2 : Nat.card ↥(C ⊓ H) ≤ Nat.card H₁ :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hCH) (Subgroup.inclusion_injective hCH)
  have h3 : Nat.card C ≤ 2 * Nat.card ↥(C ⊓ H) :=
    card_le_two_mul_inf (fun g hg => (hNw g).mp (hCN hg))
  calc Nat.card C * Nat.card Y ≤ 2 * Nat.card ↥(C ⊓ H) * Nat.card Y := Nat.mul_le_mul_right _ h3
    _ ≤ 2 * Nat.card H₁ * Nat.card Y := by gcongr
    _ = 2 * (Nat.card H₁ * Nat.card Y) := by ring
    _ ≤ 2 * Nat.card H := by gcongr

end CrossAbstract

section CrossPSL

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem fl2_cross (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F) (Y : Subgroup K) (hY : IsPGroup p ↥Y)
    (hY1 : Y ≠ ⊥) (hYα : ∀ y ∈ Y, α y ∈ Y)
    (hYc : Subgroup.closure {y : K | ∃ x ∈ Y, y = x * (α x)⁻¹} = Y) (C : Subgroup K)
    (hCfix : ∀ c ∈ C, α c = c) (hCN : ∀ c ∈ C, c ∈ normalizer (Y : Set K)) :
    Nat.card ↥C * Nat.card ↥Y ≤ Nat.card F + 1 ∧
      (Nat.card ↥C * Nat.card ↥Y = Nat.card F + 1 →
        ∀ n ∈ normalizer (Y : Set K), ∃ y ∈ Y, ∃ c ∈ C, n = y * c) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hodd := hF.1
  have hF2 : ringChar F ≠ 2 := by
    intro h
    have h1 := FiniteField.even_card_of_char_two h
    rw [← Nat.card_eq_fintype_card] at h1
    obtain ⟨k, hk⟩ := hodd
    omega
  have hq5 : 5 ≤ Fintype.card F := by
    have h3 := hF.2
    obtain ⟨k, hk⟩ := hodd
    omega
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  let φ : K ≃* PSL(2, F) := toPSL e
  obtain ⟨y₀, hy₀Y, hy₀Z, hy₀1, hord⟩ : ∃ y₀ ∈ Y, (∀ y ∈ Y, y * y₀ = y₀ * y) ∧ y₀ ≠ 1 ∧
      ∀ n : ℕ, p.Coprime n → (orderOf y₀).Coprime n := by
    have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY1
    have := hY.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center Y)
    refine ⟨((z : Y) : K), (z : Y).2, fun y hy => ?_, fun h => hz1 ?_, fun n hn => ?_⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    · apply Subtype.ext
      apply Subtype.ext
      simpa using h
    · rw [Subgroup.orderOf_coe]
      exact hY.orderOf_coprime hn _
  have hpc2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hpcq : p.Coprime (Fintype.card F) := by
    rw [← hcardF]; exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have hy₀2 : y₀ * y₀ ≠ 1 := by
    intro h
    have h1 : orderOf y₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    exact hy₀1 (orderOf_eq_one_iff.mp ((hord 2 hpc2).eq_one_of_dvd h1))
  have hφy₀1 : φ y₀ ≠ 1 := fun h => hy₀1 (φ.injective (by rw [h, map_one]))
  have hφy₀P : φ y₀ ∉ PSL2Table.conjSet (PSL2Table.unipotent F) := by
    intro h
    have h1 := PSL2Table.orderOf_dvd_of_mem_conjSet h
    rw [PSL2Table.card_unipotent h2] at h1
    have h3 : orderOf (φ y₀) = orderOf y₀ := MulEquiv.orderOf_eq φ y₀
    rw [h3] at h1
    exact hy₀1 (orderOf_eq_one_iff.mp ((hord _ hpcq).eq_one_of_dvd h1))
  obtain ⟨H₀', hH₀', hy₀H', hcard₀⟩ := L48.exists_torus_of_not_conjSet hF2 hq5 hφy₀1 hφy₀P
  let H₀ : Subgroup K := H₀'.map φ.symm.toMonoidHom
  have hH₀ : L48.IsTorus H₀ := hH₀'.map_equiv φ.symm
  have hy₀H : y₀ ∈ H₀ := by
    refine ⟨φ y₀, hy₀H', ?_⟩
    simp
  have hcardH₀ : Nat.card H₀ = Nat.card H₀' := Subgroup.card_map_of_injective φ.symm.injective
  have hYH₀ : Y ≤ H₀ := fun y hy =>
    hH₀.centralizer_le hy₀H hy₀2 (mem_centralizer_singleton_iff.mpr (hy₀Z y hy))
  have hαy₀ : α y₀ ∈ H₀ := hYH₀ (hYα y₀ hy₀Y)
  have hαy₀2 : α y₀ * α y₀ ≠ 1 := by
    intro h
    apply hy₀2
    apply α.injective
    rw [map_mul, h, map_one]
  have hαH : ∀ x ∈ H₀, α x ∈ H₀ := by
    intro x hx
    refine hH₀.centralizer_le hαy₀ hαy₀2 (mem_centralizer_singleton_iff.mpr ?_)
    rw [← map_mul, ← map_mul, hH₀.comm x hx y₀ hy₀H]
  have hCle : C ≤ normalizer (H₀ : Set K) := by
    intro c hc
    have hcY : c * y₀ * c⁻¹ ∈ Y := (mem_normalizer_iff.mp (hCN c hc) y₀).mp hy₀Y
    exact hH₀.ti y₀ hy₀H hy₀1 c (hYH₀ hcY)
  have key := cross_abstract hH₀ α hYH₀ hYα hYc hCle hCfix
  have hT := PSL2Table.card_splitTorus h2 (F := F)
  have hq' : Fintype.card F = 2 * Nat.card (PSL2Table.splitTorus F) + 1 := by
    have := Fintype.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hodd
    omega
  have hH₀le : 2 * Nat.card H₀ ≤ Nat.card F + 1 := by
    have : Nat.card H₀ ≤ Nat.card (PSL2Table.splitTorus F) + 1 := by
      rw [hcardH₀]; omega
    omega
  refine ⟨by omega, fun hext n hn => ?_⟩
  have hNY : ∀ g ∈ normalizer (Y : Set K), g ∈ normalizer (H₀ : Set K) := by
    intro g hg
    have hgY : g * y₀ * g⁻¹ ∈ Y := (mem_normalizer_iff.mp hg y₀).mp hy₀Y
    exact hH₀.ti y₀ hy₀H hy₀1 g (hYH₀ hgY)
  obtain ⟨w, hw, hw2, hinv, hNw⟩ := hH₀.exists_inv
  set N : Subgroup K := normalizer (Y : Set K) with hN
  have hcardN : Nat.card N ≤ 2 * Nat.card H₀ := by
    have h3 : Nat.card N ≤ 2 * Nat.card ↥(N ⊓ H₀) :=
      card_le_two_mul_inf (fun g hg => (hNw g).mp (hNY g hg))
    have h4 : Nat.card ↥(N ⊓ H₀) ≤ Nat.card H₀ :=
      Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_right)
        (Subgroup.inclusion_injective _)
    omega
  have hYN : Y ≤ N := Subgroup.le_normalizer
  have hCN' : C ≤ N := fun c hc => hCN c hc
  have hfixY := fixed_of_closure_eq hH₀.comm α hYH₀ hYα hYc
  have hext' : Nat.card N ≤ Nat.card Y * Nat.card C := by
    rw [Nat.mul_comm]
    omega
  exact exists_mul_of_card_le hYN hCN' (fun x hxY hxC => hfixY x hxY (hCfix x hxC)) hext' n hn

end CrossPSL

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
