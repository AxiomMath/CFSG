module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

instance normal_D_subgroupOf : (d.D.subgroupOf (d.D ⊔ d.leviShort)).Normal :=
  (normal_subgroupOf_iff_le_normalizer le_sup_left).2
    (sup_le le_normalizer d.leviShort_le_normalizer_D)

@[expose] noncomputable def leviQuotHom :
    d.leviShort →* (d.D ⊔ d.leviShort : Subgroup X) ⧸ d.D.subgroupOf (d.D ⊔ d.leviShort) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)

theorem leviQuotHom_bijective : Function.Bijective d.leviQuotHom := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, leviQuotHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf] at hs
    have h1 : (s : X) ∈ d.D ⊓ d.leviShort := Subgroup.mem_inf.2 ⟨hs, s.2⟩
    rw [d.D_inf_leviShort, mem_bot] at h1
    exact mem_bot.2 (Subtype.ext h1)
  · intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨n, hn, s, hs, hg⟩ := d.exists_mul_of_mem_D_sup_leviShort g.2
      refine ⟨⟨s, hs⟩, ?_⟩
      rw [leviQuotHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      rw [mem_subgroupOf]
      change ((s : X))⁻¹ * g ∈ d.D
      rw [hg, show (s : X)⁻¹ * (n * s) = s⁻¹ * n * s by group]
      have := (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D (inv_mem hs)) n).1 hn
      rwa [inv_inv] at this

@[expose] noncomputable def leviQuot :
    d.leviShort ≃* (d.D ⊔ d.leviShort : Subgroup X) ⧸ d.D.subgroupOf (d.D ⊔ d.leviShort) :=
  MulEquiv.ofBijective d.leviQuotHom d.leviQuotHom_bijective

theorem leviQuot_apply (s : d.leviShort) :
    d.leviQuot s = QuotientGroup.mk (Subgroup.inclusion le_sup_right s) :=
  rfl

theorem x₁_conj_x₁ (a b : d.Γ) : d.x₁ a * d.x₁ b * (d.x₁ a)⁻¹ = d.x₁ b := by
  rw [(commute_of_add d.x₁_add a b).eq, mul_inv_cancel_right]

theorem exists_conj_eq_of_trivial_on_borel (α : d.leviShort →* d.leviShort)
    (hα : Function.Injective α)
    (hU : ∀ a : d.Γ, ((α ⟨d.x₁ a, d.x₁_mem_leviShort a⟩ : d.leviShort) : X) ∈ d.U₁)
    (hJ : ∀ j (hj : j ∈ d.J₆),
      ((α ⟨j, d.J₆_le_leviShort hj⟩ : d.leviShort) : X) * j⁻¹ ∈ d.U₁) :
    ∃ s ∈ d.leviShort, ∀ y (hy : y ∈ d.leviShort), s * (α ⟨y, hy⟩ : X) * s⁻¹ = y := by
  classical
  have hJ6 : ∀ μ : d.Γˣ, d.hBCD μ ∈ d.J₆ := fun μ => by
    rw [d.J₆_eq_range_hBCD]
    exact ⟨μ, rfl⟩
  have hU' : ∀ a : d.Γ, ∃ b, d.x₁ b = ((α ⟨d.x₁ a, d.x₁_mem_leviShort a⟩ : d.leviShort) : X) :=
    fun a => hU a
  choose ψ hψ using hU'
  obtain ⟨γ₀, hγ₀⟩ := IsCyclic.exists_generator (α := d.Γˣ)
  have hγ₀1 : (γ₀ : d.Γ) ^ 2 ≠ 1 := by
    intro h1
    have hγ : γ₀ = 1 := d.units_eq_one_of_sq (Units.ext (by
      rw [Units.val_pow_eq_pow_val, h1, Units.val_one]))
    obtain ⟨m, hm⟩ := d.exists_units_ne_one
    obtain ⟨k, hk⟩ := hγ₀ m
    have hk' : (1 : d.Γˣ) ^ k = m := by rw [← hγ]; exact hk
    rw [one_zpow] at hk'
    exact hm hk'.symm
  have hμ₀ : (γ₀ : d.Γ) ^ 2 + 1 ≠ 0 := by
    intro h0
    apply hγ₀1
    have := congrArg (· + 1) h0
    simpa [add_assoc, CharTwo.add_self_eq_zero] using this
  set j₀ := d.hBCD γ₀ with hj₀
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, ((α ⟨j₀, d.J₆_le_leviShort (hJ6 γ₀)⟩ : d.leviShort) : X) =
      d.x₁ w₀ * j₀ := by
    obtain ⟨w₀, hw₀⟩ := hJ j₀ (hJ6 γ₀)
    exact ⟨w₀, by rw [hw₀, inv_mul_cancel_right]⟩
  set b := w₀ / ((γ₀ : d.Γ) ^ 2 + 1) with hb
  have hbJ : d.x₁ b * (d.x₁ w₀ * j₀) * (d.x₁ b)⁻¹ = j₀ := by
    have e1 : j₀ * (d.x₁ b)⁻¹ * j₀⁻¹ = d.x₁ ((γ₀ : d.Γ) ^ 2 * b) := by
      rw [d.x₁_inv, hj₀, d.hBCD_conj_x₁]
    calc d.x₁ b * (d.x₁ w₀ * j₀) * (d.x₁ b)⁻¹ =
        d.x₁ b * d.x₁ w₀ * (j₀ * (d.x₁ b)⁻¹ * j₀⁻¹) * j₀ := by group
      _ = j₀ := by
        rw [e1, ← d.x₁_add, ← d.x₁_add]
        have h1 : ((γ₀ : d.Γ) ^ 2 + 1) * b = w₀ := by
          rw [hb]
          field_simp
        have : b + w₀ + (γ₀ : d.Γ) ^ 2 * b = 0 := by
          rw [show b + w₀ + (γ₀ : d.Γ) ^ 2 * b = ((γ₀ : d.Γ) ^ 2 + 1) * b + w₀ by ring, h1,
            CharTwo.add_self_eq_zero]
        rw [this, d.x₁_zero, one_mul]
  set β : d.leviShort →* d.leviShort :=
    (MulAut.conj (⟨d.x₁ b, d.x₁_mem_leviShort b⟩ : d.leviShort)).toMonoidHom.comp α with hβdef
  have hβapply : ∀ y (hy : y ∈ d.leviShort), ((β ⟨y, hy⟩ : d.leviShort) : X) =
      d.x₁ b * (α ⟨y, hy⟩ : X) * (d.x₁ b)⁻¹ := fun _ _ => rfl
  have hβinj : Function.Injective β := (MulAut.conj _).injective.comp hα
  have hβj₀ : β ⟨j₀, d.J₆_le_leviShort (hJ6 γ₀)⟩ = ⟨j₀, d.J₆_le_leviShort (hJ6 γ₀)⟩ :=
    Subtype.ext (by rw [hβapply, hw₀, hbJ])
  have hβJ : ∀ j (hj : j ∈ d.J₆), ((β ⟨j, d.J₆_le_leviShort hj⟩ : d.leviShort) : X) = j := by
    intro j hj
    have hj' := hj
    rw [d.J₆_eq_range_hBCD] at hj'
    obtain ⟨μ, rfl⟩ := hj'
    obtain ⟨k, hk⟩ := hγ₀ μ
    have hk' : γ₀ ^ k = μ := hk
    have e : (⟨d.hBCD μ, d.J₆_le_leviShort hj⟩ : d.leviShort) =
        (⟨j₀, d.J₆_le_leviShort (hJ6 γ₀)⟩ : d.leviShort) ^ k := Subtype.ext (by
      rw [SubgroupClass.coe_zpow]
      change d.hBCD μ = j₀ ^ k
      rw [hj₀, ← map_zpow, hk'])
    rw [e, map_zpow, hβj₀, SubgroupClass.coe_zpow]
    change j₀ ^ k = d.hBCD μ
    rw [hj₀, ← map_zpow, hk']
  have hβU : ∀ a, ((β ⟨d.x₁ a, d.x₁_mem_leviShort a⟩ : d.leviShort) : X) = d.x₁ (ψ a) := by
    intro a
    rw [hβapply, ← hψ, d.x₁_conj_x₁]
  have hψμ : ∀ (μ : d.Γˣ) (a : d.Γ), ψ ((μ : d.Γ) * a) = μ * ψ a := by
    intro μ a
    obtain ⟨β', hβ'⟩ := d.sq_surjective_units μ
    have hh := hJ6 β'
    have e3 : (⟨d.x₁ ((μ : d.Γ) * a), d.x₁_mem_leviShort _⟩ : d.leviShort) =
        ⟨d.hBCD β', d.J₆_le_leviShort hh⟩ * ⟨d.x₁ a, d.x₁_mem_leviShort a⟩ *
          (⟨d.hBCD β', d.J₆_le_leviShort hh⟩ : d.leviShort)⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      change d.x₁ ((μ : d.Γ) * a) = d.hBCD β' * d.x₁ a * (d.hBCD β')⁻¹
      rw [d.hBCD_conj_x₁, ← hβ', Units.val_pow_eq_pow_val])
    have e4 := congrArg (fun y => ((β y : d.leviShort) : X)) e3
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at e4
    rw [hβU, hβU, hβJ _ hh, d.hBCD_conj_x₁, ← Units.val_pow_eq_pow_val, hβ'] at e4
    exact d.x₁_injective e4
  have hψ0 : ψ 0 = 0 := by
    have h1 := hβU 0
    rw [show (⟨d.x₁ 0, d.x₁_mem_leviShort 0⟩ : d.leviShort) = 1 from Subtype.ext d.x₁_zero,
      map_one] at h1
    exact d.x₁_injective (h1.symm.trans d.x₁_zero.symm)
  set c := ψ 1 with hcdef
  have hψlin : ∀ a, ψ a = a * c := by
    intro a
    by_cases ha : a = 0
    · rw [ha, hψ0, zero_mul]
    · have h1 := hψμ (Units.mk0 a ha) 1
      rw [Units.val_mk0, mul_one] at h1
      exact h1
  have hc : c ≠ 0 := by
    intro hc0
    have h1 := hβU 1
    rw [hψlin, hc0, mul_zero, d.x₁_zero] at h1
    have h2 : β ⟨d.x₁ 1, d.x₁_mem_leviShort 1⟩ = β 1 := Subtype.ext (by rw [h1, map_one]; rfl)
    have h3 := congrArg Subtype.val (hβinj h2)
    exact one_ne_zero (d.x₁_injective (h3.trans d.x₁_zero.symm))
  obtain ⟨β₁, hβ₁⟩ := d.sq_surjective_units (Units.mk0 c hc)⁻¹
  set j₁ := d.hBCD β₁ with hj₁
  set γ : d.leviShort →* d.leviShort :=
    (MulAut.conj (⟨j₁, d.J₆_le_leviShort (hJ6 β₁)⟩ : d.leviShort)).toMonoidHom.comp β
    with hγdef
  have hγapply : ∀ y (hy : y ∈ d.leviShort), ((γ ⟨y, hy⟩ : d.leviShort) : X) =
      j₁ * (β ⟨y, hy⟩ : X) * j₁⁻¹ := fun _ _ => rfl
  have hγU : ∀ a, ((γ ⟨d.x₁ a, d.x₁_mem_leviShort a⟩ : d.leviShort) : X) = d.x₁ a := by
    intro a
    rw [hγapply, hβU, hψlin, hj₁, d.hBCD_conj_x₁, ← Units.val_pow_eq_pow_val, hβ₁]
    congr 1
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
  have hγJ : ∀ j (hj : j ∈ d.J₆), ((γ ⟨j, d.J₆_le_leviShort hj⟩ : d.leviShort) : X) = j := by
    intro j hj
    rw [hγapply, hβJ j hj, d.J_commute (hJ6 β₁).1 hj.1, mul_inv_cancel_right]
  set g := ((γ ⟨d.u, d.u_mem_leviShort⟩ : d.leviShort) : X) with hgdef
  have hgL : g ∈ d.leviShort := (γ _).2
  have hinv : ∀ j (hj : j ∈ d.J₆), g * j * g⁻¹ = j⁻¹ := by
    intro j hj
    have e1 : (⟨d.u, d.u_mem_leviShort⟩ : d.leviShort) * ⟨j, d.J₆_le_leviShort hj⟩ *
        (⟨d.u, d.u_mem_leviShort⟩ : d.leviShort)⁻¹ =
          (⟨j, d.J₆_le_leviShort hj⟩ : d.leviShort)⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
      change d.u * j * d.u⁻¹ = j⁻¹
      rw [d.u_inv, d.u_conj_eq_inv_of_mem_J₆ hj])
    have e2 := congrArg (fun y => ((γ y : d.leviShort) : X)) e1
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at e2
    rw [hγJ j hj] at e2
    exact e2
  have hμ₀ne : ∀ a : d.Γ, (γ₀ : d.Γ) ^ 2 * a = a → a = 0 := by
    intro a ha
    have h1 : ((γ₀ : d.Γ) ^ 2 + 1) * a = 0 := by
      rw [add_mul, ha, one_mul, CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.1 h1).resolve_left hμ₀
  have hj₀x₁ : ∀ a, j₀ * d.x₁ a * j₀⁻¹ = d.x₁ ((γ₀ : d.Γ) ^ 2 * a) := fun a => by
    rw [hj₀, d.hBCD_conj_x₁]
  have hJU₁ : d.J ≤ normalizer (d.U₁ : Set X) := by
    rintro _ ⟨h, rfl⟩
    exact d.torus_mem_normalizer_U₁ h
  obtain ⟨h, hh, hgh⟩ : ∃ h ∈ d.J₆, g = h * d.u := by
    rcases d.mem_leviShort_iff.1 hgL with ⟨x, hx, h, hh, he⟩ | ⟨x, hx, h, hh, y, hy, he⟩
    · exfalso
      obtain ⟨a, rfl⟩ := hx
      have h1 := hinv j₀ (hJ6 γ₀)
      rw [he, show d.x₁ a * h * j₀ * (d.x₁ a * h)⁻¹ = d.x₁ a * (h * j₀ * h⁻¹) * (d.x₁ a)⁻¹ by
        group, d.J_commute hh.1 (hJ6 γ₀).1, mul_inv_cancel_right,
        show d.x₁ a * j₀ * (d.x₁ a)⁻¹ = d.x₁ a * (j₀ * (d.x₁ a)⁻¹ * j₀⁻¹) * j₀ by group,
        d.x₁_inv, hj₀x₁, ← d.x₁_add] at h1
      have h2 := (d.eq_of_mul_eq_mul_of_S_J (d.U₁_le_S (d.x₁_mem_U₁ _)) (one_mem _)
        (hJ6 γ₀).1 (inv_mem (hJ6 γ₀).1) (by rw [one_mul]; exact h1)).2
      have h3 : d.hBCD (γ₀ ^ 2) = 1 := by
        rw [map_pow, sq]
        nth_rewrite 1 [h2]
        exact inv_mul_cancel j₀
      have h4 := d.hBCD_injective (h3.trans (map_one _).symm)
      exact hγ₀1 (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one])
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨a', rfl⟩ := hy
      have h1 := hinv j₀ (hJ6 γ₀)
      have e1 : g * j₀ = j₀⁻¹ * g := by
        calc g * j₀ = g * j₀ * g⁻¹ * g := by group
          _ = j₀⁻¹ * g := by rw [h1]
      rw [he] at e1
      have hy' : j₀⁻¹ * d.x₁ a' * j₀ ∈ d.U₁ := by
        have := (mem_normalizer_iff.1 (hJU₁ (inv_mem (hJ6 γ₀).1))
          (d.x₁ a')).1 (d.x₁_mem_U₁ a')
        simpa using this
      have hx' : j₀⁻¹ * d.x₁ a * j₀ ∈ d.U₁ := by
        have := (mem_normalizer_iff.1 (hJU₁ (inv_mem (hJ6 γ₀).1))
          (d.x₁ a)).1 (d.x₁_mem_U₁ a)
        simpa using this
      have e2 : d.x₁ a * h * d.u * d.x₁ a' * j₀ =
          d.x₁ a * (h * j₀⁻¹) * d.u * (j₀⁻¹ * d.x₁ a' * j₀) := by
        have hu : d.u * j₀ = j₀⁻¹ * d.u := by
          have := d.u_conj_eq_inv_of_mem_J₆ (hJ6 γ₀)
          calc d.u * j₀ = d.u * j₀ * d.u * d.u := by rw [mul_assoc _ d.u d.u, d.u_mul_self,
                mul_one]
            _ = j₀⁻¹ * d.u := by rw [this]
        calc d.x₁ a * h * d.u * d.x₁ a' * j₀ =
            d.x₁ a * h * (d.u * j₀) * (j₀⁻¹ * d.x₁ a' * j₀) := by group
          _ = _ := by rw [hu]; group
      have e3 : j₀⁻¹ * (d.x₁ a * h * d.u * d.x₁ a') =
          (j₀⁻¹ * d.x₁ a * j₀) * (j₀⁻¹ * h) * d.u * d.x₁ a' := by group
      rw [e2, e3] at e1
      have hUu : ∀ {z}, z ∈ d.U₁ → z ∈ d.Uminus d.u := fun hz => by rw [d.Uminus_u]; exact hz
      obtain ⟨h5, -, -, h8⟩ := d.bruhat_normal_form_unique (d.U₁_le_S (d.x₁_mem_U₁ a))
        (mul_mem hh.1 (inv_mem (hJ6 γ₀).1)) d.u_mem_weyl (hUu hy') (d.U₁_le_S hx')
        (mul_mem (inv_mem (hJ6 γ₀).1) hh.1) d.u_mem_weyl (hUu (d.x₁_mem_U₁ a')) e1
      have ha : a = 0 := by
        apply hμ₀ne
        have h9 : j₀ * d.x₁ a * j₀⁻¹ = d.x₁ a := by
          calc j₀ * d.x₁ a * j₀⁻¹ = j₀ * (j₀⁻¹ * d.x₁ a * j₀) * j₀⁻¹ := by rw [← h5]
            _ = d.x₁ a := by group
        rw [hj₀x₁] at h9
        exact d.x₁_injective h9
      have ha' : a' = 0 := by
        apply hμ₀ne
        have h9 : j₀ * d.x₁ a' * j₀⁻¹ = d.x₁ a' := by
          calc j₀ * d.x₁ a' * j₀⁻¹ = j₀ * (j₀⁻¹ * d.x₁ a' * j₀) * j₀⁻¹ := by rw [h8]
            _ = d.x₁ a' := by group
        rw [hj₀x₁] at h9
        exact d.x₁_injective h9
      exact ⟨h, hh, by rw [he, ha, ha', d.x₁_zero, one_mul, mul_one]⟩
  have hgu : g = d.u := by
    have hrel : d.u * d.x₁ 1 * d.u ∈ d.leviShort :=
      mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort 1)) d.u_mem_leviShort
    rcases d.mem_leviShort_iff.1 hrel with ⟨x, hx, h₁, hh₁, he⟩ |
        ⟨x, hx, h₁, hh₁, y, hy, he⟩
    · exact absurd (he ▸ mul_mem (d.S_le_B (d.U₁_le_S hx)) (d.J_le_B hh₁.1))
        (d.u_x₁_u_not_mem_B one_ne_zero)
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    have e1 : (⟨d.u, d.u_mem_leviShort⟩ : d.leviShort) * ⟨d.x₁ 1, d.x₁_mem_leviShort 1⟩ *
        ⟨d.u, d.u_mem_leviShort⟩ = ⟨d.x₁ a, d.x₁_mem_leviShort a⟩ *
          ⟨h₁, d.J₆_le_leviShort hh₁⟩ * ⟨d.u, d.u_mem_leviShort⟩ *
            ⟨d.x₁ a', d.x₁_mem_leviShort a'⟩ := Subtype.ext he
    have e2 := congrArg (fun y => ((γ y : d.leviShort) : X)) e1
    simp only [map_mul, Subgroup.coe_mul] at e2
    rw [hγU, hγU, hγU, hγJ h₁ hh₁, ← hgdef, hgh] at e2
    have huh : d.u * h * d.u = h⁻¹ := d.u_conj_eq_inv_of_mem_J₆ hh
    have s3 : h * d.u * h = d.u := by
      calc h * d.u * h = h * (d.u * h * d.u) * d.u := by
            rw [show h * (d.u * h * d.u) * d.u = h * d.u * h * (d.u * d.u) by group,
              d.u_mul_self, mul_one]
        _ = d.u := by rw [huh, mul_inv_cancel, one_mul]
    have e3 : h * d.u * d.x₁ 1 * (h * d.u) =
        (h * d.x₁ a * h⁻¹) * (h * h₁ * h) * d.u * (h * d.x₁ a' * h⁻¹) := by
      have s1 : h * d.u * d.x₁ 1 * (h * d.u) = h * (d.u * d.x₁ 1 * d.u) * (d.u * h * d.u) := by
        rw [show h * (d.u * d.x₁ 1 * d.u) * (d.u * h * d.u) =
          h * d.u * d.x₁ 1 * (d.u * d.u) * h * d.u by group, d.u_mul_self]
        group
      have s2 : (h * d.x₁ a * h⁻¹) * (h * h₁ * h) * d.u * (h * d.x₁ a' * h⁻¹) =
          h * d.x₁ a * h₁ * (h * d.u * h) * d.x₁ a' * h⁻¹ := by group
      rw [s1, he, huh, s2, s3]
      group
    rw [e3, show d.x₁ a * h₁ * (h * d.u) * d.x₁ a' = d.x₁ a * (h₁ * h) * d.u * d.x₁ a' by
      group] at e2
    have hhx : ∀ z, h * d.x₁ z * h⁻¹ ∈ d.U₁ := fun z =>
      (mem_normalizer_iff.1 (hJU₁ hh.1) (d.x₁ z)).1 (d.x₁_mem_U₁ z)
    have hUu : ∀ {z}, z ∈ d.U₁ → z ∈ d.Uminus d.u := fun hz => by rw [d.Uminus_u]; exact hz
    obtain ⟨-, h6, -, -⟩ := d.bruhat_normal_form_unique (d.U₁_le_S (hhx a))
      (mul_mem (mul_mem hh.1 hh₁.1) hh.1) d.u_mem_weyl (hUu (hhx a'))
      (d.U₁_le_S (d.x₁_mem_U₁ a)) (mul_mem hh₁.1 hh.1) d.u_mem_weyl (hUu (d.x₁_mem_U₁ a')) e2
    have h7 : h = 1 := by
      have h8 : h * h₁ = h₁ := mul_right_cancel (h6 : h * h₁ * h = h₁ * h)
      exact mul_eq_right.1 h8
    rw [hgh, h7, one_mul]
  have hγid : ∀ y (hy : y ∈ d.leviShort), ((γ ⟨y, hy⟩ : d.leviShort) : X) = y := by
    have hE : closure ((d.U₁ : Set X) ∪ {d.u}) ≤
        (γ.eqLocus (MonoidHom.id _)).map d.leviShort.subtype := by
      rw [closure_le]
      rintro z (hz | hz)
      · obtain ⟨a, rfl⟩ := hz
        exact ⟨⟨d.x₁ a, d.x₁_mem_leviShort a⟩, Subtype.ext (hγU a), rfl⟩
      · rw [Set.mem_singleton_iff.1 hz]
        exact ⟨⟨d.u, d.u_mem_leviShort⟩, Subtype.ext hgu, rfl⟩
    intro y hy
    obtain ⟨y', hy', hyy⟩ := hE hy
    have h1 : γ y' = y' := hy'
    subst hyy
    show ((γ y' : d.leviShort) : X) = (y' : X)
    rw [h1]
  refine ⟨j₁ * d.x₁ b, mul_mem (d.J₆_le_leviShort (hJ6 β₁)) (d.x₁_mem_leviShort b),
    fun y hy => ?_⟩
  have h1 := hγid y hy
  rw [hγapply, hβapply] at h1
  calc j₁ * d.x₁ b * (α ⟨y, hy⟩ : X) * (j₁ * d.x₁ b)⁻¹ =
      j₁ * (d.x₁ b * (α ⟨y, hy⟩ : X) * (d.x₁ b)⁻¹) * j₁⁻¹ := by group
    _ = y := h1

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
