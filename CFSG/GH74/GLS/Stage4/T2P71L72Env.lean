module

public import CFSG.GH74.GLS.Stage4.T2P71Defs
public import CFSG.GH74.GLS.Stage4.T2P71L72NS

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.F1Loc

theorem sq_lt_three_pow (n : ℕ) : n ^ 2 < 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> norm_num
    · have h1 : (k + 1) ^ 2 ≤ 3 * k ^ 2 := by nlinarith
      calc (k + 1) ^ 2 ≤ 3 * k ^ 2 := h1
        _ < 3 * 3 ^ k := by omega
        _ = 3 ^ (k + 1) := by rw [pow_succ]; ring

theorem exists_sigma_fixed {G : Type} [Group G] {N : T2N3 G} {u : G} (hSec : Ch6Sec5 N u)
    {F₁ : Type} [Field F₁] [Finite F₁] (hodd : Odd (Nat.card F₁)) {φ : SL2 F₁ →* G}
    (hinj : Function.Injective φ) (hX : N.X₁ = (uSub F₁).map φ)
    (hHK : N.H ⊓ N.K₁ = (tSub F₁).map φ) (hw : N.w₁ = φ (sl2W F₁)) {f : G} (hf : f ∈ N.F)
    (hfS : ∀ s ∈ N.S, f * s = s * f) :
    ∃ σ : F₁ ≃+* F₁, ∀ M : SL2 F₁,
      f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F₁ →+* F₁) M) := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have h2 : (2 : F₁) ≠ 0 := CFSG.GorensteinWalter.two_ne_zero_of_odd_card F₁ hodd
  have hK : N.K₁ = N.X₁ ⊔ N.X₁' := hLoc.K₁_eq
  have hfH : ∀ x ∈ N.H, f * x * f⁻¹ ∈ N.H := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hF5.F_normH hf) x).1 hx
  have hfw : f * φ (sl2W F₁) = φ (sl2W F₁) * f := by
    rw [← hw]; exact hfS _ hLoc.w₁_memS
  exact exists_fieldAut_of_coord h2 φ hinj hX (by rw [← hK]; exact hHK)
    (hF5.F_normX₁ f hf) (hF5.F_normX₁' f hf) hfH hfw

section Env

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {n : ℕ} {N : T2N3 G} {u : G}

theorem card_F_le_sq (h : P71Env Gs n N u) : Nat.card ↥N.F ≤ n ^ 2 := by
  obtain ⟨F₁, F₂, iF₁, iF₂, t, hS, hR⟩ := h.setup
  have hSec := h.sec5
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have : Finite F₁ := hS.finite₁
  have : Finite F₂ := hS.finite₂
  have hq : N.q₁ = N.q₂ := h.q₁.trans h.q₂.symm
  have hcard₁ : Nat.card F₁ = N.q₁ := by rw [h.q₁]; exact hS.card₁
  have hcard₂ : Nat.card F₂ = N.q₂ := by rw [h.q₂]; exact hS.card₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hcard₁]; exact hLoc.q₁_odd
  have hodd₂ : Odd (Nat.card F₂) := by rw [hcard₂]; exact hLoc.q₂_odd
  obtain ⟨φ₁, hφ₁, hrange₁, -, hX₁, -, hw₁, hHK₁⟩ := exists_coord_over h.coord hcard₁
  obtain ⟨φ₂, hφ₂, hrange₂, -, hX₂, -, hw₂, hHK₂⟩ :=
    exists_coord_over (N := N.swap.toT2N2.toT2N1) (Ch6Coord.swap h.coord) hcard₂
  have hrange₂' : φ₂.range = N.K₂ := hrange₂
  have hFS : ∀ f ∈ N.F, ∀ s ∈ N.S, f * s = s * f := by
    intro f hf s hs
    have hfC : f ∈ centralizer (N.S : Set G) := by
      rw [hF5.centS]; exact Subgroup.mem_sup_right hf
    exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
  have hex₁ : ∀ f : ↥N.F, ∃ σ : F₁ ≃+* F₁, ∀ M : SL2 F₁,
      (f : G) * φ₁ M * (f : G)⁻¹ = φ₁ (Matrix.SpecialLinearGroup.map (σ : F₁ →+* F₁) M) := fun f =>
    exists_sigma_fixed hSec hodd₁ hφ₁ hX₁ hHK₁ hw₁ f.2 (hFS f f.2)
  have hex₂ : ∀ f : ↥N.F, ∃ σ : F₂ ≃+* F₂, ∀ M : SL2 F₂,
      (f : G) * φ₂ M * (f : G)⁻¹ = φ₂ (Matrix.SpecialLinearGroup.map (σ : F₂ →+* F₂) M) := fun f =>
    exists_sigma_fixed (N := N.swap) (hSec.swap hq) hodd₂ hφ₂ hX₂ hHK₂ hw₂ f.2 (hFS f f.2)
  choose σ₁ hσ₁ using hex₁
  choose σ₂ hσ₂ using hex₂
  let Θ : ↥N.F → (F₁ ≃+* F₁) × (F₂ ≃+* F₂) := fun f => (σ₁ f, σ₂ f)
  have hΘ : Function.Injective Θ := by
    intro f g hfg
    have h1 : σ₁ f = σ₁ g := congrArg Prod.fst hfg
    have h2 : σ₂ f = σ₂ g := congrArg Prod.snd hfg
    set d : G := ((g⁻¹ * f : ↥N.F) : G) with hd
    have hdF : d ∈ N.F := (g⁻¹ * f : ↥N.F).2
    have hd' : d = (g : G)⁻¹ * (f : G) := rfl
    have hc₁ : ∀ x ∈ N.K₁, x * d = d * x := by
      intro x hx
      rw [← hrange₁] at hx
      obtain ⟨M, rfl⟩ := hx
      have e : (f : G) * φ₁ M * (f : G)⁻¹ = (g : G) * φ₁ M * (g : G)⁻¹ := by
        rw [hσ₁ f M, hσ₁ g M, h1]
      rw [hd']
      calc φ₁ M * ((g : G)⁻¹ * (f : G)) = (g : G)⁻¹ * ((g : G) * φ₁ M * (g : G)⁻¹) * (f : G) := by group
        _ = (g : G)⁻¹ * ((f : G) * φ₁ M * (f : G)⁻¹) * (f : G) := by rw [e]
        _ = (g : G)⁻¹ * (f : G) * φ₁ M := by group
    have hc₂ : ∀ x ∈ N.K₂, x * d = d * x := by
      intro x hx
      rw [← hrange₂'] at hx
      obtain ⟨M, rfl⟩ := hx
      have e : (f : G) * φ₂ M * (f : G)⁻¹ = (g : G) * φ₂ M * (g : G)⁻¹ := by
        rw [hσ₂ f M, hσ₂ g M, h2]
      rw [hd']
      calc φ₂ M * ((g : G)⁻¹ * (f : G)) = (g : G)⁻¹ * ((g : G) * φ₂ M * (g : G)⁻¹) * (f : G) := by group
        _ = (g : G)⁻¹ * ((f : G) * φ₂ M * (f : G)⁻¹) * (f : G) := by rw [e]
        _ = (g : G)⁻¹ * (f : G) * φ₂ M := by group
    have hd1 : d = 1 :=
      F1Loc.f_eq_one_of_trivial hSec hdF (hFS d hdF) (hF5.F_odd d hdF) hc₁ hc₂
    have : g⁻¹ * f = 1 := Subtype.ext hd1
    exact (inv_mul_eq_one.1 this).symm
  have : Finite ((F₁ ≃+* F₁) × (F₂ ≃+* F₂)) :=
    have := finite_ringEquiv F₁
    have := finite_ringEquiv F₂
    inferInstance
  have hA₁ : Nat.card (F₁ ≃+* F₁) = n :=
    CFSG.GH74.GLS.IVK.card_ringAut F₁ 3 n Nat.prime_three (by rw [hS.card₁])
  have hA₂ : Nat.card (F₂ ≃+* F₂) = n :=
    CFSG.GH74.GLS.IVK.card_ringAut F₂ 3 n Nat.prime_three (by rw [hS.card₂])
  calc Nat.card ↥N.F ≤ Nat.card ((F₁ ≃+* F₁) × (F₂ ≃+* F₂)) := Nat.card_le_card_of_injective Θ hΘ
    _ = n ^ 2 := by rw [Nat.card_prod, hA₁, hA₂, sq]

theorem lt3_of_sylow (h : P71Env Gs n N u) (P : Sylow 3 G)
    (hP : (P : Subgroup G) ≤ centralizer ({N.z} : Set G)) : Lt3 G n := by
  intro R hR
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hctx := h.ctx
  obtain ⟨P₀'⟩ : Nonempty (Sylow 3 ↥N.F) := inferInstance
  set P₀ : Subgroup G := (P₀' : Subgroup ↥N.F).map N.F.subtype with hP₀
  have hP₀c : Nat.card ↥P₀ = 3 ^ (Nat.card ↥N.F).factorization 3 := by
    rw [hP₀, Subgroup.card_map_of_injective N.F.subtype_injective, Sylow.card_eq_multiplicity]
  have hP₀F : Nat.card ↥P₀ ≤ Nat.card ↥N.F := by
    apply Subgroup.card_le_of_le
    exact Subgroup.map_subtype_le _
  obtain ⟨Q, hQ⟩ := hR.exists_le_sylow
  have h1 : Nat.card ↥R ≤ Nat.card ↥(P : Subgroup G) := by
    calc Nat.card ↥R ≤ Nat.card ↥(Q : Subgroup G) := Subgroup.card_le_of_le hQ
      _ = Nat.card ↥(P : Subgroup G) := by
        rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P]
  have h2 := T6.card_pSub_C_le hctx h.q₁ h.q₂ hP₀c hP P.isPGroup'
  have h3 := card_F_le_sq h
  have h4 := sq_lt_three_pow n
  calc Nat.card ↥R ≤ N.q₁ * N.q₂ * Nat.card ↥P₀ := h1.trans h2
    _ ≤ 3 ^ n * 3 ^ n * n ^ 2 := by
        rw [h.q₁, h.q₂]; exact Nat.mul_le_mul_left _ (hP₀F.trans h3)
    _ < (3 ^ n) ^ 3 := by
      have hpos : 0 < 3 ^ n * 3 ^ n := by positivity
      calc 3 ^ n * 3 ^ n * n ^ 2 < 3 ^ n * 3 ^ n * 3 ^ n := Nat.mul_lt_mul_of_pos_left h4 hpos
        _ = (3 ^ n) ^ 3 := by ring

theorem exists_order_three (h : P71Env Gs n N u) (P : Subgroup G)
    (hPC : P ≤ centralizer ({N.z} : Set G)) (hP3 : IsPGroup 3 ↥P) (hnK : ¬ P ≤ N.K₁ ⊔ N.K₂) :
    ∃ f ∈ N.F, orderOf f = 3 ∧ 3 ≤ n := by
  have hctx := h.ctx
  have hSec := h.sec5
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  obtain ⟨x, hxP, hxK⟩ := Set.not_subset.1 hnK
  have hxC : x ∈ centralizer ({N.z} : Set G) := hPC hxP
  have hFz : ∀ f ∈ N.F, f * N.z = N.z * f := fun f hf => hctx.FS f hf _ hLoc.z_mem_S
  have hFn := t2P53_F_normC₁ hctx.ctx hFz
  obtain ⟨c, hc, f, hf, hxcf⟩ := t2P53_split hFn (hF5.C_le hxC)
  obtain ⟨k, hk⟩ := hP3 ⟨x, hxP⟩
  have hk' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hk')
  obtain ⟨c', hc', hpow⟩ := T6.t6_pow_cf (C₁ := N.K₁ ⊔ N.K₂ ⊔ N.S) (F := N.F)
    (fun f hf c hc => (Subgroup.mem_normalizer_iff.1 (hFn hf) c).1 hc) hc hf (3 ^ k)
  have hk'' := hk'
  rw [hxcf, hpow] at hk''
  have hf3 : f ^ (3 ^ k) = c'⁻¹ := by
    calc f ^ (3 ^ k) = c'⁻¹ * (c' * f ^ (3 ^ k)) := by group
      _ = c'⁻¹ := by rw [hk'']; group
  have hf3C : f ^ (3 ^ k) ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by rw [hf3]; exact Subgroup.inv_mem _ hc'
  have hfodd : Odd (orderOf (f ^ (3 ^ k))) := Odd.of_dvd_nat (hF5.F_odd f hf) (orderOf_pow_dvd _)
  have hfK := hctx.oddK _ hf3C hfodd
  have hbot : f ^ (3 ^ k) ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨N.F.pow_mem hf _, hfK⟩
  rw [hF5.F_inter_K, Subgroup.mem_bot] at hbot
  have hf1 : f ≠ 1 := by
    intro hf1
    apply hxK
    rw [hf1, mul_one] at hxcf
    rw [hxcf]
    exact hctx.oddK c hc (by rw [← hxcf]; exact hxodd)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hbot)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hf1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have h3d : 3 ∣ orderOf f := by rw [hj]; exact dvd_pow_self 3 hj0
  set f' : G := f ^ (orderOf f / 3) with hf'
  have hf'o : orderOf f' = 3 := orderOf_pow_orderOf_div (orderOf_pos f).ne' h3d
  have hf'F : f' ∈ N.F := N.F.pow_mem hf _
  refine ⟨f', hf'F, hf'o, ?_⟩
  obtain ⟨F₁, F₂, iF₁, iF₂, t, hS, hR⟩ := h.setup
  have : Finite F₁ := hS.finite₁
  have : Finite F₂ := hS.finite₂
  have hq : N.q₁ = N.q₂ := h.q₁.trans h.q₂.symm
  have hcard₁ : Nat.card F₁ = N.q₁ := by rw [h.q₁]; exact hS.card₁
  have hcard₂ : Nat.card F₂ = N.q₂ := by rw [h.q₂]; exact hS.card₂
  have hfS : ∀ s ∈ N.S, f' * s = s * f' := fun s hs => hctx.FS f' hf'F s hs
  have hf'r : f' ^ 3 = 1 := by rw [← hf'o]; exact pow_orderOf_eq_one f'
  obtain ⟨φ₁, σ₁, hφ₁, hrange₁, -, -, -, -, -, hσ₁⟩ :=
    coord_fieldAut hSec h.coord hcard₁ hf'F hfS
  obtain ⟨φ₂, σ₂, hφ₂, hrange₂, -, -, -, -, -, hσ₂⟩ :=
    coord_fieldAut₂ hSec hq h.coord hcard₂ hf'F hfS
  have hσ₁r : σ₁ ^ 3 = 1 := pow_eq_one_of_pow_eq_one φ₁ hφ₁ f' σ₁ hσ₁ hf'r
  have hσ₂r : σ₂ ^ 3 = 1 := pow_eq_one_of_pow_eq_one φ₂ hφ₂ f' σ₂ hσ₂ hf'r
  have hn0 : n ≠ 0 := by have := h.n_ge; omega
  have hdvd : ∀ {F : Type} [Field F] [Finite F], Nat.card F = 3 ^ n → ∀ σ : F ≃+* F, σ ^ 3 = 1 → σ ≠ 1 →
      3 ≤ n := by
    intro F _ _ hF σ hσ3 hσ1
    have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
    have hA : Nat.card (F ≃+* F) = n := CFSG.GH74.GLS.IVK.card_ringAut F 3 n Nat.prime_three hF
    have : 3 ∣ n := by
      rw [← hA, ← hord]
      exact orderOf_dvd_natCard σ
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) this
  by_cases h1 : σ₁ = 1
  · by_cases h2 : σ₂ = 1
    · exfalso
      have hc₁ : ∀ x ∈ N.K₁, x * f' = f' * x := by
        intro x hx
        rw [← hrange₁] at hx
        obtain ⟨M, rfl⟩ := hx
        have := centralizes_of_eq_one φ₁ f' σ₁ hσ₁ h1 M
        calc φ₁ M * f' = (f' * φ₁ M * f'⁻¹) * f' := by rw [this]
          _ = f' * φ₁ M := by group
      have hc₂ : ∀ x ∈ N.K₂, x * f' = f' * x := by
        intro x hx
        have hrange₂' : φ₂.range = N.K₂ := hrange₂
        rw [← hrange₂'] at hx
        obtain ⟨M, rfl⟩ := hx
        have := centralizes_of_eq_one φ₂ f' σ₂ hσ₂ h2 M
        calc φ₂ M * f' = (f' * φ₂ M * f'⁻¹) * f' := by rw [this]
          _ = f' * φ₂ M := by group
      have := f_eq_one_of_trivial hSec hf'F hfS (by rw [hf'o]; decide) hc₁ hc₂
      rw [this, orderOf_one] at hf'o
      omega
    · exact hdvd hS.card₂ σ₂ hσ₂r h2
  · exact hdvd hS.card₁ σ₁ hσ₁r h1

end Env

end CFSG.GH74.GLS.Stage4.Rest.L72
