module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem pow_zpow_eq_self {N : Type*} [CommGroup N] [Finite N] (a : ℕ) (u v : ℤ)
    (huv : u * (a : ℤ) + v * (Nat.card N : ℤ) = 1) (n : N) : (n ^ a) ^ u = n := by
  have h1 : (n ^ a) ^ u = n ^ ((a : ℤ) * u) := by
    rw [← zpow_natCast, ← zpow_mul]
  have h2 : (a : ℤ) * u = 1 - v * (Nat.card N : ℤ) := by linarith
  have h3 : n ^ ((Nat.card N : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]; exact pow_card_eq_one'
  rw [h1, h2, zpow_sub, zpow_one, mul_comm v, zpow_mul, h3, one_zpow]
  simp

theorem commutator_le_left {N A : Subgroup Γ} (hAN : A ≤ Subgroup.normalizer (N : Set Γ)) :
    ⁅N, A⁆ ≤ N := by
  refine Subgroup.commutator_le.2 fun n hn a ha => ?_
  have h := (Subgroup.mem_normalizer_iff.1 (hAN ha) n⁻¹).1 (N.inv_mem hn)
  have e : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact N.mul_mem hn h

theorem le_normalizer_commutator {N A : Subgroup Γ} (hAN : A ≤ Subgroup.normalizer (N : Set Γ)) :
    A ≤ Subgroup.normalizer ((⁅N, A⁆ : Subgroup Γ) : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ A, ∀ x ∈ ⁅N, A⁆, g * x * g⁻¹ ∈ ⁅N, A⁆ := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨n, hn, a, ha, rfl⟩ := hy
      have h1 : g * n * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hAN hg) n).1 hn
      have h2 : g * a * g⁻¹ ∈ A := A.mul_mem (A.mul_mem hg ha) (A.inv_mem hg)
      have e : g * ⁅n, a⁆ * g⁻¹ = ⁅g * n * g⁻¹, g * a * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator h1 h2
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]; exact (⁅N, A⁆).mul_mem hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]; exact (⁅N, A⁆).inv_mem hx
  intro x
  exact ⟨fun hx => key g hg x hx, fun hx => by
    have := key g⁻¹ (A.inv_mem hg) _ hx
    simpa [mul_assoc] using this⟩

theorem coprime_abelian_decomp (N A : Subgroup Γ) [Finite N] [Finite A]
    (hAN : A ≤ Subgroup.normalizer (N : Set Γ)) (hNab : ∀ x y : N, x * y = y * x)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) :
    (N ⊓ Subgroup.centralizer (A : Set Γ)) ⊔ ⁅N, A⁆ = N ∧
      Disjoint (N ⊓ Subgroup.centralizer (A : Set Γ)) ⁅N, A⁆ := by
  classical
  have : Fintype A := Fintype.ofFinite A
  let _ : CommGroup N := { (inferInstance : Group N) with mul_comm := hNab }
  have hconj : ∀ (a : A) (n : N), (a : Γ)⁻¹ * (n : Γ) * (a : Γ) ∈ N := fun a n => by
    have := (Subgroup.mem_normalizer_iff.1 (hAN (A.inv_mem a.2)) n).1 n.2
    simpa using this
  let act : A → N →* N := fun a =>
    { toFun := fun n => ⟨(a : Γ)⁻¹ * (n : Γ) * (a : Γ), hconj a n⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun n m => by
        apply Subtype.ext
        show (a : Γ)⁻¹ * ((n : Γ) * m) * a = ((a : Γ)⁻¹ * n * a) * ((a : Γ)⁻¹ * m * a)
        group }
  have act_coe : ∀ (a : A) (n : N), ((act a n : N) : Γ) = (a : Γ)⁻¹ * (n : Γ) * (a : Γ) :=
    fun a n => rfl
  have act_act : ∀ (a b : A) (n : N), act b (act a n) = act (a * b) n := by
    intro a b n
    apply Subtype.ext
    simp only [act_coe, Subgroup.coe_mul]
    group
  let P : N →* N :=
    { toFun := fun n => ∏ a : A, act a n
      map_one' := by simp
      map_mul' := fun n m => by simp [Finset.prod_mul_distrib] }
  have hP_fixed : ∀ (b : A) (n : N), act b (P n) = P n := by
    intro b n
    show act b (∏ a : A, act a n) = ∏ a : A, act a n
    rw [map_prod]
    simp only [act_act]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ (fun a => rfl)
  have hP_act : ∀ (b : A) (n : N), P (act b n) = P n := by
    intro b n
    show ∏ a : A, act a (act b n) = ∏ a : A, act a n
    simp only [act_act]
    exact Fintype.prod_equiv (Equiv.mulLeft b) _ _ (fun a => rfl)
  obtain ⟨u, v, huv⟩ : IsCoprime (Nat.card A : ℤ) (Nat.card N : ℤ) :=
    Nat.isCoprime_iff_coprime.2 hcop
  have huv' : u * (Nat.card A : ℤ) + v * (Nat.card N : ℤ) = 1 := by linarith
  let π : N →* N :=
    { toFun := fun n => (P n) ^ u
      map_one' := by simp
      map_mul' := fun n m => by rw [map_mul, mul_zpow] }
  have hπ_fixed : ∀ (b : A) (n : N), act b (π n) = π n := by
    intro b n
    show act b ((P n) ^ u) = (P n) ^ u
    rw [map_zpow, hP_fixed]
  have hπ_act : ∀ (b : A) (n : N), π (act b n) = π n := by
    intro b n
    show (P (act b n)) ^ u = (P n) ^ u
    rw [hP_act]
  have hP_const : ∀ n : N, (∀ b : A, act b n = n) → P n = n ^ Nat.card A := by
    intro n hn
    show ∏ a : A, act a n = n ^ Nat.card A
    simp only [hn]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]
  have hπ_id : ∀ n : N, (∀ b : A, act b n = n) → π n = n := by
    intro n hn
    show (P n) ^ u = n
    rw [hP_const n hn]
    exact pow_zpow_eq_self _ u v huv' n
  have hπ_mem : ∀ n : N, ((π n : N) : Γ) ∈ N ⊓ Subgroup.centralizer (A : Set Γ) := by
    intro n
    refine ⟨(π n).2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have h := congrArg Subtype.val (hπ_fixed ⟨a, ha⟩ n)
    rw [act_coe] at h
    have h' : (a : Γ)⁻¹ * ((π n : N) : Γ) * a = ((π n : N) : Γ) := h
    calc (a : Γ) * ((π n : N) : Γ) = a * ((a : Γ)⁻¹ * ((π n : N) : Γ) * a) := by rw [h']
      _ = ((π n : N) : Γ) * a := by group
  have hLc : ∀ (a : A) (n : N), ((n : N)⁻¹ * act a n : N) ∈ (⁅N, A⁆).subgroupOf N := by
    intro a n
    rw [Subgroup.mem_subgroupOf]
    have e : (((n : N)⁻¹ * act a n : N) : Γ) = ⁅(n : Γ)⁻¹, (a : Γ)⁻¹⁆ := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, act_coe]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (N.inv_mem n.2) (A.inv_mem a.2)
  have hπ_diff : ∀ n : N, ((n : N)⁻¹ * π n : N) ∈ (⁅N, A⁆).subgroupOf N := by
    intro n
    set Lc : Subgroup N := (⁅N, A⁆).subgroupOf N with hLcdef
    have hl : P n * (n ^ Nat.card A)⁻¹ ∈ Lc := by
      have e1 : P n * (n ^ Nat.card A)⁻¹ = ∏ a : A, (n⁻¹ * act a n) := by
        show (∏ a : A, act a n) * (n ^ Nat.card A)⁻¹ = _
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card,
          inv_pow]
        exact mul_comm _ _
      rw [e1]
      exact Subgroup.prod_mem Lc fun a _ => hLc a n
    have e2 : π n = n * (P n * (n ^ Nat.card A)⁻¹) ^ u := by
      show (P n) ^ u = n * (P n * (n ^ Nat.card A)⁻¹) ^ u
      have : P n = n ^ Nat.card A * (P n * (n ^ Nat.card A)⁻¹) := by
        rw [mul_comm (P n) (n ^ Nat.card A)⁻¹, mul_inv_cancel_left]
      conv_lhs => rw [this]
      rw [mul_zpow, pow_zpow_eq_self _ u v huv' n]
    have e3 : (n : N)⁻¹ * π n = (P n * (n ^ Nat.card A)⁻¹) ^ u := by
      rw [e2, inv_mul_cancel_left]
    rw [e3]
    exact Subgroup.zpow_mem Lc hl u
  have hker : ⁅N, A⁆ ≤ π.ker.map N.subtype := by
    refine Subgroup.commutator_le.2 fun n hn a ha => ?_
    refine ⟨(⟨n, hn⟩ : N) * (act ((⟨a, ha⟩ : A)⁻¹) ⟨n, hn⟩)⁻¹, MonoidHom.mem_ker.2 ?_, ?_⟩
    · rw [map_mul, map_inv, hπ_act, mul_inv_cancel]
    · have h1 : ((act ((⟨a, ha⟩ : A)⁻¹) ⟨n, hn⟩ : N) : Γ) = a * n * a⁻¹ := by
        rw [act_coe]; simp
      show (((⟨n, hn⟩ : N) * (act ((⟨a, ha⟩ : A)⁻¹) ⟨n, hn⟩)⁻¹ : N) : Γ) = ⁅n, a⁆
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h1, commutatorElement_def]
      group
  refine ⟨le_antisymm (sup_le inf_le_left (commutator_le_left hAN)) ?_, ?_⟩
  · intro x hx
    let x' : N := ⟨x, hx⟩
    have h1 : ((π x' : N) : Γ) ∈ N ⊓ Subgroup.centralizer (A : Set Γ) := hπ_mem x'
    have h3 : (x : Γ)⁻¹ * ((π x' : N) : Γ) ∈ ⁅N, A⁆ := Subgroup.mem_subgroupOf.1 (hπ_diff x')
    have h2 : ((π x' : N) : Γ)⁻¹ * x ∈ ⁅N, A⁆ := by
      have := (⁅N, A⁆).inv_mem h3
      simpa [mul_inv_rev] using this
    have e : x = ((π x' : N) : Γ) * (((π x' : N) : Γ)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup h1 h2
  · rw [Subgroup.disjoint_def]
    intro x hxC hxL
    obtain ⟨y, hy, hyx⟩ := hker hxL
    have hfix : ∀ b : A, act b y = y := by
      intro b
      apply Subtype.ext
      rw [act_coe]
      have hyx' : ((y : N) : Γ) = x := hyx
      rw [hyx']
      have hc := (Subgroup.mem_centralizer_iff.1 hxC.2) b b.2
      calc (b : Γ)⁻¹ * x * b = (b : Γ)⁻¹ * (x * b) := by group
        _ = (b : Γ)⁻¹ * ((b : Γ) * x) := by rw [hc]
        _ = x := by group
    have h1 : π y = y := hπ_id y hfix
    have hy1 : y = 1 := by rw [← h1]; exact MonoidHom.mem_ker.1 hy
    have hyx' : ((y : N) : Γ) = x := hyx
    rw [← hyx', hy1]
    rfl

theorem commutator_commutator_eq (N A : Subgroup Γ) [Finite N] [Finite A]
    (hAN : A ≤ Subgroup.normalizer (N : Set Γ)) (hNab : ∀ x y : N, x * y = y * x)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) : ⁅⁅N, A⁆, A⁆ = ⁅N, A⁆ := by
  obtain ⟨h1, h2⟩ := coprime_abelian_decomp N A hAN hNab hcop
  have hLN : ⁅N, A⁆ ≤ N := commutator_le_left hAN
  have hAL : A ≤ Subgroup.normalizer ((⁅N, A⁆ : Subgroup Γ) : Set Γ) := le_normalizer_commutator hAN
  have hLab : ∀ x y : (⁅N, A⁆ : Subgroup Γ), x * y = y * x := fun x y => by
    apply Subtype.ext
    have h := congrArg Subtype.val (hNab ⟨x, hLN x.2⟩ ⟨y, hLN y.2⟩)
    exact h
  have : Finite (⁅N, A⁆ : Subgroup Γ) :=
    Finite.of_injective (Subgroup.inclusion hLN) (Subgroup.inclusion_injective hLN)
  have hcopL : Nat.Coprime (Nat.card A) (Nat.card (⁅N, A⁆ : Subgroup Γ)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) hcop
  obtain ⟨h3, -⟩ := coprime_abelian_decomp (⁅N, A⁆ : Subgroup Γ) A hAL hLab hcopL
  have h5 : (⁅N, A⁆ : Subgroup Γ) ⊓ Subgroup.centralizer (A : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (N ⊓ Subgroup.centralizer (A : Set Γ)) ⊓ (⁅N, A⁆ : Subgroup Γ) :=
      ⟨⟨hLN hx.1, hx.2⟩, hx.1⟩
    exact h2.le_bot hx'
  rw [h5, bot_sup_eq] at h3
  exact h3

end CFSG.QuasithinUnique.Setup.Layer
