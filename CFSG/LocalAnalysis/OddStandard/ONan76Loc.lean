module

public import CFSG.LocalAnalysis.OddStandard.ONan76Cent
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.OddStandard.ONan76

open Subgroup

theorem card_eq_four {G : Type*} [Group G] [Finite G] {L : Subgroup G} {a b : G}
    (ha : a ∈ L) (hb : b ∈ L) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1)
    (hL : ∀ x ∈ L, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) : Nat.card L = 4 := by
  classical
  have hset : (L : Set G) = {1, a, b, a * b} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨hL x, ?_⟩
    rintro (rfl | rfl | rfl | rfl)
    · exact one_mem L
    · exact ha
    · exact hb
    · exact mul_mem ha hb
  have hab1 : a * b ≠ 1 := fun h => hab (by
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, ha2, one_mul])
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha1 (by simpa using h)
  show Nat.card (L : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair hab3.symm]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hab, hab2.symm⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hb1.symm, hab1.symm⟩

namespace AlperinFrame

variable {G : Type*} [Group G] {n : ℕ} {v₁ v₂ v₃ s t : G} (hF : AlperinFrame n v₁ v₂ v₃ s t)

include hF

theorem vec_pow_two_pow_pred (p : Vec n) :
    vec v₁ v₂ v₃ p ^ 2 ^ (n - 1) = vec v₁ v₂ v₃ ((2 ^ (n - 1) : ℕ) • p) :=
  (hF.vec_nsmul _ p).symm

theorem exists_nf_inv (hn : 2 ≤ n) {x : G} (hx : x ∈ hF.P) (hxV : x ∉ hF.V)
    (hx2 : x * x ∈ hF.V) : ∃ q : Vec n, ∃ i < 4, ∃ e < 2, (e = 1 ∨ i = 2) ∧
      x = vec v₁ v₂ v₃ q * s ^ i * t ^ e := by
  obtain ⟨q, i, hi, e, he, rfl⟩ := hF.exists_nf (by omega) hx
  have h1 := (hF.nf_sq_mem_V_iff hn q hi he).1 (by rwa [pow_two])
  have h2 : ¬ (i = 0 ∧ e = 0) := fun h => hxV ((hF.nf_mem_V_iff hn q hi he).2 h)
  exact ⟨q, i, hi, e, he, by omega, rfl⟩

theorem mul_inv_mem_V_of_pow (hn : 3 ≤ n) {b x₁ x₂ : G} (hb : b ∈ hF.V)
    (hbo : b ^ 2 ^ (n - 1) ≠ 1) (hx₁ : x₁ ∈ hF.P) (hx₂ : x₂ ∈ hF.P) (hx₁V : x₁ ∉ hF.V)
    (hx₂V : x₂ ∉ hF.V) (hx₁2 : x₁ * x₁ ∈ hF.V) (hx₂2 : x₂ * x₂ ∈ hF.V)
    (hb₁ : x₁ * b = b * x₁) (hb₂ : x₂ * b = b * x₂) : x₁ * x₂⁻¹ ∈ hF.V := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  by_contra h12
  obtain ⟨q₁, i₁, hi₁, e₁, he₁, hτ₁, rfl⟩ := hF.exists_nf_inv hn2 hx₁ hx₁V hx₁2
  obtain ⟨q₂, i₂, hi₂, e₂, he₂, hτ₂, rfl⟩ := hF.exists_nf_inv hn2 hx₂ hx₂V hx₂2
  have hne : ¬ (i₁ = i₂ ∧ e₁ = e₂) := by
    rintro ⟨rfl, rfl⟩
    apply h12
    rw [show vec v₁ v₂ v₃ q₁ * s ^ i₁ * t ^ e₁ * (vec v₁ v₂ v₃ q₂ * s ^ i₁ * t ^ e₁)⁻¹ =
      vec v₁ v₂ v₃ q₁ * (vec v₁ v₂ v₃ q₂)⁻¹ by group, ← hF.vec_sub]
    exact hF.vec_mem_V _
  obtain ⟨p, rfl⟩ := hF.exists_vec_of_mem_V hn1 hb
  have h4 := fix_pair_four hi₁ he₁ hi₂ he₂ hτ₁ hτ₂ hne ((hF.comm_nf_vec_iff hn1 _ _ _ _).1 hb₁)
    ((hF.comm_nf_vec_iff hn1 _ _ _ _).1 hb₂)
  apply hbo
  have h24 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  rw [hF.vec_pow_two_pow_pred, h24, mul_nsmul, h4, nsmul_zero, hF.vec_zero]

theorem eq_of_sq_not_mem (hn : 2 ≤ n) {x w₁ w₂ : G} (hx : x ∈ hF.P) (hx2 : x * x ∉ hF.V)
    (hw₁ : w₁ ∈ hF.W (by omega)) (hw₂ : w₂ ∈ hF.W (by omega)) (h₁ : w₁ ≠ 1) (h₂ : w₂ ≠ 1)
    (hc₁ : x * w₁ = w₁ * x) (hc₂ : x * w₂ = w₂ * x) : w₁ = w₂ := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨q, i, hi, e, he, rfl⟩ := hF.exists_nf hn1 hx
  have hτ := (hF.nf_sq_mem_V_iff hn q hi he).not.1 (by rwa [pow_two])
  have he0 : e = 0 := by omega
  have hi13 : i = 1 ∨ i = 3 := by omega
  subst he0
  have key : ∀ {w : G}, w ∈ hF.W hn1 → w ≠ 1 →
      vec v₁ v₂ v₃ q * s ^ i * t ^ 0 * w = w * (vec v₁ v₂ v₃ q * s ^ i * t ^ 0) →
      w = vec v₁ v₂ v₃ ((2 ^ (n - 1), 0, 2 ^ (n - 1)) : Vec n) := by
    intro w hw hw1 hc
    obtain ⟨p, rfl⟩ := hF.exists_vec_of_mem_V hn1 ((hF.mem_W_iff hn1).1 hw).1
    have hp2 : p + p = 0 := (hF.vec_mem_W_iff hn1).1 hw
    have hp0 : p ≠ 0 := fun h => hw1 (by rw [h, hF.vec_zero])
    obtain ⟨hb', hc'⟩ := fix_order_four hi13 ((hF.comm_nf_vec_iff hn1 _ _ _ _).1 hc)
    obtain ⟨ha', -, -⟩ := two_mul_eq_zero_vec hn1 p hp2
    congr 1
    obtain ⟨a, b, c⟩ := p
    simp only at hb' hc' ha' ⊢
    subst hb' hc'
    rcases ha' with rfl | rfl
    · exact absurd rfl hp0
    · rfl
  rw [key hw₁ h₁ hc₁, key hw₂ h₂ hc₂]

theorem eq_sq_of_pair (hn : 2 ≤ n) {x₁ x₂ d w : G} (hx₁ : x₁ ∈ hF.P) (hx₂ : x₂ ∈ hF.P)
    (hx₁V : x₁ ∉ hF.V) (hx₂V : x₂ ∉ hF.V) (hx₁2 : x₁ * x₁ ∈ hF.V) (hx₂2 : x₂ * x₂ ∈ hF.V)
    (h12 : x₁ * x₂⁻¹ ∉ hF.V) (hd : d ∈ hF.V) (hd2 : d * d ≠ 1) (hd₁ : x₁ * d = d * x₁)
    (hd₂ : x₂ * d = d * x₂) (hw : w ∈ hF.W (by omega)) (hw1 : w ≠ 1) (hw₁ : x₁ * w = w * x₁)
    (hw₂ : x₂ * w = w * x₂) : w = d * d := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨q₁, i₁, hi₁, e₁, he₁, hτ₁, rfl⟩ := hF.exists_nf_inv hn hx₁ hx₁V hx₁2
  obtain ⟨q₂, i₂, hi₂, e₂, he₂, hτ₂, rfl⟩ := hF.exists_nf_inv hn hx₂ hx₂V hx₂2
  have hne : ¬ (i₁ = i₂ ∧ e₁ = e₂) := by
    rintro ⟨rfl, rfl⟩
    apply h12
    rw [show vec v₁ v₂ v₃ q₁ * s ^ i₁ * t ^ e₁ * (vec v₁ v₂ v₃ q₂ * s ^ i₁ * t ^ e₁)⁻¹ =
      vec v₁ v₂ v₃ q₁ * (vec v₁ v₂ v₃ q₂)⁻¹ by group, ← hF.vec_sub]
    exact hF.vec_mem_V _
  obtain ⟨p, rfl⟩ := hF.exists_vec_of_mem_V hn1 hd
  obtain ⟨r, rfl⟩ := hF.exists_vec_of_mem_V hn1 ((hF.mem_W_iff hn1).1 hw).1
  have hr2 : r + r = 0 := (hF.vec_mem_W_iff hn1).1 hw
  have hr0 : r ≠ 0 := fun h => hw1 (by rw [h, hF.vec_zero])
  have hp2 : p + p ≠ 0 := fun h => hd2 (by rw [← hF.vec_add, h, hF.vec_zero])
  have fp₁ := (hF.comm_nf_vec_iff hn1 _ _ _ _).1 hd₁
  have fp₂ := (hF.comm_nf_vec_iff hn1 _ _ _ _).1 hd₂
  have fr₁ := (hF.comm_nf_vec_iff hn1 _ _ _ _).1 hw₁
  have fr₂ := (hF.comm_nf_vec_iff hn1 _ _ _ _).1 hw₂
  rcases fix_pair hi₁ he₁ hi₂ he₂ hτ₁ hτ₂ hne with h | h
  · exact absurd (h p fp₁ fp₂) hp2
  obtain ⟨hpa, hpe⟩ := h p fp₁ fp₂
  obtain ⟨hra, hre⟩ := h r fr₁ fr₂
  rw [← hF.vec_add]
  congr 1
  set ε : ZMod (2 ^ n) := 2 ^ (n - 1) with hεdef
  have hεε : ε + ε = 0 := two_pow_pred_add_self hn1
  obtain ⟨ra, -, -⟩ := two_mul_eq_zero_vec hn1 r hr2
  have hr1 : r.1 = ε := by
    rcases ra with h0 | h0
    · exact absurd (by rw [hre, h0]; simp) hr0
    · exact h0
  have hp1 : p.1 + p.1 = ε := by
    have h0 := (two_mul_eq_zero_iff hn1 (2 * p.1)).1 (by rw [← mul_assoc]; norm_num; exact hpa)
    rcases h0 with h0 | h0
    · exact absurd (by rw [hpe]; ext <;> simp <;> grind) hp2
    · rw [← two_mul]; exact h0
  rw [hre, hpe, hr1]
  ext <;> simp only [Prod.mk_add_mk] <;> grind

theorem card_W [Finite G] (hn : 1 ≤ n) : Nat.card (hF.W hn) = 8 := by
  set T := {x : ZMod (2 ^ n) // x + x = 0}
  have h1 : Nat.card (hF.W hn) = Nat.card {p : Vec n // p + p = 0} := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : {p : Vec n // p + p = 0} => (⟨vec v₁ v₂ v₃ p.1, (hF.vec_mem_W_iff hn).2 p.2⟩ :
        hF.W hn)) ⟨fun p q h => ?_, fun w => ?_⟩)).symm
    · exact Subtype.ext (hF.vec_injective hn (congrArg Subtype.val h))
    · obtain ⟨p, hp⟩ := hF.exists_vec_of_mem_V hn ((hF.mem_W_iff hn).1 w.2).1
      exact ⟨⟨p, (hF.vec_mem_W_iff hn).1 (hp ▸ w.2)⟩, Subtype.ext hp⟩
  have h2 : Nat.card {p : Vec n // p + p = 0} = Nat.card (T × T × T) := by
    refine Nat.card_congr
      { toFun := fun p => (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2.1, congrArg (·.2.1) p.2⟩,
          ⟨p.1.2.2, congrArg (·.2.2) p.2⟩)
        invFun := fun x => ⟨(x.1.1, x.2.1.1, x.2.2.1), by
          ext
          · exact x.1.2
          · exact x.2.1.2
          · exact x.2.2.2⟩
        left_inv := fun p => rfl
        right_inv := fun x => rfl }
  rw [h1, h2, Nat.card_prod, Nat.card_prod, card_two_torsion hn]

theorem inv_data (hn : 2 ≤ n) {j : G} (hj : j ∈ hF.P) (hjV : j ∉ hF.V) (hj2 : j * j = 1) :
    ∃ u₁ ∈ hF.V, ∃ u₂ ∈ hF.W (by omega), j * u₁ = u₁ * j ∧ j * u₂ = u₂ * j ∧
      u₁ ^ 2 ^ (n - 1) ≠ 1 ∧ u₂ ≠ 1 ∧ u₂ ≠ u₁ ^ 2 ^ (n - 1) ∧
      (∀ h ∈ hF.W (by omega), j * h = h * j →
        h = 1 ∨ h = u₁ ^ 2 ^ (n - 1) ∨ h = u₂ ∨ h = u₁ ^ 2 ^ (n - 1) * u₂) ∧
      (∀ h ∈ hF.W (by omega), j * h = h * j → ∃ v ∈ hF.V, v * j * v⁻¹ = j * h) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨q, i, hi, e, he, hτ, rfl⟩ :=
    hF.exists_nf_inv hn hj hjV (by rw [hj2]; exact one_mem _)
  obtain ⟨u₁, u₂, r₁, r₂, f₁, f₂, h22, h20, h1e, h12, hr₁, hr₂, hH⟩ := inv_type_data hn hi he hτ
  set x := vec v₁ v₂ v₃ q * s ^ i * t ^ e with hx
  have hcomm : ∀ p : Vec n, act i e p = p → x * vec v₁ v₂ v₃ p = vec v₁ v₂ v₃ p * x :=
    fun p hp => (hF.comm_nf_vec_iff hn1 q p i e).2 hp
  have hu₂W : vec v₁ v₂ v₃ u₂ ∈ hF.W hn1 := (hF.vec_mem_W_iff hn1).2 h22
  have hε : vec v₁ v₂ v₃ u₁ ^ 2 ^ (n - 1) = vec v₁ v₂ v₃ ((2 ^ (n - 1) : ℕ) • u₁) :=
    hF.vec_pow_two_pow_pred u₁
  have hcoords : ∀ h ∈ hF.W hn1, x * h = h * x → ∃ p : Vec n, h = vec v₁ v₂ v₃ p ∧
      (p = 0 ∨ p = (2 ^ (n - 1) : ℕ) • u₁ ∨ p = u₂ ∨ p = (2 ^ (n - 1) : ℕ) • u₁ + u₂) := by
    intro h hh hc
    obtain ⟨p, rfl⟩ := hF.exists_vec_of_mem_V hn1 ((hF.mem_W_iff hn1).1 hh).1
    exact ⟨p, rfl, hH p ((hF.comm_nf_vec_iff hn1 q p i e).1 hc) ((hF.vec_mem_W_iff hn1).1 hh)⟩
  have hcv : ∀ r : Vec n, vec v₁ v₂ v₃ r * x * (vec v₁ v₂ v₃ r)⁻¹ =
      x * vec v₁ v₂ v₃ (act i e r - r) := by
    intro r
    rw [hF.vec_sub, ← hF.conj_nf q r i e, ← hx]
    group
  refine ⟨vec v₁ v₂ v₃ u₁, hF.vec_mem_V u₁, vec v₁ v₂ v₃ u₂, hu₂W, (hcomm u₁ f₁),
    (hcomm u₂ f₂), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hε]
    intro h
    exact h1e ((hF.vec_eq_one_iff hn1).1 h)
  · intro h
    exact h20 ((hF.vec_eq_one_iff hn1).1 h)
  · rw [hε]
    intro h
    exact h12 ((hF.vec_inj hn1).1 h).symm
  · intro h hh hc
    obtain ⟨p, rfl, hp⟩ := hcoords h hh hc
    rw [hε, ← hF.vec_add]
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl hF.vec_zero
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro h hh hc
    obtain ⟨p, rfl, hp⟩ := hcoords h hh hc
    have key : ∀ r : Vec n, act i e r - r = p →
        ∃ v ∈ hF.V, v * x * v⁻¹ = x * vec v₁ v₂ v₃ p := fun r hr =>
      ⟨vec v₁ v₂ v₃ r, hF.vec_mem_V r, by rw [hcv, hr]⟩
    rcases hp with rfl | rfl | rfl | rfl
    · exact key 0 (by rw [act_zero, sub_zero])
    · exact key r₁ hr₁
    · exact key r₂ hr₂
    · exact key (r₁ + r₂) (by rw [act_add, add_sub_add_comm, hr₁, hr₂])

theorem card_le_of_comm [Finite G] (hn : 2 ≤ n) {x : G} (hx : x ∈ hF.P) (hxV : x ∉ hF.V)
    {B : Subgroup G} (hBV : B ≤ hF.V) (hB : ∀ y ∈ B, x * y = y * x) :
    Nat.card B ≤ 2 ^ n * 2 := by
  have hn1 : 1 ≤ n := by omega
  classical
  obtain ⟨q, i, hi, e, he, rfl⟩ := hF.exists_nf hn1 hx
  have hne : ¬ (i = 0 ∧ e = 0) := fun h => hxV ((hF.nf_mem_V_iff hn q hi he).2 h)
  obtain ⟨ψ, φ, hφ, hinj⟩ := fix_inj (n := n) hi he hne
  choose c hc using fun y : B => hF.exists_vec_of_mem_V hn1 (hBV y.2)
  have hfix : ∀ y : B, act i e (c y) = c y := fun y =>
    (hF.comm_nf_vec_iff hn1 q (c y) i e).1 (by rw [hc y]; exact hB y y.2)
  let f : B → ZMod (2 ^ n) × {z : ZMod (2 ^ n) // z + z = 0} :=
    fun y => (ψ (c y), ⟨φ (c y), hφ _ (hfix y)⟩)
  have hf : Function.Injective f := by
    intro y y' h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    have := hinj _ _ (hfix y) (hfix y') h.1 h.2
    apply Subtype.ext
    rw [← hc y, ← hc y', this]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_zmod, card_two_torsion hn1] at this

theorem weakly_closed [Finite G] (hn : 3 ≤ n) {g : G} (hg : ∀ v ∈ hF.V, g * v * g⁻¹ ∈ hF.P) :
    ∀ v ∈ hF.V, g * v * g⁻¹ ∈ hF.V := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hgv⟩ := hcon
  set A := hF.V.map (MulAut.conj g).toMonoidHom with hA
  have hAP : A ≤ hF.P := by
    rintro _ ⟨u, hu, rfl⟩
    exact hg u hu
  have hB : ∀ y ∈ hF.V ⊓ A, g * v * g⁻¹ * y = y * (g * v * g⁻¹) := by
    rintro y ⟨-, u, hu, rfl⟩
    show g * v * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * v * g⁻¹)
    rw [show g * v * g⁻¹ * (g * u * g⁻¹) = g * (v * u) * g⁻¹ by group, hF.V_comm hn1 hv hu]
    group
  have h1 := hF.card_le_of_comm hn2 (hg v hv) hgv inf_le_left hB
  have hVP := relIndex_mul_card (H := hF.V) (K := hF.P)
  rw [inf_of_le_left hF.V_le_P] at hVP
  have hPV := hF.card_P_le hn1
  have hVpos : 0 < Nat.card hF.V := Nat.card_pos
  have hidx : hF.V.relIndex hF.P ≤ 8 := by
    by_contra h
    push Not at h
    have : 9 * Nat.card hF.V ≤ hF.V.relIndex hF.P * Nat.card hF.V := Nat.mul_le_mul_right _ h
    omega
  have hidx0 : hF.V.relIndex hF.P ≠ 0 := by
    intro h
    rw [h, zero_mul] at hVP
    exact (Nat.card_pos (α := hF.P)).ne' hVP.symm
  have hAidx := relIndex_le_of_le_right hAP hidx0
  have hAc := relIndex_mul_card (H := hF.V) (K := A)
  have hcardA : Nat.card A = 2 ^ (3 * n) := by
    rw [hA, card_map_of_injective (MulAut.conj g).injective, hF.card_V]
  have hle : 2 ^ (3 * n) ≤ 2 ^ (n + 4) := by
    rw [← hcardA, ← hAc, pow_add]
    calc hF.V.relIndex A * Nat.card ↥(hF.V ⊓ A) ≤ 8 * (2 ^ n * 2) :=
          Nat.mul_le_mul (hAidx.trans hidx) h1
      _ = 2 ^ n * 2 ^ 4 := by ring
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  omega

end AlperinFrame

end CFSG.OddStandard.ONan76
