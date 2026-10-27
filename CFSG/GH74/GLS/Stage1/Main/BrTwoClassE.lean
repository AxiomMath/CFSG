module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassI
public import CFSG.GH74.GLS.Stage1.Main.BrIndex
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG
open scoped Pointwise

section Lift

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

theorem exists_invol_pow (hN : Odd (Nat.card N)) {k : X}
    (hkk : (QuotientGroup.mk k : X ⧸ N) * QuotientGroup.mk k = 1) (hk1 : (QuotientGroup.mk k : X ⧸ N) ≠ 1) :
    ∃ u ∈ zpowers k, orderOf u = 2 ∧ (QuotientGroup.mk u : X ⧸ N) = QuotientGroup.mk k := by
  have hkk' : k * k ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hkk
  have hodd : Odd (orderOf (k * k)) := odd_orderOf_of_mem_odd hN hkk'
  have hbar : orderOf (QuotientGroup.mk' N k) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      exact hkk
    · exact hk1
  have h2k : 2 ∣ orderOf k := by
    have := orderOf_map_dvd (QuotientGroup.mk' N) k
    rw [hbar] at this
    exact this
  obtain ⟨m, hm⟩ := h2k
  have hkpos : 0 < orderOf k := orderOf_pos k
  have hm0 : 0 < m := by omega
  have hkk'' : orderOf (k * k) = m := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) ⟨m, hm⟩, hm]
    omega
  have hmodd : Odd m := hkk'' ▸ hodd
  have hmd : m ∣ orderOf k := ⟨2, by omega⟩
  refine ⟨k ^ m, ?_, ?_, ?_⟩
  · rw [← zpow_natCast]
    exact zpow_mem_zpowers k _
  · rw [orderOf_pow_of_dvd hm0.ne' hmd, hm]
    exact Nat.mul_div_cancel 2 hm0
  · rw [QuotientGroup.mk_pow]
    obtain ⟨c, hc⟩ := hmodd
    rw [hc, pow_succ, pow_mul, sq, hkk, one_pow, one_mul]

omit [Finite X] in
theorem exists_cent_lift (hN : Odd (Nat.card N)) {Y : Subgroup X} {τ y : X} (hτY : τ ∈ Y)
    (hyY : y ∈ Y) (hτ : τ * τ = 1)
    (h : (QuotientGroup.mk τ : X ⧸ N) * QuotientGroup.mk y = QuotientGroup.mk y * QuotientGroup.mk τ) :
    ∃ n ∈ N ⊓ Y, n * y ∈ centralizer ({τ} : Set X) := by
  have hb : (y * τ * y⁻¹) * (y * τ * y⁻¹) = 1 := by
    calc (y * τ * y⁻¹) * (y * τ * y⁻¹) = y * (τ * τ) * y⁻¹ := by group
      _ = 1 := by rw [hτ]; group
  have hbY : y * τ * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hyY hτY) (Y.inv_mem hyY)
  have hab : τ * (y * τ * y⁻¹) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    have e1 : (QuotientGroup.mk (τ * (y * τ * y⁻¹)) : X ⧸ N) =
        QuotientGroup.mk τ * (QuotientGroup.mk y * QuotientGroup.mk τ * (QuotientGroup.mk y)⁻¹) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [e1, ← h]
    calc (QuotientGroup.mk τ : X ⧸ N) * (QuotientGroup.mk τ * QuotientGroup.mk y *
        (QuotientGroup.mk y)⁻¹) = QuotientGroup.mk τ * QuotientGroup.mk τ := by group
      _ = 1 := by rw [← QuotientGroup.mk_mul, hτ]; rfl
  obtain ⟨g, hg, hgτ⟩ := exists_odd_conj hτ hb (odd_orderOf_of_mem_odd hN hab)
  have hgN : g ∈ N := (Subgroup.zpowers_le.2 hab) hg
  have hgY : g ∈ Y := (Subgroup.zpowers_le.2 (Y.mul_mem hτY hbY)) hg
  refine ⟨g⁻¹, ⟨N.inv_mem hgN, Y.inv_mem hgY⟩, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e : g⁻¹ * y * τ * (g⁻¹ * y)⁻¹ = τ := by
    calc g⁻¹ * y * τ * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * τ * y⁻¹) * g := by group
      _ = g⁻¹ * (g * τ * g⁻¹) * g := by rw [hgτ]
      _ = τ := by group
  calc g⁻¹ * y * τ = (g⁻¹ * y * τ * (g⁻¹ * y)⁻¹) * (g⁻¹ * y) := by group
    _ = τ * (g⁻¹ * y) := by rw [e]

end Lift

section Four

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

theorem four_of_invols {u₁ u₂ : X} (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1) (hc : u₁ * u₂ = u₂ * u₁)
    (h1' : u₁ ≠ 1) (h2' : u₂ ≠ 1) (h12 : u₁ ≠ u₂) :
    (∀ v ∈ zpowers u₁ ⊔ zpowers u₂, v = 1 ∨ v = u₁ ∨ v = u₂ ∨ v = u₁ * u₂) ∧
      (∀ v ∈ zpowers u₁ ⊔ zpowers u₂, v * v = 1) ∧
      IsElementaryAbelian 2 ↥(zpowers u₁ ⊔ zpowers u₂) ∧
      Nat.card ↥(zpowers u₁ ⊔ zpowers u₂) = 4 := by
  classical
  have hcomm : ∀ a ∈ zpowers u₁, ∀ b ∈ zpowers u₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute u₁ u₂ from hc) k m).eq
  have hmem : ∀ v ∈ zpowers u₁ ⊔ zpowers u₂, v = 1 ∨ v = u₁ ∨ v = u₂ ∨ v = u₁ * u₂ := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hv
    rcases eq_one_or_eq_of_mem_zpowers_sq h1 ha with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers_sq h2 hb with rfl | rfl
    · left
      simp
    · right
      right
      left
      simp
    · right
      left
      simp
    · right
      right
      right
      rfl
  have hsq : ∀ v ∈ zpowers u₁ ⊔ zpowers u₂, v * v = 1 := by
    intro v hv
    rcases hmem v hv with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      exact h1
    · rw [h]
      exact h2
    · rw [h]
      calc u₁ * u₂ * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
        _ = u₁ * (u₁ * u₂) * u₂ := by rw [hc]
        _ = (u₁ * u₁) * (u₂ * u₂) := by group
        _ = 1 := by rw [h1, h2, one_mul]
  have hcommV : ∀ a ∈ zpowers u₁ ⊔ zpowers u₂, ∀ b ∈ zpowers u₁ ⊔ zpowers u₂, a * b = b * a := by
    intro a ha b hb
    have hab := hsq (a * b) (Subgroup.mul_mem _ ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    rw [mul_inv_rev, ha', hb'] at this
    exact this.symm
  refine ⟨hmem, hsq, ?_, ?_⟩
  · exact
      { is_comm := ⟨fun x y => Subtype.ext (hcommV x x.2 y y.2)⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one]; exact hsq x x.2) }
  · have hle := card_sup_zpowers_le_four h1 h2 hc
    have hsub : (({1, u₁, u₂, u₁ * u₂} : Finset X) : Set X) ⊆
        ((zpowers u₁ ⊔ zpowers u₂ : Subgroup X) : Set X) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_sup_left (mem_zpowers _)
      · rw [h]
        exact Subgroup.mem_sup_right (mem_zpowers _)
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers _))
          (Subgroup.mem_sup_right (mem_zpowers _))
    have n1 : (1 : X) ∉ ({u₁, u₂, u₁ * u₂} : Finset X) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨h1'.symm, h2'.symm, ?_⟩
      intro h
      apply h12
      calc u₁ = u₁ * (u₂ * u₂) := by rw [h2, mul_one]
        _ = (u₁ * u₂) * u₂ := by rw [mul_assoc]
        _ = u₂ := by rw [← h, one_mul]
    have n2 : u₁ ∉ ({u₂, u₁ * u₂} : Finset X) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨h12, ?_⟩
      intro h
      apply h2'
      exact mul_left_cancel (a := u₁) (by rw [mul_one]; exact h.symm)
    have n3 : u₂ ∉ ({u₁ * u₂} : Finset X) := by
      simp only [Finset.mem_singleton]
      intro h
      apply h1'
      exact mul_right_cancel (b := u₂) (by rw [one_mul]; exact h.symm)
    have hcard4 : ({1, u₁, u₂, u₁ * u₂} : Finset X).card = 4 := by
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
        Finset.card_insert_of_notMem n3, Finset.card_singleton]
    have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hcard4] at h5
    have h6 : Nat.card ↥(zpowers u₁ ⊔ zpowers u₂) =
        ((zpowers u₁ ⊔ zpowers u₂ : Subgroup X) : Set X).ncard := Nat.card_coe_set_eq _
    omega

end Four

section Frattini

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

theorem isSylowOf_sup_of_inf_eq_bot (hN : Odd (Nat.card N)) {P : Subgroup X} (hP : IsPGroup 2 ↥P)
    (hPN : P ⊓ N = ⊥) : CFSG.ABGLocalTools.IsSylowOf 2 P (N ⊔ P) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_right, hP, ?_⟩
  rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N P, ← Subgroup.inf_relIndex_right, hPN,
    Subgroup.relIndex_bot_left]
  intro hdvd
  have := (Nat.odd_iff.1 hN)
  omega

theorem exists_lift_four (hN : Odd (Nat.card N)) {τ : X} (hτ : τ * τ = 1) {v₁ v₂ w : X ⧸ N}
    (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1) (hc : v₁ * v₂ = v₂ * v₁) (h₁ : v₁ ≠ 1) (h₂ : v₂ ≠ 1)
    (h₁₂ : v₁ ≠ v₂) (hτ₁ : (QuotientGroup.mk τ : X ⧸ N) * v₁ = v₁ * QuotientGroup.mk τ)
    (hτ₂ : (QuotientGroup.mk τ : X ⧸ N) * v₂ = v₂ * QuotientGroup.mk τ)
    (hw₁ : w * v₁ * w⁻¹ = v₂) (hw₂ : w * v₂ * w⁻¹ = v₁ * v₂) :
    ∃ (V : Subgroup X) (ω : X), IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 4 ∧
      (∀ v ∈ V, τ * v = v * τ) ∧
      (∀ v ∈ V, (QuotientGroup.mk v : X ⧸ N) = 1 ∨ (QuotientGroup.mk v : X ⧸ N) = v₁ ∨
        (QuotientGroup.mk v : X ⧸ N) = v₂ ∨ (QuotientGroup.mk v : X ⧸ N) = v₁ * v₂) ∧
      (∀ v ∈ V, ω * v * ω⁻¹ ∈ V) ∧ (∃ v ∈ V, ω * v * ω⁻¹ ≠ v) ∧
      (∀ v ∈ V, ω ^ 3 * v * (ω ^ 3)⁻¹ = v) := by
  classical
  have hmk : ∀ n ∈ N, ∀ y : X, (QuotientGroup.mk (n * y) : X ⧸ N) = QuotientGroup.mk y := by
    intro n hn y
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective v₁
  obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective v₂
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨n₁, hn₁, hy₁c⟩ :=
    exists_cent_lift hN (Y := ⊤) (Subgroup.mem_top τ) (Subgroup.mem_top y₁) hτ hτ₁
  obtain ⟨u₁, hu₁mem, hu₁o, hu₁mk⟩ := exists_invol_pow hN (k := n₁ * y₁)
    (by rw [hmk _ hn₁.1]; exact hv₁) (by rw [hmk _ hn₁.1]; exact h₁)
  rw [hmk _ hn₁.1] at hu₁mk
  have hu₁c : u₁ ∈ centralizer ({τ} : Set X) := (Subgroup.zpowers_le.2 hy₁c) hu₁mem
  have hu₁sq : u₁ * u₁ = 1 := by
    have := pow_orderOf_eq_one u₁
    rwa [hu₁o, pow_two] at this
  obtain ⟨n₂, hn₂, hy₂c⟩ :=
    exists_cent_lift hN (Y := ⊤) (Subgroup.mem_top τ) (Subgroup.mem_top y₂) hτ hτ₂
  have hcom : (QuotientGroup.mk u₁ : X ⧸ N) * QuotientGroup.mk (n₂ * y₂) =
      QuotientGroup.mk (n₂ * y₂) * QuotientGroup.mk u₁ := by
    rw [hmk _ hn₂.1, hu₁mk]
    exact hc
  obtain ⟨n₃, hn₃, hy₂c'⟩ :=
    exists_cent_lift hN (Y := centralizer ({τ} : Set X)) hu₁c hy₂c hu₁sq hcom
  have hy₂Y : n₃ * (n₂ * y₂) ∈ centralizer ({τ} : Set X) :=
    (centralizer ({τ} : Set X)).mul_mem hn₃.2 hy₂c
  have hmk2 : (QuotientGroup.mk (n₃ * (n₂ * y₂)) : X ⧸ N) = QuotientGroup.mk y₂ := by
    rw [hmk _ hn₃.1, hmk _ hn₂.1]
  obtain ⟨u₂, hu₂mem, hu₂o, hu₂mk⟩ := exists_invol_pow hN (k := n₃ * (n₂ * y₂))
    (by rw [hmk2]; exact hv₂) (by rw [hmk2]; exact h₂)
  rw [hmk2] at hu₂mk
  have hu₂τ : u₂ ∈ centralizer ({τ} : Set X) := (Subgroup.zpowers_le.2 hy₂Y) hu₂mem
  have hu₂u₁ : u₂ ∈ centralizer ({u₁} : Set X) := (Subgroup.zpowers_le.2 hy₂c') hu₂mem
  have hu₂sq : u₂ * u₂ = 1 := by
    have := pow_orderOf_eq_one u₂
    rwa [hu₂o, pow_two] at this
  have hu₁1 : u₁ ≠ 1 := fun h => h₁ (by rw [← hu₁mk, h]; rfl)
  have hu₂1 : u₂ ≠ 1 := fun h => h₂ (by rw [← hu₂mk, h]; rfl)
  have hu₁₂ : u₁ ≠ u₂ := fun h => h₁₂ (by rw [← hu₁mk, ← hu₂mk, h])
  have hcu : u₁ * u₂ = u₂ * u₁ := (Subgroup.mem_centralizer_singleton_iff.1 hu₂u₁).symm
  obtain ⟨hmem4, hsq, hea, hcard⟩ := four_of_invols hu₁sq hu₂sq hcu hu₁1 hu₂1 hu₁₂
  set V : Subgroup X := zpowers u₁ ⊔ zpowers u₂ with hV
  have hu₁V : u₁ ∈ V := Subgroup.mem_sup_left (mem_zpowers _)
  have hu₂V : u₂ ∈ V := Subgroup.mem_sup_right (mem_zpowers _)
  have hVτ : V ≤ centralizer ({τ} : Set X) :=
    sup_le (Subgroup.zpowers_le.2 hu₁c) (Subgroup.zpowers_le.2 hu₂τ)
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have hab := hsq (a * b) (V.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    rw [mul_inv_rev, ha', hb'] at this
    exact this.symm
  have hP : ∀ v ∈ V, (QuotientGroup.mk v : X ⧸ N) = 1 ∨ (QuotientGroup.mk v : X ⧸ N) = QuotientGroup.mk y₁ ∨
      (QuotientGroup.mk v : X ⧸ N) = QuotientGroup.mk y₂ ∨
      (QuotientGroup.mk v : X ⧸ N) = QuotientGroup.mk y₁ * QuotientGroup.mk y₂ := by
    intro v hv
    rcases hmem4 v hv with h | h | h | h
    · left
      rw [h]
      rfl
    · right; left
      rw [h, hu₁mk]
    · right; right; left
      rw [h, hu₂mk]
    · right; right; right
      rw [h, QuotientGroup.mk_mul, hu₁mk, hu₂mk]
  have hsurjP : ∀ c : X ⧸ N, (c = 1 ∨ c = QuotientGroup.mk y₁ ∨ c = QuotientGroup.mk y₂ ∨
      c = QuotientGroup.mk y₁ * QuotientGroup.mk y₂) → ∃ v ∈ V, (QuotientGroup.mk v : X ⧸ N) = c := by
    intro c hc'
    rcases hc' with h | h | h | h
    · exact ⟨1, V.one_mem, by rw [h]; rfl⟩
    · exact ⟨u₁, hu₁V, by rw [h, hu₁mk]⟩
    · exact ⟨u₂, hu₂V, by rw [h, hu₂mk]⟩
    · exact ⟨u₁ * u₂, V.mul_mem hu₁V hu₂V, by rw [h, QuotientGroup.mk_mul, hu₁mk, hu₂mk]⟩
  have hinj : ∀ a ∈ V, ∀ b ∈ V, (QuotientGroup.mk a : X ⧸ N) = QuotientGroup.mk b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hab]
      group
    have hsq' : (a⁻¹ * b) * (a⁻¹ * b) = 1 := hsq _ (V.mul_mem (V.inv_mem ha) hb)
    have := eq_one_of_mul_self_of_mem_odd hN hmem hsq'
    calc a = a * (a⁻¹ * b) := by rw [this, mul_one]
      _ = b := by group
  have hc' : (QuotientGroup.mk y₂ : X ⧸ N) * QuotientGroup.mk y₁ = QuotientGroup.mk y₁ * QuotientGroup.mk y₂ :=
    hc.symm
  have hw₃ : (QuotientGroup.mk x : X ⧸ N) * (QuotientGroup.mk y₁ * QuotientGroup.mk y₂) *
      (QuotientGroup.mk x)⁻¹ = QuotientGroup.mk y₁ := by
    calc (QuotientGroup.mk x : X ⧸ N) * (QuotientGroup.mk y₁ * QuotientGroup.mk y₂) * (QuotientGroup.mk x)⁻¹
        = ((QuotientGroup.mk x) * QuotientGroup.mk y₁ * (QuotientGroup.mk x)⁻¹) *
          ((QuotientGroup.mk x) * QuotientGroup.mk y₂ * (QuotientGroup.mk x)⁻¹) := by group
      _ = QuotientGroup.mk y₂ * (QuotientGroup.mk y₁ * QuotientGroup.mk y₂) := by rw [hw₁, hw₂]
      _ = (QuotientGroup.mk y₂ * QuotientGroup.mk y₁) * QuotientGroup.mk y₂ := by rw [mul_assoc]
      _ = (QuotientGroup.mk y₁ * QuotientGroup.mk y₂) * QuotientGroup.mk y₂ := by rw [hc']
      _ = QuotientGroup.mk y₁ * (QuotientGroup.mk y₂ * QuotientGroup.mk y₂) := by rw [mul_assoc]
      _ = QuotientGroup.mk y₁ := by rw [hv₂, mul_one]
  have hconjP : ∀ c : X ⧸ N, (c = 1 ∨ c = QuotientGroup.mk y₁ ∨ c = QuotientGroup.mk y₂ ∨
      c = QuotientGroup.mk y₁ * QuotientGroup.mk y₂) →
      ((QuotientGroup.mk x : X ⧸ N) * c * (QuotientGroup.mk x)⁻¹ = 1 ∨
        (QuotientGroup.mk x : X ⧸ N) * c * (QuotientGroup.mk x)⁻¹ = QuotientGroup.mk y₁ ∨
        (QuotientGroup.mk x : X ⧸ N) * c * (QuotientGroup.mk x)⁻¹ = QuotientGroup.mk y₂ ∨
        (QuotientGroup.mk x : X ⧸ N) * c * (QuotientGroup.mk x)⁻¹ =
          QuotientGroup.mk y₁ * QuotientGroup.mk y₂) := by
    intro c hc''
    rcases hc'' with h | h | h | h
    · left; rw [h]; group
    · right; right; left; rw [h, hw₁]
    · right; right; right; rw [h, hw₂]
    · right; left; rw [h, hw₃]
  have hconjP' : ∀ c : X ⧸ N, (c = 1 ∨ c = QuotientGroup.mk y₁ ∨ c = QuotientGroup.mk y₂ ∨
      c = QuotientGroup.mk y₁ * QuotientGroup.mk y₂) →
      ∃ c' : X ⧸ N, (c' = 1 ∨ c' = QuotientGroup.mk y₁ ∨ c' = QuotientGroup.mk y₂ ∨
        c' = QuotientGroup.mk y₁ * QuotientGroup.mk y₂) ∧ (QuotientGroup.mk x : X ⧸ N) * c' *
          (QuotientGroup.mk x)⁻¹ = c := by
    intro c hc''
    rcases hc'' with h | h | h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; group⟩
    · exact ⟨QuotientGroup.mk y₁ * QuotientGroup.mk y₂, Or.inr (Or.inr (Or.inr rfl)), by rw [h, hw₃]⟩
    · exact ⟨QuotientGroup.mk y₁, Or.inr (Or.inl rfl), by rw [h, hw₁]⟩
    · exact ⟨QuotientGroup.mk y₂, Or.inr (Or.inr (Or.inl rfl)), by rw [h, hw₂]⟩
  have hconj3 : ∀ c : X ⧸ N, (c = 1 ∨ c = QuotientGroup.mk y₁ ∨ c = QuotientGroup.mk y₂ ∨
      c = QuotientGroup.mk y₁ * QuotientGroup.mk y₂) →
      (QuotientGroup.mk x : X ⧸ N) * ((QuotientGroup.mk x) * ((QuotientGroup.mk x) * c *
        (QuotientGroup.mk x)⁻¹) * (QuotientGroup.mk x)⁻¹) * (QuotientGroup.mk x)⁻¹ = c := by
    intro c hc''
    rcases hc'' with h | h | h | h
    · rw [h]; group
    · rw [h, hw₁, hw₂, hw₃]
    · rw [h, hw₂, hw₃, hw₁]
    · rw [h, hw₃, hw₁, hw₂]
  have hVN : V ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : (QuotientGroup.mk a : X ⧸ N) = QuotientGroup.mk 1 := by
      rw [(QuotientGroup.eq_one_iff a).2 ha.2]
      rfl
    exact Subgroup.mem_bot.2 (hinj a ha.1 1 V.one_mem h1)
  have hPV : IsPGroup 2 ↥V := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  set V' : Subgroup X := V.map (MulAut.conj x).toMonoidHom with hV'
  have hPV' : IsPGroup 2 ↥V' := hPV.map (MulAut.conj x).toMonoidHom
  have hV'N : V' ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, haN⟩
    have haN' : a ∈ N := by
      have h := (inferInstance : N.Normal).conj_mem _ haN x⁻¹
      have e : x⁻¹ * (MulAut.conj x).toMonoidHom a * x⁻¹⁻¹ = a := by
        show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a
        group
      rw [e] at h
      exact h
    have : a = 1 := Subgroup.mem_bot.1 (hVN ▸ (⟨ha, haN'⟩ : a ∈ V ⊓ N))
    rw [this]
    simp
  have hxmk : ∀ a : X, (QuotientGroup.mk ((MulAut.conj x).toMonoidHom a) : X ⧸ N) =
      QuotientGroup.mk x * QuotientGroup.mk a * (QuotientGroup.mk x)⁻¹ := by
    intro a
    simp [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hV'M : V' ≤ N ⊔ V := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbm⟩ := hsurjP _ (hconjP _ (hP a ha))
    have hbm' : (QuotientGroup.mk b : X ⧸ N) = QuotientGroup.mk ((MulAut.conj x).toMonoidHom a) := by
      rw [hbm, hxmk]
    have hn : (MulAut.conj x).toMonoidHom a * b⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hbm']
      group
    have : (MulAut.conj x).toMonoidHom a = ((MulAut.conj x).toMonoidHom a * b⁻¹) * b := by group
    rw [this]
    exact Subgroup.mul_mem_sup hn hb
  have hVV' : V ≤ N ⊔ V' := by
    intro b hb
    obtain ⟨c', hc'P, hc'e⟩ := hconjP' _ (hP b hb)
    obtain ⟨b'', hb'', hb''m⟩ := hsurjP c' hc'P
    have hbm' : (QuotientGroup.mk ((MulAut.conj x).toMonoidHom b'') : X ⧸ N) = QuotientGroup.mk b := by
      rw [hxmk, hb''m, hc'e]
    have hn : b * ((MulAut.conj x).toMonoidHom b'')⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hbm']
      group
    have : b = (b * ((MulAut.conj x).toMonoidHom b'')⁻¹) * (MulAut.conj x).toMonoidHom b'' := by group
    rw [this]
    exact Subgroup.mul_mem_sup hn (⟨b'', hb'', rfl⟩ : (MulAut.conj x).toMonoidHom b'' ∈ V')
  have hMeq : N ⊔ V' = N ⊔ V := le_antisymm (sup_le le_sup_left hV'M) (sup_le le_sup_left hVV')
  have hSV : CFSG.ABGLocalTools.IsSylowOf 2 V (N ⊔ V) := isSylowOf_sup_of_inf_eq_bot hN hPV hVN
  have hSV' : CFSG.ABGLocalTools.IsSylowOf 2 V' (N ⊔ V) := by
    rw [← hMeq]
    exact isSylowOf_sup_of_inf_eq_bot hN hPV' hV'N
  obtain ⟨m, hmM, hm⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hSV hSV'
  have hmap : (N ⊔ V).map (QuotientGroup.mk' N) = V.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  obtain ⟨b₀, hb₀, hb₀m⟩ : ∃ b₀ ∈ V, (QuotientGroup.mk b₀ : X ⧸ N) = QuotientGroup.mk m := by
    have : QuotientGroup.mk' N m ∈ (N ⊔ V).map (QuotientGroup.mk' N) := ⟨m, hmM, rfl⟩
    rw [hmap] at this
    obtain ⟨b, hb, hbm⟩ := this
    exact ⟨b, hb, hbm⟩
  have hnorm : ∀ v ∈ V, m⁻¹ * (x * v * x⁻¹) * m ∈ V := by
    intro v hv
    exact (hm (x * v * x⁻¹)).1 ⟨v, hv, by simp [MulAut.conj_apply]⟩
  have hωmk : ∀ v ∈ V, (QuotientGroup.mk (m⁻¹ * x * v * (m⁻¹ * x)⁻¹) : X ⧸ N) =
      QuotientGroup.mk x * QuotientGroup.mk v * (QuotientGroup.mk x)⁻¹ := by
    intro v hv
    obtain ⟨b, hb, hbm⟩ := hsurjP _ (hconjP _ (hP v hv))
    have e1 : (QuotientGroup.mk (m⁻¹ * x * v * (m⁻¹ * x)⁻¹) : X ⧸ N) =
        (QuotientGroup.mk b₀)⁻¹ * (QuotientGroup.mk x * QuotientGroup.mk v * (QuotientGroup.mk x)⁻¹) *
          QuotientGroup.mk b₀ := by
      rw [hb₀m]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_rev, inv_inv]
      group
    rw [e1, ← hbm]
    have : b₀⁻¹ * b * b₀ = b := by
      have := hcommV b₀ hb₀ b hb
      calc b₀⁻¹ * b * b₀ = b₀⁻¹ * (b * b₀) := by group
        _ = b₀⁻¹ * (b₀ * b) := by rw [this.symm]
        _ = b := by group
    calc (QuotientGroup.mk b₀ : X ⧸ N)⁻¹ * QuotientGroup.mk b * QuotientGroup.mk b₀
        = QuotientGroup.mk (b₀⁻¹ * b * b₀) := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = QuotientGroup.mk b := by rw [this]
  refine ⟨V, m⁻¹ * x, hea, hcard, fun v hv => ?_, hP, fun v hv => ?_, ?_, ?_⟩
  · exact (Subgroup.mem_centralizer_singleton_iff.1 (hVτ hv)).symm
  · have := hnorm v hv
    have e : m⁻¹ * x * v * (m⁻¹ * x)⁻¹ = m⁻¹ * (x * v * x⁻¹) * m := by group
    rw [e]
    exact this
  · refine ⟨u₁, hu₁V, fun h => ?_⟩
    have h1 := hωmk u₁ hu₁V
    rw [h, hu₁mk, hw₁] at h1
    exact h₁₂ h1
  · intro v hv
    have step : ∀ a ∈ V, m⁻¹ * x * a * (m⁻¹ * x)⁻¹ ∈ V := by
      intro a ha
      have := hnorm a ha
      have e : m⁻¹ * x * a * (m⁻¹ * x)⁻¹ = m⁻¹ * (x * a * x⁻¹) * m := by group
      rw [e]
      exact this
    set ω : X := m⁻¹ * x with hω
    have h1 := step v hv
    have h2 := step _ h1
    have h3 := step _ h2
    have e3 : ω ^ 3 * v * (ω ^ 3)⁻¹ = ω * (ω * (ω * v * ω⁻¹) * ω⁻¹) * ω⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e3]
    apply hinj _ h3 v hv
    rw [hωmk _ h2, hωmk _ h1, hωmk v hv]
    exact hconj3 _ (hP v hv)

end Frattini

end CFSG.GH74.GLS.Stage1.Main
