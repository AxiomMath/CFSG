module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP.Local

namespace WeightDecomp

variable {G : Type} [Group G]

theorem eq_one_of_comm_eq_one {H X : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hN : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hI : ∀ V : Subgroup G, V ≤ X → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = X)
    {h : G} (hh : h ∈ H) (hnc : h ∉ Subgroup.centralizer (X : Set G))
    {x : G} (hx : x ∈ X) (h1 : h * x * h⁻¹ * x⁻¹ = 1) : x = 1 := by
  have hinv : ∀ k ∈ H, ∀ v ∈ X ⊓ Subgroup.centralizer ({h} : Set G),
      k * v * k⁻¹ ∈ X ⊓ Subgroup.centralizer ({h} : Set G) := by
    intro k hk v hv
    have hhk : Commute h k := hH h hh k hk
    have hhv : Commute h v :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv).2).symm
    exact Subgroup.mem_inf.mpr ⟨hN k hk v (Subgroup.mem_inf.mp hv).1,
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((hhk.mul_right hhv).mul_right hhk.inv_right).eq.symm⟩
  rcases hI _ inf_le_left hinv with h0 | h0
  · have hxV : x ∈ X ⊓ Subgroup.centralizer ({h} : Set G) := by
      have e1 : h * x * h⁻¹ = x := mul_inv_eq_one.mp h1
      have e2 : h * x = x * h := mul_inv_eq_iff_eq_mul.mp e1
      exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr e2.symm⟩
    rw [h0] at hxV
    exact Subgroup.mem_bot.mp hxV
  · exfalso
    apply hnc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyV : y ∈ X ⊓ Subgroup.centralizer ({h} : Set G) := by rw [h0]; exact hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyV).2

theorem le_of_mem_ne_one {H X W : Subgroup G}
    (hN : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hI : ∀ V : Subgroup G, V ≤ X → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = X)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    {y : G} (hyX : y ∈ X) (hyW : y ∈ W) (hy1 : y ≠ 1) : X ≤ W := by
  rcases hI (X ⊓ W) inf_le_left (fun h hh v hv => ⟨hN h hh v hv.1, hW h hh v hv.2⟩) with h0 | h0
  · exfalso
    have hy : y ∈ X ⊓ W := ⟨hyX, hyW⟩
    rw [h0] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  · exact inf_eq_left.mp h0

theorem pair_dir {H P Q W : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a)
    (hN : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q)
    (hI : ∀ V : Subgroup G, V ≤ Q → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = Q)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    {h : G} (hh : h ∈ H) (hP : h ∈ Subgroup.centralizer (P : Set G))
    (hQ : h ∉ Subgroup.centralizer (Q : Set G)) :
    ∀ p ∈ P, ∀ q ∈ Q, p * q ∈ W → p ∈ W ∧ q ∈ W := by
  intro p hp q hq hpq
  by_cases hq1 : q = 1
  · subst hq1
    rw [mul_one] at hpq
    exact ⟨hpq, W.one_mem⟩
  · have hcQ : h * q * h⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hN h hh q hq) (Q.inv_mem hq)
    have hhp : Commute p h := Subgroup.mem_centralizer_iff.mp hP p hp
    have hpc : Commute p (h * q * h⁻¹ * q⁻¹) := hPQ p hp _ hcQ
    have hid : h * (p * q) * h⁻¹ * (p * q)⁻¹ = h * q * h⁻¹ * q⁻¹ := by
      calc h * (p * q) * h⁻¹ * (p * q)⁻¹
          = (h * p) * q * h⁻¹ * (q⁻¹ * p⁻¹) := by group
        _ = (p * h) * q * h⁻¹ * (q⁻¹ * p⁻¹) := by rw [← hhp.eq]
        _ = p * (h * q * h⁻¹ * q⁻¹) * p⁻¹ := by group
        _ = (h * q * h⁻¹ * q⁻¹) * p * p⁻¹ := by rw [hpc.eq]
        _ = h * q * h⁻¹ * q⁻¹ := by group
    have hcW : h * q * h⁻¹ * q⁻¹ ∈ W := by
      rw [← hid]
      exact W.mul_mem (hW h hh _ hpq) (W.inv_mem hpq)
    have hc1 : h * q * h⁻¹ * q⁻¹ ≠ 1 := fun h1 =>
      hq1 (eq_one_of_comm_eq_one hH hN hI hh hQ hq h1)
    have hqW : q ∈ W := le_of_mem_ne_one hN hI hW hcQ hcW hc1 hq
    refine ⟨?_, hqW⟩
    have := W.mul_mem hpq (W.inv_mem hqW)
    rwa [mul_inv_cancel_right] at this

theorem exists_mem_centralizer_diff {H P Q : Subgroup G}
    (hk : Subgroup.centralizer (P : Set G) ⊓ H ≠ Subgroup.centralizer (Q : Set G) ⊓ H) :
    ∃ g ∈ H, (g ∈ Subgroup.centralizer (P : Set G) ∧ g ∉ Subgroup.centralizer (Q : Set G)) ∨
      (g ∈ Subgroup.centralizer (Q : Set G) ∧ g ∉ Subgroup.centralizer (P : Set G)) := by
  by_contra hcon
  apply hk
  ext g
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h3
    exact hcon ⟨g, h2, Or.inl ⟨h1, h3⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h3
    exact hcon ⟨g, h2, Or.inr ⟨h1, h3⟩⟩

theorem pair_of_ne {H P Q W : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a)
    (hNP : ∀ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ P)
    (hNQ : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q)
    (hIP : ∀ V : Subgroup G, V ≤ P → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = P)
    (hIQ : ∀ V : Subgroup G, V ≤ Q → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = Q)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hk : Subgroup.centralizer (P : Set G) ⊓ H ≠ Subgroup.centralizer (Q : Set G) ⊓ H) :
    ∀ p ∈ P, ∀ q ∈ Q, p * q ∈ W → p ∈ W ∧ q ∈ W := by
  obtain ⟨g, hgH, ⟨hgP, hgQ⟩ | ⟨hgQ, hgP⟩⟩ := exists_mem_centralizer_diff hk
  · exact pair_dir hH hPQ hNQ hIQ hW hgH hgP hgQ
  · intro p hp q hq hpq
    have hpq' : q * p ∈ W := by rwa [← hPQ p hp q hq]
    obtain ⟨h1, h2⟩ := pair_dir hH (fun a ha b hb => (hPQ b hb a ha).symm) hNP hIP hW hgH hgQ hgP
      q hq p hp hpq'
    exact ⟨h2, h1⟩

theorem tri_dir {H A B C W : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hNB : ∀ h ∈ H, ∀ x ∈ B, h * x * h⁻¹ ∈ B)
    (hNC : ∀ h ∈ H, ∀ x ∈ C, h * x * h⁻¹ ∈ C)
    (hIB : ∀ V : Subgroup G, V ≤ B → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = B)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (pBC : ∀ b ∈ B, ∀ c ∈ C, b * c ∈ W → b ∈ W ∧ c ∈ W)
    (pAC : ∀ a ∈ A, ∀ c ∈ C, a * c ∈ W → a ∈ W ∧ c ∈ W)
    {h : G} (hh : h ∈ H) (hA : h ∈ Subgroup.centralizer (A : Set G))
    (hB : h ∉ Subgroup.centralizer (B : Set G)) :
    ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a * b * c ∈ W → a ∈ W ∧ b ∈ W ∧ c ∈ W := by
  have hAB' : ∀ a ∈ A, ∀ b ∈ B, Commute a b := hAB
  have hAC' : ∀ a ∈ A, ∀ c ∈ C, Commute a c := hAC
  have hBC' : ∀ b ∈ B, ∀ c ∈ C, Commute b c := hBC
  intro a ha b hb c hc habc
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one] at habc
    obtain ⟨h1, h2⟩ := pAC a ha c hc habc
    exact ⟨h1, W.one_mem, h2⟩
  · have hxB : h * b * h⁻¹ ∈ B := hNB h hh b hb
    have hyC : h * c * h⁻¹ ∈ C := hNC h hh c hc
    have hcB : h * b * h⁻¹ * b⁻¹ ∈ B := B.mul_mem hxB (B.inv_mem hb)
    have hcC : h * c * h⁻¹ * c⁻¹ ∈ C := C.mul_mem hyC (C.inv_mem hc)
    have hha : Commute a h := Subgroup.mem_centralizer_iff.mp hA a ha
    have hax : Commute a (h * b * h⁻¹) := hAB' a ha _ hxB
    have hay : Commute a (h * c * h⁻¹) := hAC' a ha _ hyC
    have hac : Commute a c⁻¹ := (hAC' a ha c hc).inv_right
    have hab : Commute a b⁻¹ := (hAB' a ha b hb).inv_right
    have hz : Commute a (h * b * h⁻¹ * (h * c * h⁻¹) * c⁻¹ * b⁻¹) :=
      ((hax.mul_right hay).mul_right hac).mul_right hab
    have hbyc : Commute b⁻¹ (h * c * h⁻¹ * c⁻¹) := (hBC' b hb _ hcC).inv_left
    have hid : h * (a * b * c) * h⁻¹ * (a * b * c)⁻¹
        = (h * b * h⁻¹ * b⁻¹) * (h * c * h⁻¹ * c⁻¹) := by
      have e0 : h * a * h⁻¹ = a := by
        calc h * a * h⁻¹ = a * h * h⁻¹ := by rw [← hha.eq]
          _ = a := by group
      have e1 : h * (a * b * c) * h⁻¹ = a * (h * b * h⁻¹) * (h * c * h⁻¹) := by
        calc h * (a * b * c) * h⁻¹
            = (h * a * h⁻¹) * (h * b * h⁻¹) * (h * c * h⁻¹) := by group
          _ = a * (h * b * h⁻¹) * (h * c * h⁻¹) := by rw [e0]
      calc h * (a * b * c) * h⁻¹ * (a * b * c)⁻¹
          = (a * (h * b * h⁻¹) * (h * c * h⁻¹)) * (c⁻¹ * b⁻¹ * a⁻¹) := by rw [e1]; group
        _ = a * (h * b * h⁻¹ * (h * c * h⁻¹) * c⁻¹ * b⁻¹) * a⁻¹ := by group
        _ = (h * b * h⁻¹ * (h * c * h⁻¹) * c⁻¹ * b⁻¹) * a * a⁻¹ := by rw [hz.eq]
        _ = (h * b * h⁻¹) * ((h * c * h⁻¹ * c⁻¹) * b⁻¹) := by group
        _ = (h * b * h⁻¹) * (b⁻¹ * (h * c * h⁻¹ * c⁻¹)) := by rw [← hbyc.eq]
        _ = (h * b * h⁻¹ * b⁻¹) * (h * c * h⁻¹ * c⁻¹) := by group
    have hW1 : (h * b * h⁻¹ * b⁻¹) * (h * c * h⁻¹ * c⁻¹) ∈ W := by
      rw [← hid]
      exact W.mul_mem (hW h hh _ habc) (W.inv_mem habc)
    obtain ⟨hcBW, -⟩ := pBC _ hcB _ hcC hW1
    have hcB1 : h * b * h⁻¹ * b⁻¹ ≠ 1 := fun h1 =>
      hb1 (eq_one_of_comm_eq_one hH hNB hIB hh hB hb h1)
    have hbW : b ∈ W := le_of_mem_ne_one hNB hIB hW hcB hcBW hcB1 hb
    have hbc : Commute b⁻¹ c := (hBC' b hb c hc).inv_left
    have hacW : a * c ∈ W := by
      have e : a * b * c * b⁻¹ = a * c := by
        calc a * b * c * b⁻¹ = a * b * (c * b⁻¹) := by group
          _ = a * b * (b⁻¹ * c) := by rw [← hbc.eq]
          _ = a * c := by group
      rw [← e]
      exact W.mul_mem habc (W.inv_mem hbW)
    obtain ⟨haW, hcW⟩ := pAC a ha c hc hacW
    exact ⟨haW, hbW, hcW⟩

theorem weight_decomp_core {H X₁ X₂ X₃ W : Subgroup G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (h₁₂ : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (h₁₃ : ∀ a ∈ X₁, ∀ b ∈ X₃, a * b = b * a)
    (h₂₃ : ∀ a ∈ X₂, ∀ b ∈ X₃, a * b = b * a)
    (hN₁ : ∀ h ∈ H, ∀ x ∈ X₁, h * x * h⁻¹ ∈ X₁) (hN₂ : ∀ h ∈ H, ∀ x ∈ X₂, h * x * h⁻¹ ∈ X₂)
    (hN₃ : ∀ h ∈ H, ∀ x ∈ X₃, h * x * h⁻¹ ∈ X₃)
    (hI₁ : ∀ V : Subgroup G, V ≤ X₁ → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = X₁)
    (hI₂ : ∀ V : Subgroup G, V ≤ X₂ → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = X₂)
    (hI₃ : ∀ V : Subgroup G, V ≤ X₃ → (∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) → V = ⊥ ∨ V = X₃)
    (hk₁₂ : Subgroup.centralizer (X₁ : Set G) ⊓ H ≠ Subgroup.centralizer (X₂ : Set G) ⊓ H)
    (hk₁₃ : Subgroup.centralizer (X₁ : Set G) ⊓ H ≠ Subgroup.centralizer (X₃ : Set G) ⊓ H)
    (hk₂₃ : Subgroup.centralizer (X₂ : Set G) ⊓ H ≠ Subgroup.centralizer (X₃ : Set G) ⊓ H)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W) :
    ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂, ∀ x₃ ∈ X₃, x₁ * x₂ * x₃ ∈ W → x₁ ∈ W ∧ x₂ ∈ W ∧ x₃ ∈ W := by
  have p13 := pair_of_ne hH h₁₃ hN₁ hN₃ hI₁ hI₃ hW hk₁₃
  have p23 := pair_of_ne hH h₂₃ hN₂ hN₃ hI₂ hI₃ hW hk₂₃
  obtain ⟨g, hgH, ⟨hg1, hg2⟩ | ⟨hg2, hg1⟩⟩ := exists_mem_centralizer_diff hk₁₂
  · exact tri_dir hH h₁₂ h₁₃ h₂₃ hN₂ hN₃ hI₂ hW p23 p13 hgH hg1 hg2
  · intro x₁ hx₁ x₂ hx₂ x₃ hx₃ h
    have h' : x₂ * x₁ * x₃ ∈ W := by rwa [← h₁₂ x₁ hx₁ x₂ hx₂]
    obtain ⟨a, b, c⟩ := tri_dir hH (fun a ha b hb => (h₁₂ b hb a ha).symm) h₂₃ h₁₃ hN₁ hN₃ hI₁ hW
      p13 p23 hgH hg2 hg1 x₂ hx₂ x₁ hx₁ x₃ hx₃ h'
    exact ⟨b, a, c⟩

end WeightDecomp

theorem direct_of_card {G : Type} [Group G] [Finite G] (R X₁ X₂ X₃ : Subgroup G)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (h₁ : X₁ ≤ R) (h₂ : X₂ ≤ R) (h₃ : X₃ ≤ R)
    (hgen : R ≤ X₁ ⊔ X₂ ⊔ X₃)
    (hcard : Nat.card ↥R = Nat.card ↥X₁ * Nat.card ↥X₂ * Nat.card ↥X₃) :
    (∀ r ∈ R, ∃ x₁ ∈ X₁, ∃ x₂ ∈ X₂, ∃ x₃ ∈ X₃, r = x₁ * x₂ * x₃) ∧
    (∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂, ∀ x₃ ∈ X₃, x₁ * x₂ * x₃ = 1 → x₁ = 1 ∧ x₂ = 1 ∧ x₃ = 1) := by
  have hc12 : ∀ (m : ↥X₁) (n : ↥X₂), Commute (X₁.subtype m) (X₂.subtype n) :=
    fun m n => hR m (h₁ m.2) n (h₂ n.2)
  let φ₁₂ : ↥X₁ × ↥X₂ →* G := X₁.subtype.noncommCoprod X₂.subtype hc12
  have hc3 : ∀ (m : ↥X₁ × ↥X₂) (n : ↥X₃), Commute (φ₁₂ m) (X₃.subtype n) := fun m n =>
    Commute.mul_left (hR _ (h₁ m.1.2) _ (h₃ n.2)) (hR _ (h₂ m.2.2) _ (h₃ n.2))
  let φ : (↥X₁ × ↥X₂) × ↥X₃ →* G := φ₁₂.noncommCoprod X₃.subtype hc3
  have e1 : φ₁₂.range = X₁ ⊔ X₂ := by
    rw [show φ₁₂ = X₁.subtype.noncommCoprod X₂.subtype hc12 from rfl,
      MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hrange : φ.range = X₁ ⊔ X₂ ⊔ X₃ := by
    rw [show φ = φ₁₂.noncommCoprod X₃.subtype hc3 from rfl, MonoidHom.noncommCoprod_range, e1,
      Subgroup.range_subtype]
  have hφval : ∀ (x₁ : ↥X₁) (x₂ : ↥X₂) (x₃ : ↥X₃),
      φ ((x₁, x₂), x₃) = (x₁ : G) * x₂ * x₃ := fun _ _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro r hr
    have hr' : r ∈ φ.range := by rw [hrange]; exact hgen hr
    obtain ⟨⟨⟨x₁, x₂⟩, x₃⟩, hx⟩ := hr'
    exact ⟨x₁, x₁.2, x₂, x₂.2, x₃, x₃.2, by rw [← hx, hφval]⟩
  · have hrange' : φ.range = R :=
      le_antisymm (by rw [hrange]; exact sup_le (sup_le h₁ h₂) h₃) (by rw [hrange]; exact hgen)
    have hcardle : Nat.card ((↥X₁ × ↥X₂) × ↥X₃) ≤ Nat.card ↥φ.range := by
      rw [hrange', Nat.card_prod, Nat.card_prod, hcard]
    have hbij := (MonoidHom.rangeRestrict_surjective φ).bijective_of_nat_card_le hcardle
    have hinj : Function.Injective φ := MonoidHom.rangeRestrict_injective_iff.mp hbij.1
    intro x₁ hx₁ x₂ hx₂ x₃ hx₃ h
    have key := (injective_iff_map_eq_one φ).mp hinj ((⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩), ⟨x₃, hx₃⟩)
      (by rw [hφval]; exact h)
    simp only [Prod.mk_eq_one] at key
    obtain ⟨⟨k₁, k₂⟩, k₃⟩ := key
    exact ⟨congrArg Subtype.val k₁, congrArg Subtype.val k₂, congrArg Subtype.val k₃⟩

end CFSG.GH74.GLS.SP.Local
