module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB1
public import CFSG.CGT.Timmesfeld75.Sec3TenDelta

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_mem_of_index_two [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hcard : Nat.card B = Nat.card A * 2) {a : G}
    (haB : ∀ y ∈ B, a * y * a⁻¹ ∈ B) (haA : ∀ y ∈ A, a * y * a⁻¹ ∈ A)
    (haA' : ∀ y ∈ A, a⁻¹ * y * a ∈ A) {y : G} (hy : y ∈ B) : a * y * a⁻¹ * y⁻¹ ∈ A := by
  have hidx : (A.subgroupOf B).index = 2 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hcard)
  by_cases hyA : y ∈ A
  · exact A.mul_mem (haA y hyA) (A.inv_mem hyA)
  · have hy' : (⟨y, hy⟩ : B) ∉ A.subgroupOf B := hyA
    have hay : (⟨a * y * a⁻¹, haB y hy⟩ : B) ∉ A.subgroupOf B := by
      intro h
      apply hyA
      have := haA' _ h
      simpa [mul_assoc] using this
    have hyinv : (⟨y, hy⟩ : B)⁻¹ ∉ A.subgroupOf B := fun h => hy' (by simpa using inv_mem h)
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a * y * a⁻¹, haB y hy⟩)
      (b := (⟨y, hy⟩ : B)⁻¹)).2 (iff_of_false hay hyinv)
    exact key

theorem commutator_mem_sup {M T T₁ : Subgroup G} {κ : G}
    (hTM : T ≤ Subgroup.normalizer (M : Set G)) (hT₁M : T₁ ≤ Subgroup.normalizer (M : Set G))
    (hT : ∀ x ∈ T, κ * x * κ⁻¹ * x⁻¹ ∈ M) (hT₁ : ∀ x ∈ T₁, κ * x * κ⁻¹ * x⁻¹ ∈ M) :
    ∀ x ∈ T ⊔ T₁, κ * x * κ⁻¹ * x⁻¹ ∈ M := by
  let Y : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (M : Set G) ∧ κ * x * κ⁻¹ * x⁻¹ ∈ M}
      one_mem' := ⟨(Subgroup.normalizer _).one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨(Subgroup.normalizer _).mul_mem hxN hyN, ?_⟩
        have h1 := conj_mem_of_mem_normalizer hxN hy
        have e : κ * (x * y) * κ⁻¹ * (x * y)⁻¹ =
            (κ * x * κ⁻¹ * x⁻¹) * (x * (κ * y * κ⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact M.mul_mem hx h1
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        refine ⟨(Subgroup.normalizer _).inv_mem hxN, ?_⟩
        have h1 := conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hxN)
          (M.inv_mem hx)
        have e : κ * x⁻¹ * κ⁻¹ * x⁻¹⁻¹ = x⁻¹ * (κ * x * κ⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact h1 }
  have hTY : T ≤ Y := fun x hx => ⟨hTM hx, hT x hx⟩
  have hT₁Y : T₁ ≤ Y := fun x hx => ⟨hT₁M hx, hT₁ x hx⟩
  intro x hx
  exact (sup_le hTY hT₁Y hx).2

variable {T T₁ : Subgroup G}

theorem Sec3.false_of_conj_eq [Finite G] (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n) (hn3 : 3 < n)
    (hD : Sec3Dih T T₁ n) {a : G} (haN : a ∈ Subgroup.normalizer (T : Set G))
    (haT₁ : conjSubgroup a T₁ = T₁) (haL : ∀ t ∈ T, ⁅t, a⁆ ∈ normIn T T₁) {u : G}
    (hu : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u) (hnc : ∃ l ∈ normIn T T₁, a * l ≠ l * a) : False := by
  obtain ⟨hN, ⟨e⟩⟩ := hD
  have haT : conjSubgroup a T = T := mem_normalizer_iff_conjSubgroup_eq.1 haN
  have haN₁ : a ∈ Subgroup.normalizer (T₁ : Set G) := mem_normalizer_of_conjSubgroup_eq haT₁
  have hLa : conjSubgroup a (normIn T T₁) = normIn T T₁ := by
    have := normIn_conj a T T₁
    rw [haT, haT₁] at this
    exact this.symm
  have hL₁a : conjSubgroup a (normIn T₁ T) = normIn T₁ T := by
    have := normIn_conj a T₁ T
    rw [haT, haT₁] at this
    exact this.symm
  have hMa : conjSubgroup a (cfgM T T₁) = cfgM T T₁ := by
    have := cfgM_conj a T T₁
    rw [haT, haT₁] at this
    exact this.symm
  have haM : a ∈ Subgroup.normalizer (cfgM T T₁ : Set G) := mem_normalizer_of_conjSubgroup_eq hMa
  have haL₁N : a ∈ Subgroup.normalizer (normIn T₁ T : Set G) :=
    mem_normalizer_of_conjSubgroup_eq hL₁a
  have hκM : ∀ m ∈ cfgM T T₁, a * m * a⁻¹ ∈ cfgM T T₁ := fun m hm =>
    conj_mem_of_mem_normalizer haM hm
  have hTM : T ≤ Subgroup.normalizer (cfgM T T₁ : Set G) :=
    le_sup_left.trans hS.cfg.le_normalizer_cfgM
  have hT₁M : T₁ ≤ Subgroup.normalizer (cfgM T T₁ : Set G) :=
    le_sup_right.trans hS.cfg.le_normalizer_cfgM
  have hcard₁ : Nat.card T₁ = Nat.card (normIn T₁ T) * 2 := by
    obtain ⟨x₀, -, hx₀⟩ := hS.conj
    have h1 : Nat.card T₁ = Nat.card T := by rw [hx₀, card_conjSubgroup]
    have h2 : Nat.card (normIn T₁ T) = Nat.card (normIn T T₁) := hS.card_normIn_swap
    rw [h1, h2, hS.card_eq_two_mul_dihedral hn e]
  have hT : ∀ x ∈ T, a * x * a⁻¹ * x⁻¹ ∈ cfgM T T₁ := by
    intro x hx
    have h1 : (⁅x, a⁆)⁻¹ ∈ normIn T T₁ := (normIn T T₁).inv_mem (haL x hx)
    have e1 : a * x * a⁻¹ * x⁻¹ = (⁅x, a⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact Cfg.normIn_le_cfgM_left T T₁ h1
  have hT₁ : ∀ x ∈ T₁, a * x * a⁻¹ * x⁻¹ ∈ cfgM T T₁ := by
    intro x hx
    have := commutator_mem_of_index_two (normIn_le T₁ T) hcard₁
      (fun y hy => conj_mem_of_mem_normalizer haN₁ hy)
      (fun y hy => conj_mem_of_mem_normalizer haL₁N hy)
      (fun y hy => by
        simpa using conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem haL₁N) hy) hx
    exact Cfg.normIn_le_cfgM_right T T₁ this
  have hκX := commutator_mem_sup hTM hT₁M hT hT₁
  have hu' : ∀ l ∈ normIn T T₁, a * l * a⁻¹ * l⁻¹ = 1 ∨ a * l * a⁻¹ * l⁻¹ = u⁻¹ := by
    intro l hl
    have e1 : a * l * a⁻¹ * l⁻¹ = (⁅l, a⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    rcases hu l (normIn_le T T₁ hl) with h | h
    · left
      rw [h, inv_one]
    · right
      rw [h]
  have hcent := hS.centralizes_of_delta hn hn3 e hκM hκX hu'
  obtain ⟨l, hl, hne⟩ := hnc
  apply hne
  have h1 := hcent l (Cfg.normIn_le_cfgM_left T T₁ hl)
  calc a * l = (a * l * a⁻¹) * a := by group
    _ = l * a := by rw [h1]

end CFSG.CGT.Timmesfeld75
