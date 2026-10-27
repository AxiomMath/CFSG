module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSwap
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenPerm
public import CFSG.Holt.H78.AltModelAut
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSevenWeakDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHer
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo.YOne

open Subgroup Equiv Equiv.Perm AltStdSec AltStdBal

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def moved (τ : Perm α) : Finset α := Finset.univ.filter fun x => τ x ≠ x

theorem mem_moved {τ : Perm α} {x : α} : x ∈ moved τ ↔ τ x ≠ x := by
  simp [moved]

omit [Fintype α] in
theorem apply_apply_of_mul_self {τ : Perm α} (hτ : τ * τ = 1) (x : α) : τ (τ x) = x := by
  simpa using congrArg (fun f : Perm α => f x) hτ

omit [Fintype α] [DecidableEq α] in
theorem apply_comm_of_mul_comm {g τ : Perm α} (hg : g * τ = τ * g) (x : α) :
    g (τ x) = τ (g x) := by
  simpa using congrArg (fun f : Perm α => f x) hg

theorem sq_apply_of_comm {τ g : Perm α} (hτ : τ * τ = 1) (hcard : (moved τ).card ≤ 4)
    (hg : g * τ = τ * g) {x : α} (hx : τ x ≠ x) : (g ^ 2) x = x ∨ (g ^ 2) x = τ x := by
  have hττ := apply_apply_of_mul_self hτ
  have hgτ := apply_comm_of_mul_comm hg
  have hsq : ∀ y, (g ^ 2) y = g (g y) := fun y => by rw [sq, Perm.mul_apply]
  rw [hsq]
  by_cases h1 : g x = x
  · left
    rw [h1, h1]
  by_cases h2 : g x = τ x
  · left
    rw [h2, hgτ, h2, hττ]
  set y := g x with hy
  have hyτ : τ y ≠ y := by
    intro h
    apply hx
    apply g.injective
    rw [hgτ, ← hy, h]
  have hmem : ∀ w, τ w ≠ w → w ∈ moved τ := fun w hw => mem_moved.2 hw
  have hx1 : x ≠ τ x := fun h => hx h.symm
  have hx2 : x ≠ y := fun h => h1 (h.symm)
  have hx3 : x ≠ τ y := fun h => h2 (by rw [h, hττ])
  have hx4 : τ x ≠ y := fun h => h2 h.symm
  have hx5 : τ x ≠ τ y := fun h => hx2 (τ.injective h)
  have hx6 : y ≠ τ y := fun h => hyτ h.symm
  have hgy : τ (g y) ≠ g y := by
    intro h
    apply hyτ
    apply g.injective
    rw [hgτ, h]
  by_contra hne
  rw [not_or] at hne
  have hgy1 : g y ≠ x := hne.1
  have hgy2 : g y ≠ τ x := hne.2
  have hgy3 : g y ≠ y := fun h => h1 (g.injective (by rw [← hy, h]))
  have hgy4 : g y ≠ τ y := fun h => h2 (g.injective (by rw [h, hgτ]))
  have hsub : ({g y, x, τ x, y, τ y} : Finset α) ⊆ moved τ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact hmem _ hgy
    · exact hmem _ hx
    · exact hmem _ (by rw [hττ]; exact hx1)
    · exact hmem _ hyτ
    · exact hmem _ (by rw [hττ]; exact hx6)
  have hc5 : ({g y, x, τ x, y, τ y} : Finset α).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hgy1, hgy2, hgy3, hgy4]),
      Finset.card_insert_of_notMem (by simp [hx1, hx2, hx3]),
      Finset.card_insert_of_notMem (by simp [hx4, hx5]),
      Finset.card_insert_of_notMem (by simp [hx6]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

theorem pow_four_eq_one_of_comm {τ g : Perm α} (hτ : τ * τ = 1) (hcard : (moved τ).card ≤ 4)
    (hg : g * τ = τ * g) (hfix : ∀ x, τ x = x → g x = x) : g ^ 4 = 1 := by
  have hg2 : g ^ 2 * τ = τ * g ^ 2 := by
    rw [sq, mul_assoc, hg, ← mul_assoc, hg, mul_assoc]
  ext x
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Perm.mul_apply, Perm.one_apply]
  by_cases hx : τ x = x
  · have h1 : (g ^ 2) x = x := by rw [sq, Perm.mul_apply, hfix x hx, hfix x hx]
    rw [h1, h1]
  rcases sq_apply_of_comm hτ hcard hg hx with h | h
  · rw [h, h]
  · rw [h, apply_comm_of_mul_comm hg2, h, apply_apply_of_mul_self hτ]

theorem eq_one_of_comm_of_odd {τ g : Perm α} (hτ : τ * τ = 1) (hcard : (moved τ).card ≤ 4)
    (hg : g * τ = τ * g) (hfix : ∀ x, τ x = x → g x = x) (hodd : Odd (orderOf g)) : g = 1 := by
  have h4 := orderOf_dvd_of_pow_eq_one (pow_four_eq_one_of_comm hτ hcard hg hfix)
  have h1 : orderOf g = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) h4
    interval_cases h : orderOf g
    · exact absurd hodd (by decide)
    · rfl
    · exact absurd hodd (by decide)
    · exact absurd h4 (by decide)
    · exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

theorem cyc3_pow_three {x y w : α} (hxy : x ≠ y) (hyw : y ≠ w) (hxw : x ≠ w) :
    cyc3 x y w ^ 3 = 1 := by
  ext v
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_one, Perm.mul_apply,
    Perm.mul_apply, Perm.one_apply]
  by_cases hv1 : v = x
  · subst hv1
    rw [cyc3_apply_left hxy hxw, cyc3_apply_mid hyw hxw, cyc3_apply_right]
  by_cases hv2 : v = y
  · subst hv2
    rw [cyc3_apply_mid hyw hxw, cyc3_apply_right, cyc3_apply_left hxy hxw]
  by_cases hv3 : v = w
  · subst hv3
    rw [cyc3_apply_right, cyc3_apply_left hxy hxw, cyc3_apply_mid hyw hxw]
  rw [cyc3_apply_of_ne hv1 hv2 hv3, cyc3_apply_of_ne hv1 hv2 hv3, cyc3_apply_of_ne hv1 hv2 hv3]

theorem exists_three_pairs {τ : Perm α} (hτ : τ * τ = 1) (hcard : 5 ≤ (moved τ).card) :
    ∃ ρ ρ' : Perm α, ρ ∈ alternatingGroup α ∧ ρ' ∈ alternatingGroup α ∧
      ρ * τ = τ * ρ ∧ ρ' * τ = τ * ρ' ∧ (∀ x, τ x = x → ρ x = x) ∧
      (∀ x, τ x = x → ρ' x = x) ∧ ρ ^ 3 = 1 ∧ ρ' ^ 3 = 1 ∧ orderOf (ρ⁻¹ * ρ') = 2 := by
  have hττ := apply_apply_of_mul_self hτ
  obtain ⟨a₁, ha₁⟩ : (moved τ).Nonempty := Finset.card_pos.1 (by omega)
  set M₁ := ((moved τ).erase a₁).erase (τ a₁) with hM₁
  have hM₁c : 3 ≤ M₁.card := by
    have h1 : (moved τ).card - 1 ≤ ((moved τ).erase a₁).card :=
      Finset.pred_card_le_card_erase
    have h2 : ((moved τ).erase a₁).card - 1 ≤ M₁.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨a₂, ha₂⟩ : M₁.Nonempty := Finset.card_pos.1 (by omega)
  set M₂ := (M₁.erase a₂).erase (τ a₂) with hM₂
  have hM₂c : 1 ≤ M₂.card := by
    have h1 : M₁.card - 1 ≤ (M₁.erase a₂).card := Finset.pred_card_le_card_erase
    have h2 : (M₁.erase a₂).card - 1 ≤ M₂.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨a₃, ha₃⟩ : M₂.Nonempty := Finset.card_pos.1 (by omega)
  simp only [hM₂, hM₁, Finset.mem_erase, mem_moved] at ha₂ ha₃
  rw [mem_moved] at ha₁
  obtain ⟨h21, h22, h23⟩ := ha₂
  obtain ⟨h31, h32, h33, h34, h35⟩ := ha₃
  set b₁ := τ a₁ with hb₁
  set b₂ := τ a₂ with hb₂
  set b₃ := τ a₃ with hb₃
  have hτb₁ : τ b₁ = a₁ := hττ a₁
  have hτb₂ : τ b₂ = a₂ := hττ a₂
  have hτb₃ : τ b₃ = a₃ := hττ a₃
  have d12 : a₁ ≠ a₂ := fun h => h22 h.symm
  have d13 : a₁ ≠ a₃ := fun h => h34 h.symm
  have d23 : a₂ ≠ a₃ := fun h => h32 h.symm
  have e12 : b₁ ≠ b₂ := fun h => d12 (τ.injective h)
  have e13 : b₁ ≠ b₃ := fun h => d13 (τ.injective h)
  have e23 : b₂ ≠ b₃ := fun h => d23 (τ.injective h)
  have f11 : a₁ ≠ b₁ := fun h => ha₁ h.symm
  have f22 : a₂ ≠ b₂ := fun h => h23 h.symm
  have f33 : a₃ ≠ b₃ := fun h => h35 h.symm
  have f12 : a₁ ≠ b₂ := fun h => h21 (by rw [hb₁, h, hτb₂])
  have f13 : a₁ ≠ b₃ := fun h => h33 (by rw [hb₁, h, hτb₃])
  have f21 : a₂ ≠ b₁ := h21
  have f23 : a₂ ≠ b₃ := fun h => h31 (by rw [hb₂, h, hτb₃])
  have f31 : a₃ ≠ b₁ := h33
  have f32 : a₃ ≠ b₂ := h31
  set ca := cyc3 a₁ a₂ a₃ with hca
  set cb := cyc3 b₁ b₂ b₃ with hcb
  have hca_fix : ∀ v, v ≠ a₁ → v ≠ a₂ → v ≠ a₃ → ca v = v := fun v h1 h2 h3 =>
    cyc3_apply_of_ne h1 h2 h3
  have hcb_fix : ∀ v, v ≠ b₁ → v ≠ b₂ → v ≠ b₃ → cb v = v := fun v h1 h2 h3 =>
    cyc3_apply_of_ne h1 h2 h3
  have hdisj : Perm.Disjoint ca cb := by
    intro v
    by_cases h : v = a₁ ∨ v = a₂ ∨ v = a₃
    · right
      rcases h with rfl | rfl | rfl
      · exact hcb_fix _ f11 f12 f13
      · exact hcb_fix _ f21 f22 f23
      · exact hcb_fix _ f31 f32 f33
    · left
      push Not at h
      exact hca_fix v h.1 h.2.1 h.2.2
  set ρ := ca * cb with hρ
  have hρalt : ρ ∈ alternatingGroup α :=
    mul_mem (mem_alt_cyc3 d12 d23) (mem_alt_cyc3 e12 e23)
  have hρτ : ρ * τ = τ * ρ := by
    have h1 : τ * ca * τ⁻¹ = cb := by rw [hca, cyc3_conj]
    have h2 : τ * cb * τ⁻¹ = ca := by rw [hcb, cyc3_conj, hτb₁, hτb₂, hτb₃]
    have h3 : τ * ρ * τ⁻¹ = ρ := by
      calc τ * ρ * τ⁻¹ = (τ * ca * τ⁻¹) * (τ * cb * τ⁻¹) := by rw [hρ]; group
        _ = cb * ca := by rw [h1, h2]
        _ = ρ := hdisj.commute.eq.symm
    calc ρ * τ = (τ * ρ * τ⁻¹) * τ := by rw [h3]
      _ = τ * ρ := by group
  have hmovA : ∀ v, τ v = v → v ≠ a₁ ∧ v ≠ a₂ ∧ v ≠ a₃ ∧ v ≠ b₁ ∧ v ≠ b₂ ∧ v ≠ b₃ := by
    intro v hv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact ha₁ hv
    · exact h23 hv
    · exact h35 hv
    · exact f11 (by rw [← hτb₁, hv])
    · exact f22 (by rw [← hτb₂, hv])
    · exact f33 (by rw [← hτb₃, hv])
  have hρfix : ∀ v, τ v = v → ρ v = v := by
    intro v hv
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hmovA v hv
    rw [hρ, Perm.mul_apply, hcb_fix v g4 g5 g6, hca_fix v g1 g2 g3]
  have hρ3 : ρ ^ 3 = 1 := by
    rw [hρ, hdisj.commute.mul_pow, cyc3_pow_three d12 d23 d13, cyc3_pow_three e12 e23 e13,
      one_mul]
  set s₂ := swap a₂ b₂ with hs₂
  set s₃ := swap a₃ b₃ with hs₃
  have hs₃τ : s₃ * τ = τ * s₃ := by
    have h1 : τ * s₃ * τ⁻¹ = s₃ := by
      rw [hs₃, ← swap_apply_apply, hτb₃, swap_comm]
    calc s₃ * τ = (τ * s₃ * τ⁻¹) * τ := by rw [h1]
      _ = τ * s₃ := by group
  have hs₃fix : ∀ v, τ v = v → s₃ v = v := by
    intro v hv
    obtain ⟨-, -, g3, -, -, g6⟩ := hmovA v hv
    exact swap_apply_of_ne_of_ne g3 g6
  set ρ' := s₃ * ρ * s₃ with hρ'
  have hs₃inv : s₃⁻¹ = s₃ := swap_inv _ _
  refine ⟨ρ, ρ', hρalt, ?_, hρτ, ?_, hρfix, ?_, hρ3, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, hρ', Perm.sign_mul, Perm.sign_mul,
      Perm.mem_alternatingGroup.1 hρalt, Perm.sign_swap f33]
    decide
  · calc ρ' * τ = s₃ * ρ * (s₃ * τ) := by rw [hρ']; group
      _ = τ * ρ' := by
        rw [hs₃τ, ← mul_assoc, mul_assoc s₃, hρτ, ← mul_assoc, hs₃τ, hρ']
        group
  · intro v hv
    rw [hρ', Perm.mul_apply, Perm.mul_apply, hs₃fix v hv, hρfix v hv, hs₃fix v hv]
  · have : ρ' = s₃ * ρ * s₃⁻¹ := by rw [hρ', hs₃inv]
    rw [this, conj_pow, hρ3, mul_one, mul_inv_cancel]
  ·
    have hρa₂ : ρ a₂ = a₃ := by
      rw [hρ, Perm.mul_apply, hcb_fix a₂ f21 f22 f23, hca, cyc3_apply_mid d23 d13]
    have hρb₂ : ρ b₂ = b₃ := by
      rw [hρ, Perm.mul_apply, hcb, cyc3_apply_mid e23 e13,
        hca_fix b₃ (Ne.symm f13) (Ne.symm f23) (Ne.symm f33)]
    have hconj : ρ⁻¹ * s₃ * ρ = s₂ := by
      have h1 : ρ⁻¹ a₃ = a₂ := by rw [Perm.inv_eq_iff_eq, hρa₂]
      have h2 : ρ⁻¹ b₃ = b₂ := by rw [Perm.inv_eq_iff_eq, hρb₂]
      have h3 := swap_apply_apply ρ⁻¹ a₃ b₃
      rw [h1, h2, inv_inv] at h3
      rw [hs₂, h3]
    have hprod : ρ⁻¹ * ρ' = s₂ * s₃ := by
      calc ρ⁻¹ * ρ' = (ρ⁻¹ * s₃ * ρ) * s₃ := by rw [hρ']; group
        _ = s₂ * s₃ := by rw [hconj]
    rw [hprod]
    have hcomm : s₂ * s₃ = s₃ * s₂ := by
      apply Perm.Disjoint.commute
      apply Perm.disjoint_swap_swap
      simp [d23, f22, f23, Ne.symm f32, e23, f33]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · calc (s₂ * s₃) ^ 2 = s₂ * (s₃ * s₂) * s₃ := by rw [sq]; group
        _ = s₂ * s₂ * (s₃ * s₃) := by rw [← hcomm]; group
        _ = 1 := by rw [hs₂, hs₃, swap_mul_self, swap_mul_self, one_mul]
    · intro h
      have h1 := congrArg (fun f : Perm α => f a₂) h
      simp only [Perm.mul_apply, Perm.one_apply] at h1
      rw [hs₃, swap_apply_of_ne_of_ne d23 f23, hs₂, swap_apply_left] at h1
      exact f22 h1.symm

theorem preserves_of_comm_cyc3 {F : Finset α} (hF : 3 ≤ F.card) {g : Perm α}
    (h : ∀ x ∈ F, ∀ y ∈ F, ∀ w ∈ F, x ≠ y → y ≠ w → x ≠ w →
      g * cyc3 x y w = cyc3 x y w * g) : ∀ x, x ∈ F ↔ g x ∈ F := by
  have hmaps : ∀ x ∈ F, g x ∈ F := by
    intro x hx
    have hc : 2 ≤ (F.erase x).card := by
      rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨y, w, hy, hw, hyw⟩ := Finset.one_lt_card_iff.1 (by omega : 1 < (F.erase x).card)
    rw [Finset.mem_erase] at hy hw
    have hxy : x ≠ y := fun e => hy.1 e.symm
    have hxw : x ≠ w := fun e => hw.1 e.symm
    have h1 := (comm_apply_ne_iff (h x hx y hy.2 w hw.2 hxy hyw hxw) x).2
      (by rw [cyc3_apply_left hxy hxw]; exact hxy.symm)
    rcases (cyc3_apply_ne_iff (g x) hxy hyw hxw).1 h1 with e | e | e
    · rw [e]; exact hx
    · rw [e]; exact hy.2
    · rw [e]; exact hw.2
  have himage : F.image g = F := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hmaps x hx
    · rw [Finset.card_image_of_injective _ g.injective]
  intro x
  refine ⟨hmaps x, fun hgx => ?_⟩
  rw [← himage] at hgx
  obtain ⟨x', hx', hgx'⟩ := Finset.mem_image.1 hgx
  rw [← g.injective hgx']
  exact hx'

theorem isSolvable_of_preserves {P : Subgroup (Perm α)} {U₁ U₂ U₃ : Finset α}
    (h₁ : U₁.card ≤ 4) (h₂ : U₂.card ≤ 4) (h₃ : U₃.card ≤ 4)
    (hp₁ : ∀ g ∈ P, ∀ x, x ∈ U₁ ↔ g x ∈ U₁) (hp₂ : ∀ g ∈ P, ∀ x, x ∈ U₂ ↔ g x ∈ U₂)
    (hp₃ : ∀ g ∈ P, ∀ x, x ∈ U₃ ↔ g x ∈ U₃)
    (hfix : ∀ g ∈ P, ∀ x, x ∉ U₁ → x ∉ U₂ → x ∉ U₃ → g x = x) : Group.IsSolvable P := by
  let res : ∀ U : Finset α, (∀ g ∈ P, ∀ x, x ∈ U ↔ g x ∈ U) → P →* Perm U := fun U hU =>
    { toFun := fun g => (g : Perm α).subtypePerm fun x => (hU g g.2 x).symm
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hres : ∀ (U : Finset α) (hU : ∀ g ∈ P, ∀ x, x ∈ U ↔ g x ∈ U) (g : P) (x : U),
      ((res U hU g x : U) : α) = (g : Perm α) x := fun _ _ _ _ => rfl
  let f : P →* Perm U₁ × (Perm U₂ × Perm U₃) :=
    (res U₁ hp₁).prod ((res U₂ hp₂).prod (res U₃ hp₃))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : res U₁ hp₁ g = 1 ∧ res U₂ hp₂ g = 1 ∧ res U₃ hp₃ g = 1 := by
      simp only [f, MonoidHom.prod_apply, Prod.mk_eq_one] at hg
      exact ⟨hg.1, hg.2.1, hg.2.2⟩
    have hfixU : ∀ (U : Finset α) (hU : ∀ g ∈ P, ∀ x, x ∈ U ↔ g x ∈ U), res U hU g = 1 →
        ∀ x ∈ U, (g : Perm α) x = x := by
      intro U hU h x hx
      have := congrArg (fun φ : Perm U => ((φ ⟨x, hx⟩ : U) : α)) h
      simpa [hres] using this
    apply Subtype.ext
    ext x
    by_cases hx1 : x ∈ U₁
    · exact hfixU U₁ hp₁ hg'.1 x hx1
    by_cases hx2 : x ∈ U₂
    · exact hfixU U₂ hp₂ hg'.2.1 x hx2
    by_cases hx3 : x ∈ U₃
    · exact hfixU U₃ hp₃ hg'.2.2 x hx3
    exact hfix g g.2 x hx1 hx2 hx3
  have hs : ∀ U : Finset α, U.card ≤ 4 → Group.IsSolvable (Perm U) := fun U hU =>
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hU)
  have := hs U₁ h₁
  have := hs U₂ h₂
  have := hs U₃ h₃
  exact Group.isSolvable_of_isSolvable_injective hinj

theorem perfect_eq_bot_of_comm {P : Subgroup (Perm α)} [Group.IsPerfect P] {ε : Perm α}
    {F : Finset α} (hF : 3 ≤ F.card) (hεF : ∀ x ∈ F, ε x = x) (hmov : (moved ε).card ≤ 4)
    (hrest : (Finset.univ.filter fun x => x ∉ F ∧ ε x = x).card ≤ 4)
    (hε : ∀ g ∈ P, g * ε = ε * g)
    (hc : ∀ g ∈ P, ∀ x ∈ F, ∀ y ∈ F, ∀ w ∈ F, x ≠ y → y ≠ w → x ≠ w →
      g * cyc3 x y w = cyc3 x y w * g) : P = ⊥ := by
  classical
  set R := Finset.univ.filter fun x => x ∉ F ∧ ε x = x with hR
  have hpF : ∀ g ∈ P, ∀ x, x ∈ F ↔ g x ∈ F := fun g hg => preserves_of_comm_cyc3 hF (hc g hg)
  have hpM : ∀ g ∈ P, ∀ x, x ∈ moved ε ↔ g x ∈ moved ε := by
    intro g hg x
    rw [mem_moved, mem_moved]
    exact (comm_apply_ne_iff (hε g hg) x).symm
  have hpR : ∀ g ∈ P, ∀ x, x ∈ R ↔ g x ∈ R := by
    intro g hg x
    have h1 := hpF g hg x
    have h2 := hpM g hg x
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_moved, mem_moved] at h2
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun h => hx1 (h1.2 h), by_contra fun h => (h2.2 h) hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun h => hx1 (h1.1 h), by_contra fun h => (h2.1 h) hx2⟩
  have hsolv : Group.IsSolvable P := by
    by_cases h4 : 4 ≤ F.card
    · refine isSolvable_of_preserves hmov hrest (Finset.card_empty.le.trans (by norm_num))
        hpM hpR (fun _ _ _ => by simp) ?_
      intro g hg x hx1 hx2 _
      have hxF : x ∈ F := by
        by_contra hxF
        apply hx2
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hxF, ?_⟩
        by_contra h
        exact hx1 (mem_moved.2 h)
      exact fixes_of_comm_cyc3 h4 (hc g hg) x hxF
    · refine isSolvable_of_preserves hmov hrest (by omega) hpM hpR hpF ?_
      intro g hg x hx1 hx2 hx3
      exfalso
      apply hx2
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hx3, ?_⟩
      by_contra h
      exact hx1 (mem_moved.2 h)
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  exact Group.IsPerfect.not_isSolvable P hsolv

theorem exists_equiv_of_mulEquiv_alternatingGroup {Ω Δ : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype Δ] [DecidableEq Δ] (h5 : 5 ≤ Fintype.card Ω) (h6 : Fintype.card Ω ≠ 6)
    (hcard : Fintype.card Ω = Fintype.card Δ) (φ : alternatingGroup Ω ≃* alternatingGroup Δ) :
    ∃ β : Ω ≃ Δ, ∀ (g : alternatingGroup Ω) (ω : Ω), (φ g : Perm Δ) (β ω) = β ((g : Perm Ω) ω) := by
  set β₀ : Ω ≃ Δ := Fintype.equivOfCardEq hcard
  obtain ⟨σ, hσ⟩ := Holt.H78.exists_perm_conj_eq_of_mulAut_alternatingGroup h5 h6
    (φ.trans β₀.altCongrHom.symm)
  refine ⟨σ.trans β₀, fun g ω => ?_⟩
  have h1 := hσ g
  have h2 : (φ g : alternatingGroup Δ) = β₀.altCongrHom ((φ.trans β₀.altCongrHom.symm) g) := by
    simp
  rw [h2, Equiv.altCongrHom_apply_coe, h1]
  simp [Equiv.permCongrHom, Equiv.permCongr_apply]

end Perm

section Data

variable {X : Type} [Group X] [Finite X]

structure LocalDatum (t : X) (D : Subgroup X) (Ω : Type) [Fintype Ω] : Prop where
  kgroup : CFSG.SectionRank.IsKGroupCat X
  core : CFSG.oddCore X = ⊥
  order : orderOf t = 2
  card : 7 ≤ Fintype.card Ω
  le_cent : D ≤ centralizer ({t} : Set X)
  normal : centralizer ({t} : Set X) ≤ normalizer (D : Set X)
  lam : ∀ x ∈ centralizer ({t} : Set X) ⊓ centralizer (D : Set X),
    ∀ y ∈ centralizer ({t} : Set X) ⊓ centralizer (D : Set X),
      Odd (orderOf x) → Odd (orderOf y) → Odd (orderOf (x * y))

@[expose] def AltLookupAt (m : ℕ) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (W : Subgroup A) [W.Normal], IsSimpleGroup W →
    (∃ x y : W, x * y ≠ y * x) → centralizer (W : Set A) = ⊥ → CFSG.Blueprint.Catalog W →
    ∀ a : A, orderOf a = 2 → ∀ B : Subgroup A, B ≤ W →
      CFSG.Assembly.IsComponentOf B (centralizer ({a} : Set A)) →
      Nonempty (B ≃* alternatingGroup (Fin m)) →
        ∃ N : ℕ, Nonempty (W ≃* alternatingGroup (Fin N))

theorem altLookupAt_of_altComponentLookup (h : AltComponentLookup) {m : ℕ} (hm : 9 ≤ m)
    (hm10 : m ≠ 10) : AltLookupAt m := by
  intro A _ _ W _ hWs hWn hC hcat a ha B hBW hB e
  rcases h A W hWs hWn hC hcat a ha B hBW hB m hm e with h1 | ⟨h2, -⟩
  · exact h1
  · exact absurd h2 hm10

theorem altLookupAt_seven_of_weakA7Lookup (h : WeakA7Lookup) : AltLookupAt 7 := by
  intro A _ _ W _ hWs hWn hC hcat a ha B hBW hB e
  exact h A W hWs hWn hC hcat a ha B hBW hB e

variable {t : X} {D : Subgroup X} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem LocalDatum.isSimpleGroup (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω) :
    IsSimpleGroup D := by
  have : IsSimpleGroup (alternatingGroup Ω) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; have := h.card; omega)
  exact η.isSimpleGroup

theorem LocalDatum.nonab (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω) :
    ∃ a b : D, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ a b : alternatingGroup Ω, a * b = b * a := fun a b => by
    have := hcon (η.symm a) (η.symm b)
    have h2 := congrArg η this
    simpa using h2
  have h3 := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Ω)).1 ⟨⟨hcomm⟩⟩
  have h7 := h.card
  rw [Nat.card_eq_fintype_card] at h3
  omega

theorem LocalDatum.isQuasisimple (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω) :
    CFSG.IsQuasisimple D :=
  have := h.isSimpleGroup η
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (h.nonab η)).1

theorem LocalDatum.center_eq_bot (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω) :
    center D = ⊥ :=
  have := h.isSimpleGroup η
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (h.nonab η)).2

theorem LocalDatum.isPerfect (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω) :
    Group.IsPerfect D :=
  (h.isQuasisimple η).1

theorem LocalDatum.isComponent (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω) :
    CFSG.IsComponent (D.subgroupOf (centralizer ({t} : Set X))) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe h.le_cent).symm
    (h.isQuasisimple η), ?_⟩
  have hn : (D.subgroupOf (centralizer ({t} : Set X))).Normal :=
    normal_subgroupOf_of_le_normalizer h.normal
  exact hn.isSubnormal

end Data

section Corr

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] noncomputable def altEquivAltSub (F : Finset α) : alternatingGroup F ≃* altSub F :=
  (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := F))).trans
    (Subgroup.equivMapOfInjective _ _ (alternatingGroup α).subtype_injective)

theorem coe_altEquivAltSub (F : Finset α) (k : alternatingGroup F) :
    ((altEquivAltSub F k : altSub F) : Perm α) = Perm.ofSubtype (k : Perm F) :=
  rfl

theorem moved_eq_support (τ : Perm α) : moved τ = τ.support := by
  ext x
  simp [moved, Perm.mem_support]

theorem card_fixFin {n : ℕ} (σ : Perm (Fin n)) : (fixFin σ).card = n - σ.support.card := by
  have h : fixFin σ = σ.supportᶜ := by
    ext i
    simp [mem_fixFin, Perm.mem_support]
  rw [h, Finset.card_compl, Fintype.card_fin]

end Corr

section Four

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

@[expose] def fixGroup (θ : L ≃* alternatingGroup (Fin n)) (w : L) : Subgroup G :=
  corr θ (altSub (fixFin ((θ w : alternatingGroup (Fin n)) : Perm (Fin n))))

theorem fixGroup_le (θ : L ≃* alternatingGroup (Fin n)) (w : L) : fixGroup θ w ≤ L :=
  corr_le θ _

theorem fixGroup_le_centralizer (θ : L ≃* alternatingGroup (Fin n)) (w : L) :
    fixGroup θ w ≤ centralizer ({(w : G)} : Set G) := by
  intro x hx
  obtain ⟨hxL, hxT⟩ := mem_corr.1 hx
  rw [mem_centralizer_singleton_iff]
  have hfix := (mem_altSub.1 hxT).2
  have hd : Perm.Disjoint ((θ ⟨x, hxL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
      ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro i
    by_cases hi : ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)) i = i
    · exact Or.inr hi
    · exact Or.inl (hfix i (fun h => hi (mem_fixFin.1 h)))
  have h1 : θ (w * ⟨x, hxL⟩) = θ (⟨x, hxL⟩ * w) := by
    rw [map_mul, map_mul]
    exact Subtype.ext hd.commute.eq.symm
  have h2 := congrArg Subtype.val (θ.injective h1)
  simp only [Subgroup.coe_mul] at h2
  exact h2.symm

theorem mem_normalizer_fixGroup (B : Two.Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    (w : L) {c : G} (hc : c ∈ centralizer ({z} : Set G)) (hcw : c * w = w * c) :
    c ∈ normalizer (fixGroup θ w : Set G) := by
  have hw : (w : G) ∈ centralizer ({z} : Set G) := le_cent_single B.std B.cyc w.2
  have h := Two.mem_normalizer_corr_fixFin B θ hw hc hcw
  rwa [Two.permOf_of_mem B θ hw w.2] at h

@[expose] noncomputable def fixGroupEquiv (θ : L ≃* alternatingGroup (Fin n)) (F : Finset (Fin n)) :
    corr (X := G) θ (altSub F) ≃* alternatingGroup F :=
  let φ₀ : corr (X := G) θ (altSub F) →* altSub F :=
    (((alternatingGroup (Fin n)).subtype.comp θ.toMonoidHom).comp
      (Subgroup.inclusion (corr_le θ (altSub F)))).codRestrict (altSub F)
      (fun x => (mem_corr.1 x.2).2)
  MulEquiv.ofBijective ((altEquivAltSub F).symm.toMonoidHom.comp φ₀) <| by
    refine ⟨(altEquivAltSub F).symm.injective.comp fun x y hxy => ?_, fun k => ?_⟩
    · have h1 := congrArg (fun g : altSub F => (g : Perm (Fin n))) hxy
      simp only [φ₀, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom] at h1
      have h2 := θ.injective (Subtype.ext h1)
      exact Subgroup.inclusion_injective _ h2
    · set g : altSub F := altEquivAltSub F k
      have hgA : (g : Perm (Fin n)) ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup F g.2
      set l : L := θ.symm ⟨g, hgA⟩
      have hl : ((θ l : alternatingGroup (Fin n)) : Perm (Fin n)) = g := by simp [l]
      have hlT : (l : G) ∈ corr (X := G) θ (altSub F) := by
        refine mem_corr.2 ⟨l.2, ?_⟩
        change ((θ l : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ altSub F
        rw [hl]
        exact g.2
      refine ⟨⟨l, hlT⟩, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change ((θ l : alternatingGroup (Fin n)) : Perm (Fin n)) = _
      rw [hl]

theorem ofSubtype_fixGroupEquiv (θ : L ≃* alternatingGroup (Fin n)) (F : Finset (Fin n))
    (x : corr (X := G) θ (altSub F)) :
    Perm.ofSubtype ((fixGroupEquiv θ F x : alternatingGroup F) : Perm F) =
      ((θ ⟨x, corr_le θ _ x.2⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  rw [← coe_altEquivAltSub]
  simp [fixGroupEquiv]
  rfl

end Four

section Sub

variable {G : Type*} [Group G]

theorem mem_centralizer_mk_iff {H : Subgroup G} {g : G} (hg : g ∈ H) {x : H} :
    x ∈ centralizer ({⟨g, hg⟩} : Set H) ↔ (x : G) ∈ centralizer ({g} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem mem_centralizer_subgroupOf_iff {H M : Subgroup G} (hMH : M ≤ H) {x : H} :
    x ∈ centralizer ((M.subgroupOf H : Subgroup H) : Set H) ↔
      (x : G) ∈ centralizer (M : Set G) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h m hm
    exact congrArg Subtype.val (h ⟨m, hMH hm⟩ hm)
  · intro h m hm
    exact Subtype.ext (h m hm)

theorem mem_normalizer_subgroupOf_iff {H M : Subgroup G} (hMH : M ≤ H) {x : H} :
    x ∈ normalizer ((M.subgroupOf H : Subgroup H) : Set H) ↔
      (x : G) ∈ normalizer (M : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h g
    by_cases hg : g ∈ H
    · exact h ⟨g, hg⟩
    · have h1 : g ∉ M := fun hm => hg (hMH hm)
      have h2 : (x : G) * g * (x : G)⁻¹ ∉ M := by
        intro hm
        apply hg
        have := hMH hm
        have h3 : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x := by group
        rw [h3]
        exact mul_mem (mul_mem (inv_mem x.2) this) x.2
      exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
  · intro h g
    exact h g

end Sub

section Step0

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem not_odd_orderOf_oddY_mul (B : Two.Base G L Q n z) {y : G}
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G))) :
    ¬ Odd (orderOf (y * z)) := by
  rintro ⟨k, hk⟩
  have hyz : Commute y z :=
    (mem_centralizer_singleton_iff.1 (Two.oddY_le_centralizer_z B.cyc hy))
  have h1 : (y * z) ^ orderOf (y * z) = 1 := pow_orderOf_eq_one _
  rw [hyz.mul_pow] at h1
  have hz2 : z ^ 2 = 1 := by rw [← B.cyc.order]; exact pow_orderOf_eq_one z
  have hzk : z ^ orderOf (y * z) = z := by rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul]
  rw [hzk] at h1
  have hyk : y ^ orderOf (y * z) = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hmem : z ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ⊓ zpowers z := by
    refine ⟨?_, mem_zpowers z⟩
    have h3 := inv_mem (pow_mem hy (orderOf (y * z)))
    rwa [hyk, inv_inv] at h3
  rw [Two.oddY_inf_zpowers B.cyc B.card, mem_bot] at hmem
  have := B.cyc.order
  rw [hmem, orderOf_one] at this
  omega

theorem mem_oddY_of_lambda (B : Two.Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    {w : L} (hw : orderOf w = 2)
    (hw4 : ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 4)
    {x : G} (hxz : x ∈ centralizer ({z} : Set G)) (hxw : x * w = w * x)
    (hxL : x ∈ centralizer (fixGroup θ w : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
  set σ : Perm (Fin n) := ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)) with hσ
  have hσ2 : σ * σ = 1 := by
    have h1 : w * w = 1 := by rw [← sq, ← hw]; exact pow_orderOf_eq_one w
    have := congrArg (fun l : L => ((θ l : alternatingGroup (Fin n)) : Perm (Fin n))) h1
    simpa [map_mul] using this
  set π := Two.permOf B θ hxz with hπ
  have hwz : (w : G) ∈ centralizer ({z} : Set G) := le_cent_single B.std B.cyc w.2
  have hπσ : π * σ = σ * π := by
    have h1 := Two.permOf_mul B θ hxz hwz (mul_mem hxz hwz)
    have h2 := Two.permOf_mul B θ hwz hxz (mul_mem hwz hxz)
    have h3 : Two.permOf B θ (mul_mem hxz hwz) = Two.permOf B θ (mul_mem hwz hxz) :=
      Two.permOf_congr B θ hxw _ _
    rw [h1, h2, Two.permOf_of_mem B θ hwz w.2] at h3
    exact h3
  have hπfix : ∀ i, σ i = i → π i = i := by
    have hc := rho_mem_centralizer θ B.hn (altSub_le_alternatingGroup _)
      (cent_le_normalizer B.std B.cyc hxz) hxL
    have hF : 4 ≤ (fixFin σ).card := by rw [card_fixFin, hw4]; have := B.hn; omega
    intro i hi
    exact (mem_centralizer_altSub_iff hF).1 hc i (mem_fixFin.2 hi)
  have hπodd : Odd (orderOf π) := by
    refine Odd.of_dvd_nat hodd ?_
    have := orderOf_map_dvd (rho θ B.hn) ⟨x, cent_le_normalizer B.std B.cyc hxz⟩
    rwa [Subgroup.orderOf_mk] at this
  have hπ1 : π = 1 :=
    eq_one_of_comm_of_odd hσ2 (by rw [moved_eq_support, hw4]) hπσ hπfix hπodd
  have hxK : x ∈ centralizer (L : Set G) := (Two.permOf_eq_one_iff B θ hxz).1 hπ1
  obtain ⟨y, hy, rfl | rfl⟩ := Two.exists_oddY_of_mem_inf B.cyc B.card ⟨hxK, hxz⟩
  · exact hy
  · exact absurd hodd (not_odd_orderOf_oddY_mul B hy)

theorem mem_centralizer_of_mem_of_base {_θ : L ≃* alternatingGroup (Fin n)}
    (B : Two.Base G L Q n z) (w : L) :
    z ∈ centralizer ({(w : G)} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_singleton_iff.1 (le_cent_single B.std B.cyc w.2)).symm

omit [Finite G] in
theorem centralizer_ne_top (hS : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {w : G}
    (hw : w ≠ 1) : centralizer ({w} : Set G) ≠ ⊤ := by
  intro htop
  have hZ : center G = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.1 (h1 ▸ mem_top b) a)
  have hwc : w ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({w} : Set G) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.1 hg
  rw [hZ, mem_bot] at hwc
  exact hw hwc

theorem localDatum_of_four_of_core {θ : L ≃* alternatingGroup (Fin n)}
    (B : Two.Base G L Q n z) (hn : 11 ≤ n) {w : L} (hw : orderOf w = 2)
    (hw4 : ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 4)
    (hcore : CFSG.oddCore (centralizer ({(w : G)} : Set G)) = ⊥) :
    LocalDatum (⟨z, mem_centralizer_of_mem_of_base (_θ := θ) B w⟩ : centralizer ({(w : G)} : Set G))
      ((fixGroup θ w).subgroupOf (centralizer ({(w : G)} : Set G)))
      (fixFin ((θ w : alternatingGroup (Fin n)) : Perm (Fin n))) := by
  set X := centralizer ({(w : G)} : Set G) with hX
  have hLX := fixGroup_le_centralizer θ w
  have hw1 : (w : G) ≠ 1 := by
    intro h
    have h1 : w = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hw
    omega
  refine ⟨isKGroupCat_of_kProper B.std.kProper _ (centralizer_ne_top B.std.simple B.std.nonab hw1),
    hcore, by rw [Subgroup.orderOf_mk]; exact B.cyc.order, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_coe, card_fixFin, hw4]
    omega
  · intro d hd
    rw [mem_centralizer_mk_iff]
    exact le_cent_single B.std B.cyc (fixGroup_le θ w hd)
  · intro c hc
    rw [mem_centralizer_mk_iff] at hc
    rw [mem_normalizer_subgroupOf_iff hLX]
    exact mem_normalizer_fixGroup B θ w hc (mem_centralizer_singleton_iff.1 c.2)
  · have key : ∀ x : X, x ∈ centralizer ({(⟨z, mem_centralizer_of_mem_of_base (_θ := θ) B w⟩ : X)} : Set X) ⊓
        centralizer (((fixGroup θ w).subgroupOf X : Subgroup X) : Set X) → Odd (orderOf x) →
        (x : G) ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
      intro x hx hodd
      rw [mem_inf, mem_centralizer_mk_iff, mem_centralizer_subgroupOf_iff hLX] at hx
      refine mem_oddY_of_lambda B θ hw hw4 hx.1 ?_ hx.2 (by rwa [Subgroup.orderOf_coe])
      exact mem_centralizer_singleton_iff.1 x.2
    intro x hx y hy hxo hyo
    have hxy := mul_mem (key x hx hxo) (key y hy hyo)
    rw [← Subgroup.orderOf_coe]
    exact Two.odd_orderOf_of_mem_oddY B.cyc hxy

end Step0

end CFSG.OddStandard.AltStdCycTwo.YOne
