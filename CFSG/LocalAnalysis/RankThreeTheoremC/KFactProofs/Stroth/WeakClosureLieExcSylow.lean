module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcLines
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_sylow_of_commute {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G} {k : ℕ}
    (hx : x ^ p ^ k = 1) (hc : ∀ s ∈ (P : Subgroup G), s * x = x * s) :
    x ∈ (P : Subgroup G) := by
  have hz : IsPGroup p (Subgroup.zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx
  have hnorm : (P : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro s hs
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
    exact ((Commute.zpow_right (show Commute s x from hc s hs) i).eq).symm
  have hQ : IsPGroup p ((P : Subgroup G) ⊔ Subgroup.zpowers x : Subgroup G) :=
    P.isPGroup'.to_sup_of_normal_right' hz hnorm
  have hQeq : ((P : Subgroup G) ⊔ Subgroup.zpowers x : Subgroup G) = (P : Subgroup G) :=
    P.is_maximal' hQ le_sup_left
  rw [← hQeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem pow_eq_one_of_card_eq_prime {p : ℕ} {A : Subgroup G} (hA : Nat.card A = p) {x : G}
    (hx : x ∈ A) : x ^ p = 1 := by
  have := pow_card_eq_one' (G := A) (x := ⟨x, hx⟩)
  rw [hA] at this
  exact congrArg Subtype.val this

theorem exists_dc_moves_line {p : ℕ} [Fact p.Prime] {Γ S A : Subgroup G} (hSΓ : S ≤ Γ)
    (hAS : A ≤ S) (hA : Nat.card A = p) {c₁ c₂ c₃ c₄ : G}
    (h₁ : c₁ ∈ Subgroup.normalizer (S : Set G)) (h₂ : c₂ ∈ Subgroup.normalizer (S : Set G))
    (h₃ : c₃ ∈ Subgroup.normalizer (S : Set G)) (h₄ : c₄ ∈ Subgroup.normalizer (S : Set G))
    (hΓ₁ : ⁅c₁, c₂⁆ ∈ Γ) (hΓ₂ : ⁅c₃, c₄⁆ ∈ Γ)
    (hfpf : ∀ x ∈ S, x ^ p = 1 → ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆ * x * ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆⁻¹ = x → x = 1) :
    ∃ n : G, n ∈ Γ ∧ n ∈ Subgroup.normalizer (S : Set G) ∧
      A.map (MulAut.conj n).toMonoidHom ≠ A := by
  have hmove := exists_not_normalizes_of_doubleCommutator_fpf (p := p) (E := A) (A := A) le_rfl hA
    (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (c₄ := c₄)
    (fun x hx hxu => hfpf x (hAS hx) (pow_eq_one_of_card_eq_prime hA hx) hxu)
  have hn : ∀ {a b : G}, a ∈ Subgroup.normalizer (S : Set G) → b ∈ Subgroup.normalizer (S : Set G) →
      ⁅a, b⁆ ∈ Subgroup.normalizer (S : Set G) := fun {a b} ha hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  rcases hmove with h | h
  · exact ⟨⁅c₁, c₂⁆, hΓ₁, hn h₁ h₂, h⟩
  · exact ⟨⁅c₃, c₄⁆, hΓ₂, hn h₃ h₄, h⟩

theorem exists_dc2_moves_line {p : ℕ} [Fact p.Prime] {Γ S A : Subgroup G} (hSΓ : S ≤ Γ)
    (hAS : A ≤ S) (hA : Nat.card A = p) {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : G}
    (h₁ : c₁ ∈ Subgroup.normalizer (S : Set G)) (h₂ : c₂ ∈ Subgroup.normalizer (S : Set G))
    (h₃ : c₃ ∈ Subgroup.normalizer (S : Set G)) (h₄ : c₄ ∈ Subgroup.normalizer (S : Set G))
    (h₅ : c₅ ∈ Subgroup.normalizer (S : Set G)) (h₆ : c₆ ∈ Subgroup.normalizer (S : Set G))
    (h₇ : c₇ ∈ Subgroup.normalizer (S : Set G)) (h₈ : c₈ ∈ Subgroup.normalizer (S : Set G))
    (hΓ₁ : ⁅c₁, c₂⁆ ∈ Γ) (hΓ₂ : ⁅c₃, c₄⁆ ∈ Γ) (hΓ₃ : ⁅c₅, c₆⁆ ∈ Γ) (hΓ₄ : ⁅c₇, c₈⁆ ∈ Γ)
    (hfpf : ∀ x ∈ S, x ^ p = 1 → ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆ * x * ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆⁻¹ = x →
      ⁅⁅c₅, c₆⁆, ⁅c₇, c₈⁆⁆ * x * ⁅⁅c₅, c₆⁆, ⁅c₇, c₈⁆⁆⁻¹ = x → x = 1) :
    ∃ n : G, n ∈ Γ ∧ n ∈ Subgroup.normalizer (S : Set G) ∧
      A.map (MulAut.conj n).toMonoidHom ≠ A := by
  have hn : ∀ {a b : G}, a ∈ Subgroup.normalizer (S : Set G) → b ∈ Subgroup.normalizer (S : Set G) →
      ⁅a, b⁆ ∈ Subgroup.normalizer (S : Set G) := fun {a b} ha hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  by_contra hcon
  push Not at hcon
  have hnorm : ∀ n : G, n ∈ Γ → n ∈ Subgroup.normalizer (S : Set G) →
      A.map (MulAut.conj n).toMonoidHom = A := fun n hΓ hN => hcon n hΓ hN
  have hu₁ := commutatorElement_centralizes_of_normalizes_line hA (hnorm _ hΓ₁ (hn h₁ h₂))
    (hnorm _ hΓ₂ (hn h₃ h₄))
  have hu₂ := commutatorElement_centralizes_of_normalizes_line hA (hnorm _ hΓ₃ (hn h₅ h₆))
    (hnorm _ hΓ₄ (hn h₇ h₈))
  have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 fun a ha =>
    hfpf a (hAS ha) (pow_eq_one_of_card_eq_prime hA ha) (hu₁ a ha) (hu₂ a ha)
  rw [hbot, Subgroup.card_bot] at hA
  exact (Fact.out : p.Prime).one_lt.ne hA

theorem exists_c_moves_line {p : ℕ} [Fact p.Prime] {Γ S A : Subgroup G} (hAS : A ≤ S)
    (hA : Nat.card A = p) {c₁ c₂ : G}
    (h₁ : c₁ ∈ Subgroup.normalizer (S : Set G)) (h₂ : c₂ ∈ Subgroup.normalizer (S : Set G))
    (hΓ₁ : c₁ ∈ Γ) (hΓ₂ : c₂ ∈ Γ)
    (hfpf : ∀ x ∈ S, x ^ p = 1 → ⁅c₁, c₂⁆ * x * ⁅c₁, c₂⁆⁻¹ = x → x = 1) :
    ∃ n : G, n ∈ Γ ∧ n ∈ Subgroup.normalizer (S : Set G) ∧
      A.map (MulAut.conj n).toMonoidHom ≠ A := by
  have hmove := exists_not_normalizes_of_commutator_fpf (p := p) (E := A) (A := A) le_rfl hA
    (c₁ := c₁) (c₂ := c₂)
    (fun x hx hxu => hfpf x (hAS hx) (pow_eq_one_of_card_eq_prime hA hx) hxu)
  rcases hmove with h | h
  · exact ⟨c₁, hΓ₁, h₁, h⟩
  · exact ⟨c₂, hΓ₂, h₂, h⟩

theorem exists_mem_normalizer_move_of_ambient {Γ : Subgroup G} {S₀ A : Subgroup Γ} {n : G}
    (hnΓ : n ∈ Γ) (hn : n ∈ Subgroup.normalizer ((S₀.map Γ.subtype : Subgroup G) : Set G))
    (hmove : (A.map Γ.subtype).map (MulAut.conj n).toMonoidHom ≠ A.map Γ.subtype) :
    ∃ m ∈ Subgroup.normalizer (S₀ : Set Γ), A.map (MulAut.conj m).toMonoidHom ≠ A := by
  refine ⟨⟨n, hnΓ⟩, ?_, fun heq => hmove ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 hn (x : G)
    have e1 : (x ∈ S₀) ↔ ((x : G) ∈ S₀.map Γ.subtype) :=
      (Subgroup.mem_map_iff_mem Γ.subtype_injective).symm
    have e2 : (⟨n, hnΓ⟩ * x * ⟨n, hnΓ⟩⁻¹ ∈ S₀) ↔
        (((⟨n, hnΓ⟩ * x * ⟨n, hnΓ⟩⁻¹ : Γ) : G) ∈ S₀.map Γ.subtype) :=
      (Subgroup.mem_map_iff_mem Γ.subtype_injective).symm
    rw [e1, e2]
    exact h1
  · ext g
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have : (⟨n, hnΓ⟩ * a * ⟨n, hnΓ⟩⁻¹ : Γ) ∈ A.map (MulAut.conj (⟨n, hnΓ⟩ : Γ)).toMonoidHom :=
        ⟨a, ha, by simp [MulAut.conj_apply]⟩
      rw [heq] at this
      exact ⟨_, this, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      have hn' : (⟨n, hnΓ⟩⁻¹ * a * ⟨n, hnΓ⟩ : Γ) ∈ A := by
        have : a ∈ A.map (MulAut.conj (⟨n, hnΓ⟩ : Γ)).toMonoidHom := by rw [heq]; exact ha
        obtain ⟨b, hb, hba⟩ := this
        have : b = ⟨n, hnΓ⟩⁻¹ * a * ⟨n, hnΓ⟩ := by
          rw [← hba]; simp [MulAut.conj_apply, mul_assoc]
        rw [← this]; exact hb
      refine ⟨_, ⟨(⟨n, hnΓ⟩⁻¹ * a * ⟨n, hnΓ⟩ : Γ), hn', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
