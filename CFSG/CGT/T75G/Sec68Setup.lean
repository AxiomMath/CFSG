module

public import CFSG.CGT.T75G.Sec68Basic
public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.CGT.Timmesfeld75.Sec4OneCommon

public section

namespace CFSG.CGT.T75G

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}

structure Cfg68 (T T₁ : Subgroup G) (m : ℕ) : Prop where
  hy : StepHyp T T₁
  hm : 2 ≤ m
  hq : Nat.card T / Nat.card ↥(normIn T T₁) = 2 ^ m
  hT : Nat.card T = (2 ^ m) ^ 2
  hnat : NaturalSL T (hSub T (normIn T₁ T)) 2 m
  hDD : ∀ d ∈ classD T, ∀ e ∈ classD T, d ≠ e → d * e = e * d → d * e ∈ classD T
  hcl : ∀ d ∈ normIn T T₁, d ≠ 1 →
    Subgroup.closure {e : G | e ∈ classD T ∧ e * d = d * e} = T ⊔ normIn T₁ T
  hZ : ∀ z ∈ T ⊔ normIn T₁ T,
    ((∀ w ∈ T ⊔ normIn T₁ T, z * w = w * z) ↔ z ∈ normIn T T₁)
  hab : ∀ a ∈ T ⊔ normIn T₁ T, ∀ b ∈ T ⊔ normIn T₁ T, ⁅a, b⁆ ∈ normIn T T₁

namespace Cfg68

variable (c : Cfg68 T T₁ m)
include c

theorem cfg : Cfg T T₁ := by
  have := c.hy.finite
  exact cfg_of_conj_conj c.hy.pair.wc ⟨1, (conjSubgroup_one T).symm⟩ c.hy.pair.conj
    c.hy.pair.ne c.hy.pair.nontriv

theorem isTI : IsTI T := c.hy.pair.wc.isTI

theorem isElemAbelian : IsElemAbelian 2 T := c.hy.pair.wc.1

theorem card_L : Nat.card (normIn T T₁) = 2 ^ m := by
  have := c.hy.finite
  have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hdvd : Nat.card (normIn T T₁) ∣ Nat.card T :=
    Subgroup.card_dvd_of_le (normIn_le T T₁)
  have h1 : Nat.card T = 2 ^ m * Nat.card (normIn T T₁) := by
    have := (Nat.div_mul_cancel hdvd).symm
    rwa [c.hq] at this
  rw [c.hT, sq] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm

theorem isElemAbelian₁ : IsElemAbelian 2 T₁ := by
  obtain ⟨x, hx⟩ := c.hy.pair.conj
  exact hx ▸ isElemAbelian_conjSubgroup c.isElemAbelian x

theorem classD_iff {d : G} (hdT : d ∈ T) (hd1 : d ≠ 1) (g : G) :
    g ∈ classD T ↔ IsConj d g := by
  constructor
  · rintro ⟨k, t, ht, ht1, rfl⟩
    obtain ⟨h, -, hts⟩ := NaturalSL.exists_conj c.hnat (le_sup_left : T ≤ hSub T (normIn T₁ T))
      hdT hd1 ht ht1
    exact (isConj_iff.2 ⟨h, hts⟩).trans (isConj_iff.2 ⟨k⁻¹, by group⟩)
  · intro hx
    obtain ⟨k, hk⟩ := isConj_iff.1 hx
    exact ⟨k⁻¹, d, hdT, hd1, by rw [← hk]; group⟩

theorem setup {d : G} (hd : d ∈ normIn T T₁) (hd1 : d ≠ 1) : CorB.Setup d := by
  have := c.hy.finite
  have hP := c.hy.pair
  have hTab := hP.wc.1
  have hdT : d ∈ T := normIn_le T T₁ hd
  have hdd : d * d = 1 := elemAbelian_mul_self hTab hdT
  have hord : orderOf d = 2 := orderOf_eq_prime (by simpa [pow_two] using hdd) hd1
  have hdD : d ∈ classD T := mem_classD_of_mem hdT hd1
  have hDcl := c.classD_iff hdT hd1
  have hS : CorB.conjCent d = {e : G | e ∈ classD T ∧ e * d = d * e} := by
    ext e
    constructor
    · rintro ⟨hc', hj⟩
      exact ⟨(hDcl e).2 hj, hc'⟩
    · rintro ⟨hD, hc'⟩
      exact ⟨hc', (hDcl e).1 hD⟩
  have hK : CorB.weakClosure d = T ⊔ normIn T₁ T := by
    rw [CorB.weakClosure, hS]
    exact c.hcl d hd hd1
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun x hx => (mem_normIn.1 hx).2
  have hT2 : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hTab
  have hL₁2 : IsPGroup 2 (normIn T₁ T) :=
    (isPGroup_two_of_isElemAbelian c.isElemAbelian₁).to_le (normIn_le T₁ T)
  have hK2 : IsPGroup 2 ↥(CorB.weakClosure d) := by
    rw [hK]
    exact IsPGroup.to_sup_of_normal_left' hT2 hL₁2 hL₁N
  have hcl2 : ⁅⁅CorB.weakClosure d, CorB.weakClosure d⁆, CorB.weakClosure d⁆ = ⊥ := by
    rw [hK, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have hcomm : ⁅T ⊔ normIn T₁ T, T ⊔ normIn T₁ T⁆ ≤ normIn T T₁ := by
      rw [Subgroup.commutator_le]
      exact c.hab
    have haL : a ∈ normIn T T₁ := hcomm ha
    have haK : a ∈ T ⊔ normIn T₁ T :=
      (le_sup_left : T ≤ T ⊔ normIn T₁ T) (normIn_le T T₁ haL)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (c.hZ a haK).2 haL b hb
  have hsec2 : ∀ τ : G, τ * d = d * τ → IsConj d τ → τ ≠ d → IsConj d (d * τ) := by
    intro τ hc' hj hne
    have hτD : τ ∈ classD T := (hDcl τ).2 hj
    exact (hDcl _).1 (c.hDD d hdD τ hτD (Ne.symm hne) hc'.symm)
  exact ⟨hord, hK2, hcl2, hsec2⟩

end Cfg68

end CFSG.CGT.T75G
