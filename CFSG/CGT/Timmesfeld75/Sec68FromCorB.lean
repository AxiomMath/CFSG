module

public import CFSG.CGT.Timmesfeld75.Sec68Stmt
public import CFSG.CGT.Timmesfeld75.Sec7Nine
public import CFSG.LargeExtraspecial.S8CorBStatement

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def CorBExceptional (Y : Type) [Group Y] : Prop :=
  (∃ f : ℕ, LieModel Y .G2 0 2 f) ∨ LieModel Y .PSU 3 3 1 ∨
    (∃ f : ℕ, LieModel Y .trialityD4 0 2 f) ∨ NativeSporadic.IsSporadic Y .J2

theorem statedClassicalModel_of_lieModel_of_ne_zero {Y : Type} [Group Y] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : LieModel Y t n p f) : StatedClassicalModel Y t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem listGroup_or_exceptional_of_corBList {Y : Type} [Group Y]
    (h : LargeExtraspecial.S8.CorBList Y) : ListGroup Y ∨ CorBExceptional Y := by
  rcases h with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | ⟨f, h⟩ | h | h
  · have hm := statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) h
    exact Or.inl (Or.inl ⟨2, f, le_rfl, hm.1.2.1, hm⟩)
  · have hm := statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) h
    refine Or.inl (Or.inr (Or.inl ⟨f, ?_, hm⟩))
    obtain ⟨-, hf1, -, hne⟩ := hm.1
    by_contra hf2
    have hf : f = 1 := by omega
    exact hne (by simp [hf])
  · obtain ⟨-, a, ha, K, -, -, hf, -, -⟩ := lieModel_twistedB2_iff.1 h
    refine Or.inl (Or.inr (Or.inr (Or.inl ⟨f, ⟨a, by omega⟩, by omega, h⟩)))
  · have hm := statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) h
    exact Or.inl (Or.inl ⟨3, f, by norm_num, hm.1.2.1, hm⟩)
  · exact Or.inr (Or.inl ⟨f, h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, by norm_num, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

@[expose] def Sec68Inspection : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (m : ℕ), StepHyp T T₁ → 2 ≤ m →
    Nat.card T / Nat.card ↥(normIn T T₁) = 2 ^ m → Nat.card T = (2 ^ m) ^ 2 →
    NaturalSL T (hSub T (normIn T₁ T)) 2 m →
    (∀ d ∈ classD T, ∀ e ∈ classD T, d ≠ e → d * e = e * d → d * e ∈ classD T) →
    (∀ d ∈ normIn T T₁, d ≠ 1 →
      Subgroup.closure {e : G | e ∈ classD T ∧ e * d = d * e} = T ⊔ normIn T₁ T) →
    (∀ z ∈ T ⊔ normIn T₁ T,
      ((∀ w ∈ T ⊔ normIn T₁ T, z * w = w * z) ↔ z ∈ normIn T T₁)) →
    (∀ a ∈ T ⊔ normIn T₁ T, ∀ b ∈ T ⊔ normIn T₁ T, ⁅a, b⁆ ∈ normIn T T₁) →
    (∀ N : Subgroup G, N ≤ hSub T (normIn T₁ T) →
      (∀ h ∈ hSub T (normIn T₁ T), conjSubgroup h N = N) → IsPGroup 2 N → N ≤ T) →
    ∀ (Y : Type) [Group Y], Nonempty (G ≃* Y) → ¬ CorBExceptional Y

theorem sec68CorB_of (h57 : Step57) (hCorB : LargeExtraspecial.S8.TimmesfeldCorBInput)
    (hIns : Sec68Inspection) : Sec68CorB := by
  intro G _ T T₁ m hy hm hq hT hnat hDD hcl hZ hab hO2
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hTab := hP.wc.1
  obtain ⟨⟨d, hdL⟩, hd1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP.nontriv
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hdT : d ∈ T := normIn_le T T₁ hdL
  have hdd : d * d = 1 := elemAbelian_mul_self hTab hdT
  have hord : orderOf d = 2 := orderOf_eq_prime (by simpa [pow_two] using hdd) hd1
  have hdD : d ∈ classD T := mem_classD_of_mem hdT hd1
  have hDcl : ∀ g : G, g ∈ classD T ↔ IsConj d g := by
    obtain ⟨d₀, hd₀⟩ := classD_isConj h57 hy
    have hd0d : IsConj d₀ d := by
      rw [hd₀] at hdD
      exact hdD
    intro g
    rw [hd₀]
    exact ⟨fun h => hd0d.symm.trans h, fun h => hd0d.trans h⟩
  have hS : LargeExtraspecial.S8.conjCent d = {e : G | e ∈ classD T ∧ e * d = d * e} := by
    ext e
    constructor
    · intro h
      obtain ⟨hc, hj⟩ : e * d = d * e ∧ IsConj d e := h
      exact ⟨(hDcl e).2 hj, hc⟩
    · intro h
      obtain ⟨hD, hc⟩ : e ∈ classD T ∧ e * d = d * e := h
      exact show e * d = d * e ∧ IsConj d e from ⟨hc, (hDcl e).1 hD⟩
  have hK : Subgroup.closure (LargeExtraspecial.S8.conjCent d) = T ⊔ normIn T₁ T := by
    rw [hS]
    exact hcl d hdL hd1
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun x hx => (mem_normIn.1 hx).2
  have hT2 : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hTab
  have hL₁2 : IsPGroup 2 (normIn T₁ T) := by
    obtain ⟨x, hx⟩ := hP.conj
    have hT₁ab : IsElemAbelian 2 T₁ := hx ▸ isElemAbelian_conjSubgroup hTab x
    exact (isPGroup_two_of_isElemAbelian hT₁ab).to_le (normIn_le T₁ T)
  have hK2 : IsPGroup 2 ↥(Subgroup.closure (LargeExtraspecial.S8.conjCent d)) := by
    rw [hK]
    exact IsPGroup.to_sup_of_normal_left' hT2 hL₁2 hL₁N
  have hcl2 : ⁅⁅Subgroup.closure (LargeExtraspecial.S8.conjCent d),
      Subgroup.closure (LargeExtraspecial.S8.conjCent d)⁆,
      Subgroup.closure (LargeExtraspecial.S8.conjCent d)⁆ = ⊥ := by
    rw [hK, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have hcomm : ⁅T ⊔ normIn T₁ T, T ⊔ normIn T₁ T⁆ ≤ normIn T T₁ := by
      rw [Subgroup.commutator_le]
      exact hab
    have haL : a ∈ normIn T T₁ := hcomm ha
    have haK : a ∈ T ⊔ normIn T₁ T :=
      (le_sup_left : T ≤ T ⊔ normIn T₁ T) (normIn_le T T₁ haL)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hZ a haK).2 haL b hb
  have hsec2 : ∀ τ : G, τ * d = d * τ → IsConj d τ → τ ≠ d → IsConj d (d * τ) := by
    intro τ hc hj hne
    have hτD : τ ∈ classD T := (hDcl τ).2 hj
    exact (hDcl _).1 (hDD d hdD τ hτD (Ne.symm hne) hc.symm)
  have hres := hCorB G d hord hK2 hcl2 hsec2
  have hNtop : Subgroup.normalClosure ({d} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({d} : Set G)) with
      h | h
    · exfalso
      apply hd1
      have : d ∈ Subgroup.normalClosure ({d} : Set G) := Subgroup.subset_normalClosure rfl
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exact h
  have hnonab := hy.nonab
  rcases hres with ⟨K', hK'le, hK'n, hK'odd, hK'eq⟩ | hab' | hlist
  · exfalso
    have hK'norm : K'.Normal := by
      refine ⟨fun k hk g => ?_⟩
      have hkN : k ∈ Subgroup.normalClosure ({d} : Set G) := hNtop ▸ Subgroup.mem_top k
      have hgN : g ∈ Subgroup.normalClosure ({d} : Set G) := hNtop ▸ Subgroup.mem_top g
      have hk' : (⟨k, hkN⟩ : ↥(Subgroup.normalClosure ({d} : Set G))) ∈
          K'.subgroupOf (Subgroup.normalClosure ({d} : Set G)) := Subgroup.mem_subgroupOf.2 hk
      have h := Subgroup.mem_subgroupOf.1 (hK'n.conj_mem _ hk' ⟨g, hgN⟩)
      simpa using h
    rw [hNtop] at hK'eq
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K' with h | h
    · obtain ⟨a, b, hab''⟩ := hnonab
      apply hab''
      rw [h, bot_sup_eq] at hK'eq
      have ha : a ∈ Subgroup.zpowers d := hK'eq ▸ Subgroup.mem_top a
      have hb : b ∈ Subgroup.zpowers d := hK'eq ▸ Subgroup.mem_top b
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self d i j).eq
    · rw [h, Subgroup.card_top] at hK'odd
      have heven : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard d
      exact (Nat.not_even_iff_odd.2 hK'odd) (even_iff_two_dvd.2 heven)
  · exfalso
    obtain ⟨a, b, hab''⟩ := hnonab
    have ha : a ∈ Subgroup.normalClosure ({d} : Set G) := hNtop ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.normalClosure ({d} : Set G) := hNtop ▸ Subgroup.mem_top b
    exact hab'' (hab' a ha b hb).1
  · set N := Subgroup.normalClosure ({d} : Set G) with hN
    have hcenN : Subgroup.center ↥N = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have hzc : (z : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ N := hNtop ▸ Subgroup.mem_top g
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
      rw [center_eq_bot_of_simple_nonabelian G hnonab] at hzc
      exact Subtype.ext (Subgroup.mem_bot.1 hzc)
    let eN : ↥N ≃* G := (MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv
    let eQ : ↥N ⧸ Subgroup.center ↥N ≃* ↥N :=
      (QuotientGroup.quotientMulEquivOfEq hcenN).trans QuotientGroup.quotientBot
    let e : G ≃* ↥N ⧸ Subgroup.center ↥N := (eQ.trans eN).symm
    rcases listGroup_or_exceptional_of_corBList hlist with hLG | hexc
    · exact ListGroup.of_mulEquiv e.symm hLG
    · exact absurd hexc (hIns G T T₁ m hy hm hq hT hnat hDD hcl hZ hab hO2 _ ⟨e⟩)

end CFSG.CGT.Timmesfeld75
