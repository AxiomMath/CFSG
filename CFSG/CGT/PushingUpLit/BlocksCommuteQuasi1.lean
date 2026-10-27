module

public import CFSG.CGT.PushingUpLit.BlocksCommuteBar

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_of_pow_mem_odd {t : G} (ht : ∃ k : ℕ, t ^ 2 ^ k = 1) {n : ℕ} (hn : Odd n)
    (S : Subgroup G) (h : t ^ n ∈ S) : t ∈ S := by
  obtain ⟨k, hk⟩ := ht
  have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime n (orderOf t) :=
    Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hn))
  exact (Subgroup.zpowers_le.2 h) (CFSG.Quasithin.A4.mem_zpowers_pow_of_coprime hcop)

theorem exists_pow_eq_one_of_mem_oTwoIn {X : Subgroup G} {t : G} (ht : t ∈ oTwoIn X) :
    ∃ k : ℕ, t ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := isPGroup_oTwoIn X ⟨t, ht⟩
  exact ⟨k, congrArg Subtype.val hk⟩

variable [Finite G]

theorem blockU_commute {X : Subgroup G} (hX : IsShortGroup ↥X) {u v : G}
    (hu : u ∈ blockU X) (hv : v ∈ blockU X) : u * v = v * u :=
  blockU_comm_of_short hX u hu v (blockU_le_oTwoIn X hv)

omit [Finite G] in
theorem commutator_mem_blockU_of_mem {X : Subgroup G} {x r : G} (hx : x ∈ X)
    (hr : r ∈ oTwoIn X) : ⁅x, r⁆ ∈ blockU X := by
  have h1 : ⁅x, r⁆ ∈ ⁅(X : Subgroup G), oTwoIn X⁆ := Subgroup.commutator_mem_commutator hx hr
  rw [Subgroup.commutator_comm] at h1
  exact h1

theorem commutator_mem_pCore_of_qs {X Y : Subgroup G} (hX : IsBlockOf X)
    (hq : IsQuasisimple (↥X ⧸ pCore 2 ↥X)) (hY : IsBlockOf Y) (hne : X ≠ Y) :
    ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ pCore 2 G := by
  have hc₁ := isComponent_barImg hX hq
  rcases CFSG.LocalCores.component_subnormal_subgroup hc₁ (barImg_subnormal hY.1) with
    hle | hcomm
  · exfalso
    rcases hY.2.quotient_type with hq₂ | hp
    · have hc₂ := isComponent_barImg hY hq₂
      rcases CFSG.LocalCores.component_subnormal_subgroup hc₂ (barImg_subnormal hX.1) with
        hle' | hcomm'
      · have heq : barImg X = barImg Y := le_antisymm hle hle'
        have e1 : X ≤ Y := le_of_le_sup_pCore hX hY (le_sup_pCore_of_barImg_le heq.le)
        have e2 : Y ≤ X := le_of_le_sup_pCore hY hX (le_sup_pCore_of_barImg_le heq.ge)
        exact hne (le_antisymm e1 e2)
      · rw [Subgroup.commutator_comm] at hcomm'
        exact false_of_le_of_commutator_eq_bot hc₁.1 hle hcomm'
    · have hp' : (Nat.card ↥(barImg Y)).Prime := by rw [card_barImg hY]; exact hp
      have : Fact (Nat.card ↥(barImg Y)).Prime := ⟨hp'⟩
      have hcyc : IsCyclic ↥(barImg Y) := isCyclic_of_prime_card rfl
      refine false_of_le_of_commutator_eq_bot hc₁.1 hle (le_bot_iff.mp ?_)
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [Subgroup.mem_bot]
      have hab : (⟨a, hle ha⟩ : ↥(barImg Y)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, hle ha⟩ :=
        (IsCyclic.commGroup (α := ↥(barImg Y))).mul_comm _ _
      have h2 : a * b = b * a := congrArg Subtype.val hab
      rw [commutatorElement_def, h2]
      group
  · exact commutator_mem_pCore_of_barImg hcomm

theorem le_normalizer_of_commutator_mem {X Y : Subgroup G} (hY : IsBlockOf Y)
    (h : ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ pCore 2 G) : X ≤ Subgroup.normalizer (Y : Set G) := by
  have key : ∀ a ∈ X, ∀ z ∈ Y, a * z * a⁻¹ ∈ Y := by
    intro a ha z hz
    have hle : Y.map (MulAut.conj a).toMonoidHom ≤ Y ⊔ pCore 2 G := by
      rintro _ ⟨w, hw, rfl⟩
      have hc := h a ha w hw
      have e : (MulAut.conj a).toMonoidHom w = ⁅a, w⁆ * w := by
        simp [commutatorElement_def, MulAut.conj_apply]
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup hc hw
    have := le_of_le_sup_pCore (hY.map_conj a) hY hle ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using this
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key a ha g hg, fun hg => ?_⟩
  have := key a⁻¹ (inv_mem ha) _ hg
  simpa [mul_assoc] using this

theorem commutator_mem_blockU {Y : Subgroup G} (hY : IsBlockOf Y) {a : G}
    (h : ∀ l ∈ Y, ⁅a, l⁆ ∈ oTwoIn Y) : ∀ l ∈ Y, ⁅a, l⁆ ∈ blockU Y := by
  have hnorm : ∀ g ∈ Y, ∀ u ∈ blockU Y, g * u * g⁻¹ ∈ blockU Y :=
    fun g hg u hu => conj_mem_blockU (Subgroup.le_normalizer hg) hu
  let N : Subgroup G :=
    { carrier := {l | l ∈ Y ∧ ⁅a, l⁆ ∈ blockU Y}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro l₁ l₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨mul_mem h₁ h₂, ?_⟩
        have e : ⁅a, l₁ * l₂⁆ = ⁅a, l₁⁆ * (l₁ * ⁅a, l₂⁆ * l₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem h₁' (hnorm l₁ h₁ _ h₂')
      inv_mem' := by
        rintro l ⟨h₁, h₁'⟩
        refine ⟨inv_mem h₁, ?_⟩
        have e : ⁅a, l⁻¹⁆ = l⁻¹ * ⁅a, l⁆⁻¹ * l := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := hnorm l⁻¹ (inv_mem h₁) _ (inv_mem h₁')
        simpa using this }
  have hodd : ∀ g ∈ Y, Odd (orderOf g) → g ∈ N := by
    intro g hg hgo
    refine ⟨hg, ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, t = ⁅a, g⁆ := ⟨_, rfl⟩
    have htR : t ∈ oTwoIn Y := ht ▸ h g hg
    have key : ∀ m : ℕ, ∃ u ∈ blockU Y, ⁅a, g ^ m⁆ = t ^ m * u := by
      intro m
      induction m with
      | zero => exact ⟨1, one_mem _, by simp⟩
      | succ m ih =>
        obtain ⟨u, hu, e⟩ := ih
        have hv : ⁅g ^ m, t⁆ ∈ blockU Y := commutator_mem_blockU_of_mem (pow_mem hg m) htR
        refine ⟨t⁻¹ * (u * ⁅g ^ m, t⁆) * t, ?_, ?_⟩
        · have := hnorm t⁻¹ (inv_mem (oTwoIn_le Y htR)) _ (mul_mem hu hv)
          simpa using this
        · have e2 : ⁅a, g ^ (m + 1)⁆ = ⁅a, g ^ m⁆ * (g ^ m * t * (g ^ m)⁻¹) := by
            rw [ht]
            simp only [commutatorElement_def]
            group
          rw [e2, e]
          simp only [commutatorElement_def]
          group
    obtain ⟨u, hu, e⟩ := key (orderOf g)
    rw [pow_orderOf_eq_one] at e
    have htn : t ^ orderOf g ∈ blockU Y := by
      have e' : t ^ orderOf g = u⁻¹ := by
        have : t ^ orderOf g * u = 1 := by simpa using e.symm
        exact eq_inv_of_mul_eq_one_left this
      rw [e']
      exact inv_mem hu
    have := mem_of_pow_mem_odd (exists_pow_eq_one_of_mem_oTwoIn htR) hgo (blockU Y) htn
    rw [← ht]
    exact this
  intro l hl
  have hYN : Y ≤ N := by
    refine (eq_oTwoUpper_of_short hY.2).le.trans ?_
    exact (Subgroup.closure_le N).2 fun g hg => hodd g hg.1 hg.2
  exact (hYN hl).2

end CFSG.CGT.PushingUpLit
