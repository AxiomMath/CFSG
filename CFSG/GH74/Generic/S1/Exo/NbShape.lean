module

public import CFSG.GH74.Generic.S1.Exo.NbLoc
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.GH74.Generic.S1.Exo.NbDefs

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG Subgroup CFSG.GH74 CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

theorem nb_quasi_of_sl2 {K : Type} [Group K] {q : ℕ} (hK : HasSL2Model K (fun r => r = q))
    (h5 : 5 ≤ q) : IsQuasisimple K := by
  obtain ⟨F, _, _, hq, ⟨e⟩⟩ := hK
  have e' : SL(2, F) ≃* K := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans e.symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e'
    (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 (by omega))

namespace NbhdHyp

variable {H : Type} [Group H] [Finite H] {q : ℕ} {w y : H} {J₂ J₄ : Subgroup H}
  (h : NbhdHyp H q w y J₂ J₄)

include h

theorem mem_cent_iff (g : H) : g ∈ centralizer ({w * y} : Set H) ↔ g * y = y * g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : w * y * g = w * (y * g) := by rw [mul_assoc]
  have e2 : g * (w * y) = w * (g * y) := by rw [← mul_assoc, h.w_central g, mul_assoc]
  rw [e1, e2]
  exact ⟨fun h' => mul_left_cancel h', fun h' => by rw [h']⟩

theorem cent_eq : centralizer ({w * y} : Set H) = centralizer ({y} : Set H) := by
  ext g
  rw [h.mem_cent_iff, Subgroup.mem_centralizer_singleton_iff]

theorem J₂_le_cent : J₂ ≤ centralizer ({w * y} : Set H) := fun a ha =>
  (h.mem_cent_iff a).2 (h.comm a ha y h.y_mem)

theorem J₄_le_cent : J₄ ≤ centralizer ({w * y} : Set H) := fun b hb =>
  (h.mem_cent_iff b).2 (h.y_cent b hb).symm

theorem J₂_quasi : IsQuasisimple ↥J₂ := nb_quasi_of_sl2 h.sl₂ h.five
theorem J₄_quasi : IsQuasisimple ↥J₄ := nb_quasi_of_sl2 h.sl₄ h.five
theorem J₂_perf : Group.IsPerfect ↥J₂ := h.J₂_quasi.1
theorem J₄_perf : Group.IsPerfect ↥J₄ := h.J₄_quasi.1

theorem y_mem_layer : y ∈ layer H := h.le_layer (Subgroup.mem_sup_right h.y_mem)

theorem comp_le {K : Subgroup H} (hK : IsComponent K) (hKX : K ≤ centralizer ({w * y} : Set H)) :
    K ≤ J₂ ⊔ J₄ := by
  have hc : IsComponent (K.subgroupOf (centralizer ({w * y} : Set H))) :=
    CFSG.LocalCores.component_overgroup hK hKX
  have hb := h.bal _ hc
  intro g hg
  exact hb ⟨⟨g, hKX hg⟩, hg, rfl⟩

theorem sup_cent_J₄ {g : H} (hg : g ∈ J₂ ⊔ J₄) (hgc : ∀ c ∈ J₄, g * c = c * g) :
    ∃ a ∈ J₂, ∃ z ∈ Subgroup.zpowers y, g = a * z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := nb_mem_sup_of_commute h.comm hg
  have hbc : ∀ c ∈ J₄, b * c = c * b := by
    intro c hc
    have h1 := hgc c hc
    have e : a * c = c * a := h.comm a ha c hc
    have : a * (b * c) = a * (c * b) := by
      calc a * (b * c) = a * b * c := by rw [mul_assoc]
        _ = c * (a * b) := h1
        _ = c * a * b := by rw [mul_assoc]
        _ = a * c * b := by rw [e]
        _ = a * (c * b) := by rw [mul_assoc]
    exact mul_left_cancel this
  rcases h.cent₄ b hb hbc with h1 | h1
  · exact ⟨a, ha, 1, Subgroup.one_mem _, by rw [h1]⟩
  · exact ⟨a, ha, y, Subgroup.mem_zpowers y, by rw [h1]⟩

theorem comp_le_J₂ {K : Subgroup H} (hK : IsComponent K) (hKX : K ≤ centralizer ({w * y} : Set H))
    (hKc : ∀ a ∈ K, ∀ c ∈ J₄, a * c = c * a) : K ≤ J₂ := by
  have hle := h.comp_le hK hKX
  refine nb_perfect_le_of_comm_pair (Z := Subgroup.zpowers y) ?_ ?_ hK.1.1 ?_
  · intro k hk z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((Commute.zpow_right (h.comm k hk y h.y_mem : Commute k y) n)).eq
  · intro z hz z' hz'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
    exact ((Commute.refl y).zpow_zpow n m).eq
  · intro g hg
    exact h.sup_cent_J₄ (hle hg) (fun c hc => hKc g hg c hc)

theorem same_case {K K' : Subgroup H} (hK : IsComponent K) (hK' : IsComponent K') (hne : K' ≠ K)
    (h2 : J₂ ≤ K) (h4 : J₄ ≤ K) : False := by
  have hcomm : ∀ a ∈ K', ∀ b ∈ K, a * b = b * a :=
    nb_comm_of_commutator_eq_bot ((CFSG.LocalCores.distinct_components_commute hK' hK).resolve_left hne)
  have hK'X : K' ≤ centralizer ({w * y} : Set H) :=
    fun a ha => (h.mem_cent_iff a).2 (hcomm a ha y (h4 h.y_mem))
  have hle : K' ≤ K := (h.comp_le hK' hK'X).trans (sup_le h2 h4)
  exact nb_false_of_comm_self hK'.1 (fun a ha b hb => hcomm a ha b (hle hb))

theorem loc_comp {K₁ K₂ Λ : Subgroup H} (hK₁ : IsComponent K₁) (hlayer : layer H = K₁ ⊔ K₂)
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hΛX : Λ ≤ centralizer ({w * y} : Set H))
    (hΛc : IsComponent (Λ.subgroupOf (centralizer ({w * y} : Set H))))
    (hΛperf : Group.IsPerfect ↥Λ) (hΛl : Λ ≤ layer H) : Λ ≤ K₁ ∨ Λ ≤ K₂ := by
  rw [h.cent_eq] at hΛX hΛc
  rcases nb_dichotomy hΛX hΛc hK₁ with h1 | h1
  · exact Or.inl h1
  · right
    refine nb_loc h12 hΛperf (fun l hl => nb_mem_sup_of_commute h12 (hlayer ▸ hΛl hl)) ?_
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hΛX hl)) h1
    exact nb_mem_sup_of_commute h12 (hlayer ▸ h.y_mem_layer)

theorem two_case {Ka Kb : Subgroup H} (hKa : IsComponent Ka) (hKb : IsComponent Kb) (hne : Ka ≠ Kb)
    (hall : ∀ K, IsComponent K → K = Ka ∨ K = Kb) (h2 : J₂ ≤ Ka) (h4 : J₄ ≤ Kb) :
    Ka = J₂ ∧ J₄ ≠ Kb ∧ layer H = J₂ ⊔ Kb := by
  have hcomm : ∀ a ∈ Ka, ∀ b ∈ Kb, a * b = b * a :=
    nb_comm_of_commutator_eq_bot ((CFSG.LocalCores.distinct_components_commute hKa hKb).resolve_left hne)
  have hKaX : Ka ≤ centralizer ({w * y} : Set H) :=
    fun a ha => (h.mem_cent_iff a).2 (hcomm a ha y (h4 h.y_mem))
  have hKaJ : Ka ≤ J₂ := h.comp_le_J₂ hKa hKaX (fun a ha c hc => hcomm a ha c (h4 hc))
  have hEq : Ka = J₂ := le_antisymm hKaJ h2
  have hlayer : layer H = Ka ⊔ Kb := nb_layer_eq_of_components hKa hKb hall
  refine ⟨hEq, ?_, hEq ▸ hlayer⟩
  intro hJ
  apply h.growth
  rw [hlayer, hEq, ← hJ]

theorem struct (hnc : NoCommonComponent J₂ J₄) :
    ∃ N₂ : Subgroup H, IsComponent J₂ ∧ IsComponent N₂ ∧ layer H = J₂ ⊔ N₂ ∧ J₄ ≤ N₂ ∧ J₄ ≠ N₂ ∧
      (∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) ∧ (∀ K, IsComponent K → K = J₂ ∨ K = N₂) := by
  by_cases hex : ∃ K₁ K₂ : Subgroup H, IsComponent K₁ ∧ IsComponent K₂ ∧ K₁ ≠ K₂
  · obtain ⟨K₁, K₂, hK₁, hK₂, hne⟩ := hex
    have hall : ∀ K, IsComponent K → K = K₁ ∨ K = K₂ := by
      intro K hK
      rcases nb_components_le_two h.gen4 hK hK₁ hK₂ with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd h1 hne
    have hall' : ∀ K, IsComponent K → K = K₂ ∨ K = K₁ := fun K hK => (hall K hK).symm
    have hlayer : layer H = K₁ ⊔ K₂ := nb_layer_eq_of_components hK₁ hK₂ hall
    have h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a :=
      nb_comm_of_commutator_eq_bot ((CFSG.LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hne)
    have hJ₂ := h.loc_comp hK₁ hlayer h12 h.J₂_le_cent h.comp₂ h.J₂_perf
      (le_trans le_sup_left h.le_layer)
    have hJ₄ := h.loc_comp hK₁ hlayer h12 h.J₄_le_cent h.comp₄ h.J₄_perf
      (le_trans le_sup_right h.le_layer)
    rcases hJ₂ with h2 | h2 <;> rcases hJ₄ with h4 | h4
    · exact (h.same_case hK₁ hK₂ hne.symm h2 h4).elim
    · obtain ⟨hEq, hneq, hl⟩ := h.two_case hK₁ hK₂ hne hall h2 h4
      refine ⟨K₂, hEq ▸ hK₁, hK₂, hl, h4, hneq, ?_, ?_⟩
      · intro a ha b hb
        exact h12 a (hEq ▸ ha) b hb
      · intro K hK
        rcases hall K hK with h1 | h1
        · exact Or.inl (h1.trans hEq)
        · exact Or.inr h1
    · obtain ⟨hEq, hneq, hl⟩ := h.two_case hK₂ hK₁ hne.symm hall' h2 h4
      refine ⟨K₁, hEq ▸ hK₂, hK₁, hl, h4, hneq, ?_, ?_⟩
      · intro a ha b hb
        have := h12 b hb a (hEq ▸ ha)
        exact this.symm
      · intro K hK
        rcases hall K hK with h1 | h1
        · exact Or.inr h1
        · exact Or.inl (h1.trans hEq)
    · exact (h.same_case hK₂ hK₁ hne h2 h4).elim
  · push Not at hex
    exfalso
    by_cases hnone : ∃ K₀ : Subgroup H, IsComponent K₀
    · obtain ⟨K₀, hK₀⟩ := hnone
      have hall : ∀ K, IsComponent K → K = K₀ ∨ K = K₀ := fun K hK => Or.inl (hex K K₀ hK hK₀)
      have hlayer : layer H = K₀ ⊔ K₀ := nb_layer_eq_of_components hK₀ hK₀ hall
      rw [sup_idem] at hlayer
      exact hnc K₀ hK₀ ⟨hlayer ▸ (le_trans le_sup_left h.le_layer),
        hlayer ▸ (le_trans le_sup_right h.le_layer)⟩
    · push Not at hnone
      apply h.growth
      rw [nb_layer_eq_bot_of_no_component hnone]
      exact bot_le

end NbhdHyp

end CFSG.GH74.Generic.S1.Exo
