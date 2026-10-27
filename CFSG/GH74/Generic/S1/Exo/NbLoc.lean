module

public import CFSG.GH74.Generic.S3.LyRank3
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG Subgroup
open scoped commutatorElement

section Generic

variable {H : Type*} [Group H]

theorem nb_step1 {K₁ K₂ : Subgroup H} {a₁ a₂ l₁ l₂ : H}
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (ha₁ : a₁ ∈ K₁) (ha₂ : a₂ ∈ K₂) (hl₁ : l₁ ∈ K₁) (hl₂ : l₂ ∈ K₂)
    (hy : l₁ * l₂ * (a₁ * a₂) = a₁ * a₂ * (l₁ * l₂)) :
    l₁ * a₁ * l₁⁻¹ * a₁⁻¹ ∈ K₁ ⊓ K₂ := by
  have c12 : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b := fun a ha b hb => h12 a ha b hb
  have h1 : l₁ * a₁ * l₁⁻¹ * a₁⁻¹ ∈ K₁ :=
    K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hl₁ ha₁) (K₁.inv_mem hl₁)) (K₁.inv_mem ha₁)
  refine ⟨h1, ?_⟩
  have hg : l₂ * a₂ * l₂⁻¹ * a₂⁻¹ ∈ K₂ :=
    K₂.mul_mem (K₂.mul_mem (K₂.mul_mem hl₂ ha₂) (K₂.inv_mem hl₂)) (K₂.inv_mem ha₂)
  set g := l₂ * a₂ * l₂⁻¹ * a₂⁻¹ with hgdef
  have hg' : g⁻¹ ∈ K₂ := K₂.inv_mem hg
  suffices h : l₁ * a₁ * l₁⁻¹ * a₁⁻¹ = g⁻¹ by rw [h]; exact hg'
  have e1 : l₂ * a₁ = a₁ * l₂ := (c12 a₁ ha₁ l₂ hl₂).symm.eq
  have e2 : l₁ * a₂ = a₂ * l₁ := (c12 l₁ hl₁ a₂ ha₂).eq
  have star : l₁ * a₁ * (l₂ * a₂) = a₁ * l₁ * (a₂ * l₂) := by
    calc l₁ * a₁ * (l₂ * a₂) = l₁ * (a₁ * l₂) * a₂ := by simp only [mul_assoc]
      _ = l₁ * (l₂ * a₁) * a₂ := by rw [e1]
      _ = l₁ * l₂ * (a₁ * a₂) := by simp only [mul_assoc]
      _ = a₁ * a₂ * (l₁ * l₂) := hy
      _ = a₁ * (a₂ * l₁) * l₂ := by simp only [mul_assoc]
      _ = a₁ * (l₁ * a₂) * l₂ := by rw [e2]
      _ = a₁ * l₁ * (a₂ * l₂) := by simp only [mul_assoc]
  have h2 : a₁ * l₁ = l₁ * a₁ * g := by
    have := congrArg (fun z => z * (a₂ * l₂)⁻¹) star.symm
    simp only [mul_inv_cancel_right] at this
    rw [this, hgdef]
    group
  have h3 : g⁻¹ = l₁⁻¹ * a₁⁻¹ * l₁ * a₁ := by
    have : g = a₁⁻¹ * l₁⁻¹ * (a₁ * l₁) := by rw [h2]; group
    rw [this]; group
  have hl₁g : Commute l₁ g := c12 l₁ hl₁ g hg
  have ha₁g : Commute a₁ g := c12 a₁ ha₁ g hg
  calc l₁ * a₁ * l₁⁻¹ * a₁⁻¹ = a₁ * (l₁ * (l₁⁻¹ * a₁⁻¹ * l₁ * a₁) * l₁⁻¹) * a₁⁻¹ := by group
    _ = a₁ * (l₁ * g⁻¹ * l₁⁻¹) * a₁⁻¹ := by rw [← h3]
    _ = a₁ * g⁻¹ * a₁⁻¹ := by rw [hl₁g.inv_right.mul_inv_cancel]
    _ = g⁻¹ := ha₁g.inv_right.mul_inv_cancel

theorem nb_central_of_mem_inf {K₁ K₂ : Subgroup H}
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) {z l : H} (hz : z ∈ K₁ ⊓ K₂)
    (hl : ∃ a ∈ K₁, ∃ b ∈ K₂, l = a * b) : z * l = l * z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hl
  have h1 : z * a = a * z := (h12 a ha z hz.2).symm
  have h2 : z * b = b * z := h12 z hz.1 b hb
  calc z * (a * b) = (z * a) * b := by rw [mul_assoc]
    _ = (a * z) * b := by rw [h1]
    _ = a * (z * b) := by rw [mul_assoc]
    _ = a * (b * z) := by rw [h2]
    _ = a * b * z := by rw [mul_assoc]

theorem nb_comm_mul_mul {a b c d : H} (hbc : Commute b c) (hbd : Commute b d) (hda : Commute d a) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ := by
  have e1 : b * c * d * b⁻¹ = c * d := by
    rw [hbc.eq, mul_assoc c b d, hbd.eq]
    group
  rw [commutatorElement_def, commutatorElement_def]
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = a * (b * c * d * b⁻¹) * a⁻¹ * d⁻¹ * c⁻¹ := by
        group
    _ = a * c * (d * a⁻¹) * d⁻¹ * c⁻¹ := by rw [e1]; group
    _ = a * c * (a⁻¹ * d) * d⁻¹ * c⁻¹ := by rw [hda.inv_right.eq]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem nb_loc {K₁ K₂ Λ : Subgroup H} {y : H}
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hperf : Group.IsPerfect ↥Λ)
    (hΛN : ∀ l ∈ Λ, ∃ a ∈ K₁, ∃ b ∈ K₂, l = a * b)
    (hy : ∃ a ∈ K₁, ∃ b ∈ K₂, y = a * b)
    (hΛy : ∀ l ∈ Λ, l * y = y * l)
    (hcomm : ∀ l ∈ Λ, ∀ u ∈ K₁, u * y = y * u → l * u = u * l) : Λ ≤ K₂ := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hy
  have c12 : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b := fun a ha b hb => h12 a ha b hb
  have ha12 : Commute a₁ a₂ := c12 a₁ ha₁ a₂ ha₂
  have hZ : ∀ k : ℤ, ∀ l ∈ Λ, ⁅l, a₁ ^ k⁆ ∈ centralizer (Λ : Set H) := by
    intro k l hl
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := hΛN l hl
    have hy' : l₁ * l₂ * (a₁ ^ k * a₂ ^ k) = a₁ ^ k * a₂ ^ k * (l₁ * l₂) := by
      have := ((show Commute (l₁ * l₂) (a₁ * a₂) from hΛy _ hl)).zpow_right k
      rw [ha12.mul_zpow] at this
      exact this.eq
    have hz := nb_step1 h12 (K₁.zpow_mem ha₁ k) (K₂.zpow_mem ha₂ k) hl₁ hl₂ hy'
    have hcl₂ : Commute l₂ (a₁ ^ k) := (c12 _ (K₁.zpow_mem ha₁ k) l₂ hl₂).symm
    have : ⁅l₁ * l₂, a₁ ^ k⁆ = l₁ * a₁ ^ k * l₁⁻¹ * (a₁ ^ k)⁻¹ := by
      rw [commutatorElement_def, mul_inv_rev]
      calc l₁ * l₂ * a₁ ^ k * (l₂⁻¹ * l₁⁻¹) * (a₁ ^ k)⁻¹
          = l₁ * (l₂ * a₁ ^ k * l₂⁻¹) * l₁⁻¹ * (a₁ ^ k)⁻¹ := by group
        _ = l₁ * a₁ ^ k * l₁⁻¹ * (a₁ ^ k)⁻¹ := by rw [hcl₂.mul_inv_cancel]
    rw [this]
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    exact (nb_central_of_mem_inf h12 hz (hΛN l' hl')).symm
  have hbot : ⁅Λ, zpowers a₁⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator hperf
    rw [eq_bot_iff]
    have : ⁅Λ, zpowers a₁⁆ ≤ centralizer (Λ : Set H) := by
      rw [Subgroup.commutator_le]
      intro l hl x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact hZ k l hl
    calc ⁅⁅Λ, zpowers a₁⁆, Λ⁆ ≤ ⁅centralizer (Λ : Set H), Λ⁆ :=
          Subgroup.commutator_mono this le_rfl
      _ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have step1 : ∀ l ∈ Λ, l * a₁ = a₁ * l := by
    intro l hl
    have h := Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers a₁)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have step2 : ∀ l ∈ Λ, ∃ l₁ ∈ K₁, ∃ l₂ ∈ K₂, l = l₁ * l₂ ∧ l₁ * (a₁ * a₂) = (a₁ * a₂) * l₁ ∧
      ∀ v ∈ K₁, v * (a₁ * a₂) = (a₁ * a₂) * v → l₁ * v = v * l₁ := by
    intro l hl
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := hΛN l hl
    refine ⟨l₁, hl₁, l₂, hl₂, rfl, ?_, ?_⟩
    · have h1 : l₁ * a₁ = a₁ * l₁ := by
        have := step1 _ hl
        have e : l₂ * a₁ = a₁ * l₂ := (c12 a₁ ha₁ l₂ hl₂).symm.eq
        calc l₁ * a₁ = l₁ * (a₁ * l₂) * l₂⁻¹ := by group
          _ = l₁ * (l₂ * a₁) * l₂⁻¹ := by rw [e]
          _ = (l₁ * l₂ * a₁) * l₂⁻¹ := by simp only [mul_assoc]
          _ = (a₁ * (l₁ * l₂)) * l₂⁻¹ := by rw [this]
          _ = a₁ * l₁ := by group
      have e2 : l₁ * a₂ = a₂ * l₁ := (c12 l₁ hl₁ a₂ ha₂).eq
      calc l₁ * (a₁ * a₂) = (l₁ * a₁) * a₂ := by rw [mul_assoc]
        _ = (a₁ * l₁) * a₂ := by rw [h1]
        _ = a₁ * (l₁ * a₂) := by rw [mul_assoc]
        _ = a₁ * (a₂ * l₁) := by rw [e2]
        _ = a₁ * a₂ * l₁ := by rw [mul_assoc]
    · intro v hv hvy
      have h := hcomm _ hl v hv hvy
      have e : l₂ * v = v * l₂ := (c12 v hv l₂ hl₂).symm.eq
      calc l₁ * v = l₁ * (v * l₂) * l₂⁻¹ := by group
        _ = l₁ * (l₂ * v) * l₂⁻¹ := by rw [e]
        _ = (l₁ * l₂ * v) * l₂⁻¹ := by simp only [mul_assoc]
        _ = (v * (l₁ * l₂)) * l₂⁻¹ := by rw [h]
        _ = v * l₁ := by group
  have step3 : ⁅Λ, Λ⁆ ≤ K₂ := by
    rw [Subgroup.commutator_le]
    intro l hl l' hl'
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl, hl₁y, hl₁c⟩ := step2 l hl
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl, hm₁y, hm₁c⟩ := step2 l' hl'
    have hlm : l₁ * m₁ = m₁ * l₁ := hl₁c m₁ hm₁ hm₁y
    have hc₁ : Commute l₁ m₁ := hlm
    have hc₂ : Commute l₁ m₂ := c12 l₁ hl₁ m₂ hm₂
    have hc₃ : Commute m₁ l₂ := c12 m₁ hm₁ l₂ hl₂
    have hc₄ : Commute l₁ l₂ := c12 l₁ hl₁ l₂ hl₂
    have hc₅ : Commute m₁ m₂ := c12 m₁ hm₁ m₂ hm₂
    have : ⁅l₁ * l₂, m₁ * m₂⁆ = ⁅l₂, m₂⁆ := by
      rw [hc₄.eq, hc₅.eq]
      exact nb_comm_mul_mul hc₂ hc₁ hc₃
    rw [this]
    exact K₂.mul_mem (K₂.mul_mem (K₂.mul_mem hl₂ hm₂) (K₂.inv_mem hl₂)) (K₂.inv_mem hm₂)
  have hperf' : ⁅Λ, Λ⁆ = Λ := Subgroup.isPerfect_iff.1 hperf
  rw [← hperf']
  exact step3


theorem nb_comm_of_commutator_eq_bot {A B : Subgroup H} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem nb_mem_sup_of_commute {K₁ K₂ : Subgroup H} (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    {g : H} (hg : g ∈ K₁ ⊔ K₂) : ∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b := by
  let S : Subgroup H :=
    { carrier := {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
        have : b * a' = a' * b := (h12 a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
          _ = a * (a' * b) * b' := by rw [this]
          _ = a * a' * (b * b') := by simp only [mul_assoc]
      one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
        have hc : Commute a b := h12 a ha b hb
        rw [mul_inv_rev]
        exact (hc.inv_inv).symm.eq }
  have hle : K₁ ⊔ K₂ ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, K₂.one_mem, by simp⟩) (fun b hb => ⟨1, K₁.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem nb_false_of_comm_self {K : Subgroup H} (hK : IsQuasisimple ↥K)
    (h : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : False := by
  obtain ⟨_, _, a, b, hab⟩ := hK
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (h a' a'.2 b' b'.2)

theorem nb_perfect_le_of_comm_pair {K Z Λ : Subgroup H}
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hperf : Group.IsPerfect ↥Λ) (hΛ : ∀ g ∈ Λ, ∃ a ∈ K, ∃ z ∈ Z, g = a * z) : Λ ≤ K := by
  have hperf' : ⁅Λ, Λ⁆ = Λ := Subgroup.isPerfect_iff.1 hperf
  have h : ⁅Λ, Λ⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    obtain ⟨a, ha, z, hz, rfl⟩ := hΛ g hg
    obtain ⟨a', ha', z', hz', rfl⟩ := hΛ g' hg'
    have hzc : Commute z a' := (hKZ a' ha' z hz).symm
    have hzz : Commute z z' := hZ z hz z' hz'
    have hz'a : Commute z' a := (hKZ a ha z' hz').symm
    rw [nb_comm_mul_mul hzc hzz hz'a]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha ha') (K.inv_mem ha)) (K.inv_mem ha')
  rw [← hperf']
  exact h

theorem nb_dichotomy [Finite H] {y : H} {Λ K : Subgroup H}
    (hΛX : Λ ≤ centralizer ({y} : Set H))
    (hΛ : IsComponent (Λ.subgroupOf (centralizer ({y} : Set H)))) (hK : IsComponent K) :
    Λ ≤ K ∨ ∀ l ∈ Λ, ∀ u ∈ K, u * y = y * u → l * u = u * l := by
  have hU : (K.subgroupOf (centralizer ({y} : Set H))).IsSubnormal := hK.2.subgroupOf
  rcases CFSG.LocalCores.component_subnormal_subgroup hΛ hU with h | h
  · left
    intro g hg
    have hg' : (⟨g, hΛX hg⟩ : ↥(centralizer ({y} : Set H))) ∈
        Λ.subgroupOf (centralizer ({y} : Set H)) := hg
    exact h hg'
  · right
    intro l hl u hu huy
    have hl' : (⟨l, hΛX hl⟩ : ↥(centralizer ({y} : Set H))) ∈
        Λ.subgroupOf (centralizer ({y} : Set H)) := hl
    have hu' : (⟨u, Subgroup.mem_centralizer_singleton_iff.2 huy⟩ : ↥(centralizer ({y} : Set H))) ∈
        K.subgroupOf (centralizer ({y} : Set H)) := hu
    have := nb_comm_of_commutator_eq_bot h _ hl' _ hu'
    exact congrArg Subtype.val this

theorem nb_layer_eq_of_components {Ka Kb : Subgroup H} (hKa : IsComponent Ka) (hKb : IsComponent Kb)
    (hall : ∀ K, IsComponent K → K = Ka ∨ K = Kb) : layer H = Ka ⊔ Kb := by
  have hset : {K : Subgroup H | IsComponent K} = {Ka, Kb} :=
    Set.ext fun K => ⟨hall K, by rintro (rfl | rfl); exact hKa; exact hKb⟩
  simp only [CFSG.layer.eq_sSup]
  rw [hset, sSup_pair]

theorem nb_layer_eq_bot_of_no_component (hnone : ∀ K : Subgroup H, ¬ IsComponent K) : layer H = ⊥ := by
  simp only [CFSG.layer.eq_sSup]
  have : {K : Subgroup H | IsComponent K} = ∅ := Set.eq_empty_of_forall_notMem fun K hK => hnone K hK
  rw [this, sSup_empty]

end Generic

section Rank

variable {H : Type} [Group H] [Finite H]

theorem nb_components_le_two (hgen : CFSG.GH74.Gen4 H) {K₁ K₂ K₃ : Subgroup H} (h₁ : IsComponent K₁)
    (h₂ : IsComponent K₂) (h₃ : IsComponent K₃) : K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have c12 := nb_comm_of_commutator_eq_bot
    ((CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left h12)
  have c13 := nb_comm_of_commutator_eq_bot
    ((CFSG.LocalCores.distinct_components_commute h₁ h₃).resolve_left h13)
  have c23 := nb_comm_of_commutator_eq_bot
    ((CFSG.LocalCores.distinct_components_commute h₂ h₃).resolve_left h23)
  exact CFSG.GH74.Generic.S3.not_gen4_of_three_commuting_quasisimple h₁.1 h₂.1 h₃.1 c12 c13 c23 hgen

end Rank

end CFSG.GH74.Generic.S1.Exo
