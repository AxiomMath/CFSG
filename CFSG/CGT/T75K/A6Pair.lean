module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveRho
public import CFSG.CGT.T75K.A6Comm

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T T₃ : Subgroup G}

section Pair

variable (c : Cfg T T₃)

include c

theorem pr_mul_self_T {t : G} (ht : t ∈ T) : t * t = 1 := elemAbelian_mul_self c.wc.1 ht

theorem pr_mul_self_U {u : G} (hu : u ∈ normIn T₃ T) : u * u = 1 :=
  elemAbelian_mul_self c.wc₁.1 (normIn_le _ _ hu)

omit c in
theorem pr_U_normalizes {u : G} (hu : u ∈ normIn T₃ T) :
    u ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hu).2

theorem pr_cm_mem_A {t u : G} (ht : t ∈ T) (hu : u ∈ normIn T₃ T) : cm t u ∈ normIn T T₃ := by
  by_cases hu1 : u = 1
  · rw [hu1, cm_one_right]
    exact (normIn T T₃).one_mem
  · rw [← c.inf_centralizer_eq_normIn hu hu1]
    refine ⟨cm_mem_T ht (pr_U_normalizes hu), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact cm_comm_u c.wc.1 ht (pr_U_normalizes hu) (pr_mul_self_U c hu)

theorem pr_cm_eq_one_iff {t u : G} (ht : t ∈ T) (hu : u ∈ normIn T₃ T) (hu1 : u ≠ 1) :
    cm t u = 1 ↔ t ∈ normIn T T₃ := by
  rw [cm_eq_one_iff, ← c.inf_centralizer_eq_normIn hu hu1, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩

theorem pr_cm_mul_right {t u u' : G} (ht : t ∈ T) (hu : u ∈ normIn T₃ T)
    (hu' : u' ∈ normIn T₃ T) : cm t (u * u') = cm t u * cm t u' := by
  have hA : cm t u' ∈ normIn T T₃ := pr_cm_mem_A c ht hu'
  have hcomm : cm t u' * u = u * cm t u' := c.comm_L_L₁ hA hu
  calc cm t (u * u') = cm t u * (u * cm t u' * u⁻¹) := by unfold cm; group
    _ = cm t u * cm t u' := by rw [← hcomm]; group

theorem pr_cm_right_inj {t u u' : G} (ht : t ∈ T) (htA : t ∉ normIn T T₃)
    (hu : u ∈ normIn T₃ T) (hu' : u' ∈ normIn T₃ T) (h : cm t u = cm t u') : u = u' := by
  have hvU : u'⁻¹ * u ∈ normIn T₃ T := (normIn T₃ T).mul_mem ((normIn T₃ T).inv_mem hu') hu
  have h1 : cm t u = cm t u' * cm t (u'⁻¹ * u) := by
    rw [← pr_cm_mul_right c ht hu' hvU]
    congr 1
    group
  have h2 : cm t (u'⁻¹ * u) = 1 := by
    have : cm t u' * cm t (u'⁻¹ * u) = cm t u' * 1 := by rw [← h1, mul_one, h]
    exact mul_left_cancel this
  by_contra hne
  have hv1 : u'⁻¹ * u ≠ 1 := by
    intro h'
    exact hne (inv_mul_eq_one.1 h').symm
  exact htA ((pr_cm_eq_one_iff c ht hvU hv1).1 h2)

theorem pr_exists_cm_eq [Finite G] (hcard : Nat.card (normIn T₃ T) = Nat.card (normIn T T₃))
    {t a : G} (ht : t ∈ T) (htA : t ∉ normIn T T₃) (ha : a ∈ normIn T T₃) :
    ∃ u ∈ normIn T₃ T, cm t u = a := by
  let f : ↥(normIn T₃ T) → ↥(normIn T T₃) := fun u => ⟨cm t (u : G), pr_cm_mem_A c ht u.2⟩
  have hinj : Function.Injective f := fun u v h =>
    Subtype.ext (pr_cm_right_inj c ht htA u.2 v.2 (congrArg Subtype.val h))
  obtain ⟨u, hu⟩ := (Function.Injective.bijective_of_nat_card_le hinj hcard.ge).2 ⟨a, ha⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

omit c in
theorem pr_conj_mem_U {g u : G} (hgT : g ∈ Subgroup.normalizer (T : Set G))
    (hgT₃ : g ∈ Subgroup.normalizer (T₃ : Set G)) (hu : u ∈ normIn T₃ T) :
    g * u * g⁻¹ ∈ normIn T₃ T := by
  obtain ⟨huT₃, huN⟩ := mem_normIn.1 hu
  exact mem_normIn.2 ⟨conj_mem_of_mem_normalizer hgT₃ huT₃,
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hgT huN)
      ((Subgroup.normalizer (T : Set G)).inv_mem hgT)⟩

omit c in
theorem pr_exists_three [Finite G] (h4 : Nat.card T = 4 * Nat.card (normIn T T₃)) :
    ∃ t₁ ∈ T, t₁ ∉ normIn T T₃ ∧ ∃ t₂ ∈ T, t₂ ∉ normIn T T₃ ∧ t₁ * t₂ ∉ normIn T T₃ := by
  have hApos : 0 < Nat.card (normIn T T₃) := Nat.card_pos
  obtain ⟨t₁, ht₁, ht₁A⟩ : ∃ t₁ ∈ T, t₁ ∉ normIn T T₃ := by
    by_contra hcon
    push Not at hcon
    have hle : T ≤ normIn T T₃ := hcon
    have := Subgroup.card_le_of_le hle
    omega
  refine ⟨t₁, ht₁, ht₁A, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcover : ∀ t ∈ T, t ∈ normIn T T₃ ∨ t₁ * t ∈ normIn T T₃ := by
    intro t ht
    by_cases hA : t ∈ normIn T T₃
    · exact Or.inl hA
    · exact Or.inr (hcon t ht hA)
  have hsub : (T : Set G) ⊆
      (normIn T T₃ : Set G) ∪ (fun a => t₁⁻¹ * a) '' (normIn T T₃ : Set G) := by
    intro t ht
    rcases hcover t ht with h | h
    · exact Or.inl h
    · exact Or.inr ⟨t₁ * t, h, by group⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (normIn T T₃ : Set G)
    ((fun a => t₁⁻¹ * a) '' (normIn T T₃ : Set G))
  have h3 : ((fun a => t₁⁻¹ * a) '' (normIn T T₃ : Set G)).ncard =
      (normIn T T₃ : Set G).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective t₁⁻¹)
  have hT' : (T : Set G).ncard = Nat.card T := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have hA' : (normIn T T₃ : Set G).ncard = Nat.card (normIn T T₃) := by
    rw [← Nat.card_coe_set_eq]
    rfl
  omega

theorem final_contra [Finite G] (hcard : Nat.card (normIn T₃ T) = Nat.card (normIn T T₃))
    (h4 : Nat.card T = 4 * Nat.card (normIn T T₃)) {Lm : G → Prop} {p a₀ g : G}
    (hp : p ∈ normIn T T₃) (hp1 : p ≠ 1) (hpLm : Lm p) (ha₀ : a₀ ∈ normIn T T₃) (ha₀Lm : ¬ Lm a₀)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) (hgT₃ : g ∈ Subgroup.normalizer (T₃ : Set G))
    (hfix : ∀ t ∈ T, Lm t → g * t * g⁻¹ = t) (hmove : ∀ t ∈ T, ¬ Lm t → g * t * g⁻¹ = t * p) :
    False := by
  have hpT : p ∈ T := normIn_le _ _ hp
  have ha₀T : a₀ ∈ T := normIn_le _ _ ha₀
  have hpp : p * p = 1 := pr_mul_self_T c hpT
  have hginv : ∀ t ∈ T, g⁻¹ * t * g = t ∨ g⁻¹ * t * g = t * p := by
    intro t ht
    have hg' : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer (T : Set G)).inv_mem hgT
    have ht' : g⁻¹ * t * g ∈ T := by
      have := conj_mem_of_mem_normalizer hg' ht
      simpa using this
    by_cases hLm : Lm (g⁻¹ * t * g)
    · left
      have h1 := hfix _ ht' hLm
      have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      rw [e] at h1
      exact h1.symm
    · right
      have := hmove _ ht' hLm
      have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      rw [e] at this
      calc g⁻¹ * t * g = (g⁻¹ * t * g * p) * p := by
            rw [mul_assoc (g⁻¹ * t * g) p p, hpp, mul_one]
        _ = t * p := by rw [← this]
  have hrel : ∀ t ∈ T, ∀ u ∈ normIn T₃ T, cm t (g * u * g⁻¹) = g * cm t u * g⁻¹ := by
    intro t ht u hu
    have e : cm t (g * u * g⁻¹) = g * cm (g⁻¹ * t * g) u * g⁻¹ := by unfold cm; group
    rw [e]
    have hcp : cm p u = 1 := by
      rw [cm_eq_one_iff]
      exact c.comm_L_L₁ hp hu
    rcases hginv t ht with h | h
    · rw [h]
    · rw [h, cm_mul_left c.wc.1 ht hpT (pr_U_normalizes hu), hcp, one_mul]
  have hα : ∀ a ∈ normIn T T₃, (Lm a → g * a * g⁻¹ = a) ∧ (¬ Lm a → g * a * g⁻¹ = a * p) :=
    fun a ha => ⟨hfix a (normIn_le _ _ ha), hmove a (normIn_le _ _ ha)⟩
  obtain ⟨t₁, ht₁, ht₁A, t₂, ht₂, ht₂A, ht₁₂A⟩ := pr_exists_three h4
  obtain ⟨u₁, hu₁, hcu₁⟩ := pr_exists_cm_eq c hcard ht₁ ht₁A hp
  obtain ⟨u₀, hu₀, hcu₀⟩ := pr_exists_cm_eq c hcard ht₁ ht₁A ha₀
  have hgu₁ : g * u₁ * g⁻¹ ∈ normIn T₃ T := pr_conj_mem_U hgT hgT₃ hu₁
  have hgu₀ : g * u₀ * g⁻¹ ∈ normIn T₃ T := pr_conj_mem_U hgT hgT₃ hu₀
  have hfix₁ : g * u₁ * g⁻¹ = u₁ := by
    apply pr_cm_right_inj c ht₁ ht₁A hgu₁ hu₁
    rw [hrel t₁ ht₁ u₁ hu₁, hcu₁, hfix p hpT hpLm]
  have hmv₀ : g * u₀ * g⁻¹ = u₀ * u₁ := by
    apply pr_cm_right_inj c ht₁ ht₁A hgu₀ ((normIn T₃ T).mul_mem hu₀ hu₁)
    rw [hrel t₁ ht₁ u₀ hu₀, hcu₀, pr_cm_mul_right c ht₁ hu₀ hu₁, hcu₀, hcu₁,
      hmove a₀ ha₀T ha₀Lm]
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    rw [h, cm_one_right] at hcu₁
    exact hp1 hcu₁.symm
  have hcu₁₂ : cm t₂ u₁ = p := by
    have hA' : cm t₂ u₀ ∈ normIn T T₃ := pr_cm_mem_A c ht₂ hu₀
    have h1 := hrel t₂ ht₂ u₀ hu₀
    rw [hmv₀, pr_cm_mul_right c ht₂ hu₀ hu₁] at h1
    have hne : cm t₂ u₁ ≠ 1 := fun h => ht₂A ((pr_cm_eq_one_iff c ht₂ hu₁ hu₁1).1 h)
    by_cases hLm : Lm (cm t₂ u₀)
    · rw [(hα _ hA').1 hLm] at h1
      exfalso
      apply hne
      have : cm t₂ u₀ * cm t₂ u₁ = cm t₂ u₀ * 1 := by rw [h1, mul_one]
      exact mul_left_cancel this
    · rw [(hα _ hA').2 hLm] at h1
      exact mul_left_cancel h1
  have hfin : cm (t₁ * t₂) u₁ = 1 := by
    rw [cm_mul_left c.wc.1 ht₁ ht₂ (pr_U_normalizes hu₁), hcu₁₂, hcu₁, hpp]
  exact ht₁₂A ((pr_cm_eq_one_iff c (T.mul_mem ht₁ ht₂) hu₁ hu₁1).1 hfin)

end Pair

end CFSG.CGT.T75K
