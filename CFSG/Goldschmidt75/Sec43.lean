module

public import CFSG.Goldschmidt75.Sec43a

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_normalClosureIn {H S : Subgroup G} {c y : G} (hc : c ∈ H)
    (hy : y ∈ normalClosureIn H S) : c * y * c⁻¹ ∈ normalClosureIn H S := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, (normalClosure_normal).conj_mem _ hy' _, rfl⟩

omit [Finite G] in
theorem le_normalizer_normalClosureIn (H S : Subgroup G) :
    H ≤ normalizer ((normalClosureIn H S : Subgroup G) : Set G) := fun _ hc =>
  mem_normalizer_of_forall (fun _ hy => conj_mem_normalClosureIn hc hy)
    (fun _ hy => by simpa using conj_mem_normalClosureIn (inv_mem hc) hy)

omit [Finite G] in
theorem le_normalizer_oddCoreOf_of_le_normalizer {L N : Subgroup G}
    (hL : L ≤ normalizer (N : Set G)) : L ≤ normalizer ((oddCoreOf N : Subgroup G) : Set G) :=
  fun l hl => mem_normalizer_of_conjSub_eq (by
    rw [conjSub_oddCoreOf, conjSub_eq_of_mem_normalizer (hL hl)])

omit [Finite G] in
theorem le_normalizer_sup_of_maps {X A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ B) (hB : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ B) :
    X ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ z ∈ A ⊔ B, x * z * x⁻¹ ∈ A ⊔ B := by
    intro x hx z hz
    have hz' : z ∈ ((A ⊔ B : Subgroup G) : Set G) := hz
    rw [coe_mul_of_left_le_normalizer_right _ _ hAB] at hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := hz'
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact mul_mem (hA x hx a ha) (mem_sup_right (hB x hx b hb))
  intro x hx
  exact mem_normalizer_of_forall (key x hx) (by simpa using key x⁻¹ (inv_mem hx))

variable {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.exists_hat (h : MinCE G T S₁ S₂) {L R₁ R₂ : Subgroup G} (hR₁ : R₁ ≤ S₁)
    (hR₂ : R₂ ≤ S₂) (hR₁L : R₁ ≤ L) (hR₂L : R₂ ≤ L) :
    ∃ (P : Sylow 2 L) (Q₁ Q₂ : Subgroup G), R₁ ≤ Q₁ ∧ R₂ ≤ Q₂ ∧ Q₁ ≤ L ∧ Q₂ ≤ L ∧
      Q₁.subgroupOf L ≤ P ∧ Q₂.subgroupOf L ≤ P ∧
      fusionStronglyClosed ((Q₁.subgroupOf L : Subgroup L) : Set L) P ∧
      fusionStronglyClosed ((Q₂.subgroupOf L : Subgroup L) : Set L) P ∧
      Q₁ ≤ centralizer (Q₂ : Set G) ∧ Q₁ ⊓ Q₂ = ⊥ := by
  have hp : IsPGroup 2 ((R₁ ⊔ R₂).subgroupOf L) :=
    (T.isPGroup'.to_le (sup_le (hR₁.trans h.le₁) (hR₂.trans h.le₂))).comap_subtype
  obtain ⟨P, hPR⟩ := hp.exists_le_sylow
  obtain ⟨T', hT'⟩ := (P.isPGroup'.map L.subtype).exists_le_sylow
  obtain ⟨x₁, hx₁, hx₁c, hx₁m⟩ := exists_conj_le_sylow T T' h.le₁ h.sc₁
  obtain ⟨x₂, hx₂, hx₂c, hx₂m⟩ := exists_conj_le_sylow T T' h.le₂ h.sc₂
  have hRT' : ∀ {R : Subgroup G}, R ≤ R₁ ⊔ R₂ → R ≤ L → R ≤ T' := fun hR hRL x hx =>
    hT' ⟨⟨x, hRL hx⟩, hPR (mem_subgroupOf.mpr (hR hx)), rfl⟩
  have hdisj : conjSub x₁ S₁ ⊓ conjSub x₂ S₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have h1 := mem_conjSub.mp hy.1
    have h2 := mem_conjSub.mp hy.2
    have e : (x₂ * x₁⁻¹)⁻¹⁻¹ * (x₁ * y * x₁⁻¹) * (x₂ * x₁⁻¹)⁻¹ = x₂ * y * x₂⁻¹ := by group
    have h3 : x₂ * y * x₂⁻¹ ∈ S₁ := by
      have h4 := h.sc₁ _ h1 _ (by rw [e]; exact h.le₂ h2)
      rwa [e] at h4
    have h5 : x₂ * y * x₂⁻¹ ∈ S₁ ⊓ S₂ := ⟨h3, h2⟩
    rw [h.disj, mem_bot] at h5
    have : y = x₂⁻¹ * (x₂ * y * x₂⁻¹) * x₂ := by group
    rw [this, h5]
    group
  refine ⟨P, conjSub x₁ S₁ ⊓ L, conjSub x₂ S₂ ⊓ L,
    fun u hu => ⟨hx₁m u (hRT' le_sup_left hR₁L hu) 1 (by simpa using hR₁ hu), hR₁L hu⟩,
    fun u hu => ⟨hx₂m u (hRT' le_sup_right hR₂L hu) 1 (by simpa using hR₂ hu), hR₂L hu⟩,
    inf_le_right, inf_le_right, trace_le_sylow T' hx₁ P hT', trace_le_sylow T' hx₂ P hT',
    stronglyClosed_trace T' hx₁c P hT', stronglyClosed_trace T' hx₂c P hT', ?_, ?_⟩
  · intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    replace ha := (mem_inf.mp ha).1
    replace hb := (mem_inf.mp hb).1
    have hN₁ := sylow_le_normalizer T' hx₁ hx₁c
    have hN₂ := sylow_le_normalizer T' hx₂ hx₂c
    have hc : a * b * a⁻¹ * b⁻¹ ∈ conjSub x₁ S₁ ⊓ conjSub x₂ S₂ := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have := (mem_normalizer_iff.mp (hN₁ (hx₂ hb)) a⁻¹).mp (inv_mem ha)
        have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
        rw [e]
        exact mul_mem ha this
      · have := (mem_normalizer_iff.mp (hN₂ (hx₁ ha)) b).mp hb
        exact mul_mem this (inv_mem hb)
    rw [hdisj, mem_bot] at hc
    have := mul_inv_eq_one.mp hc
    calc b * a = (a * b * a⁻¹) * a := by rw [this]
      _ = a * b := by group
  · rw [eq_bot_iff]
    intro y hy
    have : y ∈ conjSub x₁ S₁ ⊓ conjSub x₂ S₂ := ⟨hy.1.1, hy.2.1⟩
    rwa [hdisj] at this

end CFSG.Goldschmidt75
