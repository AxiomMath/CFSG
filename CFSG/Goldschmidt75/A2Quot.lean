module

public import CFSG.Goldschmidt75.A2Comp2
public import CFSG.Goldschmidt75.A2Basic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup

variable {G : Type} [Group G] [Finite G]

namespace A2Comp

variable {T : Sylow 2 G} {S₁ S₂ K : Subgroup G}

omit [Finite G] in
theorem inf_centralizer_eq_bot (h : A2Comp T S₁ S₂ K) : K ⊓ centralizer (K : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, (mem_inf.mp hx).1⟩ : K) ∈ Subgroup.center K := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (mem_inf.mp hx).2 y y.2)
  rw [h.center_eq, mem_bot] at hxZ
  exact (mem_bot).mpr (congrArg Subtype.val hxZ)

omit [Finite G] in
theorem inf_sup_le_of_le (h : A2Comp T S₁ S₂ K) (hR : (T : Subgroup G) ⊓ K ≤ S₂) :
    S₁ ⊓ (S₂ ⊔ K) ≤ S₂ := by
  have : K.Normal := h.normal
  intro x hx
  have h1 := inf_sup_le_sup_inf (S := S₂) (K := K) h.le₂
    (mem_inf.mpr ⟨h.le₁ (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩)
  rwa [sup_eq_left.mpr hR] at h1

theorem inf_sup_le_of_typeI
    (h : A2Comp T S₁ S₂ K) (hI : IsGoldTypeI K)
    (h₁ : S₁ ⊓ ((T : Subgroup G) ⊓ K) ≤ Omega1 ((T : Subgroup G) ⊓ K))
    (h₂ : S₂ ⊓ ((T : Subgroup G) ⊓ K) ≤ Omega1 ((T : Subgroup G) ⊓ K)) :
    S₂ ⊓ (S₁ ⊔ K) ≤ S₁ := by
  have : K.Normal := h.normal
  set R := (T : Subgroup G) ⊓ K with hRdef
  set C := centralizer (K : Set G) with hC
  set P := (T : Subgroup G) ⊓ C with hP
  have hS₁K : S₁ ≤ K ⊔ C := h.inner_typeI hI fun α hα t ht => h₁ (h.mem_inf_of_mem hα ht)
  have hS₂K : S₂ ≤ K ⊔ C := h.symm.inner_typeI hI fun α hα t ht =>
    h₂ (h.symm.mem_inf_of_mem hα ht)
  have hTRP : (T : Subgroup G) ⊓ (K ⊔ C) ≤ R ⊔ P :=
    inf_sup_le_of_disjoint T h.inf_centralizer_eq_bot le_rfl
  have hPC : P ≤ C := inf_le_right
  have hPR : P ≤ centralizer (R : Set G) := fun p hp => by
    rw [mem_centralizer_iff]
    intro r hr
    exact (mem_centralizer_iff.mp (hPC hp) r (mem_inf.mp hr).2)
  obtain ⟨d, hdK, hdR, hfree⟩ := h.exists_borel hI
  have hdP : ∀ p ∈ P, d⁻¹ * p * d = p := by
    intro p hp
    have := mem_centralizer_iff.mp (hPC hp) d hdK
    calc d⁻¹ * p * d = d⁻¹ * (p * d) := by group
      _ = d⁻¹ * (d * p) := by rw [this]
      _ = p := by group
  have hRPT : R ⊔ P ≤ (T : Subgroup G) := sup_le inf_le_left inf_le_left
  have hdRP : ∀ v ∈ R ⊔ P, d⁻¹ * v * d ∈ R ⊔ P := by
    intro v hv
    have hPN : P ≤ normalizer (R : Set G) := hPR.trans (centralizer_le_normalizer _)
    have hv' : v ∈ ((P ⊔ R : Subgroup G) : Set G) := by rw [sup_comm]; exact hv
    rw [coe_mul_of_left_le_normalizer_right _ _ hPN] at hv'
    obtain ⟨p, hp, r, hr, rfl⟩ := hv'
    have e : d⁻¹ * (p * r) * d = (d⁻¹ * p * d) * (d⁻¹ * r * d) := by group
    rw [e, hdP p hp]
    exact mul_mem (mem_sup_right hp) (mem_sup_left (hdR r hr))
  have hsplit : ∀ {S : Subgroup G}, fusionStronglyClosed (S : Set G) T → ∀ v ∈ S ⊓ (R ⊔ P),
      ∃ r ∈ (S ⊓ (R ⊔ P)) ⊓ R, ∃ p ∈ (S ⊓ (R ⊔ P)) ⊓ P, v = r * p := by
    intro S hS v hv
    refine exists_mul_of_fixedPointFree hPR hdR hfree hdP inf_le_right (fun w hw => ?_) hv
    have h1 := hdRP w (mem_inf.mp hw).2
    exact mem_inf.mpr ⟨hS w (mem_inf.mp hw).1 d (hRPT h1), h1⟩
  intro y hy
  have hyS₂ := (mem_inf.mp hy).1
  have hyRP : y ∈ R ⊔ P := hTRP (mem_inf.mpr ⟨h.le₂ hyS₂,
    (sup_le hS₁K le_sup_left) (mem_inf.mp hy).2⟩)
  obtain ⟨r, hr, p, hp, rfl⟩ := hsplit h.sc₂ y (mem_inf.mpr ⟨hyS₂, hyRP⟩)
  have hrS₁ : r ∈ S₁ := (mem_inf.mp (h.omega1_le (h₂ (mem_inf.mpr
    ⟨(mem_inf.mp (mem_inf.mp hr).1).1, (mem_inf.mp hr).2⟩)))).1
  have hpS₁K : p ∈ S₁ ⊔ K := by
    have := mul_mem (inv_mem (mem_sup_left (T := K) hrS₁)) (mem_inf.mp hy).2
    simpa using this
  have hp' : p ∈ ((S₁ ⊔ K : Subgroup G) : Set G) := hpS₁K
  rw [mul_normal] at hp'
  obtain ⟨s, hs, k, hk, hsk⟩ := hp'
  obtain ⟨r', hr', p', hp'', rfl⟩ := hsplit h.sc₁ s (mem_inf.mpr ⟨hs,
    hTRP (mem_inf.mpr ⟨h.le₁ hs, hS₁K hs⟩)⟩)
  have hpP := (mem_inf.mp hp).2
  have hp'P := (mem_inf.mp hp'').2
  have hr'K : r' ∈ K := (mem_inf.mp (mem_inf.mp hr').2).2
  have hcomm : p' * r' = r' * p' := (mem_centralizer_iff.mp (hPC hp'P) r' hr'K).symm
  have hmem : p'⁻¹ * p ∈ K ⊓ C := by
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem (hPC hp'P)) (hPC hpP)⟩
    have e : p'⁻¹ * p = r' * k := by
      rw [← hsk]
      calc p'⁻¹ * (r' * p' * k) = p'⁻¹ * (p' * r') * k := by rw [hcomm]; group
        _ = r' * k := by group
    rw [e]
    exact mul_mem hr'K hk
  rw [h.inf_centralizer_eq_bot, mem_bot, inv_mul_eq_one] at hmem
  rw [← hmem]
  exact mul_mem hrS₁ (mem_inf.mp (mem_inf.mp hp'').1).1

theorem inf_sup_le_or
    (h : A2Comp T S₁ S₂ K) :
    S₁ ⊓ (S₂ ⊔ K) ≤ S₂ ∨ S₂ ⊓ (S₁ ⊔ K) ≤ S₁ := by
  rcases h.trichotomy with h1 | h2 | ⟨hI, h₁, h₂⟩
  · exact Or.inr (h.symm.inf_sup_le_of_le h1)
  · exact Or.inl (h.inf_sup_le_of_le h2)
  · exact Or.inr (h.inf_sup_le_of_typeI hI h₁ h₂)

theorem inf_sup_le
    (h : A2Comp T S₁ S₂ K) : (S₁ ⊔ K) ⊓ (S₂ ⊔ K) ≤ (S₁ ⊓ S₂) ⊔ K := by
  have : K.Normal := h.normal
  intro x hx
  rcases h.inf_sup_le_or with h1 | h2
  · have hx1 : x ∈ ((S₁ ⊔ K : Subgroup G) : Set G) := (mem_inf.mp hx).1
    rw [mul_normal] at hx1
    obtain ⟨s, hs, k, hk, rfl⟩ := hx1
    have hs2 : s ∈ S₂ ⊔ K := by
      have := mul_mem (mem_inf.mp hx).2 (inv_mem (mem_sup_right (S := S₂) hk))
      simpa using this
    exact mul_mem_sup (mem_inf.mpr ⟨hs, h1 (mem_inf.mpr ⟨hs, hs2⟩)⟩) hk
  · have hx2 : x ∈ ((S₂ ⊔ K : Subgroup G) : Set G) := (mem_inf.mp hx).2
    rw [mul_normal] at hx2
    obtain ⟨s, hs, k, hk, rfl⟩ := hx2
    have hs1 : s ∈ S₁ ⊔ K := by
      have := mul_mem (mem_inf.mp hx).1 (inv_mem (mem_sup_right (S := S₁) hk))
      simpa using this
    exact mul_mem_sup (mem_inf.mpr ⟨h2 (mem_inf.mpr ⟨hs, hs1⟩), hs⟩) hk

end A2Comp

end CFSG.Goldschmidt75
