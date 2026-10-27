module

public import CFSG.CGT.T75L.Fusion

public section

namespace CFSG.CGT.T75L

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

section Swap

omit [Finite G] in
theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.comm_mem_cfgM (h : Sec4Hyp T T₁ a T₂) {w : G}
    (hfixT : ∀ t ∈ T, w * t * w⁻¹ * t⁻¹ ∈ normIn T T₁)
    (hfixT₁ : ∀ s ∈ T₁, w * s * w⁻¹ * s⁻¹ ∈ normIn T₁ T) :
    ∀ y ∈ T ⊔ T₁, w * y * w⁻¹ * y⁻¹ ∈ cfgM T T₁ := by
  intro y hy
  have hc := h.sec3.cfg
  have hX : T ⊔ T₁ = Subgroup.closure ((T : Set G) ∪ (T₁ : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hX] at hy
  refine Subgroup.closure_induction (p := fun y _ => w * y * w⁻¹ * y⁻¹ ∈ cfgM T T₁) ?_ ?_ ?_ ?_ hy
  · rintro x (hx | hx)
    · exact Cfg.normIn_le_cfgM_left T T₁ (hfixT x hx)
    · exact Cfg.normIn_le_cfgM_right T T₁ (hfixT₁ x hx)
  · simp
  · intro x y hx hy hpx hpy
    have hxX : x ∈ T ⊔ T₁ := by rw [hX]; exact hx
    have e : w * (x * y) * w⁻¹ * (x * y)⁻¹ =
        (w * x * w⁻¹ * x⁻¹) * (x * (w * y * w⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact (cfgM T T₁).mul_mem hpx (hc.conj_mem_cfgM hxX hpy)
  · intro x hx hpx
    have hxX : x ∈ T ⊔ T₁ := by rw [hX]; exact hx
    have e : w * x⁻¹ * w⁻¹ * x⁻¹⁻¹ = x⁻¹ * (w * x * w⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact hc.conj_mem_cfgM ((T ⊔ T₁).inv_mem hxX) ((cfgM T T₁).inv_mem hpx)

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.centralizes_normIn₁ (h : Sec4Hyp T T₁ a T₂) {w : G}
    (hfixT : ∀ t ∈ T, w * t * w⁻¹ * t⁻¹ ∈ normIn T T₁)
    (hfixT₁ : ∀ s ∈ T₁, w * s * w⁻¹ * s⁻¹ ∈ normIn T₁ T)
    (hL : ∀ l ∈ normIn T T₁, w * l = l * w) : ∀ l ∈ normIn T₁ T, w * l = l * w := by
  obtain ⟨s, hsX, hss, hsT, hsT₁⟩ := h.sec3.exists_swap
  have hB := h.comm_mem_cfgM hfixT hfixT₁
  have hMab := h.sec3.cfg.isElemAbelian_cfgM
  have hLs : normIn T₁ T = conjSubgroup s (normIn T T₁) := by
    have e := normIn_conj s T T₁
    rw [hsT, hsT₁] at e
    exact e
  intro l₁ hl₁
  rw [hLs, mem_conjSubgroup] at hl₁
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hm : s⁻¹ * w * s * w⁻¹ ∈ cfgM T T₁ := by
    have h1 := hB s⁻¹ ((T ⊔ T₁).inv_mem hsX)
    have h2 := (cfgM T T₁).inv_mem h1
    have e : (w * s⁻¹ * w⁻¹ * s⁻¹⁻¹)⁻¹ = s⁻¹ * w * s * w⁻¹ := by group
    rwa [e] at h2
  have hlM : s⁻¹ * l₁ * s ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁ hl₁
  have hcomm : (s⁻¹ * w * s) * (s⁻¹ * l₁ * s) = (s⁻¹ * l₁ * s) * (s⁻¹ * w * s) := by
    have hwl := hL _ hl₁
    have e1 : s⁻¹ * w * s = (s⁻¹ * w * s * w⁻¹) * w := by group
    rw [e1]
    set m := s⁻¹ * w * s * w⁻¹ with hmdef
    set l := s⁻¹ * l₁ * s with hldef
    calc (m * w) * l = m * (w * l) := mul_assoc _ _ _
      _ = m * (l * w) := by rw [hwl]
      _ = (m * l) * w := (mul_assoc _ _ _).symm
      _ = (l * m) * w := by rw [elemAbelian_mul_comm hMab hm hlM]
      _ = l * (m * w) := mul_assoc _ _ _
  have := conj_comm_iff (c := s) |>.2 hcomm
  have e1 : s * (s⁻¹ * w * s) * s⁻¹ = w := by group
  have e2 : s * (s⁻¹ * l₁ * s) * s⁻¹ = l₁ := by group
  rw [e1, e2] at this
  exact this

end Swap

section Fixed

omit [Finite G] in
theorem exists_fixed_ne_one {A : Subgroup G} {w : G} (hA : IsElemAbelian 2 A) (hne : A ≠ ⊥)
    (hwA : ∀ y ∈ A, w * y * w⁻¹ ∈ A) (hww : w * w = 1) :
    ∃ x ∈ A, x ≠ 1 ∧ w * x = x * w := by
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hu' : w * y * w⁻¹ ∈ A := hwA y hy
  by_cases hu : y * (w * y * w⁻¹) = 1
  · refine ⟨y, hy, hy1', ?_⟩
    have h1 : w * y * w⁻¹ = y⁻¹ := eq_inv_of_mul_eq_one_right hu
    rw [elemAbelian_inv hA hy] at h1
    calc w * y = (w * y * w⁻¹) * w := by group
      _ = y * w := by rw [h1]
  · refine ⟨y * (w * y * w⁻¹), A.mul_mem hy hu', hu, ?_⟩
    have hc : (w * y * w⁻¹) * y = y * (w * y * w⁻¹) := elemAbelian_mul_comm hA hu' hy
    have hwiw : w * (w * y * w⁻¹) * w⁻¹ = y := by
      calc w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w⁻¹ * w⁻¹) := by group
        _ = y := by rw [hww, ← mul_inv_rev, hww, inv_one, mul_one, one_mul]
    calc w * (y * (w * y * w⁻¹)) = (w * (y * (w * y * w⁻¹)) * w⁻¹) * w := by group
      _ = ((w * y * w⁻¹) * (w * (w * y * w⁻¹) * w⁻¹)) * w := by group
      _ = ((w * y * w⁻¹) * y) * w := by rw [hwiw]
      _ = (y * (w * y * w⁻¹)) * w := by rw [hc]

end Fixed

section Nonidentity

omit [Finite G] in
theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.mem_props_normIn₁ (h : Sec4Hyp T T₁ a T₂) {y : G}
    (hy : y ∈ normIn T₁ T) (hy1 : y ≠ 1) :
    y ∈ sec4N T T₁ T₂ ∧ y ∈ classD T ∧ y ∉ T := by
  refine ⟨normIn_le_sec4N_mid hy, ?_, fun hyT => hy1 ?_⟩
  · obtain ⟨k, hk⟩ := h.pair.conj
    exact mem_classD_of_mem_conjSubgroup (k := k) (hk ▸ (mem_normIn.1 hy).1) hy1
  · have : y ∈ T ⊓ T₁ := ⟨hyT, (mem_normIn.1 hy).1⟩
    rw [h.sec3.cfg.inf, Subgroup.mem_bot] at this
    exact this

omit [Finite G] in
theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.mem_props_normIn₂ (h : Sec4Hyp T T₁ a T₂) {y : G}
    (hy : y ∈ normIn T₂ T) (hy1 : y ≠ 1) :
    y ∈ sec4N T T₁ T₂ ∧ y ∈ classD T ∧ y ∉ T := by
  refine ⟨normIn_le_sec4N_right hy, ?_, fun hyT => hy1 ?_⟩
  · obtain ⟨k, hk⟩ := h.conj
    exact mem_classD_of_mem_conjSubgroup (k := k) (hk ▸ (mem_normIn.1 hy).1) hy1
  · have : y ∈ T ⊓ T₂ := ⟨hyT, (mem_normIn.1 hy).1⟩
    rw [h.inf_left_eq_bot, Subgroup.mem_bot] at this
    exact this

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_mul_of_mem_sec4N (h : Sec4Hyp T T₁ a T₂)
    {n : G} (hn : n ∈ sec4N T T₁ T₂) : ∃ ℓ ∈ normIn T₂ T, ∃ m ∈ cfgM T T₁, n = ℓ * m := by
  have hMN : cfgM T T₁ ≤ sec4N T T₁ T₂ := le_sup_left
  have hle : normIn T₂ T ≤ Subgroup.normalizer (cfgM T T₁ : Set G) := by
    intro ℓ hℓ
    refine Subgroup.centralizer_le_normalizer (cfgM T T₁ : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact elemAbelian_mul_comm h.isElemAbelian_sec4N (hMN hm) (normIn_le_sec4N_right hℓ)
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₂ T) (cfgM T T₁) hle
  have hsup : sec4N T T₁ T₂ = normIn T₂ T ⊔ cfgM T T₁ := sup_comm _ _
  have hn' : n ∈ ((normIn T₂ T : Set G) * (cfgM T T₁ : Set G)) := by
    rw [← hmul, ← hsup]
    exact hn
  obtain ⟨ℓ, hℓ, m, hm, hnm⟩ := hn'
  exact ⟨ℓ, hℓ, m, hm, hnm.symm⟩

end Nonidentity

section Kernel

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.inf_sec4Ker_eq₁ (h : Sec4Hyp T T₁ a T₂) :
    T₁ ⊓ sec4Ker T T₁ T₂ = normIn T₁ T := by
  obtain ⟨s, hsX, hss, hsT, hsT₁⟩ := h.sec3.exists_swap
  have hsY : s ∈ sec4Y T T₁ T₂ := (sup_le left_le_sec4Y mid_le_sec4Y) hsX
  have hLs : normIn T₁ T = conjSubgroup s (normIn T T₁) := by
    have e := normIn_conj s T T₁
    rw [hsT, hsT₁] at e
    exact e
  apply le_antisymm
  · rintro y ⟨hyT₁, hyK⟩
    have h1 : s⁻¹ * y * s ∈ T := by
      have : y ∈ conjSubgroup s T := hsT ▸ hyT₁
      exact mem_conjSubgroup.1 this
    have h2 : s⁻¹ * y * s⁻¹⁻¹ ∈ sec4Ker T T₁ T₂ :=
      h.conj_mem_sec4Ker hyK ((sec4Y T T₁ T₂).inv_mem hsY)
    have h3 : s⁻¹ * y * s ∈ T ⊓ sec4Ker T T₁ T₂ := ⟨h1, by simpa using h2⟩
    rw [h.inf_sec4Ker_eq] at h3
    rw [hLs, mem_conjSubgroup]
    exact h3
  · intro y hy
    refine ⟨normIn_le _ _ hy, ?_⟩
    rw [hLs, mem_conjSubgroup] at hy
    have h1 : s⁻¹ * y * s ∈ sec4Ker T T₁ T₂ :=
      h.sec4N_le_sec4Ker (normIn_le_sec4N_left hy)
    have h2 := h.conj_mem_sec4Ker h1 hsY
    have e : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    rwa [e] at h2

end Kernel

section Branch1

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.comm_mem_of_centralizes_cfgM (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) {w : G}
    (hwN : w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hww : w * w = 1)
    (hfixT : ∀ t ∈ T, w * t * w⁻¹ * t⁻¹ ∈ normIn T T₁)
    (hwM : ∀ m ∈ cfgM T T₁, w * m = m * w) (hwT₂ : w ∉ Subgroup.normalizer (T₂ : Set G)) :
    ∀ n ∈ sec4N T T₁ T₂, w * n * w⁻¹ * n⁻¹ ∈ T := by
  have hNab := h.isElemAbelian_sec4N
  have hc := h.sec3.cfg
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hLM : ∀ l ∈ normIn T T₁, w * l = l * w := fun l hl =>
    hwM l (Cfg.normIn_le_cfgM_left T T₁ hl)
  have hMN : cfgM T T₁ ≤ sec4N T T₁ T₂ := le_sup_left
  have key : ∀ ℓ ∈ normIn T₂ T, w * ℓ * w⁻¹ * ℓ⁻¹ ∈ T := by
    intro ℓ hℓ
    have hℓN : ℓ ∈ sec4N T T₁ T₂ := normIn_le_sec4N_right hℓ
    have hℓnorm : ℓ ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hℓ).2
    have hwℓN : w * ℓ * w⁻¹ ∈ sec4N T T₁ T₂ := (Subgroup.mem_normalizer_iff.1 hwN ℓ).1 hℓN
    have hℓinv : ℓ⁻¹ = ℓ := elemAbelian_inv hNab hℓN
    have heN : w * ℓ * w⁻¹ * ℓ⁻¹ ∈ sec4N T T₁ T₂ :=
      (sec4N T T₁ T₂).mul_mem hwℓN ((sec4N T T₁ T₂).inv_mem hℓN)
    have hcomm' : ℓ * (w * ℓ * w) = (w * ℓ * w) * ℓ := by
      have := elemAbelian_mul_comm hNab hℓN hwℓN
      rwa [hwi] at this
    have hew : w * (w * ℓ * w⁻¹ * ℓ⁻¹) = (w * ℓ * w⁻¹ * ℓ⁻¹) * w := by
      rw [hwi, hℓinv]
      calc w * (w * ℓ * w * ℓ) = (w * w) * ℓ * w * ℓ := by group
        _ = ℓ * w * ℓ := by rw [hww, one_mul]
        _ = ℓ * w * ℓ * (w * w) := by rw [hww, mul_one]
        _ = (ℓ * (w * ℓ * w)) * w := by group
        _ = ((w * ℓ * w) * ℓ) * w := by rw [hcomm']
        _ = (w * ℓ * w * ℓ) * w := by group
    have heM : w * ℓ * w⁻¹ * ℓ⁻¹ ∈ cfgM T T₁ := by
      obtain ⟨ℓ', hℓ', m', hm', hee⟩ := h.exists_mul_of_mem_sec4N heN
      have hℓ'eq : ℓ' = (w * ℓ * w⁻¹ * ℓ⁻¹) * m'⁻¹ := by rw [hee]; group
      have hwm' : w * m'⁻¹ = m'⁻¹ * w := hwM _ ((cfgM T T₁).inv_mem hm')
      have hℓ'w : w * ℓ' = ℓ' * w := by
        rw [hℓ'eq]
        calc w * ((w * ℓ * w⁻¹ * ℓ⁻¹) * m'⁻¹) = (w * (w * ℓ * w⁻¹ * ℓ⁻¹)) * m'⁻¹ :=
              (mul_assoc _ _ _).symm
          _ = ((w * ℓ * w⁻¹ * ℓ⁻¹) * w) * m'⁻¹ := by rw [hew]
          _ = (w * ℓ * w⁻¹ * ℓ⁻¹) * (w * m'⁻¹) := mul_assoc _ _ _
          _ = (w * ℓ * w⁻¹ * ℓ⁻¹) * (m'⁻¹ * w) := by rw [hwm']
          _ = ((w * ℓ * w⁻¹ * ℓ⁻¹) * m'⁻¹) * w := (mul_assoc _ _ _).symm
      have hℓ'1 : ℓ' = 1 := by
        by_contra hne
        exact hwT₂ (h.isWC₂.centralizer_le_normalizer (mem_normIn.1 hℓ').1 hne
          (Subgroup.mem_centralizer_singleton_iff.2 hℓ'w))
      rw [hee, hℓ'1, one_mul]
      exact hm'
    have heT : ∀ t ∈ T, (w * ℓ * w⁻¹ * ℓ⁻¹) * t = t * (w * ℓ * w⁻¹ * ℓ⁻¹) := by
      intro t ht
      have hlam : t * w * t⁻¹ * w⁻¹ ∈ normIn T T₁ := by
        have h1 := (normIn T T₁).inv_mem (hfixT t ht)
        have e : (w * t * w⁻¹ * t⁻¹)⁻¹ = t * w * t⁻¹ * w⁻¹ := by group
        rwa [e] at h1
      have hlam' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ normIn T T₁ := by
        have hT' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ T := by
          have e : t * ℓ * t⁻¹ * ℓ⁻¹ = t * (ℓ * t⁻¹ * ℓ⁻¹) := by group
          rw [e]
          exact T.mul_mem ht (conj_mem_of_mem_normalizer hℓnorm (T.inv_mem ht))
        have hN' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ sec4N T T₁ T₂ :=
          (sec4N T T₁ T₂).mul_mem ((Subgroup.mem_normalizer_iff.1
            (h.left_le_normalizer_sec4N ht) ℓ).1 hℓN) ((sec4N T T₁ T₂).inv_mem hℓN)
        have : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ T ⊓ sec4N T T₁ T₂ := ⟨hT', hN'⟩
        rwa [h.inf_sec4N_eq] at this
      have hlamN : t * w * t⁻¹ * w⁻¹ ∈ sec4N T T₁ T₂ :=
        hMN (Cfg.normIn_le_cfgM_left T T₁ hlam)
      have hlam'N : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ sec4N T T₁ T₂ :=
        hMN (Cfg.normIn_le_cfgM_left T T₁ hlam')
      have hwlam' : w * (t * ℓ * t⁻¹ * ℓ⁻¹) = (t * ℓ * t⁻¹ * ℓ⁻¹) * w := hLM _ hlam'
      have hlam_eq : t * w * t⁻¹ = (t * w * t⁻¹ * w⁻¹) * w := by group
      have hlam'_eq : t * ℓ * t⁻¹ = (t * ℓ * t⁻¹ * ℓ⁻¹) * ℓ := by group
      have hu : t * (w * ℓ * w⁻¹) * t⁻¹ = (t * ℓ * t⁻¹ * ℓ⁻¹) * (w * ℓ * w⁻¹) := by
        obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = t * w * t⁻¹ * w⁻¹ := ⟨_, rfl⟩
        obtain ⟨lam', hlam'def⟩ : ∃ lam', lam' = t * ℓ * t⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
        rw [← hlamdef] at hlam_eq hlamN
        rw [← hlam'def] at hlam'_eq hlam'N hwlam' ⊢
        calc t * (w * ℓ * w⁻¹) * t⁻¹
            = (t * w * t⁻¹) * (t * ℓ * t⁻¹) * (t * w * t⁻¹)⁻¹ := by group
          _ = (lam * w) * (lam' * ℓ) * (lam * w)⁻¹ := by rw [← hlam_eq, ← hlam'_eq]
          _ = lam * (w * lam') * ℓ * w⁻¹ * lam⁻¹ := by group
          _ = lam * (lam' * w) * ℓ * w⁻¹ * lam⁻¹ := by rw [hwlam']
          _ = lam * (lam' * (w * ℓ * w⁻¹)) * lam⁻¹ := by group
          _ = lam' * (w * ℓ * w⁻¹) := by
              have hcl : lam * (lam' * (w * ℓ * w⁻¹)) = (lam' * (w * ℓ * w⁻¹)) * lam :=
                elemAbelian_mul_comm hNab hlamN ((sec4N T T₁ T₂).mul_mem hlam'N hwℓN)
              rw [hcl]
              group
      have hconj : t * (w * ℓ * w⁻¹ * ℓ⁻¹) * t⁻¹ = w * ℓ * w⁻¹ * ℓ⁻¹ := by
        obtain ⟨lam', hlam'def⟩ : ∃ lam', lam' = t * ℓ * t⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
        rw [← hlam'def] at hlam'_eq hlam'N hu
        calc t * (w * ℓ * w⁻¹ * ℓ⁻¹) * t⁻¹
            = (t * (w * ℓ * w⁻¹) * t⁻¹) * (t * ℓ * t⁻¹)⁻¹ := by group
          _ = (lam' * (w * ℓ * w⁻¹)) * (lam' * ℓ)⁻¹ := by rw [hu, ← hlam'_eq]
          _ = lam' * ((w * ℓ * w⁻¹) * ℓ⁻¹) * lam'⁻¹ := by group
          _ = w * ℓ * w⁻¹ * ℓ⁻¹ := by
              have hcl : lam' * ((w * ℓ * w⁻¹) * ℓ⁻¹) = ((w * ℓ * w⁻¹) * ℓ⁻¹) * lam' :=
                elemAbelian_mul_comm hNab hlam'N heN
              rw [hcl]
              group
      calc (w * ℓ * w⁻¹ * ℓ⁻¹) * t = (t * (w * ℓ * w⁻¹ * ℓ⁻¹) * t⁻¹) * t := by rw [hconj]
        _ = t * (w * ℓ * w⁻¹ * ℓ⁻¹) := by group
    obtain ⟨l₀, hl₀, l₁, hl₁, hel⟩ := hc.mem_cfgM_iff.1 heM
    by_cases hl₁1 : l₁ = 1
    · rw [hel, hl₁1, mul_one]
      exact normIn_le _ _ hl₀
    · exfalso
      obtain ⟨hl₁N, hl₁D, hl₁T⟩ := h.mem_props_normIn₁ hl₁ hl₁1
      have hcomm₁ : ∀ t ∈ T, l₁ * t = t * l₁ := by
        intro t ht
        have hl₀T : l₀ ∈ T := normIn_le _ _ hl₀
        have e1 : l₁ = l₀⁻¹ * (w * ℓ * w⁻¹ * ℓ⁻¹) := by rw [hel]; group
        rw [e1]
        calc l₀⁻¹ * (w * ℓ * w⁻¹ * ℓ⁻¹) * t = l₀⁻¹ * ((w * ℓ * w⁻¹ * ℓ⁻¹) * t) :=
              mul_assoc _ _ _
          _ = l₀⁻¹ * (t * (w * ℓ * w⁻¹ * ℓ⁻¹)) := by rw [heT t ht]
          _ = (l₀⁻¹ * t) * (w * ℓ * w⁻¹ * ℓ⁻¹) := (mul_assoc _ _ _).symm
          _ = (t * l₀⁻¹) * (w * ℓ * w⁻¹ * ℓ⁻¹) := by
              rw [elemAbelian_mul_comm hc.wc.1 (T.inv_mem hl₀T) ht]
          _ = t * (l₀⁻¹ * (w * ℓ * w⁻¹ * ℓ⁻¹)) := mul_assoc _ _ _
      have hTL : T ≤ normIn T T₁ := fun t ht => (h.comm_iff_mem_normIn hl₁N hl₁D hl₁T ht).1
        (hcomm₁ t ht)
      have := Subgroup.card_le_of_le hTL
      omega
  intro n hn
  obtain ⟨ℓ, hℓ, m, hm, rfl⟩ := h.exists_mul_of_mem_sec4N hn
  have hwm := hwM m hm
  have e : w * (ℓ * m) * w⁻¹ * (ℓ * m)⁻¹ = w * ℓ * w⁻¹ * ℓ⁻¹ := by
    have hwmw : w * m * w⁻¹ = m := by rw [hwm]; group
    calc w * (ℓ * m) * w⁻¹ * (ℓ * m)⁻¹ = w * ℓ * w⁻¹ * (w * m * w⁻¹) * m⁻¹ * ℓ⁻¹ := by group
      _ = w * ℓ * w⁻¹ * m * m⁻¹ * ℓ⁻¹ := by rw [hwmw]
      _ = w * ℓ * w⁻¹ * ℓ⁻¹ := by group
  rw [e]
  exact key ℓ hℓ

end Branch1

end CFSG.CGT.T75L
