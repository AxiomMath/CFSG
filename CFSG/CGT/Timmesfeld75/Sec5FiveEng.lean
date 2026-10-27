module

public import CFSG.CGT.Timmesfeld75.Sec5FiveEngII
public import CFSG.CGT.Timmesfeld75.Sec5FiveEngHelp
public import CFSG.CGT.Timmesfeld75.Sec3OddSubgroup
public import CFSG.CGT.Timmesfeld75.Sec5FiveEngI

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem engine (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hA4 : secA T T₁ ≠ normIn T T₁) {x₀ : G} (hx₀ : T₁ = conjSubgroup x₀ T) {x : G}
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxx : x * x = 1) (hxD : x ∈ classD T)
    (hE2 : ∀ l ∈ normIn T₁ T, x * l * x⁻¹ ∈ normIn T₁ T ⊔ T)
    (hE4 : ∀ a ∈ conjSubgroup x₀ (secA T T₁), ⁅a, x⁆ ∈ T)
    (hne : ∃ a ∈ conjSubgroup x₀ (secA T T₁), ⁅a, x⁆ ≠ 1) :
    ∃ t ∈ T, ∀ y ∈ T ⊔ T₁, y⁻¹ * ((x * t) * y * (x * t)⁻¹) ∈ cfgM T T₁ := by
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hsec3 : Sec3 T T₁ := hP.sec3 hS
  have hcfg := hsec3.cfg
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxT : conjSubgroup x T = T := mem_normalizer_iff_conjSubgroup_eq.1 hxN
  have hx₀ne : conjSubgroup x₀ T ≠ T := by rw [← hx₀]; exact hP.ne
  have hL₁ne : normIn T₁ T ≠ ⊥ := hcfg.ne₁
  have hA₁L : conjSubgroup x₀ (secA T T₁) ≤ normIn T₁ T := by
    have := conjSubgroup_secA_le_normIn hP hS hx₀ne (by rw [← hx₀]; exact hcfg.ne₁)
    rwa [← hx₀] at this
  have hA₁1 : conjSubgroup x₀ (secA T T₁) ≠ ⊥ := by
    obtain ⟨a₀, ha₀, ha₀1⟩ := hne
    intro h'
    rw [h', Subgroup.mem_bot] at ha₀
    exact ha₀1 (by rw [ha₀]; simp)
  have hA1 : secA T T₁ ≠ ⊥ := fun h' => hA₁1 (by rw [h']; exact conjSubgroup_bot x₀)
  have hxN1 : x ∉ Subgroup.normalizer (T₁ : Set G) := by
    intro hxT₁
    have hxN' : x ∈ Subgroup.normalizer ((conjSubgroup x₀ T : Subgroup G) : Set G) := by
      rw [← hx₀]; exact hxT₁
    have hcomm := conjSubgroup_secA_comm_of_mem_normalizer hP hS hxD hxN'
    obtain ⟨a₀, ha₀, ha₀1⟩ := hne
    exact ha₀1 (commutatorElement_eq_one_iff_mul_comm.2 (hcomm a₀ ha₀))
  obtain ⟨T₂, hT₂⟩ : ∃ T₂ : Subgroup G, T₂ = conjSubgroup x T₁ := ⟨_, rfl⟩
  have hT₂x : conjSubgroup x T₂ = T₁ := by
    rw [hT₂, conjSubgroup_conjSubgroup, hxx, conjSubgroup_one]
  have hT₂T₁ : T₂ ≠ T₁ := fun h' =>
    hxN1 (mem_normalizer_of_conjSubgroup_eq (by rw [← hT₂]; exact h'))
  have hT₂T : T₂ ≠ T := fun h' => hP.ne (by rw [← hT₂x, h', hxT])
  have hTT₂ : T ⊓ T₂ = ⊥ := by
    have hT₂' : T₂ = conjSubgroup (x * x₀) T := by rw [hT₂, hx₀, conjSubgroup_conjSubgroup]
    rw [hT₂'] at hT₂T ⊢
    exact hP.wc.inf_conj_eq_bot hT₂T
  have hT₁T₂ : T₁ ⊓ T₂ = ⊥ := by
    rw [hT₂]
    exact hcfg.wc₁.inf_conj_eq_bot (by rw [← hT₂]; exact hT₂T₁)
  have hL₁M : ∀ l ∈ normIn T₁ T, x * l * x⁻¹ ∈ cfgM T T₁ := by
    intro l hl
    by_cases hl1 : l = 1
    · rw [hl1]
      simp
    have hlT₁ : l ∈ T₁ := normIn_le _ _ hl
    have hy2 : (x * l * x⁻¹) * (x * l * x⁻¹) = 1 := by
      have hll : l * l = 1 := elemAbelian_mul_self hcfg.wc₁.1 hlT₁
      calc (x * l * x⁻¹) * (x * l * x⁻¹) = x * (l * l) * x⁻¹ := by group
        _ = 1 := by rw [hll]; group
    have hyT₂ : x * l * x⁻¹ ∈ T₂ := by rw [hT₂]; exact conj_mem_conjSubgroup x hlT₁
    have hyT : x * l * x⁻¹ ∉ T := fun hyT => by
      have h2 : x * l * x⁻¹ ∈ T ⊓ T₂ := ⟨hyT, hyT₂⟩
      rw [hTT₂, Subgroup.mem_bot] at h2
      exact hl1 (by
        calc l = x⁻¹ * (x * l * x⁻¹) * x := by group
          _ = 1 := by rw [h2]; group)
    exact hcfg.mem_cfgM_of_mul_self_eq_one_of_mem_sup hy2 (hE2 l hl) hyT
  have hconjL₁M : conjSubgroup x (normIn T₁ T) ≤ cfgM T T₁ := fun z hz => by
    have e : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [e]
    exact hL₁M _ (mem_conjSubgroup.1 hz)
  obtain ⟨⟨l₀, hl₀⟩, hl₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hL₁ne
  have hl₀1' : l₀ ≠ 1 := fun h' => hl₀1 (Subtype.ext h')
  have hl'1 : x * l₀ * x⁻¹ ≠ 1 := fun h' => hl₀1' (by
    calc l₀ = x⁻¹ * (x * l₀ * x⁻¹) * x := by group
      _ = 1 := by rw [h']; group)
  have hl'T₂ : x * l₀ * x⁻¹ ∈ T₂ := by rw [hT₂]; exact conj_mem_conjSubgroup x (normIn_le _ _ hl₀)
  have hMab := hcfg.isElemAbelian_cfgM
  have hwc₂ : IsWC T₂ := by rw [hT₂]; exact hcfg.wc₁.conj x
  have hL₁le : normIn T₁ T ≤ normIn T₁ T₂ := by
    intro l hl
    refine mem_normIn.2 ⟨normIn_le _ _ hl, ?_⟩
    have hlM : l ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ hl
    have hcom : l * (x * l₀ * x⁻¹) = (x * l₀ * x⁻¹) * l :=
      elemAbelian_mul_comm hMab hlM (hL₁M l₀ hl₀)
    exact hwc₂.centralizer_le_normalizer hl'T₂ hl'1 (Subgroup.mem_centralizer_singleton_iff.2 hcom)
  have hN12 : normIn T₁ T = normIn T₁ T₂ := by
    refine Subgroup.eq_of_le_of_card_ge hL₁le ?_
    rw [hT₂]
    exact (card_normIn_conj_le hP hx₀ (by rw [← hT₂]; exact hT₂T₁)).trans
      hsec3.card_normIn_swap.ge
  have hN21 : normIn T₂ T₁ = conjSubgroup x (normIn T₁ T) := by
    have h1 := normIn_conj x T₁ T₂
    rw [← hT₂, hT₂x, ← hN12] at h1
    exact h1
  have hS₁ : Sec3Global T₁ := by rw [hx₀]; exact hS.conj x₀
  have hI₁ : Sec3IsoGlobal T₁ := by rw [hx₀]; exact hI.conj x₀
  have hL₁₂ne : normIn T₁ (conjSubgroup x T₁) ≠ ⊥ := by rw [← hT₂, ← hN12]; exact hL₁ne
  have hS₁₂ : Sec3 T₁ T₂ := by rw [hT₂]; exact hS₁ x (by rw [← hT₂]; exact hT₂T₁) hL₁₂ne
  have hI₁₂ : Sec3Iso T₁ T₂ := by rw [hT₂]; exact hI₁ x (by rw [← hT₂]; exact hT₂T₁) hL₁₂ne
  have hxD₁ : x ∈ classD T₁ := by rw [hx₀]; exact mem_classD_conjSubgroup hxD x₀
  rcases swap_inner_or_field hy.nonab hS₁₂ hI₁₂ hS₁ hI₁ hxx hT₂.symm hxD₁ with
    ⟨h16, h4⟩ | ⟨h, hh, t, ht, hxt⟩
  ·
    exfalso
    have hTcard : Nat.card T = 16 := by rw [← card_conjSubgroup x₀ T, ← hx₀]; exact h16
    have hL₁card : Nat.card (normIn T₁ T) = 4 := by rw [hN12]; exact h4
    have hLcard : Nat.card (normIn T T₁) = 4 := by rw [← hsec3.card_normIn_swap]; exact hL₁card
    have hIso : Sec3Iso T T₁ := by
      rw [hx₀]
      exact hI x₀ hx₀ne (by rw [← hx₀]; exact hcfg.ne)
    obtain ⟨hN, f, hf, hiso⟩ := hIso
    have := hN
    have hmul := hsec3.card_eq_mul hf hiso
    rw [hTcard, hLcard] at hmul
    have h2f : 4 ≤ Nat.card (secA T T₁) :=
      have h2 : 2 ^ f = 4 := by omega
      h2 ▸ hsec3.two_pow_le_card_of_normal_normalizer hf hiso hA1
        (secA_le_normIn.trans (Cfg.normIn_le_cfgM_left T T₁)) fun n hn => conjSubgroup_secA hn
    exact hA4 (Subgroup.eq_of_le_of_card_ge secA_le_normIn (by rw [hLcard]; exact h2f))
  ·
    have hBL : conjSubgroup x₀ (secA T T₁) ≤ normIn T₁ T₂ := hN12 ▸ hA₁L
    have hBN : ∀ n ∈ Subgroup.normalizer (T₁ : Set G),
        conjSubgroup n (conjSubgroup x₀ (secA T T₁)) = conjSubgroup x₀ (secA T T₁) := fun n hn =>
      conjSubgroup_secA_conj_of_mem_normalizer (by rw [← hx₀]; exact hn)
    obtain ⟨b, hb, hb1, hub⟩ :=
      exists_fixed_of_swap_inner hS₁₂ hI₁₂ hxx hT₂.symm hBL hA₁1 hBN hh ht hxt
    obtain ⟨hbx1, hbxt, hbt⟩ := commutator_swap_facts hS₁₂ hxx hT₂.symm hBL hh ht hb hb1 hub
    have hbxT : ⁅b, x⁆ ∈ T := hE4 b hb
    have hbxT' : ⁅b, x⁆ ∈ conjSubgroup h T₁ := hbxt ▸ hbt
    have hcj : conjSubgroup h T₁ = conjSubgroup (h * x₀) T := by
      rw [hx₀, conjSubgroup_conjSubgroup]
    have hh_eq : conjSubgroup h T₁ = T := by
      have hnb : T ⊓ conjSubgroup (h * x₀) T ≠ ⊥ := by
        intro h'
        have hmem : ⁅b, x⁆ ∈ T ⊓ conjSubgroup (h * x₀) T := ⟨hbxT, hcj ▸ hbxT'⟩
        rw [h', Subgroup.mem_bot] at hmem
        exact hbx1 hmem
      rw [hcj]
      exact hP.wc.conj_eq_of_inf_ne_bot hnb
    refine ⟨t, hh_eq ▸ ht, fun y hy => ?_⟩
    have hTle : T ≤ T₁ ⊔ T₂ := by
      rw [← hh_eq]
      exact conjSubgroup_le_of_le_of_mem le_sup_left hh
    have hy' : y ∈ T₁ ⊔ T₂ := (sup_le hTle le_sup_left) hy
    have hMle : cfgM T₁ T₂ ≤ cfgM T T₁ := by
      refine sup_le ?_ ?_
      · rw [← hN12]
        exact Cfg.normIn_le_cfgM_right T T₁
      · rw [hN21]
        exact hconjL₁M
    exact hMle (hxt y hy')

end CFSG.CGT.Timmesfeld75
