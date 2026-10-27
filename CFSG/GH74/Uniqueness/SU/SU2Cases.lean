module

public import CFSG.GH74.Uniqueness.SU.SU2Struct

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section Cases

variable {X : Type} [Group X] (V : Type) [Group V] [MulDistribMulAction X V]

@[expose] def OnanConclusion (Y : Subgroup X) : Prop :=
  (omega V Y = {fixSub V Y} ∧ ∀ x : X, x • fixSub V Y = fixSub V Y) ∨
  (omega V Y = {fixSub V Y, commSub V Y} ∧
    ∃ x : X, (∃ m : ℕ, orderOf x = 2 ^ m) ∧ x • fixSub V Y = commSub V Y ∧
      x • commSub V Y = fixSub V Y) ∨
  ((omega V Y).ncard = 2 ^ (shapeN V - shapeK V Y) ∧
    (⋃ W ∈ omega V Y, {v : V | v ∈ W ∧ v ≠ 1}) = {v : V | v ∉ commSub V Y} ∧
    ∀ x : X, x • commSub V Y = commSub V Y) ∨
  (shapeK V Y = 1 ∧ shapeN V = 3 ∧ Nat.card X = 21 ∧ ∃ a b : X, a * b ≠ b * a)

variable {V}

theorem exists_two_power_swap {G α : Type*} [Group G] [MulAction G α] [Finite G] {g : G}
    {a b : α} (h1 : g • a = b) (h2 : g • b = a) :
    ∃ x : G, (∃ m : ℕ, orderOf x = 2 ^ m) ∧ x • a = b ∧ x • b = a := by
  have hpos : 0 < orderOf g := orderOf_pos g
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  obtain ⟨j, hj⟩ := hm
  have hmpos : m ≠ 0 := by rintro rfl; simp at hj
  have hdvd : m ∣ orderOf g := ⟨2 ^ k, by rw [hkm]; ring⟩
  have hord : orderOf (g ^ m) = 2 ^ k := by
    rw [orderOf_pow_of_dvd hmpos hdvd, hkm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hmpos)]
  have hsq : ∀ n : ℕ, (g ^ 2) ^ n • a = a ∧ (g ^ 2) ^ n • b = b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have ha : g ^ 2 • a = a := by rw [pow_two, mul_smul, h1, h2]
      have hb : g ^ 2 • b = b := by rw [pow_two, mul_smul, h2, h1]
      rw [pow_succ, mul_smul, mul_smul, ha, hb]
      exact ih
  have hgm : g ^ m = (g ^ 2) ^ j * g := by
    rw [hj, pow_succ, pow_mul]
  refine ⟨g ^ m, ⟨k, hord⟩, ?_, ?_⟩
  · rw [hgm, mul_smul, h1, (hsq j).2]
  · rw [hgm, mul_smul, h2, (hsq j).1]

namespace GOPair

variable {Y : Subgroup X}

theorem conclusion_i (hA : omegaA V Y = ∅) (hB : omegaB V Y = ∅) :
    omega V Y = {fixSub V Y} ∧ ∀ x : X, x • fixSub V Y = fixSub V Y := by
  have hΩ : omega V Y = {fixSub V Y} := by rw [omega_eq, hA, hB]; simp
  refine ⟨hΩ, fun x => ?_⟩
  have : x • fixSub V Y ∈ omega V Y := smul_mem_omega (fixSub_mem_omega Y) x
  rwa [hΩ] at this

theorem conclusion_iii [Finite X] [Finite V] (hGO : GOPair V Y) (hA : omegaA V Y = ∅)
    {W₂ : Subgroup V} (hW₂ : W₂ ∈ omegaB V Y) :
    (omega V Y).ncard = 2 ^ (shapeN V - shapeK V Y) ∧
      (⋃ W ∈ omega V Y, {v : V | v ∈ W ∧ v ≠ 1}) = {v : V | v ∉ commSub V Y} ∧
      ∀ x : X, x • commSub V Y = commSub V Y := by
  have hΩ : ∀ W ∈ omega V Y, W = fixSub V Y ∨ W ∈ omegaB V Y := by
    intro W hW
    by_cases h0 : W = fixSub V Y
    · exact Or.inl h0
    · refine Or.inr ⟨hW, h0, fun hle => ?_⟩
      have : W ∈ omegaA V Y := ⟨hW, h0, hle⟩
      rw [hA] at this
      exact this
  have hV₀V₁ : ∀ v ∈ fixSub V Y, v ∈ commSub V Y → v = 1 := fun v h0 h1 => by
    have : v ∈ commSub V Y ⊓ fixSub V Y := ⟨h1, h0⟩
    rw [hGO.commSub_inf_fixSub'] at this
    exact this
  have hunion : (⋃ W ∈ omega V Y, {v : V | v ∈ W ∧ v ≠ 1}) = {v : V | v ∉ commSub V Y} := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨W, hW, hvW, hv1⟩ hv
      rcases hΩ W hW with rfl | hWB
      · exact hv1 (hV₀V₁ v hvW hv)
      · have : v ∈ W ⊓ commSub V Y := ⟨hvW, hv⟩
        rw [hGO.typeB_inf_eq_bot hWB.1 hWB.2.1 hWB.2.2] at this
        exact hv1 this
    · intro hv
      by_cases hv0 : v ∈ fixSub V Y
      · exact ⟨fixSub V Y, fixSub_mem_omega Y, hv0, fun h => hv (h ▸ one_mem _)⟩
      · obtain ⟨y, hy, hvy⟩ := hGO.typeB_cover hW₂.1 hW₂.2.1 hW₂.2.2 hv0 hv
        exact ⟨y • W₂, smul_mem_omega hW₂.1 y, hvy, fun h => hv0 (h ▸ one_mem _)⟩
  refine ⟨?_, hunion, ?_⟩
  · rw [ncard_omega, hA, Set.ncard_empty, hGO.omegaB_eq_orbit hW₂, zero_add,
      ← MulAction.index_stabilizer]
    have hbot : MulAction.stabilizer ↥Y W₂ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have := hGO.typeB_stab_trivial hW₂.1 hW₂.2.1 hW₂.2.2 y.2 (MulAction.mem_stabilizer_iff.1 hy)
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    rw [hbot, Subgroup.index_bot, ← hGO.card_commSub, ← hGO.card_Y_add_one]
  ·
    have hinv : ∀ (x : X) (v : V), v ∉ commSub V Y → x • v ∉ commSub V Y := by
      intro x v hv
      have hv' : v ∈ ⋃ W ∈ omega V Y, {v : V | v ∈ W ∧ v ≠ 1} := by rw [hunion]; exact hv
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hv'
      obtain ⟨W, hW, hvW, hv1⟩ := hv'
      have : x • v ∈ ⋃ W ∈ omega V Y, {v : V | v ∈ W ∧ v ≠ 1} := by
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
        refine ⟨x • W, smul_mem_omega hW x, Subgroup.smul_mem_pointwise_smul v x W hvW, ?_⟩
        intro h
        apply hv1
        have : x • v = x • (1 : V) := by rw [smul_one]; exact h
        exact MulAction.injective x this
      rw [hunion] at this
      exact this
    have hle : ∀ x : X, x • commSub V Y ≤ commSub V Y := by
      intro x m hm
      obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm
      by_contra hxs
      have := hinv x⁻¹ _ hxs
      rw [inv_smul_smul] at this
      exact this hs
    intro x
    refine le_antisymm (hle x) ?_
    have := (Subgroup.pointwise_smul_subset_iff (a := x⁻¹)).1 (hle x⁻¹)
    rwa [inv_inv] at this

theorem conclusion_ii [Finite X] [Finite V] (hGO : GOPair V Y) (hB : omegaB V Y = ∅)
    {W₁ : Subgroup V} (hW₁ : W₁ ∈ omegaA V Y) :
    omega V Y = {fixSub V Y, commSub V Y} ∧
      ∃ x : X, (∃ m : ℕ, orderOf x = 2 ^ m) ∧ x • fixSub V Y = commSub V Y ∧
        x • commSub V Y = fixSub V Y := by
  have hΩ : omega V Y = insert (fixSub V Y) (omegaA V Y) := by
    rw [omega_eq, hB]; simp
  have hmem : ∀ A ∈ omega V Y, ∀ a ∈ A, a ∈ fixSub V Y ∨ a ∈ commSub V Y := by
    intro A hA a ha
    rw [hΩ] at hA
    rcases hA with rfl | hA
    · exact Or.inl ha
    · exact Or.inr (hA.2.2 ha)
  have hV₀V₁ : ∀ v ∈ fixSub V Y, v ∈ commSub V Y → v = 1 := fun v h0 h1 => by
    have : v ∈ commSub V Y ⊓ fixSub V Y := ⟨h1, h0⟩
    rw [hGO.commSub_inf_fixSub'] at this
    exact this
  obtain ⟨g, hg⟩ := mem_omega_iff.1 hW₁.1
  have hT : ((g • commSub V Y : Subgroup V) : Set V) ⊆ (fixSub V Y : Set V) ∪ (commSub V Y : Set V) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 ht
    by_cases hu1 : u = 1
    · left; rw [hu1, smul_one]; exact one_mem _
    · obtain ⟨y, hy, huy⟩ := hGO.typeA_cover hW₁.1 hW₁.2.2 hu hu1
      have hA : g • (y • W₁) ∈ omega V Y := smul_mem_omega (smul_mem_omega hW₁.1 y) g
      exact hmem _ hA _ (Subgroup.smul_mem_pointwise_smul u g _ huy)
  have hcardT : Nat.card (g • commSub V Y : Subgroup V) = Nat.card (commSub V Y) :=
    (Nat.card_congr (Subgroup.equivSMul g (commSub V Y)).toEquiv).symm
  have hcardW : Nat.card W₁ = Nat.card (fixSub V Y) := card_eq_of_mem_omega hW₁.1
  have hW₁V : W₁ = commSub V Y := by
    rcases le_or_le_of_subset_union hT with hT0 | hT1
    ·
      refine Subgroup.eq_of_le_of_card_ge hW₁.2.2 ?_
      rw [hcardW, ← hcardT]
      exact Subgroup.card_le_of_le hT0
    · exfalso
      have hTeq : g • commSub V Y = commSub V Y :=
        Subgroup.eq_of_le_of_card_ge hT1 (by rw [hcardT])
      apply hGO.fixSub_ne_bot
      rw [Subgroup.eq_bot_iff_forall]
      intro c hc
      have hgc : g • c ∈ W₁ := hg ▸ Subgroup.smul_mem_pointwise_smul c g _ hc
      have : g • c ∈ g • commSub V Y := by rw [hTeq]; exact hW₁.2.2 hgc
      obtain ⟨u, hu, hug⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 this
      have : u = c := MulAction.injective g hug
      exact hV₀V₁ c hc (this ▸ hu)
  have hAeq : omegaA V Y = {commSub V Y} := by
    rw [hGO.omegaA_eq_orbit hW₁, hW₁V]
    ext A
    simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact hGO.smul_commSub_eq (smul_fixSub_of_mem y.2)
    · rintro rfl
      exact ⟨1, one_smul _ _⟩
  have hV₁Ω : commSub V Y ∈ omega V Y := hW₁V ▸ hW₁.1
  have hne : fixSub V Y ≠ commSub V Y := by
    intro h
    apply hGO.fixSub_ne_bot
    have : fixSub V Y ≤ commSub V Y ⊓ fixSub V Y := le_inf (h ▸ le_rfl) le_rfl
    rw [hGO.commSub_inf_fixSub'] at this
    exact eq_bot_iff.2 this
  have hΩ2 : omega V Y = {fixSub V Y, commSub V Y} := by rw [hΩ, hAeq]
  refine ⟨hΩ2, ?_⟩
  have hg1 : g • fixSub V Y = commSub V Y := hg.trans hW₁V
  have hg2 : g • commSub V Y = fixSub V Y := by
    have hmem2 : g • commSub V Y ∈ omega V Y := smul_mem_omega hV₁Ω g
    rw [hΩ2] at hmem2
    rcases hmem2 with h | h
    · exact h
    · exfalso
      apply hne
      have : g • commSub V Y = g • fixSub V Y := by rw [h, hg1]
      exact (MulAction.injective g this).symm
  obtain ⟨x, hx2, hx⟩ := exists_two_power_swap hg1 hg2
  exact ⟨x, hx2, hx⟩

theorem step12 [Finite X] [Finite V] (hGO : GOPair V Y) :
    OnanConclusion V Y ∨ ((omegaA V Y).Nonempty ∧ (omegaB V Y).Nonempty) := by
  by_cases hA : (omegaA V Y).Nonempty
  · by_cases hB : (omegaB V Y).Nonempty
    · exact Or.inr ⟨hA, hB⟩
    · obtain ⟨W₁, hW₁⟩ := hA
      exact Or.inl (Or.inr (Or.inl (hGO.conclusion_ii (Set.not_nonempty_iff_eq_empty.1 hB) hW₁)))
  · by_cases hB : (omegaB V Y).Nonempty
    · obtain ⟨W₂, hW₂⟩ := hB
      exact Or.inl (Or.inr (Or.inr (Or.inl
        (hGO.conclusion_iii (Set.not_nonempty_iff_eq_empty.1 hA) hW₂))))
    · exact Or.inl (Or.inl (conclusion_i (Set.not_nonempty_iff_eq_empty.1 hA)
        (Set.not_nonempty_iff_eq_empty.1 hB)))

end GOPair

end Cases

end CFSG.GH74.Uniqueness.SU.SU2
