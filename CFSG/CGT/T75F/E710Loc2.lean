module

public import CFSG.CGT.T75F.E710Loc1
public import CFSG.CGT.T75F.E710Fib

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}
  [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

noncomputable def lineElt (M : TModel T T₁ 3 m) (v : Fin 3 → GaloisField 2 m)
    (r : GaloisField 2 m) : G :=
  ((M.φ.symm (Multiplicative.ofAdd (r • v)) : ↥T) : G)

theorem lineElt_mem (M : TModel T T₁ 3 m) (v : Fin 3 → GaloisField 2 m) (r : GaloisField 2 m) :
    lineElt M v r ∈ T := (M.φ.symm (Multiplicative.ofAdd (r • v))).2

theorem toAdd_phi_lineElt (M : TModel T T₁ 3 m) (v : Fin 3 → GaloisField 2 m)
    (r : GaloisField 2 m) :
    Multiplicative.toAdd (M.φ ⟨lineElt M v r, lineElt_mem M v r⟩) = r • v := by
  have : (⟨lineElt M v r, lineElt_mem M v r⟩ : ↥T) = M.φ.symm (Multiplicative.ofAdd (r • v)) :=
    rfl
  rw [this, M.φ.apply_symm_apply]
  rfl

theorem lineElt_injective (M : TModel T T₁ 3 m) {v : Fin 3 → GaloisField 2 m} (hv : v ≠ 0) :
    Function.Injective (lineElt M v) := by
  intro r s hrs
  have h1 : (⟨lineElt M v r, lineElt_mem M v r⟩ : ↥T) = ⟨lineElt M v s, lineElt_mem M v s⟩ :=
    Subtype.ext hrs
  have h2 := congrArg (fun x => Multiplicative.toAdd (M.φ x)) h1
  simp only [toAdd_phi_lineElt] at h2
  have h3 : (r - s) • v = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hv

theorem exists_lineElt_of_mem (M : TModel T T₁ 3 m) {v : Fin 3 → GaloisField 2 m} {l : G}
    (hl : l ∈ T) {r : GaloisField 2 m} (hr : Multiplicative.toAdd (M.φ ⟨l, hl⟩) = r • v) :
    lineElt M v r = l := by
  have h1 : M.φ ⟨l, hl⟩ = Multiplicative.ofAdd (r • v) := hr
  have h2 : (⟨l, hl⟩ : ↥T) = M.φ.symm (Multiplicative.ofAdd (r • v)) := by
    rw [← h1, M.φ.symm_apply_apply]
  exact (congrArg Subtype.val h2).symm

section Count

theorem ncard_mul_mem_D (M : TModel T T₁ 3 m) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 3 m) {e : G}
    (he : e ∈ normIn T₁ T) (he1 : e ≠ 1) :
    {l : G | l ∈ normIn T T₁ ∧ e * l ∈ classD T}.ncard = 2 ^ m := by
  have := hc.finite
  obtain ⟨hD, hT⟩ := mem_normD_of_mem_normIn₁ hc he he1
  obtain ⟨f, v, hf, hv, hfv, hdata, hL⟩ := exists_data_normIn₁ M h63 hc he he1
  have hset : {l : G | l ∈ normIn T T₁ ∧ e * l ∈ classD T} =
      Set.range (lineElt M v) := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨hlL, hlD⟩
      have hlT := normIn_le _ _ hlL
      obtain ⟨r, hr⟩ := (hc.mem_classD_mul_iff h62 h63 M hD hT hf hdata hlT).1 hlD
      exact ⟨r, exists_lineElt_of_mem M hlT hr⟩
    · rintro ⟨r, rfl⟩
      have hlT := lineElt_mem M v r
      refine ⟨?_, (hc.mem_classD_mul_iff h62 h63 M hD hT hf hdata hlT).2
        ⟨r, toAdd_phi_lineElt M v r⟩⟩
      rw [hL _ hlT, toAdd_phi_lineElt M v r, map_smul, hfv, smul_zero]
  rw [hset, ← Set.image_univ, Set.ncard_image_of_injective _ (lineElt_injective M hv),
    Set.ncard_univ]
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hc.hy.card
    rw [hc.hT] at this
    simp at this
  exact GaloisField.card 2 m hm0

theorem card_mul_le (M : TModel T T₁ 3 m) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 3 m) {e : G}
    (he : e ∈ classD T) (heM : e ∈ cfgM T T₁) (heL : e ∉ normIn T T₁) :
    Nat.card {l : G | l ∈ normIn T T₁ ∧ e * l ∈ classD T} ≤ 2 ^ m := by
  have := hc.finite
  have hcfg := hc.sec3.cfg
  obtain ⟨l₀, hl₀, e₁, he₁, rfl⟩ := hcfg.mem_cfgM_iff.1 heM
  have he₁1 : e₁ ≠ 1 := by
    rintro rfl
    exact heL (by simpa using hl₀)
  have hT : l₀ * e₁ ∉ T := fun hT => heL (mem_normIn_of_mem_cfgM hc heM hT)
  have hN : l₀ * e₁ ∈ Subgroup.normalizer (T : Set G) := by
    refine (Subgroup.normalizer (T : Set G)).mul_mem ?_ (mem_normIn.1 he₁).2
    exact Subgroup.le_normalizer (normIn_le _ _ hl₀)
  have hD : l₀ * e₁ ∈ normD T := ⟨he, hN⟩
  obtain ⟨f, v, hfv, hv, hf, hdata⟩ := M.exists_data hD hT
  have hsub : {l : G | l ∈ normIn T T₁ ∧ l₀ * e₁ * l ∈ classD T} ⊆ Set.range (lineElt M v) := by
    rintro l ⟨hlL, hlD⟩
    have hlT := normIn_le _ _ hlL
    obtain ⟨r, hr⟩ := (hc.mem_classD_mul_iff h62 h63 M hD hT hf hdata hlT).1 hlD
    exact ⟨r, exists_lineElt_of_mem M hlT hr⟩
  have h1 : {l : G | l ∈ normIn T T₁ ∧ l₀ * e₁ * l ∈ classD T}.ncard ≤ 2 ^ m := by
    calc {l : G | l ∈ normIn T T₁ ∧ l₀ * e₁ * l ∈ classD T}.ncard
        ≤ (Set.range (lineElt M v)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 2 ^ m := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ (lineElt_injective M hv),
          Set.ncard_univ]
        have hm0 : m ≠ 0 := by
          rintro rfl
          have := hc.hy.card
          rw [hc.hT] at this
          simp at this
        exact GaloisField.card 2 m hm0
  rw [← Nat.card_coe_set_eq] at h1
  exact h1

omit [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] in
theorem classD_inter_cfgM_eq_image (hc : Sec6Ctx T T₁ 3 m) :
    classD T ∩ (cfgM T T₁ : Set G) =
      (fun p : G × G => p.1 * p.2) ''
        {p : G × G | p.1 ∈ normIn T T₁ ∧ p.2 ∈ normIn T₁ T ∧ p.1 * p.2 ∈ classD T} := by
  have hcfg := hc.sec3.cfg
  ext a
  constructor
  · rintro ⟨haD, haM⟩
    obtain ⟨l, hl, e, he, rfl⟩ := hcfg.mem_cfgM_iff.1 haM
    exact ⟨(l, e), ⟨hl, he, haD⟩, rfl⟩
  · rintro ⟨⟨l, e⟩, ⟨hl, he, haD⟩, rfl⟩
    exact ⟨haD, hcfg.mem_cfgM_iff.2 ⟨l, hl, e, he, rfl⟩⟩

omit [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] in
theorem mul_injOn_normIn (hc : Sec6Ctx T T₁ 3 m) :
    Set.InjOn (fun p : G × G => p.1 * p.2)
      {p : G × G | p.1 ∈ normIn T T₁ ∧ p.2 ∈ normIn T₁ T ∧ p.1 * p.2 ∈ classD T} := by
  have hcfg := hc.sec3.cfg
  rintro ⟨l, e⟩ ⟨hl, he, -⟩ ⟨l', e'⟩ ⟨hl', he', -⟩ heq
  have heq' : l * e = l' * e' := heq
  have h1 : l'⁻¹ * l = e' * e⁻¹ := by
    calc l'⁻¹ * l = l'⁻¹ * (l * e) * e⁻¹ := by group
      _ = l'⁻¹ * (l' * e') * e⁻¹ := by rw [heq']
      _ = e' * e⁻¹ := by group
  have h2 : l'⁻¹ * l ∈ T ⊓ T₁ :=
    ⟨T.mul_mem (T.inv_mem (normIn_le _ _ hl')) (normIn_le _ _ hl), by
      rw [h1]
      exact T₁.mul_mem (normIn_le _ _ he') (T₁.inv_mem (normIn_le _ _ he))⟩
  rw [hcfg.inf, Subgroup.mem_bot] at h2
  have hll : l = l' := (inv_mul_eq_one.1 h2).symm
  subst hll
  have : e = e' := mul_left_cancel heq'
  rw [this]

theorem ncard_delta_three (M : TModel T T₁ 3 m) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 3 m) :
    (classD T ∩ (cfgM T T₁ : Set G)).ncard = (2 ^ m + 1) * ((2 ^ m) ^ 2 - 1) := by
  have := hc.finite
  have hcfg := hc.sec3.cfg
  rw [classD_inter_cfgM_eq_image hc, (mul_injOn_normIn hc).ncard_image]
  set S : Set (G × G) :=
    {p : G × G | p.1 ∈ normIn T T₁ ∧ p.2 ∈ normIn T₁ T ∧ p.1 * p.2 ∈ classD T} with hS
  have hSsplit : S = {p ∈ S | p.2 = 1} ∪ {p ∈ S | p.2 ≠ 1} := by
    ext p
    simp only [Set.mem_union, Set.mem_sep_iff]
    tauto
  have hdisj : Disjoint {p ∈ S | p.2 = 1} {p ∈ S | p.2 ≠ 1} := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  rw [hSsplit, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  have hLcard : ((normIn T T₁ : Set G)).ncard = (2 ^ m) ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact card_normIn_three hc
  have hL₁card : ((normIn T₁ T : Set G)).ncard = (2 ^ m) ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact card_normIn₁_three hc
  have h1 : {p ∈ S | p.2 = 1}.ncard = (2 ^ m) ^ 2 - 1 := by
    have hset : {p ∈ S | p.2 = 1} =
        (fun l : G => (l, (1 : G))) '' ((normIn T T₁ : Set G) \ ({1} : Set G)) := by
      ext ⟨l, e⟩
      simp only [hS, Set.mem_ofPred_eq, Set.mem_image, Set.mem_sdiff,
        SetLike.mem_coe, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hl, -, hD⟩, rfl⟩
        refine ⟨l, ⟨hl, ?_⟩, rfl, rfl⟩
        rintro rfl
        exact ne_one_of_mem_classD (by simpa using hD) rfl
      · rintro ⟨l', ⟨hl', hl'1⟩, rfl, rfl⟩
        exact ⟨⟨hl', (normIn T₁ T).one_mem, by
          simpa using mem_classD_of_mem (normIn_le _ _ hl') hl'1⟩, rfl⟩
    rw [hset, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h),
      Set.ncard_sdiff_singleton_of_mem (normIn T T₁).one_mem, hLcard]
  have h2 : {p ∈ S | p.2 ≠ 1}.ncard = ((2 ^ m) ^ 2 - 1) * 2 ^ m := by
    have hmaps : ∀ p ∈ {p ∈ S | p.2 ≠ 1}, p.2 ∈ ((normIn T₁ T : Set G) \ ({1} : Set G)) := by
      rintro p ⟨⟨-, he, -⟩, hne⟩
      exact ⟨he, hne⟩
    have := ncard_eq_mul_of_fibres {p ∈ S | p.2 ≠ 1} ((normIn T₁ T : Set G) \ ({1} : Set G))
      Prod.snd hmaps (2 ^ m) (by
        rintro e ⟨he, he1⟩
        have he1' : e ≠ 1 := he1
        have hfib : {p : G × G | p ∈ {p ∈ S | p.2 ≠ 1} ∧ p.2 = e} =
            (fun l : G => (l, e)) '' {l : G | l ∈ normIn T T₁ ∧ l * e ∈ classD T} := by
          ext ⟨l, e'⟩
          simp only [hS, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨⟨hl, -, hD⟩, -⟩, rfl⟩
            exact ⟨l, ⟨hl, hD⟩, rfl, rfl⟩
          · rintro ⟨l', ⟨hl', hD⟩, rfl, rfl⟩
            exact ⟨⟨⟨hl', he, hD⟩, he1'⟩, rfl⟩
        have hcomm : {l : G | l ∈ normIn T T₁ ∧ l * e ∈ classD T} =
            {l : G | l ∈ normIn T T₁ ∧ e * l ∈ classD T} := by
          ext l
          simp only [Set.mem_ofPred_eq]
          constructor
          · rintro ⟨hl, hD⟩
            exact ⟨hl, by rwa [← hcfg.comm_L_L₁ hl he]⟩
          · rintro ⟨hl, hD⟩
            exact ⟨hl, by rwa [hcfg.comm_L_L₁ hl he]⟩
        rw [hfib, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h), hcomm]
        exact ncard_mul_mem_D M h62 h63 hc he he1')
    rw [this, Set.ncard_sdiff_singleton_of_mem (normIn T₁ T).one_mem, hL₁card]
  rw [h1, h2]
  ring_nf

omit [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] in
theorem closure_classD_cfgM {n : ℕ} (hc : Sec6Ctx T T₁ n m) :
    Subgroup.closure (classD T ∩ (cfgM T T₁ : Set G)) = cfgM T T₁ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact Set.inter_subset_right
  · refine sup_le ?_ ?_
    · intro l hl
      by_cases hl1 : l = 1
      · rw [hl1]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨mem_classD_of_mem (normIn_le _ _ hl) hl1,
          Cfg.normIn_le_cfgM_left T T₁ hl⟩
    · intro e he
      by_cases he1 : e = 1
      · rw [he1]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨(mem_normD_of_mem_normIn₁ hc he he1).1.1,
          Cfg.normIn_le_cfgM_right T T₁ he⟩

end Count

end CFSG.CGT.T75F
