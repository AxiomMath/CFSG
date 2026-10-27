module

public import CFSG.Holt.H78.Sec4Defs
public import CFSG.Holt.H78.DataSylow

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise commutatorElement

section Elementary

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

private theorem three_le_card_of_mem {Γ : Set Ω} [Finite Γ] {a b c : Ω} (ha : a ∈ Γ)
    (hb : b ∈ Γ) (hc : c ∈ Γ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card Γ := by
  rw [Nat.card_coe_set_eq]
  have h3 : ({a, b, c} : Set Ω).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard (Set.insert_subset ha (Set.insert_subset hb
    (Set.singleton_subset_iff.mpr hc))) (Set.toFinite Γ)

theorem mem_longInvSwap_of_mem_stabilizer_pair {α β : Ω} (hαβ : α ≠ β) {x : G}
    (hx : x ∈ longInv G Ω) (hxαβ : x ∈ stabilizer G ({α, β} : Set Ω)) :
    x ∈ longInvSwap G Ω α β := by
  have hmem : ∀ ω ∈ ({α, β} : Set Ω), x • ω ∈ ({α, β} : Set Ω) := fun ω hω => by
    rw [← mem_stabilizer_iff.mp hxαβ]
    exact Set.smul_mem_smul_set hω
  refine ⟨hx, ?_⟩
  rcases hmem α (Set.mem_insert α _) with h | h
  · exfalso
    have hβ : x • β = β := by
      rcases hmem β (Set.mem_insert_of_mem α rfl) with h' | h'
      · exact absurd (smul_left_cancel x (h'.trans h.symm)) (Ne.symm hαβ)
      · exact h'
    obtain ⟨ω, -, huniq⟩ := hx.2
    exact hαβ ((huniq α h).trans (huniq β hβ).symm)
  · exact h

theorem smul_eq_of_orderOf_eq_two {α β : Ω} {y : G} (hy : orderOf y = 2) (hyαβ : y • α = β) :
    y • β = α := by
  rw [← hyαβ, ← mul_smul, ← sq, ← hy, pow_orderOf_eq_one, one_smul]

theorem mem_stabilizer_pair_of_orderOf_eq_two {α β : Ω} {y : G} (hy : orderOf y = 2)
    (hyαβ : y • α = β) : y ∈ stabilizer G ({α, β} : Set Ω) := by
  rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, hyαβ,
    smul_eq_of_orderOf_eq_two hy hyαβ, Set.pair_comm]

private theorem exists_conj_eq_mul_of_odd {x k : G} (hx : x * x = 1) (hk : Odd (orderOf k))
    (hxk : x * k * (x * k) = 1) : ∃ g : G, g * x * g⁻¹ = x * k := by
  obtain ⟨j, hj⟩ := hk
  set m := k ^ (j + 1) with hm_def
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hmm : m * m = k := by
    rw [hm_def, ← pow_add, show j + 1 + (j + 1) = orderOf k + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hinv : x * k * x⁻¹ = k⁻¹ := by
    rw [hxinv]
    exact eq_inv_of_mul_eq_one_left (by rw [← hxk]; group)
  have hxm : x * m * x⁻¹ = m⁻¹ := by
    rw [hm_def, ← conj_pow, hinv, inv_pow]
  refine ⟨m⁻¹, ?_⟩
  have h1 : x * m = m⁻¹ * x := by
    rw [← hxm]
    group
  have h2 : x * k = k⁻¹ * x := by
    rw [← hinv]
    group
  rw [h2, ← hmm, inv_inv, mul_assoc, h1, ← mul_assoc, mul_inv_rev]

end Elementary

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

namespace Sec4Setting

theorem exists_mem_longInvSwap_centralizer_of_mem_holtDelta (hS : Sec4Setting G Ω)
    {α β δ : Ω} (hαβ : α ≠ β) (hδ : δ ∈ holtDelta G Ω α β) {V : Subgroup G}
    (hV : IsPGroup 2 V) (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (hVδ : V ≤ stabilizer G δ) :
    ∃ u ∈ longInvSwap G Ω α β, u • δ = δ ∧ u ∈ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hVT, hT⟩ := exists_fusionIsSylowIn_ge hV (le_inf hVαβ hVδ)
  obtain ⟨-, u, hu, huδ, huT⟩ := hS.sylow_twoPoint hαβ hδ hT
  exact ⟨u, hu, huδ, Subgroup.centralizer_le (fun v hv => hVT hv) huT⟩

theorem exists_mem_holtDelta_mem_fixSet (hS : Sec4Setting G Ω) {α β : Ω} {V : Subgroup G}
    (hV : IsPGroup 2 V) (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) :
    ∃ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω V :=
  exists_mem_fixSet_of_le_stabilizer hV (hS.star.odd_card_holtDelta α β)
    (hVαβ.trans ((stabilizer_inf_le_stabilizer_pair α β).trans (stabilizer_pair_le α β)))

theorem exists_mem_longInvSwap_centralizer (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) :
    ∃ u ∈ longInvSwap G Ω α β, u ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨δ, hδ, hδV⟩ := hS.exists_mem_holtDelta_mem_fixSet hV hVαβ
  obtain ⟨u, hu, -, huV⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta hαβ hδ hV
    hVαβ (mem_fixSet_iff_le_stabilizer.mp hδV)
  exact ⟨u, hu, huV⟩

@[nolint unusedArguments]
theorem exists_mem_longInvSwap_centralizer_eqOn (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) {Λ : Set Ω} (_hΛ : Λ.Nonempty)
    (hΛV : Λ ⊆ fixSet Ω V) {y : G} (hy : y ∈ longInvSwap G Ω α β)
    (hyΛ : y ∈ stabilizer G Λ) :
    ∃ c ∈ longInvSwap G Ω α β, c ∈ Subgroup.centralizer (V : Set G) ∧
      ∀ δ ∈ Λ, c • δ = y • δ := by
  by_cases hsub : Λ ⊆ {α, β}
  · obtain ⟨c, hc, hcV⟩ := hS.exists_mem_longInvSwap_centralizer hαβ hV hVαβ
    refine ⟨c, hc, hcV, fun δ hδ => ?_⟩
    rcases hsub hδ with rfl | rfl
    · rw [hc.2, hy.2]
    · rw [smul_eq_of_mem_longInvSwap hc, smul_eq_of_mem_longInvSwap hy]
  · obtain ⟨γ, hγΛ, hγ⟩ := Set.not_subset.mp hsub
    have hγα : γ ≠ α := fun h => hγ (Or.inl h)
    have hγβ : γ ≠ β := fun h => hγ (Or.inr h)
    have h3 : 3 ≤ Nat.card ↥(({α, β} : Set Ω) ∪ Λ) :=
      three_le_card_of_mem (Or.inl (Or.inl rfl)) (Or.inl (Or.inr rfl)) (Or.inr hγΛ) hαβ
        (Ne.symm hγα) (Ne.symm hγβ)
    have hVΓ : V ≤ fixingSubgroup G (({α, β} : Set Ω) ∪ Λ) := by
      intro v hv
      rw [mem_fixingSubgroup_iff]
      rintro ω (hω | hω)
      · rcases hω with rfl | rfl
        · exact mem_stabilizer_iff.mp (hVαβ hv).1
        · exact mem_stabilizer_iff.mp (hVαβ hv).2
      · exact hΛV hω v hv
    have hyΓ : y ∈ stabilizer G (({α, β} : Set Ω) ∪ Λ) := by
      rw [mem_stabilizer_iff, Set.smul_set_union,
        mem_stabilizer_iff.mp (closure_longInvSwap_le_stabilizer_pair α β
          (Subgroup.subset_closure hy)), mem_stabilizer_iff.mp hyΛ]
    obtain ⟨c, hc, hcV, hcΓ⟩ := hS.frattini h3 hV hVΓ hy.1 hyΓ
    refine ⟨c, ⟨hc, ?_⟩, hcV, fun δ hδ => hcΓ δ (Or.inr hδ)⟩
    rw [hcΓ α (Or.inl (Or.inl rfl)), hy.2]

end Sec4Setting

end Lift

section Centralizer

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

abbrev centralizerImageElt {V : Subgroup G} {c : G} (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    centralizerImage Ω V :=
  ⟨MulAction.toPermHom (Subgroup.centralizer (V : Set G)) (fixSet Ω V) ⟨c, hc⟩, ⟨c, hc⟩, rfl⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
@[simp] theorem coe_centralizerImageElt_apply {V : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) (ω : fixSet Ω V) :
    (((centralizerImageElt (Ω := Ω) hc : centralizerImage Ω V) : Equiv.Perm (fixSet Ω V)) ω :
      Ω) = c • (ω : Ω) := rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
private theorem mem_longInv_of_centralizerImage_bot [Finite Ω] [FaithfulSMul G Ω] {c : G}
    (hc : c ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G))
    (hπ : centralizerImageElt (Ω := Ω) hc ∈
      longInv (centralizerImage Ω (⊥ : Subgroup G)) (fixSet Ω (⊥ : Subgroup G))) :
    c ∈ longInv G Ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : ∀ ω : Ω, ω ∈ fixSet Ω (⊥ : Subgroup G) := fun ω => by
    rw [fixSet_bot]
    exact Set.mem_univ ω
  rw [mem_longInv_subgroup_iff] at hπ
  obtain ⟨hord, ω₀, hω₀, huniq⟩ := hπ
  set π := ((centralizerImageElt (Ω := Ω) hc : centralizerImage Ω ⊥) :
    Equiv.Perm (fixSet Ω (⊥ : Subgroup G))) with hπ_def
  have hπ2 : π * π = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
  have hcc : c * c = 1 := by
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun ω => ?_
    have h : π (π ⟨ω, hF ω⟩) = ⟨ω, hF ω⟩ := by
      rw [← Equiv.Perm.mul_apply, hπ2, Equiv.Perm.one_apply]
    calc (c * c) • ω = ((π (π ⟨ω, hF ω⟩) : fixSet Ω (⊥ : Subgroup G)) : Ω) := by
          rw [mul_smul]
          rfl
      _ = (1 : G) • ω := by rw [h, one_smul]
  have hc1 : c ≠ 1 := by
    rintro rfl
    refine absurd hord ?_
    have : π = 1 := Equiv.ext fun ω => Subtype.ext (by
      rw [hπ_def, coe_centralizerImageElt_apply, one_smul, Equiv.Perm.coe_one, id_eq])
    rw [this, orderOf_one]
    norm_num
  refine ⟨orderOf_eq_prime (by rw [sq]; exact hcc) hc1, ω₀, ?_, fun ω hω => ?_⟩
  · have h := congrArg Subtype.val hω₀
    rwa [Equiv.Perm.smul_def, coe_centralizerImageElt_apply] at h
  · have h := huniq ⟨ω, hF ω⟩ (Subtype.ext (by
      rw [Equiv.Perm.smul_def, coe_centralizerImageElt_apply]
      exact hω))
    exact congrArg Subtype.val h

theorem Sec4Setting.mem_longInv_centralizerImage_iff [FaithfulSMul G Ω] (hS : Sec4Setting G Ω)
    {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    (π : centralizerImage Ω V) :
    π ∈ longInv (centralizerImage Ω V) (fixSet Ω V) ↔
      ∃ c ∈ longInv G Ω, c ∈ Subgroup.centralizer (V : Set G) ∧
        ∀ ω : fixSet Ω V, ((π : Equiv.Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := hS.star.odd_card_fixSet hV
  constructor
  · intro hπ
    obtain ⟨_, ⟨c, hc⟩, rfl⟩ := π
    rcases eq_or_ne V ⊥ with rfl | hV1
    · exact ⟨c, mem_longInv_of_centralizerImage_bot hc hπ, hc, fun ω => rfl⟩
    · obtain ⟨a, ha⟩ := hS.star.fixSet_nonempty hV
      obtain ⟨t, ht, htV⟩ := hS.star.star a V hV (mem_fixSet_iff_le_stabilizer.mp ha) h3
      obtain ⟨x, hxJ, hxπ⟩ := (hS.longInv_inducedPerm (centralizer_le_stabilizer_fixSet V)
        (card_centralizerImage_lt_card hV hV1) (hS.star_centralizerImage hV h3)
        ⟨t, htV, ht.1⟩ _).mp hπ
      exact ⟨x, hxJ, x.2, fun ω =>
        (congrArg (fun σ : Equiv.Perm (fixSet Ω V) => ((σ ω : fixSet Ω V) : Ω)) hxπ).symm⟩
  · rintro ⟨c, hcJ, hcV, hcπ⟩
    exact mem_longInv_inducedPerm_of_eq (X := Subgroup.centralizer (V : Set G))
      (hX := centralizer_le_stabilizer_fixSet V) (x := ⟨c, hcV⟩) hodd h3 hcJ (y := π)
      (Equiv.ext fun ω => Subtype.ext (hcπ ω).symm)

theorem Sec4Setting.mem_longInvSwap_centralizerImage_iff [FaithfulSMul G Ω]
    (hS : Sec4Setting G Ω) {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    {a b : fixSet Ω V} (π : centralizerImage Ω V) :
    π ∈ longInvSwap (centralizerImage Ω V) (fixSet Ω V) a b ↔
      ∃ c ∈ longInvSwap G Ω a b, c ∈ Subgroup.centralizer (V : Set G) ∧
        ∀ ω : fixSet Ω V, ((π : Equiv.Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω) := by
  rw [mem_longInvSwap, hS.mem_longInv_centralizerImage_iff hV h3]
  constructor
  · rintro ⟨⟨c, hcJ, hcV, hcπ⟩, hab⟩
    refine ⟨c, ⟨hcJ, ?_⟩, hcV, hcπ⟩
    rw [← hcπ a, ← hab]
    rfl
  · rintro ⟨c, ⟨hcJ, hcab⟩, hcV, hcπ⟩
    exact ⟨⟨c, hcJ, hcV, hcπ⟩, Subtype.ext ((hcπ a).trans hcab)⟩

theorem Sec4Setting.mem_longInvAt_centralizerImage_iff [FaithfulSMul G Ω]
    (hS : Sec4Setting G Ω) {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    {a : fixSet Ω V} (π : centralizerImage Ω V) :
    π ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V) a ↔
      ∃ c ∈ longInvAt G Ω a, c ∈ Subgroup.centralizer (V : Set G) ∧
        ∀ ω : fixSet Ω V, ((π : Equiv.Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω) :=
  hS.mem_longInvSwap_centralizerImage_iff hV h3 π

theorem Sec4Setting.holtDelta_centralizerImage [FaithfulSMul G Ω] (hS : Sec4Setting G Ω)
    {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V)) {a b : fixSet Ω V}
    (hab : a ≠ b) :
    holtDelta (centralizerImage Ω V) (fixSet Ω V) a b =
      Subtype.val ⁻¹' holtDelta G Ω (a : Ω) (b : Ω) := by
  ext δ
  constructor
  · rintro ⟨π, hπ, hπδ⟩
    obtain ⟨c, hc, -, hcπ⟩ := (hS.mem_longInvSwap_centralizerImage_iff hV h3 π).mp hπ
    exact ⟨c, hc, (hcπ δ).symm.trans (congrArg Subtype.val hπδ)⟩
  · intro hδ
    obtain ⟨u, hu, huδ, huV⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta
      (fun h => hab (Subtype.ext h)) hδ hV
      (le_inf (mem_fixSet_iff_le_stabilizer.mp a.2) (mem_fixSet_iff_le_stabilizer.mp b.2))
      (mem_fixSet_iff_le_stabilizer.mp δ.2)
    exact ⟨centralizerImageElt huV,
      (hS.mem_longInvSwap_centralizerImage_iff hV h3 _).mpr ⟨u, hu, huV, fun ω => rfl⟩,
      Subtype.ext huδ⟩

theorem Sec4Setting.mem_holtDelta_centralizerImage_iff [FaithfulSMul G Ω] (hS : Sec4Setting G Ω)
    {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V)) {a b : fixSet Ω V}
    (hab : a ≠ b) {δ : fixSet Ω V} :
    δ ∈ holtDelta (centralizerImage Ω V) (fixSet Ω V) a b ↔
      (δ : Ω) ∈ holtDelta G Ω (a : Ω) (b : Ω) := by
  rw [hS.holtDelta_centralizerImage hV h3 hab, Set.mem_preimage]

@[expose] def Sec4Setting.holtDeltaCentralizerImageEquiv [FaithfulSMul G Ω] (hS : Sec4Setting G Ω)
    {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V)) {a b : fixSet Ω V}
    (hab : a ≠ b) :
    holtDelta (centralizerImage Ω V) (fixSet Ω V) a b ≃
      ↥(holtDelta G Ω (a : Ω) (b : Ω) ∩ fixSet Ω V) where
  toFun δ := ⟨δ.1.1, (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mp δ.2, δ.1.2⟩
  invFun ω := ⟨⟨ω.1, ω.2.2⟩, (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mpr ω.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem Sec4Setting.coe_holtDeltaCentralizerImageEquiv_apply [FaithfulSMul G Ω]
    (hS : Sec4Setting G Ω) {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    {a b : fixSet Ω V} (hab : a ≠ b) (δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) :
    ((hS.holtDeltaCentralizerImageEquiv hV h3 hab δ : ↥(holtDelta G Ω (a : Ω) (b : Ω) ∩
      fixSet Ω V)) : Ω) = ((δ : fixSet Ω V) : Ω) := rfl

@[simp] theorem Sec4Setting.coe_holtDeltaCentralizerImageEquiv_symm_apply [FaithfulSMul G Ω]
    (hS : Sec4Setting G Ω) {V : Subgroup G} (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    {a b : fixSet Ω V} (hab : a ≠ b) (ω : ↥(holtDelta G Ω (a : Ω) (b : Ω) ∩ fixSet Ω V)) :
    (((hS.holtDeltaCentralizerImageEquiv hV h3 hab).symm ω : fixSet Ω V) : Ω) = (ω : Ω) := rfl

end Centralizer

section TwoPoint

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

abbrev twoPointElt {α β : Ω} {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    twoPointSection G Ω α β :=
  ⟨twoPointHom G Ω α β ⟨g, hg⟩, twoPointHom_mem_twoPointSection _⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
@[simp] theorem coe_twoPointElt_apply {α β : Ω} {g : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) (δ : holtDelta G Ω α β) :
    (((twoPointElt hg : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) δ : Ω) =
      g • (δ : Ω) := rfl

theorem Sec4Setting.mem_longInv_twoPointSection_iff (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) (π : twoPointSection G Ω α β) :
    π ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) ↔
      ∃ c ∈ longInvSwap G Ω α β, ∀ δ : holtDelta G Ω α β,
        ((π : Equiv.Perm (holtDelta G Ω α β)) δ : Ω) = c • (δ : Ω) := by
  constructor
  · intro hπ
    obtain ⟨w, hw⟩ := longInvSwap_nonempty hS.star α β
    obtain ⟨x, hxJ, hxπ⟩ := (hS.longInv_inducedPerm (stabilizer_pair_le α β)
      (hS.card_twoPoint_lt α β hαβ) (hS.star_twoPoint hαβ h3)
      ⟨w, closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hw), hw.1⟩
      π).mp hπ
    exact ⟨x, mem_longInvSwap_of_mem_stabilizer_pair hαβ hxJ x.2, fun δ =>
      (congrArg (fun σ : Equiv.Perm (holtDelta G Ω α β) => ((σ δ : holtDelta G Ω α β) : Ω))
        hxπ).symm⟩
  · rintro ⟨c, hc, hcπ⟩
    exact mem_longInv_inducedPerm_of_eq (X := stabilizer G ({α, β} : Set Ω))
      (hX := stabilizer_pair_le α β)
      (x := ⟨c, closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc)⟩)
      (hS.star.odd_card_holtDelta α β) h3 hc.1 (y := π)
      (Equiv.ext fun δ => Subtype.ext (hcπ δ).symm)

theorem Sec4Setting.mem_longInvAt_twoPointSection_iff (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) {δ : holtDelta G Ω α β}
    (π : twoPointSection G Ω α β) :
    π ∈ longInvAt (twoPointSection G Ω α β) (holtDelta G Ω α β) δ ↔
      ∃ c ∈ longInvSwap G Ω α β, c • (δ : Ω) = δ ∧ ∀ ε : holtDelta G Ω α β,
        ((π : Equiv.Perm (holtDelta G Ω α β)) ε : Ω) = c • (ε : Ω) := by
  rw [mem_longInvAt, hS.mem_longInv_twoPointSection_iff hαβ h3]
  constructor
  · rintro ⟨⟨c, hc, hcπ⟩, hδ⟩
    exact ⟨c, hc, (hcπ δ).symm.trans (congrArg Subtype.val hδ), hcπ⟩
  · rintro ⟨c, hc, hcδ, hcπ⟩
    exact ⟨⟨c, hc, hcπ⟩, Subtype.ext ((hcπ δ).trans hcδ)⟩

theorem Sec4Setting.mem_longInv_iff_of_odd_twoPointKernel (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (hT : Odd (Nat.card (twoPointKernel G Ω α β)))
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) {y : G} (hy : orderOf y = 2) (hyαβ : y • α = β) :
    y ∈ longInv G Ω ↔ ∃! δ, δ ∈ holtDelta G Ω α β ∧ y • δ = δ := by
  constructor
  · intro hyJ
    obtain ⟨γ, hγ, huniq⟩ := hyJ.2
    exact ⟨γ, ⟨⟨y, ⟨hyJ, hyαβ⟩, hγ⟩, hγ⟩, fun δ hδ => huniq δ hδ.2⟩
  · rintro ⟨δ₀, ⟨hδ₀Δ, hδ₀⟩, huniq⟩
    have hyX := mem_stabilizer_pair_of_orderOf_eq_two hy hyαβ
    have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
    have hŷ : twoPointElt hyX ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
      rw [mem_longInv_subgroup_iff]
      have : Nontrivial (holtDelta G Ω α β) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      refine (mem_longInvAt_of_mul_self (δ := ⟨δ₀, hδ₀Δ⟩) ?_ (fun ε => ?_) (exists_ne _)).1
      · rw [← map_mul, show (⟨y, hyX⟩ : stabilizer G ({α, β} : Set Ω)) * ⟨y, hyX⟩ = 1 from
          Subtype.ext hyy, map_one]
      · rw [Equiv.Perm.smul_def, Subtype.ext_iff, Subtype.ext_iff]
        exact ⟨fun h => huniq _ ⟨ε.2, h⟩, fun h => by rw [coe_twoPointHom_apply, h]; exact hδ₀⟩
    obtain ⟨x, hx, hxy⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3 _).mp hŷ
    have hk : x⁻¹ * y ∈ twoPointKernel G Ω α β := by
      rw [mem_twoPointKernel]
      refine ⟨?_, ?_, fun δ hδ => ?_⟩
      · rw [mul_smul, hyαβ, inv_smul_eq_iff, hx.2]
      · rw [mul_smul, smul_eq_of_orderOf_eq_two hy hyαβ, inv_smul_eq_iff,
          smul_eq_of_mem_longInvSwap hx]
      · rw [mul_smul, inv_smul_eq_iff]
        exact hxy ⟨δ, hδ⟩
    have hodd : Odd (orderOf (x⁻¹ * y)) := Odd.of_dvd_nat hT (Subgroup.orderOf_dvd_natCard _ hk)
    obtain ⟨g, hg⟩ := exists_conj_eq_mul_of_odd (mul_self_eq_one_of_mem_longInv hx.1) hodd
      (by rw [mul_inv_cancel_left]; exact hyy)
    rw [mul_inv_cancel_left] at hg
    rw [← hg]
    exact conj_mem_longInv hx.1 g

end TwoPoint

section Pair

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem smul_pair_of_mem_stabilizer_pair {α β : Ω} {g : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    (g • α = α ∧ g • β = β) ∨ (g • α = β ∧ g • β = α) := by
  rwa [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton,
    Set.pair_eq_pair_iff] at hg

theorem commutatorElement_mem_stabilizer_inf {α β : Ω} {g h : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) (hh : h ∈ stabilizer G ({α, β} : Set Ω)) :
    ⁅g, h⁆ ∈ stabilizer G α ⊓ stabilizer G β := by
  have key : ∀ {x y : G}, x ∈ stabilizer G ({α, β} : Set Ω) →
      y ∈ stabilizer G ({α, β} : Set Ω) → x • y • α = y • x • α ∧ x • y • β = y • x • β := by
    intro x y hx hy
    rcases smul_pair_of_mem_stabilizer_pair hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
      rcases smul_pair_of_mem_stabilizer_pair hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
      simp only [hx1, hx2, hy1, hy2, and_self]
  obtain ⟨h1, h2⟩ := key (inv_mem hg) (inv_mem hh)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_stabilizer_iff, commutatorElement_def, mul_smul, mul_smul, mul_smul, h1,
      smul_inv_smul, smul_inv_smul]
  · rw [mem_stabilizer_iff, commutatorElement_def, mul_smul, mul_smul, mul_smul, h2,
      smul_inv_smul, smul_inv_smul]

theorem commutator_stabilizer_pair_le (α β : Ω) :
    ⁅stabilizer G ({α, β} : Set Ω), stabilizer G ({α, β} : Set Ω)⁆ ≤
      stabilizer G α ⊓ stabilizer G β :=
  Subgroup.commutator_le.mpr fun _ hg _ hh => commutatorElement_mem_stabilizer_inf hg hh

variable (G Ω) in
@[expose] def twoPointJFix (α β : Ω) : Subgroup (Equiv.Perm (holtDelta G Ω α β)) :=
  inducedPerm (Subgroup.closure (longInvSwap G Ω α β) ⊓ (stabilizer G α ⊓ stabilizer G β))
    (holtDelta G Ω α β) (inf_le_left.trans (closure_longInvSwap_le_stabilizer α β))

theorem mem_twoPointJFix {α β : Ω} {π : Equiv.Perm (holtDelta G Ω α β)} :
    π ∈ twoPointJFix G Ω α β ↔ ∃ g ∈ Subgroup.closure (longInvSwap G Ω α β),
      g • α = α ∧ g • β = β ∧ ∀ δ : holtDelta G Ω α β, (π δ : Ω) = g • (δ : Ω) := by
  rw [twoPointJFix, mem_inducedPerm]
  constructor
  · rintro ⟨g, ⟨hg, hgα, hgβ⟩, hπ⟩
    exact ⟨g, hg, hgα, hgβ, hπ⟩
  · rintro ⟨g, hg, hgα, hgβ, hπ⟩
    exact ⟨g, ⟨hg, hgα, hgβ⟩, hπ⟩

theorem commutator_twoPointJ_le (α β : Ω) :
    ⁅twoPointJ G Ω α β, twoPointJ G Ω α β⁆ ≤ twoPointJFix G Ω α β := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨k₁, rfl⟩ _ ⟨k₂, rfl⟩
  rw [← map_commutatorElement]
  exact mem_inducedPerm.mpr ⟨((⁅k₁, k₂⁆ : Subgroup.closure (longInvSwap G Ω α β)) : G),
    ⟨(⁅k₁, k₂⁆ : Subgroup.closure (longInvSwap G Ω α β)).2,
      commutatorElement_mem_stabilizer_inf (closure_longInvSwap_le_stabilizer_pair α β k₁.2)
        (closure_longInvSwap_le_stabilizer_pair α β k₂.2)⟩, fun δ => rfl⟩

end Pair

section TwoPointJ

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem holtDelta_self_subset (α : Ω) : holtDelta G Ω α α ⊆ {α} := by
  rintro γ ⟨t, ht, htγ⟩
  exact (smul_eq_iff_of_mem_longInvAt ht γ).mp htγ

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem ne_of_three_le_card_holtDelta {α β : Ω} (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) :
    α ≠ β := by
  rintro rfl
  have h := Nat.card_mono (Set.finite_singleton α) (holtDelta_self_subset (G := G) α)
  have h1 : Nat.card ({α} : Set Ω) = 1 := Nat.card_unique
  omega

omit [DecidableEq Ω] in
private theorem subsingleton_holtDelta (hG : IsStarGroup G Ω) {α β : Ω}
    (h : Nat.card (holtDelta G Ω α β) < 3) : Subsingleton (holtDelta G Ω α β) := by
  obtain ⟨k, hk⟩ := hG.odd_card_holtDelta α β
  exact Finite.card_le_one_iff_subsingleton.mp (by omega)

omit [DecidableEq Ω] in
theorem twoPointElt_mem_jHull (hG : IsStarGroup G Ω) {α β : Ω} {w : G}
    (hw : w ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hw) ∈
      jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
  rcases lt_or_ge (Nat.card (holtDelta G Ω α β)) 3 with h | h3
  · have := subsingleton_holtDelta hG h
    rw [Subsingleton.elim (twoPointElt _) 1]
    exact one_mem _
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    exact Subgroup.subset_closure (mem_longInv_inducedPerm_of_eq (hX := stabilizer_pair_le α β)
      (x := ⟨x, _⟩) (hG.odd_card_holtDelta α β) h3 hx.1 (y := twoPointElt _) rfl)
  | one =>
    rw [show twoPointElt (G := G) (α := α) (β := β) (closure_longInvSwap_le_stabilizer_pair α β
      (one_mem _)) = 1 from Subtype.ext (map_one (twoPointHom G Ω α β))]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    rw [show twoPointElt (closure_longInvSwap_le_stabilizer_pair α β (mul_mem hx hy)) =
      twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hx) *
        twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hy) from
      Subtype.ext (map_mul (twoPointHom G Ω α β) ⟨x, _⟩ ⟨y, _⟩)]
    exact mul_mem ihx ihy
  | inv x hx ih =>
    rw [show twoPointElt (closure_longInvSwap_le_stabilizer_pair α β (inv_mem hx)) =
      (twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hx))⁻¹ from
      Subtype.ext (map_inv (twoPointHom G Ω α β) ⟨x, _⟩)]
    exact inv_mem ih

omit [DecidableEq Ω] in
theorem twoPointJ_le_map_jHull (hG : IsStarGroup G Ω) (α β : Ω) :
    twoPointJ G Ω α β ≤ (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)).map
      (twoPointSection G Ω α β).subtype := by
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  exact ⟨_, twoPointElt_mem_jHull hG hw, rfl⟩

theorem Sec4Setting.twoPointJ_eq_map_jHull (hS : Sec4Setting G Ω) (α β : Ω) :
    twoPointJ G Ω α β = (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)).map
      (twoPointSection G Ω α β).subtype := by
  refine le_antisymm (twoPointJ_le_map_jHull hS.star α β) ?_
  rcases lt_or_ge (Nat.card (holtDelta G Ω α β)) 3 with h | h3
  · have := subsingleton_holtDelta hS.star h
    intro π _
    rw [Subsingleton.elim π 1]
    exact one_mem _
  rw [Subgroup.map_le_iff_le_comap, jHull_le_iff]
  intro π hπ
  obtain ⟨c, hc, hcπ⟩ :=
    (hS.mem_longInv_twoPointSection_iff (ne_of_three_le_card_holtDelta h3) h3 π).mp hπ
  exact mem_twoPointJ.mpr ⟨c, Subgroup.subset_closure hc, hcπ⟩

end TwoPointJ

section Components

theorem HoltData.rho_mem_M_of_isNaturalSE {K X : Type*} [Group K] [MulAction K X]
    (D : HoltData K X) {i : D.ι} (hi : IsNaturalSE (D.M i)) (h : jHull K X) :
    D.ρ i h ∈ D.M i := by
  rw [← D.range_rho_of_not_isOuterFactor hi.not_isOuterFactor]
  exact ⟨h, rfl⟩

theorem HoltData.jHull_le_L_of_isNaturalSE {K X : Type*} [Group K] [MulAction K X]
    [FaithfulSMul K X] (D : HoltData K X) (hO : jOddCore K X = ⊥) {i : D.ι} (hι : ∀ j, j = i)
    (hi : IsNaturalSE (D.M i)) : jHull K X ≤ D.L i := by
  intro g hg
  obtain ⟨l, hl, hli⟩ := D.mem_M.mp (D.rho_mem_M_of_isNaturalSE hi ⟨g, hg⟩)
  have hk : ((l⁻¹ * ⟨g, hg⟩ : jHull K X) : K) ∈ jOrbitKernel K X := by
    rw [D.mem_jOrbitKernel_iff_rho]
    intro j
    rw [hι j, map_mul, map_inv, hli, inv_mul_cancel]
  rw [jOrbitKernel_eq_bot hO, Subgroup.mem_bot, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_mul_eq_one] at hk
  have hlg : (l : K) = g := hk
  exact hlg ▸ hl

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [MulAction G Ω]

theorem rho_twoPointElt_mem_M_of_isNaturalSE (hG : IsStarGroup G Ω) {α β : Ω}
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {i : D.ι}
    (hi : IsNaturalSE (D.M i)) {w : G} (hw : w ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    D.ρ i ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hw),
      twoPointElt_mem_jHull hG hw⟩ ∈ D.M i :=
  D.rho_mem_M_of_isNaturalSE hi _

theorem three_le_card_holtDelta_of_holtData (hG : IsStarGroup G Ω) {α β : Ω}
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) :
    3 ≤ Nat.card (holtDelta G Ω α β) := by
  by_contra h
  have := subsingleton_holtDelta hG (not_le.mp h)
  have h2 := D.t_mem.1
  rw [Subsingleton.elim D.t 1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

end Components

section Known

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

theorem Sec4Setting.holtTheorem1Below_centralizerImage (hS : Sec4Setting G Ω)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (h3 : 3 ≤ Nat.card (fixSet Ω P)) :
    HoltTheorem1Below (Nat.card (centralizerImage Ω P)) (Nat.card (fixSet Ω P) + 1) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hS.known_inducedPerm (centralizer_le_stabilizer_fixSet P)
    (card_centralizerImage_lt_card hP hP1) (hS.star_centralizerImage hP h3)

theorem Sec4Setting.holtData_centralizerImage (hS : Sec4Setting G Ω) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (h3 : 3 ≤ Nat.card (fixSet Ω P)) :
    HoltStructure (centralizerImage Ω P) (fixSet Ω P) :=
  hS.holtTheorem1Below_centralizerImage hP hP1 h3 (centralizerImage Ω P) (fixSet Ω P)
    (Or.inr ⟨rfl, Nat.lt_succ_self _⟩) (hS.star_centralizerImage hP h3)

omit [Finite G] in
theorem Sec4Setting.holtTheorem1Below_twoPoint (hS : Sec4Setting G Ω) {α β : Ω}
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) :
    HoltTheorem1Below (Nat.card (twoPointSection G Ω α β)) (Nat.card (holtDelta G Ω α β) + 1) :=
  hS.known_inducedPerm (stabilizer_pair_le α β)
    (hS.card_twoPoint_lt α β (ne_of_three_le_card_holtDelta h3))
    (hS.star_twoPoint (ne_of_three_le_card_holtDelta h3) h3)

omit [Finite G] in
theorem Sec4Setting.holtData_twoPoint (hS : Sec4Setting G Ω) {α β : Ω}
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) :
    HoltStructure (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
  hS.holtTheorem1Below_twoPoint h3 (twoPointSection G Ω α β) (holtDelta G Ω α β)
    (Or.inr ⟨rfl, Nat.lt_succ_self _⟩)
    (hS.star_twoPoint (ne_of_three_le_card_holtDelta h3) h3)

omit [Finite G] [DecidableEq Ω] in
theorem three_le_card_fixSet_of_isTypeL (hG : IsStarGroup G Ω) {α : Ω} {v : G}
    (hv : IsTypeL G Ω α v) : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers v)) := by
  have h2 := hv.orderOf_eq_two
  have hvα := hv.smul_eq
  rw [three_le_card_fixSet_iff hG.odd_card (isPGroup_zpowers_of_orderOf_eq_two h2)]
  by_contra h
  have := Finite.card_le_one_iff_subsingleton.mp (not_lt.mp h)
  obtain ⟨-, -, -, -, -, -, -, hvJ⟩ := hv
  refine hvJ ⟨h2, α, hvα, fun ω hω => ?_⟩
  have hα : α ∈ fixSet Ω (Subgroup.zpowers v) := by rw [fixSet_zpowers, mem_fixedBy]; exact hvα
  have hω' : ω ∈ fixSet Ω (Subgroup.zpowers v) := by rw [fixSet_zpowers, mem_fixedBy]; exact hω
  exact congrArg Subtype.val (Subsingleton.elim (⟨ω, hω'⟩ : fixSet Ω _) ⟨α, hα⟩)

omit [Finite G] in
theorem Sec4Setting.star_typeLSection (hS : Sec4Setting G Ω) {α : Ω} {v : G}
    (hv : IsTypeL G Ω α v) : IsStarGroup (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  hS.star_centralizerImage (isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two)
    (three_le_card_fixSet_of_isTypeL hS.star hv)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
private theorem zpowers_ne_bot_of_isTypeL {α : Ω} {v : G} (hv : IsTypeL G Ω α v) :
    Subgroup.zpowers v ≠ ⊥ := by
  refine Subgroup.zpowers_ne_bot.mpr fun h1 => ?_
  have h2 := hv.orderOf_eq_two
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem Sec4Setting.holtTheorem1Below_typeLSection (hS : Sec4Setting G Ω) {α : Ω} {v : G}
    (hv : IsTypeL G Ω α v) :
    HoltTheorem1Below (Nat.card (typeLSection G Ω v))
      (Nat.card (fixSet Ω (Subgroup.zpowers v)) + 1) :=
  hS.holtTheorem1Below_centralizerImage (isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two)
    (zpowers_ne_bot_of_isTypeL hv) (three_le_card_fixSet_of_isTypeL hS.star hv)

theorem Sec4Setting.holtData_typeLSection (hS : Sec4Setting G Ω) {α : Ω} {v : G}
    (hv : IsTypeL G Ω α v) :
    HoltStructure (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  hS.holtData_centralizerImage (isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two)
    (zpowers_ne_bot_of_isTypeL hv) (three_le_card_fixSet_of_isTypeL hS.star hv)

end Known

end CFSG.Holt.H78
