module

public import CFSG.Holt.H78.Conjugacy
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

section Core

variable {X : Type*} [Group X] {Δ : Type} [Finite Δ]

theorem mem_longInv_range_iff_of_conj_mem (φ : X →* Equiv.Perm Δ)
    (hY : IsStarGroup φ.range Δ) (hBY : HoltTheorem1Below (Nat.card φ.range) (Nat.card Δ + 1))
    {Z : Set X} (hZJ : ∀ z ∈ Z, φ z ∈ longInv (Equiv.Perm Δ) Δ) (hZ : Z.Nonempty)
    (hZc : ∀ x, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z) (y : φ.range) :
    y ∈ longInv φ.range Δ ↔ ∃ z ∈ Z, φ z = y := by
  constructor
  · intro hy
    obtain ⟨z₀, hz₀⟩ := hZ
    have hy₀ : (⟨φ z₀, z₀, rfl⟩ : φ.range) ∈ longInv φ.range Δ :=
      mem_longInv_subgroup_iff.mpr (hZJ z₀ hz₀)
    obtain ⟨c, -, hc⟩ := exists_mem_jHull_conj_eq hY hBY hy₀ hy
    obtain ⟨x, hx⟩ := c.2
    refine ⟨x * z₀ * x⁻¹, hZc x z₀ hz₀, ?_⟩
    rw [map_mul, map_mul, map_inv, hx]
    exact congrArg Subtype.val hc
  · rintro ⟨z, hz, hzy⟩
    rw [mem_longInv_subgroup_iff, ← hzy]
    exact hZJ z hz

end Core

section Induced

variable {G : Type*} [Group G] {Ω : Type} [MulAction G Ω]
  [Finite Ω]

@[nolint unusedArguments]
theorem mem_longInv_inducedPerm_iff (_hG : IsStarGroup G Ω) {X : Subgroup G} {Δ : Set Ω}
    (hX : X ≤ stabilizer G Δ) (hY : IsStarGroup ↥(inducedPerm X Δ hX) Δ)
    (hBY : HoltTheorem1Below (Nat.card (inducedPerm X Δ hX)) (Nat.card Δ + 1))
    (hne : ∃ x ∈ X, x ∈ longInv G Ω) (y : inducedPerm X Δ hX) :
    y ∈ longInv ↥(inducedPerm X Δ hX) Δ ↔
      ∃ x : X, (x : G) ∈ longInv G Ω ∧ inducedHom X Δ hX x = (y : Equiv.Perm Δ) :=
  mem_longInv_range_iff_of_conj_mem (inducedHom X Δ hX) hY hBY
    (Z := {x : X | (x : G) ∈ longInv G Ω})
    (fun _ hz => inducedHom_mem_longInv hX hY.odd_card hY.three_le_card hz)
    (let ⟨x, hxX, hx⟩ := hne; ⟨⟨x, hxX⟩, hx⟩) (fun x _ hz => conj_mem_longInv hz x) y

end Induced

section FixSet

variable {G : Type*} [Group G] {Ω : Type} [MulAction G Ω]

private theorem conj_mem_centralizer_of_mem_normalizer' {P : Subgroup G} {x c : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) (hc : c ∈ Subgroup.centralizer (P : Set G)) :
    x * c * x⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro h hh
  have hh' : x⁻¹ * h * x ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * h * x)).mpr (by simpa [mul_assoc] using hh)
  have hc' := hc _ hh'
  calc h * (x * c * x⁻¹) = x * ((x⁻¹ * h * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * h * x)) * x⁻¹ := by rw [hc']
    _ = x * c * x⁻¹ * h := by group

variable [Finite G] [Finite Ω]

theorem HoltTheorem1Below.induced (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1))
    (X : Subgroup G) (Δ : Set Ω) (hX : X ≤ stabilizer G Δ) :
    HoltTheorem1Below (Nat.card (inducedPerm X Δ hX)) (Nat.card Δ + 1) :=
  hB.of_le (card_inducedPerm_le.trans (Subgroup.card_le_card_group X))
    (Nat.add_le_add_right (Finite.card_subtype_le (· ∈ Δ)) 1)

omit [Finite Ω] in
theorem HoltTheorem1Below.induced_fixSet (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω))
    {p : ℕ} [Fact p.Prime] {P X : Subgroup G} (hP : IsPGroup p P) (hP1 : P ≠ ⊥)
    (hCX : Subgroup.centralizer (P : Set G) ≤ X) (hXN : X ≤ Subgroup.normalizer (P : Set G))
    (d : ℕ) : HoltTheorem1Below
      (Nat.card (inducedPerm X (fixSet Ω P) (hXN.trans (normalizer_le_stabilizer_fixSet P)))) d :=
  hB.mono (Or.inl (card_inducedPerm_fixSet_lt_card hP hP1 hCX hXN))

theorem mem_longInv_inducedPerm_fixSet_iff (hG : IsStarGroup G Ω) {P X : Subgroup G}
    (hP : IsPGroup 2 P) (h3 : 3 ≤ Nat.card (fixSet Ω P))
    (hCX : Subgroup.centralizer (P : Set G) ≤ X) (hXN : X ≤ Subgroup.normalizer (P : Set G))
    (hBY : HoltTheorem1Below (Nat.card (inducedPerm X (fixSet Ω P)
      (hXN.trans (normalizer_le_stabilizer_fixSet P)))) (Nat.card (fixSet Ω P) + 1))
    (y : inducedPerm X (fixSet Ω P) (hXN.trans (normalizer_le_stabilizer_fixSet P))) :
    y ∈ longInv ↥(inducedPerm X (fixSet Ω P) (hXN.trans (normalizer_le_stabilizer_fixSet P)))
        (fixSet Ω P) ↔
      ∃ x : X, (x : G) ∈ longInv G Ω ∧ (x : G) ∈ Subgroup.centralizer (P : Set G) ∧
        inducedHom X (fixSet Ω P) (hXN.trans (normalizer_le_stabilizer_fixSet P)) x =
          (y : Equiv.Perm (fixSet Ω P)) := by
  have hY := isStarGroup_inducedPerm_fixSet hG hP h3 hCX hXN
  have hne : Nonempty (fixSet Ω P) := (Nat.card_pos_iff.mp (by omega)).1
  obtain ⟨⟨α, hα⟩⟩ := hne
  obtain ⟨t, htα, htC⟩ := hG.star α P hP (mem_fixSet_iff_le_stabilizer.mp hα) h3
  refine (mem_longInv_range_iff_of_conj_mem _ hY hBY
    (Z := {x : X | (x : G) ∈ longInv G Ω ∧ (x : G) ∈ Subgroup.centralizer (P : Set G)})
    (fun _ hz => inducedHom_mem_longInv _ hY.odd_card hY.three_le_card hz.1)
    ⟨⟨t, hCX htC⟩, htα.1, htC⟩ (fun x _ hz => ⟨conj_mem_longInv hz.1 x,
      conj_mem_centralizer_of_mem_normalizer' (hXN x.2) hz.2⟩) y).trans ?_
  simp only [Set.mem_ofPred_eq, and_assoc]

end FixSet

section Cosets

variable {G : Type} [Group G] [Finite G] {Ω : Type}
  [MulAction G Ω] [Finite Ω]

theorem mem_longInv_range_quotient_iff (hG : IsStarGroup G Ω) {α : Ω} {K : Subgroup G}
    (hK : stabilizer G α ≤ K) (h3 : 3 ≤ K.index)
    (hBY : HoltTheorem1Below (Nat.card (toPermHom G (G ⧸ K)).range) (Nat.card (G ⧸ K) + 1))
    (y : (toPermHom G (G ⧸ K)).range) :
    y ∈ longInv ↥(toPermHom G (G ⧸ K)).range (G ⧸ K) ↔
      ∃ t ∈ longInv G Ω, toPermHom G (G ⧸ K) t = (y : Equiv.Perm (G ⧸ K)) := by
  have := hG.isPretransitive
  exact mem_longInv_range_iff_of_conj_mem _ (isStarGroup_range_quotient hG hK h3) hBY
    (fun _ ht => mem_longInv_subgroup_iff.mp
      (rangeRestrict_mem_longInv_quotient hG.odd_card hK (by omega) ht))
    hG.longInv_nonempty (fun x _ ht => conj_mem_longInv ht x) y

theorem mem_longInv_range_block_iff (hG : IsStarGroup G Ω) {α : Ω} {K : Subgroup G}
    (hK : stabilizer G α ≤ K) (h3 : 3 ≤ (stabilizer G α).relIndex K)
    (hBY : HoltTheorem1Below (Nat.card (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range)
      (Nat.card (K ⧸ (stabilizer G α).subgroupOf K) + 1))
    (y : (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range) :
    y ∈ longInv ↥(toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) ↔
      ∃ t : K, (t : G) ∈ longInv G Ω ∧
        toPermHom K (K ⧸ (stabilizer G α).subgroupOf K) t =
          (y : Equiv.Perm (K ⧸ (stabilizer G α).subgroupOf K)) := by
  have := hG.isPretransitive
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  exact mem_longInv_range_iff_of_conj_mem _ (isStarGroup_range_block hG hK h3) hBY
    (Z := {k : K | (k : G) ∈ longInv G Ω})
    (fun k hk => mem_longInv_subgroup_iff.mp
      (rangeRestrict_mem_longInv_block hG.odd_card hK (by omega) k.2 hk))
    ⟨⟨t, hK ht.2⟩, ht.1⟩ (fun x _ hz => conj_mem_longInv hz x) y

end Cosets

section Lemma26

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fusionIsSylowIn_of_isSylowOf' {p : ℕ} {P K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) : fusionIsSylowIn p P K := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, fun R hRK hR hQR => ?_⟩
  have hQR' : (Q : Subgroup K) ≤ R.subgroupOf K := fun x hx => hQR ⟨x, hx, rfl⟩
  rw [← Q.is_maximal' (hR.comap_of_injective K.subtype K.subtype_injective) hQR']
  exact ((Subgroup.subgroupOf_map_subtype R K).trans (inf_eq_left.mpr hRK)).symm

private theorem exists_fusionIsSylowIn_mem_normalizer' {p : ℕ} [Fact p.Prime] {Y : Subgroup G}
    {s : G} (hs : IsPGroup p (Subgroup.zpowers s))
    (hsY : s ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ P, fusionIsSylowIn p P Y ∧ s ∈ Subgroup.normalizer (P : Set G) := by
  have hY' : Y ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsY)
  obtain ⟨Q, hsQ, hQ⟩ := exists_fusionIsSylowIn_ge hs (le_sup_right : _ ≤ Y ⊔ Subgroup.zpowers s)
  refine ⟨Q ⊓ Y, fusionIsSylowIn_of_isSylowOf'
    (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
      (exists_sylow_map_eq_of_fusionIsSylowIn hQ) le_sup_left hY'), ?_⟩
  have hsQ' : s ∈ Q := hsQ (Subgroup.mem_zpowers s)
  refine Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨?_, hsY⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => Q.mul_mem (Q.mul_mem hsQ' hx) (Q.inv_mem hsQ'), fun hx => ?_⟩
  have := Q.mul_mem (Q.mul_mem (Q.inv_mem hsQ') hx) hsQ'
  simpa [mul_assoc] using this

variable {Ω : Type} [MulAction G Ω]

omit [Finite G] in
private theorem smul_mem_of_mem_stabilizer' {Γ : Set Ω} {g : G} (hg : g ∈ stabilizer G Γ) {γ : Ω}
    (hγ : γ ∈ Γ) : g • γ ∈ Γ := by
  rw [← mem_stabilizer_iff.mp hg]
  exact Set.smul_mem_smul_set hγ

omit [Finite G] in
private theorem mem_normalizer_fixingSubgroup' {Γ : Set Ω} {y : G} (hy : y ∈ stabilizer G Γ) :
    y ∈ Subgroup.normalizer (fixingSubgroup G Γ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro f
  simp only [mem_fixingSubgroup_iff]
  constructor
  · intro hf γ hγ
    rw [mul_smul, mul_smul, hf _ (smul_mem_of_mem_stabilizer' (inv_mem hy) hγ), smul_inv_smul]
  · intro hf γ hγ
    have h := hf _ (smul_mem_of_mem_stabilizer' hy hγ)
    rw [mul_smul, mul_smul, inv_smul_smul] at h
    exact smul_left_cancel y h

variable [Finite Ω]

theorem exists_mem_longInv_centralizer_smul_eq (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {Γ : Set Ω} (hΓ : 3 ≤ Nat.card Γ)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hVΓ : V ≤ fixingSubgroup G Γ) {y : G}
    (hy : y ∈ longInv G Ω) (hyΓ : y ∈ stabilizer G Γ) :
    ∃ c ∈ longInv G Ω, c ∈ Subgroup.centralizer (V : Set G) ∧ ∀ γ ∈ Γ, c • γ = y • γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀, hyQ₀⟩ := exists_fusionIsSylowIn_mem_normalizer'
    (isPGroup_zpowers_of_orderOf_eq_two hy.1) (mem_normalizer_fixingSubgroup' hyΓ)
  obtain ⟨Q, hVQ, hQ⟩ := exists_fusionIsSylowIn_ge hV hVΓ
  obtain ⟨f, hfF, hfQ⟩ := exists_mem_conj_of_fusionIsSylowIn hQ₀ hQ
  have hy' : f * y * f⁻¹ ∈ longInv G Ω := conj_mem_longInv hy f
  have hy'Q : f * y * f⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hfQ x, hfQ (f * y * f⁻¹ * x * (f * y * f⁻¹)⁻¹),
      Subgroup.mem_normalizer_iff.mp hyQ₀ (f⁻¹ * x * f)]
    have e : f⁻¹ * (f * y * f⁻¹ * x * (f * y * f⁻¹)⁻¹) * f = y * (f⁻¹ * x * f) * y⁻¹ := by
      group
    rw [e]
  have hy'Γ : ∀ γ ∈ Γ, (f * y * f⁻¹) • γ = y • γ := fun γ hγ => by
    rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp (inv_mem hfF) γ hγ,
      (mem_fixingSubgroup_iff G).mp hfF _ (smul_mem_of_mem_stabilizer' hyΓ hγ)]
  by_cases hQ1 : Q = ⊥
  · refine ⟨y, hy, ?_, fun γ _ => rfl⟩
    have hV1 : V = ⊥ := le_bot_iff.mp (hQ1 ▸ hVQ)
    rw [hV1, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]
  have hΓQ : Γ ⊆ fixSet Ω Q := fun γ hγ q hq => (mem_fixingSubgroup_iff G).mp (hQ.1 hq) γ hγ
  have h3 : 3 ≤ Nat.card (fixSet Ω Q) := hΓ.trans (Nat.card_mono (Set.toFinite _) hΓQ)
  have hBY := hB.induced_fixSet hQ.2.1 hQ1 (Subgroup.centralizer_le_normalizer _) le_rfl
    (Nat.card (fixSet Ω Q) + 1)
  have hy'Y : (⟨_, ⟨f * y * f⁻¹, hy'Q⟩, rfl⟩ : inducedPerm (Subgroup.normalizer (Q : Set G))
      (fixSet Ω Q) ((le_rfl : Subgroup.normalizer (Q : Set G) ≤ _).trans
        (normalizer_le_stabilizer_fixSet Q))) ∈ longInv _ (fixSet Ω Q) :=
    mem_longInv_inducedPerm_of_eq (hG.odd_card_fixSet hQ.2.1) h3 (x := ⟨_, hy'Q⟩) hy' rfl
  obtain ⟨c, hcJ, hcC, hc⟩ := (mem_longInv_inducedPerm_fixSet_iff hG hQ.2.1 h3
    (Subgroup.centralizer_le_normalizer _) le_rfl hBY _).mp hy'Y
  refine ⟨c, hcJ, Subgroup.centralizer_le hVQ hcC, fun γ hγ => ?_⟩
  have h := congrArg (fun σ : Equiv.Perm (fixSet Ω Q) => (σ ⟨γ, hΓQ hγ⟩ : Ω)) hc
  simp only [coe_inducedHom_apply] at h
  rw [h, hy'Γ γ hγ]

end Lemma26

end CFSG.Holt.H78
