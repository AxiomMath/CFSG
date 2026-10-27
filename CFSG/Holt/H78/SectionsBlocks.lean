module

public import CFSG.Holt.H78.Sections
public import CFSG.Holt.H78.Dihedral

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section BlockCoset

variable [IsPretransitive G Ω]

noncomputable def blockCoset (α : Ω) (K : Subgroup G) (ω : Ω) : G ⧸ K :=
  ((exists_smul_eq G α ω).choose : G ⧸ K)

variable {α : Ω} {K : Subgroup G}

theorem blockCoset_eq_of_smul_eq (hK : stabilizer G α ≤ K) {g : G} {ω : Ω} (hg : g • α = ω) :
    blockCoset α K ω = (g : G ⧸ K) := by
  have h := (exists_smul_eq G α ω).choose_spec
  unfold blockCoset
  generalize (exists_smul_eq G α ω).choose = c at h ⊢
  rw [QuotientGroup.eq]
  apply hK
  rw [mem_stabilizer_iff, mul_smul, hg, ← h, inv_smul_smul]

theorem blockCoset_smul_self (hK : stabilizer G α ≤ K) (g : G) :
    blockCoset α K (g • α) = (g : G ⧸ K) :=
  blockCoset_eq_of_smul_eq hK rfl

theorem blockCoset_self (hK : stabilizer G α ≤ K) : blockCoset α K α = ((1 : G) : G ⧸ K) := by
  simpa using blockCoset_smul_self hK 1

theorem blockCoset_smul (hK : stabilizer G α ≤ K) (g : G) (ω : Ω) :
    blockCoset α K (g • ω) = g • blockCoset α K ω := by
  obtain ⟨h, rfl⟩ := exists_smul_eq G α ω
  rw [← mul_smul, blockCoset_smul_self hK, blockCoset_smul_self hK, MulAction.Quotient.smul_mk,
    smul_eq_mul]

theorem blockCoset_surjective (hK : stabilizer G α ≤ K) : Function.Surjective (blockCoset α K) := by
  intro c
  induction c using QuotientGroup.induction_on with
  | H g => exact ⟨g • α, blockCoset_smul_self hK g⟩

theorem blockCoset_eq_one_iff (hK : stabilizer G α ≤ K) {ω : Ω} :
    blockCoset α K ω = ((1 : G) : G ⧸ K) ↔ ω ∈ orbit K α := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
  rw [blockCoset_smul_self hK, QuotientGroup.eq, mul_one, inv_mem_iff]
  constructor
  · intro hg
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨k, hk⟩
    have hgk : g⁻¹ * k ∈ K := hK (by
      rw [mem_stabilizer_iff, mul_smul, show (k : G) • α = g • α from hk, inv_smul_smul])
    simpa using K.mul_mem k.2 (K.inv_mem hgk)

theorem blockCoset_preimage_mk (hK : stabilizer G α ≤ K) (g : G) :
    blockCoset α K ⁻¹' {(g : G ⧸ K)} = g • orbit K α := by
  ext ω
  rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_smul_set_iff_inv_smul_mem,
    ← blockCoset_eq_one_iff hK, blockCoset_smul hK, inv_smul_eq_iff, MulAction.Quotient.smul_mk,
    smul_eq_mul, mul_one]

end BlockCoset

section Card

theorem card_orbit_eq_relIndex (α : Ω) (K : Subgroup G) :
    Nat.card (orbit K α) = (stabilizer G α).relIndex K := by
  rw [Subgroup.relIndex, show (stabilizer G α).subgroupOf K = stabilizer K α from rfl,
    index_stabilizer, Nat.card_coe_set_eq]

variable [IsPretransitive G Ω] {α : Ω} {K : Subgroup G}

theorem card_eq_index_mul_relIndex (hK : stabilizer G α ≤ K) :
    Nat.card Ω = K.index * (stabilizer G α).relIndex K := by
  rw [← index_stabilizer_of_transitive G α, ← Subgroup.relIndex_mul_index hK, mul_comm]

theorem odd_index_of_le (hΩ : Odd (Nat.card Ω)) (hK : stabilizer G α ≤ K) : Odd K.index :=
  (Nat.odd_mul.mp (card_eq_index_mul_relIndex hK ▸ hΩ)).1

theorem odd_relIndex_of_le (hΩ : Odd (Nat.card Ω)) (hK : stabilizer G α ≤ K) :
    Odd ((stabilizer G α).relIndex K) :=
  (Nat.odd_mul.mp (card_eq_index_mul_relIndex hK ▸ hΩ)).2

theorem odd_card_orbit_of_le (hΩ : Odd (Nat.card Ω)) (hK : stabilizer G α ≤ K) :
    Odd (Nat.card (orbit K α)) := by
  rw [card_orbit_eq_relIndex]
  exact odd_relIndex_of_le hΩ hK

theorem card_blockCoset_preimage (hK : stabilizer G α ≤ K) (c : G ⧸ K) :
    Nat.card (blockCoset α K ⁻¹' {c}) = (stabilizer G α).relIndex K := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    rw [blockCoset_preimage_mk hK, ← Set.image_smul,
      Nat.card_image_of_injective (MulAction.injective g), card_orbit_eq_relIndex]

theorem exists_mem_fixSet_blockCoset_eq (hΩ : Odd (Nat.card Ω)) (hK : stabilizer G α ≤ K)
    {R : Subgroup G} (hR : IsPGroup 2 R) {c : G ⧸ K} (hc : ∀ r ∈ R, r • c = c) :
    ∃ ω ∈ fixSet Ω R, blockCoset α K ω = c := by
  have hodd : Odd (Nat.card (blockCoset α K ⁻¹' {c})) := by
    rw [card_blockCoset_preimage hK]
    exact odd_relIndex_of_le hΩ hK
  have hRΛ : R ≤ stabilizer G (blockCoset α K ⁻¹' {c}) := fun r hr => by
    rw [mem_stabilizer_set]
    intro ω
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff,
      blockCoset_smul hK]
    constructor
    · intro h
      rw [← hc r hr] at h
      exact (smul_left_cancel_iff r).mp h
    · intro h
      rw [h, hc r hr]
  have : Finite (blockCoset α K ⁻¹' {c}) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  obtain ⟨ω, hωΛ, hω⟩ := exists_mem_fixSet_of_le_stabilizer hR hodd hRΛ
  exact ⟨ω, hω, hωΛ⟩

theorem smul_eq_iff_of_mem_longInvAt_quotient (hΩ : Odd (Nat.card Ω)) (hK : stabilizer G α ≤ K)
    {t : G} {β : Ω} (ht : t ∈ longInvAt G Ω β) (c : G ⧸ K) :
    t • c = c ↔ c = blockCoset α K β := by
  constructor
  · intro h
    obtain ⟨ω, hω, rfl⟩ := exists_mem_fixSet_blockCoset_eq hΩ hK
      (isPGroup_zpowers_of_orderOf_eq_two ht.1.1) (c := c)
      fun r hr => mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr h) hr)
    rw [fixSet_zpowers] at hω
    rw [(smul_eq_iff_of_mem_longInvAt ht ω).mp hω]
  · rintro rfl
    rw [← blockCoset_smul hK, ht.2]

end Card

section BlockPoint

@[expose] def blockPoint (α : Ω) (K : Subgroup G) : K ⧸ (stabilizer G α).subgroupOf K → Ω :=
  ofQuotientStabilizer K α

variable {α : Ω} {K : Subgroup G}

@[simp] theorem blockPoint_mk (k : K) :
    blockPoint α K (k : K ⧸ (stabilizer G α).subgroupOf K) = (k : G) • α := rfl

theorem blockPoint_injective : Function.Injective (blockPoint α K) :=
  injective_ofQuotientStabilizer K α

theorem blockPoint_smul (k : K) (c : K ⧸ (stabilizer G α).subgroupOf K) :
    blockPoint α K (k • c) = (k : G) • blockPoint α K c :=
  ofQuotientStabilizer_smul K α k c

theorem blockPoint_mem_orbit (c : K ⧸ (stabilizer G α).subgroupOf K) :
    blockPoint α K c ∈ orbit K α :=
  ofQuotientStabilizer_mem_orbit K α c

theorem exists_blockPoint_eq {ω : Ω} (hω : ω ∈ orbit K α) : ∃ c, blockPoint α K c = ω := by
  obtain ⟨k, rfl⟩ := hω
  exact ⟨k, rfl⟩

theorem smul_eq_iff_blockPoint (k : K) (c : K ⧸ (stabilizer G α).subgroupOf K) :
    k • c = c ↔ (k : G) • blockPoint α K c = blockPoint α K c := by
  rw [← blockPoint_smul, blockPoint_injective.eq_iff]

theorem le_stabilizer_orbit (K : Subgroup G) (α : Ω) : K ≤ stabilizer G (orbit K α) :=
  fun k hk => by
    rw [mem_stabilizer_iff]
    exact smul_orbit (⟨k, hk⟩ : K) α

theorem stabilizer_le_of_mem_orbit (hK : stabilizer G α ≤ K) {β : Ω} (hβ : β ∈ orbit K α) :
    stabilizer G β ≤ K := by
  obtain ⟨k, rfl⟩ := hβ
  intro g hg
  have hg' : g • (k : G) • α = (k : G) • α := hg
  have h : (k : G)⁻¹ * g * k ∈ K := hK (by
    rw [mem_stabilizer_iff, mul_smul, mul_smul, hg', inv_smul_smul])
  have hgk : g = k * ((k : G)⁻¹ * g * k) * (k : G)⁻¹ := by group
  rw [hgk]
  exact K.mul_mem (K.mul_mem k.2 h) (K.inv_mem k.2)

end BlockPoint

section Lift

@[simp] theorem rangeRestrict_toPermHom_smul {Δ : Type*} [MulAction G Δ] (g : G) (δ : Δ) :
    (toPermHom G Δ).rangeRestrict g • δ = g • δ := rfl

theorem exists_isPGroup_lift_range [Finite G] {p : ℕ} [Fact p.Prime] {Δ : Type*}
    [MulAction G Δ] {R : Subgroup (toPermHom G Δ).range} (hR : IsPGroup p R) :
    ∃ R' : Subgroup G, IsPGroup p R' ∧
      (∀ r ∈ R', ∃ y ∈ R, ∀ δ : Δ, (y : Equiv.Perm Δ) δ = r • δ) ∧
      (∀ y ∈ R, ∃ r ∈ R', ∀ δ : Δ, (y : Equiv.Perm Δ) δ = r • δ) := by
  obtain ⟨R', -, -, hR', hR'Q⟩ := exists_isPGroup_map_eq_of_map_le (toPermHom G Δ)
    (hR.map (toPermHom G Δ).range.subtype)
    (by rw [← MonoidHom.range_eq_map]; exact Subgroup.map_subtype_le R) IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  refine ⟨R', hR', fun r hr => ?_, fun y hy => ?_⟩
  · have hmem : toPermHom G Δ r ∈ R.map (toPermHom G Δ).range.subtype := by
      rw [← hR'Q]
      exact Subgroup.mem_map_of_mem _ hr
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp hmem
    refine ⟨y, hy, fun δ => ?_⟩
    rw [Subgroup.coe_subtype] at hyr
    rw [hyr]
    rfl
  · have hmem : (y : Equiv.Perm Δ) ∈ R'.map (toPermHom G Δ) := by
      rw [hR'Q]
      exact Subgroup.mem_map_of_mem _ hy
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp hmem
    refine ⟨r, hr, fun δ => ?_⟩
    rw [← hry]
    rfl

end Lift

section Images

variable [Finite G] {α : Ω} {K : Subgroup G}

theorem rangeRestrict_mem_longInvAt_quotient [IsPretransitive G Ω] (hΩ : Odd (Nat.card Ω))
    (hK : stabilizer G α ≤ K) (h1 : 1 < K.index) {t : G} {β : Ω} (ht : t ∈ longInvAt G Ω β) :
    (toPermHom G (G ⧸ K)).rangeRestrict t ∈
      longInvAt ↥(toPermHom G (G ⧸ K)).range (G ⧸ K) (blockCoset α K β) := by
  have : Nontrivial (G ⧸ K) := Finite.one_lt_card_iff_nontrivial.mp h1
  refine mem_longInvAt_of_mul_self ?_ (fun c => ?_) (exists_ne _)
  · rw [← map_mul, mul_self_eq_one_of_mem_longInv ht.1, map_one]
  · rw [rangeRestrict_toPermHom_smul]
    exact smul_eq_iff_of_mem_longInvAt_quotient hΩ hK ht c

theorem rangeRestrict_mem_longInv_quotient [IsPretransitive G Ω] (hΩ : Odd (Nat.card Ω))
    (hK : stabilizer G α ≤ K) (h1 : 1 < K.index) {t : G} (ht : t ∈ longInv G Ω) :
    (toPermHom G (G ⧸ K)).rangeRestrict t ∈ longInv ↥(toPermHom G (G ⧸ K)).range (G ⧸ K) := by
  obtain ⟨β, hβ⟩ := exists_mem_longInvAt ht
  exact (rangeRestrict_mem_longInvAt_quotient hΩ hK h1 hβ).1

theorem rangeRestrict_mem_longInvAt_block (h1 : 1 < (stabilizer G α).relIndex K) {t : G}
    (htK : t ∈ K) {c : K ⧸ (stabilizer G α).subgroupOf K}
    (ht : t ∈ longInvAt G Ω (blockPoint α K c)) :
    (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict ⟨t, htK⟩ ∈
      longInvAt ↥(toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) c := by
  have : Nontrivial (K ⧸ (stabilizer G α).subgroupOf K) :=
    Finite.one_lt_card_iff_nontrivial.mp h1
  refine mem_longInvAt_of_mul_self ?_ (fun c' => ?_) (exists_ne _)
  · rw [← map_mul, show (⟨t, htK⟩ : K) * ⟨t, htK⟩ = 1 from
      Subtype.ext (mul_self_eq_one_of_mem_longInv ht.1), map_one]
  · rw [rangeRestrict_toPermHom_smul, smul_eq_iff_blockPoint, smul_eq_iff_of_mem_longInvAt ht,
      blockPoint_injective.eq_iff]

theorem rangeRestrict_mem_longInv_block [IsPretransitive G Ω] (hΩ : Odd (Nat.card Ω))
    (hK : stabilizer G α ≤ K) (h1 : 1 < (stabilizer G α).relIndex K) {t : G} (htK : t ∈ K)
    (ht : t ∈ longInv G Ω) :
    (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict ⟨t, htK⟩ ∈
      longInv ↥(toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) := by
  obtain ⟨β, hβ⟩ := exists_mem_longInvAt ht
  have : Finite (orbit K α) :=
    Nat.finite_of_card_ne_zero (odd_card_orbit_of_le hΩ hK).pos.ne'
  have hβB : β ∈ orbit K α := mem_of_mem_longInvAt_of_mem_stabilizer hβ
    (odd_card_orbit_of_le hΩ hK) (le_stabilizer_orbit K α htK)
  obtain ⟨c, rfl⟩ := exists_blockPoint_eq hβB
  exact (rangeRestrict_mem_longInvAt_block h1 htK hβ).1

end Images

section Star

variable [Finite G] [Finite Ω]

theorem isStarGroup_range_quotient (hG : IsStarGroup G Ω) {α : Ω} {K : Subgroup G}
    (hK : stabilizer G α ≤ K) (h3 : 3 ≤ K.index) :
    IsStarGroup ↥(toPermHom G (G ⧸ K)).range (G ⧸ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hG.isPretransitive
  refine ⟨odd_index_of_le hG.odd_card hK, h3, fun b R hR hRb hR3 => ?_⟩
  obtain ⟨R', hR', hlift, hlift'⟩ := exists_isPGroup_lift_range hR
  have hfix : ∀ c ∈ fixSet (G ⧸ K) R, ∀ r ∈ R', r • c = c := fun c hc r hr => by
    obtain ⟨y, hy, hyr⟩ := hlift r hr
    rw [← hyr]
    exact hc y hy
  have : Nonempty Ω := ⟨α⟩
  choose! ω hωR hωc using fun c (hc : c ∈ fixSet (G ⧸ K) R) =>
    exists_mem_fixSet_blockCoset_eq hG.odd_card hK hR' (hfix c hc)
  have hb : b ∈ fixSet (G ⧸ K) R := fun y hy => hRb hy
  have h3' : 3 ≤ Nat.card (fixSet Ω R') := by
    refine hR3.trans (Nat.card_le_card_of_injective (fun c => ⟨ω c, hωR c c.2⟩) fun c c' h => ?_)
    apply Subtype.ext
    rw [← hωc c c.2, ← hωc c' c'.2]
    exact congrArg (blockCoset α K) (Subtype.ext_iff.mp h)
  obtain ⟨t, htβ, htR⟩ := hG.star (ω b) R' hR' (mem_fixSet_iff_le_stabilizer.mp (hωR b hb)) h3'
  refine ⟨(toPermHom G (G ⧸ K)).rangeRestrict t, ?_,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  · have h := rangeRestrict_mem_longInvAt_quotient hG.odd_card hK (by omega) htβ
    rwa [hωc b hb] at h
  · obtain ⟨r, hr, hry⟩ := hlift' y hy
    refine Subtype.ext (Equiv.ext fun c => ?_)
    simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hry,
      MonoidHom.coe_rangeRestrict, toPermHom_apply, toPerm_apply]
    rw [← mul_smul, ← mul_smul, Subgroup.mem_centralizer_iff.mp htR r hr]

theorem isStarGroup_range_block (hG : IsStarGroup G Ω) {α : Ω} {K : Subgroup G}
    (hK : stabilizer G α ≤ K) (h3 : 3 ≤ (stabilizer G α).relIndex K) :
    IsStarGroup ↥(toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hG.isPretransitive
  refine ⟨odd_relIndex_of_le hG.odd_card hK, h3, fun b R hR hRb hR3 => ?_⟩
  obtain ⟨R', hR', hlift, hlift'⟩ := exists_isPGroup_lift_range hR
  have hfix : ∀ c ∈ fixSet (K ⧸ (stabilizer G α).subgroupOf K) R,
      blockPoint α K c ∈ fixSet Ω (R'.map K.subtype) := by
    rintro c hc _ ⟨r, hr, rfl⟩
    obtain ⟨y, hy, hyr⟩ := hlift r hr
    rw [Subgroup.coe_subtype, ← smul_eq_iff_blockPoint r c, ← hyr c]
    exact hc y hy
  have h3' : 3 ≤ Nat.card (fixSet Ω (R'.map K.subtype)) :=
    hR3.trans (Nat.card_le_card_of_injective (fun c => ⟨blockPoint α K c, hfix c c.2⟩)
      fun c c' h => Subtype.ext (blockPoint_injective (Subtype.ext_iff.mp h)))
  have hb : b ∈ fixSet (K ⧸ (stabilizer G α).subgroupOf K) R := fun y hy => hRb hy
  obtain ⟨t, htβ, htR⟩ := hG.star (blockPoint α K b) (R'.map K.subtype) (hR'.map _)
    (mem_fixSet_iff_le_stabilizer.mp (hfix b hb)) h3'
  have htK : t ∈ K := stabilizer_le_of_mem_orbit hK (blockPoint_mem_orbit b) htβ.2
  refine ⟨(toPermHom K _).rangeRestrict ⟨t, htK⟩, rangeRestrict_mem_longInvAt_block (by omega)
    htK htβ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨r, hr, hry⟩ := hlift' y hy
  refine Subtype.ext (Equiv.ext fun c => ?_)
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hry,
    MonoidHom.coe_rangeRestrict, toPermHom_apply, toPerm_apply]
  rw [← mul_smul, ← mul_smul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htR r ⟨r, hr, rfl⟩)

end Star

section Order

variable [Finite G]

theorem card_range_toPermHom_le (Δ : Type*) [MulAction G Δ] :
    Nat.card (toPermHom G Δ).range ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _)

variable [Finite Ω] [IsPretransitive G Ω] {α : Ω} {K : Subgroup G}

theorem card_quotient_lt_card (hK : stabilizer G α < K) : Nat.card (G ⧸ K) < Nat.card Ω := by
  have h := card_eq_index_mul_relIndex hK.le
  have h1 : (stabilizer G α).relIndex K ≠ 1 := fun h1 =>
    hK.not_ge (Subgroup.relIndex_eq_one.mp h1)
  have hpos : 0 < Nat.card Ω := Nat.card_pos_iff.mpr ⟨⟨α⟩, inferInstance⟩
  have hidx : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hrel : 0 < (stabilizer G α).relIndex K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at h
    omega
  change K.index < Nat.card Ω
  rw [h]
  exact lt_mul_of_one_lt_right hidx (by omega)

theorem lex_lt_range_quotient (hK : stabilizer G α < K) :
    Nat.card (toPermHom G (G ⧸ K)).range < Nat.card G ∨
      (Nat.card (toPermHom G (G ⧸ K)).range = Nat.card G ∧ Nat.card (G ⧸ K) < Nat.card Ω) := by
  rcases (card_range_toPermHom_le (G := G) (G ⧸ K)).lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, card_quotient_lt_card hK⟩

omit [Finite Ω] [IsPretransitive G Ω] in
theorem card_range_block_lt (hK : K < ⊤) :
    Nat.card (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range < Nat.card G :=
  (card_range_toPermHom_le _).trans_lt (by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt hK)

end Order

end CFSG.Holt.H78
