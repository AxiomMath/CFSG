module

public import CFSG.Holt.H78.JImages
public import CFSG.Holt.H78.Count

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Statement

@[expose] def Lemma27iAt (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω] (α β : Ω) : Prop :=
  Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) ∧
    ∀ γ ∈ holtDelta' G Ω α β, holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ

@[expose] def Lemma27iBelow (n d : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Δ : Type) [MulAction X Δ] [Finite Δ] [FaithfulSMul X Δ],
    (Nat.card X < n ∨ (Nat.card X = n ∧ Nat.card Δ < d)) → IsStarGroup X Δ →
    HoltTheorem1Below (Nat.card X) (Nat.card Δ + 1) → ∀ α β : Δ, α ≠ β → Lemma27iAt X Δ α β

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem holtDelta'_eq_orbit_of_subset {α β γ : Ω} (hγ : γ ∈ holtDelta' G Ω α β)
    (h : holtDelta' G Ω α β ⊆ orbit ↥(stabilizer G α ⊓ stabilizer G β) γ) :
    holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ := by
  refine h.antisymm ?_
  rintro _ ⟨g, rfl⟩
  have hg := mem_stabilizer_iff.mp (stabilizer_inf_le_stabilizer_holtDelta' (G := G) α β g.2)
  rw [← hg]
  exact Set.smul_mem_smul_set hγ

end Statement

section Block

variable {G : Type*} [Group G] {Ω : Type} [MulAction G Ω]

theorem IsStarGroup.odd_card_of_isBlock [Finite G] [Finite Ω] (hG : IsStarGroup G Ω)
    {Γ : Set Ω} (hΓ : IsBlock G Γ) (hne : Γ.Nonempty) : Odd (Nat.card Γ) := by
  have := hG.isPretransitive
  rw [Nat.card_coe_set_eq]
  exact hG.odd_card.of_dvd_nat (hΓ.ncard_dvd_card hne)

theorem IsStarGroup.three_le_card_of_isBlock [Finite G] [Finite Ω] (hG : IsStarGroup G Ω)
    {Γ : Set Ω} (hΓ : IsBlock G Γ) {α β : Ω} (hα : α ∈ Γ) (hβ : β ∈ Γ) (hαβ : α ≠ β) :
    3 ≤ Nat.card Γ := by
  have hodd := hG.odd_card_of_isBlock hΓ ⟨α, hα⟩
  have : Nontrivial Γ := ⟨⟨⟨α, hα⟩, ⟨β, hβ⟩, fun h => hαβ (congrArg Subtype.val h)⟩⟩
  have h2 : 1 < Nat.card Γ := Finite.one_lt_card_iff_nontrivial.mpr this
  obtain ⟨k, hk⟩ := hodd
  omega

theorem isStarGroup_inducedPerm_block [Finite G] [Finite Ω] (hG : IsStarGroup G Ω)
    {Γ : Set Ω} (hΓ : IsBlock G Γ) (h3 : 3 ≤ Nat.card Γ) :
    IsStarGroup ↥(inducedPerm (stabilizer G Γ) Γ le_rfl) ↥Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ : Γ.Nonempty := Set.nonempty_of_ncard_ne_zero (by
    rw [← Nat.card_coe_set_eq]; omega)
  refine ⟨hG.odd_card_of_isBlock hΓ ⟨α, hα⟩, h3, fun δ R hR hRδ hR3 => ?_⟩
  obtain ⟨R', hR'X, hR', hlift, hlift'⟩ := exists_isPGroup_lift_inducedPerm hR
  have hR'δ : R' ≤ stabilizer G (δ : Ω) := fun r hr => by
    obtain ⟨y, hy, hyr⟩ := hlift r hr
    rw [mem_stabilizer_iff, ← hyr δ]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp (hRδ hy))
  have h3R' : 3 ≤ Nat.card (fixSet Ω R') := by
    refine hR3.trans (Nat.card_le_card_of_injective (fun ε => ⟨((ε : Γ) : Ω), ?_⟩) ?_)
    · intro r hr
      obtain ⟨y, hy, hyr⟩ := hlift r hr
      rw [← hyr]
      exact congrArg Subtype.val (ε.2 y hy)
    · intro ε ε' h
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  obtain ⟨t, htδ, htR⟩ := hG.star δ R' hR' hR'δ h3R'
  have htX : t ∈ stabilizer G Γ := hΓ.stabilizer_le δ.2 htδ.2
  have : Nontrivial Γ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨⟨inducedHom (stabilizer G Γ) Γ le_rfl ⟨t, htX⟩, ⟨t, htX⟩, rfl⟩,
    mem_longInvAt_subgroup_iff.mpr (inducedHom_mem_longInvAt _ (x := ⟨t, htX⟩) htδ
      (exists_ne δ)), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨r, hr, hry⟩ := hlift' y hy
  refine Subtype.ext (Equiv.ext fun ε => Subtype.ext ?_)
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hry,
    coe_inducedHom_apply]
  rw [← mul_smul, ← mul_smul, Subgroup.mem_centralizer_iff.mp htR r hr]

theorem card_inducedPerm_block_lt [Finite G] [IsPretransitive G Ω] {Γ : Set Ω}
    (hΓ : Γ ≠ Set.univ) {α : Ω} (hα : α ∈ Γ) :
    Nat.card (inducedPerm (stabilizer G Γ) Γ le_rfl) < Nat.card G := by
  refine card_inducedPerm_le.trans_lt (lt_of_not_ge fun h => hΓ ?_)
  have htop := Subgroup.eq_top_of_le_card _ h
  refine Set.eq_univ_of_forall fun ω => ?_
  obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
  have hg : g • Γ = Γ := mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top g)
  rw [← hg]
  exact Set.smul_mem_smul_set hα

end Block

section Case1

theorem card_preimage_eq_mul {A B : Type*} [Finite A] (f : A → B) {S : Set B} [Finite S]
    {l : ℕ} (hl : ∀ b ∈ S, Nat.card {a // f a = b} = l) :
    Nat.card (f ⁻¹' S) = l * Nat.card S := by
  classical
  have := Fintype.ofFinite S
  let g : f ⁻¹' S → S := fun a => ⟨f a, a.2⟩
  have hfib : ∀ b : S, Nat.card {a : f ⁻¹' S // g a = b} = l := fun b => by
    rw [← hl b b.2]
    exact Nat.card_congr
      { toFun := fun a => ⟨a.1.1, congrArg Subtype.val a.2⟩
        invFun := fun a => ⟨⟨a.1, by rw [Set.mem_preimage, a.2]; exact b.2⟩, Subtype.ext a.2⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma,
    Finset.sum_congr rfl fun b _ => hfib b,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

variable {G : Type} [Group G] [Finite G] {Ω : Type}
  [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

theorem exists_mem_stabilizer_conj_eq_of_isBlock (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {Γ : Set Ω} (hΓ : IsBlock G Γ)
    (hodd : Odd (Nat.card Γ)) {t u : G} (ht : t ∈ longInv G Ω) (htΓ : t ∈ stabilizer G Γ)
    (hu : u ∈ longInv G Ω) (huΓ : u ∈ stabilizer G Γ) :
    ∃ h ∈ stabilizer G Γ, h * t * h⁻¹ = u := by
  obtain ⟨h, -, rfl⟩ := exists_mem_jHull_conj_eq hG hB ht hu
  obtain ⟨δ, hδ⟩ := exists_mem_longInvAt ht
  have hδΓ := mem_of_mem_longInvAt_of_mem_stabilizer hδ hodd htΓ
  have hhδΓ := mem_of_mem_longInvAt_of_mem_stabilizer (conj_mem_longInvAt hδ h) hodd huΓ
  exact ⟨h, mem_stabilizer_iff.mpr (hΓ.smul_eq_of_mem hδΓ hhδΓ), rfl⟩

variable (G) in
private abbrev BlockInv (Γ : Set Ω) : Type := {g : G // g ∈ longInv G Ω ∧ g ∈ stabilizer G Γ}

private def blockRes (Γ : Set Ω) (a : BlockInv G Γ) : Equiv.Perm Γ :=
  inducedHom (stabilizer G Γ) Γ le_rfl ⟨a.1, a.2.2⟩

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
private theorem blockRes_conj {Γ : Set Ω} {h : G} (hh : h ∈ stabilizer G Γ) (a : BlockInv G Γ) :
    blockRes Γ ⟨h * a.1 * h⁻¹, conj_mem_longInv a.2.1 h, (stabilizer G Γ).mul_mem
      ((stabilizer G Γ).mul_mem hh a.2.2) ((stabilizer G Γ).inv_mem hh)⟩ =
      inducedHom _ Γ le_rfl ⟨h, hh⟩ * blockRes Γ a * (inducedHom _ Γ le_rfl ⟨h, hh⟩)⁻¹ := by
  simp only [blockRes]
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
private theorem card_fibre_blockRes_eq_of_conj {Γ : Set Ω} {h : G} (hh : h ∈ stabilizer G Γ)
    {σ₀ σ₁ : Equiv.Perm Γ}
    (hσ : inducedHom _ Γ le_rfl ⟨h, hh⟩ * σ₀ * (inducedHom _ Γ le_rfl ⟨h, hh⟩)⁻¹ = σ₁) :
    Nat.card {a : BlockInv G Γ // blockRes Γ a = σ₀} =
      Nat.card {a : BlockInv G Γ // blockRes Γ a = σ₁} := by
  set X := stabilizer G Γ
  let e : BlockInv G Γ ≃ BlockInv G Γ :=
    { toFun := fun a => ⟨h * a.1 * h⁻¹, conj_mem_longInv a.2.1 h,
        X.mul_mem (X.mul_mem hh a.2.2) (X.inv_mem hh)⟩
      invFun := fun a => ⟨h⁻¹ * a.1 * h⁻¹⁻¹, conj_mem_longInv a.2.1 h⁻¹,
        X.mul_mem (X.mul_mem (X.inv_mem hh) a.2.2) (X.inv_mem (X.inv_mem hh))⟩
      left_inv := fun a => Subtype.ext (by group)
      right_inv := fun a => Subtype.ext (by group) }
  refine Nat.card_congr (e.subtypeEquiv fun a => ?_)
  rw [show blockRes Γ (e a) = _ from blockRes_conj hh a, ← hσ]
  exact ⟨fun ha => by rw [ha], fun ha => mul_left_cancel (mul_right_cancel ha)⟩

private theorem card_fibre_blockRes_eq (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {Γ : Set Ω} (hΓ : IsBlock G Γ)
    (hodd : Odd (Nat.card Γ)) (a₀ a₁ : BlockInv G Γ) :
    Nat.card {a : BlockInv G Γ // blockRes Γ a = blockRes Γ a₀} =
      Nat.card {a : BlockInv G Γ // blockRes Γ a = blockRes Γ a₁} := by
  obtain ⟨h, hhX, hh⟩ :=
    exists_mem_stabilizer_conj_eq_of_isBlock hG hB hΓ hodd a₀.2.1 a₀.2.2 a₁.2.1 a₁.2.2
  refine card_fibre_blockRes_eq_of_conj hhX ?_
  rw [← blockRes_conj hhX a₀]
  exact congrArg (blockRes Γ) (Subtype.ext hh)

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
private theorem longInvAt_eq_image_blockRes {Γ : Set Ω} (hΓ : IsBlock G Γ) {α β : Ω}
    (hα : α ∈ Γ) (hβ : β ∈ Γ) (hαβ : α ≠ β) :
    longInvAt G Ω α = (fun a : BlockInv G Γ => a.1) '' (blockRes Γ ⁻¹'
      (Subtype.val '' longInvAt ↥(inducedPerm (stabilizer G Γ) Γ le_rfl) Γ ⟨α, hα⟩)) := by
  ext s
  constructor
  · intro hs
    have hsX : s ∈ stabilizer G Γ := hΓ.stabilizer_le hα hs.2
    refine ⟨⟨s, hs.1, hsX⟩, ⟨⟨blockRes Γ ⟨s, hs.1, hsX⟩, ⟨s, hsX⟩, rfl⟩, ?_, rfl⟩, rfl⟩
    exact mem_longInvAt_subgroup_iff.mpr (inducedHom_mem_longInvAt le_rfl (x := ⟨s, hsX⟩)
      (α := ⟨α, hα⟩) hs ⟨⟨β, hβ⟩, fun h => hαβ (congrArg Subtype.val h).symm⟩)
  · rintro ⟨a, ⟨y, hy, hya⟩, rfl⟩
    have h1 : ((y : Equiv.Perm Γ) ⟨α, hα⟩ : Ω) = α :=
      congrArg Subtype.val (mem_longInvAt_subgroup_iff.mp hy).2
    rw [hya] at h1
    exact ⟨a.2.1, h1⟩

omit [FaithfulSMul G Ω] in
private theorem longInvSwap_eq_image_blockRes (hG : IsStarGroup G Ω) {Γ : Set Ω}
    (hΓ : IsBlock G Γ) {α β : Ω} (hα : α ∈ Γ) (hβ : β ∈ Γ) (hαβ : α ≠ β) :
    longInvSwap G Ω α β = (fun a : BlockInv G Γ => a.1) '' (blockRes Γ ⁻¹'
      (Subtype.val '' longInvSwap ↥(inducedPerm (stabilizer G Γ) Γ le_rfl) Γ ⟨α, hα⟩
        ⟨β, hβ⟩)) := by
  have hodd := hG.odd_card_of_isBlock hΓ ⟨α, hα⟩
  have h3 := hG.three_le_card_of_isBlock hΓ hα hβ hαβ
  ext s
  constructor
  · intro hs
    have hsX : s ∈ stabilizer G Γ :=
      mem_stabilizer_iff.mpr (hΓ.smul_eq_of_mem hα (by rw [hs.2]; exact hβ))
    refine ⟨⟨s, hs.1, hsX⟩, ⟨⟨blockRes Γ ⟨s, hs.1, hsX⟩, ⟨s, hsX⟩, rfl⟩, ⟨?_, ?_⟩, rfl⟩, rfl⟩
    · exact mem_longInv_subgroup_iff.mpr
        (inducedHom_mem_longInv le_rfl hodd h3 (x := ⟨s, hsX⟩) hs.1)
    · exact Subtype.ext hs.2
  · rintro ⟨a, ⟨y, hy, hya⟩, rfl⟩
    have h1 : ((y : Equiv.Perm Γ) ⟨α, hα⟩ : Ω) = β := congrArg Subtype.val hy.2
    rw [hya] at h1
    exact ⟨a.2.1, h1⟩

theorem lemma27iAt_of_isBlock (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1))
    (hIH : Lemma27iBelow (Nat.card G) (Nat.card Ω)) {Γ : Set Ω} (hΓ : IsBlock G Γ)
    (hΓu : Γ ≠ Set.univ) {α β : Ω} (hα : α ∈ Γ) (hβ : β ∈ Γ) (hαβ : α ≠ β) :
    Lemma27iAt G Ω α β := by
  have := hG.isPretransitive
  have hodd := hG.odd_card_of_isBlock hΓ ⟨α, hα⟩
  have h3 := hG.three_le_card_of_isBlock hΓ hα hβ hαβ
  set X := stabilizer G Γ
  set Y := inducedPerm X Γ le_rfl
  have hY : IsStarGroup ↥Y ↥Γ := isStarGroup_inducedPerm_block hG hΓ h3
  have hBY : HoltTheorem1Below (Nat.card Y) (Nat.card Γ + 1) := hB.induced X Γ le_rfl
  have hY27 := hIH ↥Y ↥Γ (Or.inl (card_inducedPerm_block_lt hΓu hα)) hY hBY ⟨α, hα⟩ ⟨β, hβ⟩
    fun h => hαβ (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  set a₀ : BlockInv G Γ := ⟨t, ht.1, hΓ.stabilizer_le hα ht.2⟩
  have hl : ∀ σ ∈ Subtype.val '' longInv ↥Y ↥Γ,
      Nat.card {a : BlockInv G Γ // blockRes Γ a = σ} =
        Nat.card {a : BlockInv G Γ // blockRes Γ a = blockRes Γ a₀} := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ :=
      (mem_longInv_inducedPerm_iff hG le_rfl hY hBY ⟨t, a₀.2.2, ht.1⟩ y).mp hy
    rw [← show blockRes (G := G) Γ ⟨(x : G), hx, x.2⟩ = y from hxy]
    exact card_fibre_blockRes_eq hG hB hΓ hodd _ _
  have hinj : Function.Injective (fun a : BlockInv G Γ => a.1) := Subtype.val_injective
  have hcardAt : Nat.card (longInvAt G Ω α) = Nat.card {a : BlockInv G Γ //
      blockRes Γ a = blockRes Γ a₀} * Nat.card (longInvAt ↥Y ↥Γ ⟨α, hα⟩) := by
    rw [longInvAt_eq_image_blockRes hΓ hα hβ hαβ, Nat.card_image_of_injective hinj,
      card_preimage_eq_mul _ fun σ hσ => hl σ (Set.image_mono (fun _ hy => hy.1) hσ),
      Nat.card_image_of_injective Subtype.val_injective]
  have hcardSwap : Nat.card (longInvSwap G Ω α β) = Nat.card {a : BlockInv G Γ //
      blockRes Γ a = blockRes Γ a₀} * Nat.card (longInvSwap ↥Y ↥Γ ⟨α, hα⟩ ⟨β, hβ⟩) := by
    rw [longInvSwap_eq_image_blockRes hG hΓ hα hβ hαβ, Nat.card_image_of_injective hinj,
      card_preimage_eq_mul _ fun σ hσ => hl σ (Set.image_mono (fun _ hy => hy.1) hσ),
      Nat.card_image_of_injective Subtype.val_injective]
  refine ⟨by rw [hcardSwap, hcardAt, hY27.1], fun γ hγ => holtDelta'_eq_orbit_of_subset hγ ?_⟩
  have hβα : (⟨β, hβ⟩ : Γ) ≠ ⟨α, hα⟩ := fun h => hαβ (congrArg Subtype.val h).symm
  have hmem : ∀ δ ∈ holtDelta' G Ω α β, ∃ hδ : δ ∈ Γ,
      (⟨δ, hδ⟩ : Γ) ∈ holtDelta' ↥Y ↥Γ ⟨α, hα⟩ ⟨β, hβ⟩ := by
    rintro _ ⟨s, hs, rfl⟩
    have hsX : s ∈ X := hΓ.stabilizer_le hα hs.2
    refine ⟨by rw [← mem_stabilizer_iff.mp hsX]; exact Set.smul_mem_smul_set hβ,
      ⟨blockRes Γ ⟨s, hs.1, hsX⟩, ⟨s, hsX⟩, rfl⟩, mem_longInvAt_subgroup_iff.mpr
        (inducedHom_mem_longInvAt le_rfl (x := ⟨s, hsX⟩) (α := ⟨α, hα⟩) hs ⟨_, hβα⟩), rfl⟩
  intro δ hδ
  obtain ⟨hγΓ, hγY⟩ := hmem γ hγ
  obtain ⟨hδΓ, hδY⟩ := hmem δ hδ
  rw [hY27.2 _ hγY] at hδY
  obtain ⟨⟨y, hyα, hyβ⟩, hy⟩ := hδY
  obtain ⟨k, -, hk⟩ := mem_inducedPerm.mp y.2
  have hkα : k • α = α := by
    rw [← hk ⟨α, hα⟩]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp hyα)
  have hkβ : k • β = β := by
    rw [← hk ⟨β, hβ⟩]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp hyβ)
  refine ⟨⟨k, Subgroup.mem_inf.mpr ⟨hkα, hkβ⟩⟩, ?_⟩
  show k • γ = δ
  rw [← hk ⟨γ, hγΓ⟩]
  exact congrArg Subtype.val hy

end Case1

section Section

variable {G : Type} [Group G] [Finite G] {Ω : Type}
  [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

omit [Finite G] [FaithfulSMul G Ω] in
private theorem exists_longInv_eq_blockRes {Γ : Set Ω} (hodd : Odd (Nat.card Γ))
    (h3 : 3 ≤ Nat.card Γ) {X : Subgroup G} (hX : X ≤ stabilizer G Γ)
    (hext : ∀ y ∈ longInv G Ω, y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ X ∧ ∀ γ ∈ Γ, c • γ = y • γ) (a : BlockInv G Γ) :
    ∃ y ∈ longInv ↥(inducedPerm X Γ hX) Γ, (y : Equiv.Perm Γ) = blockRes Γ a := by
  obtain ⟨c, hc, hcX, hcγ⟩ := hext a.1 a.2.1 a.2.2
  exact ⟨⟨inducedHom X Γ hX ⟨c, hcX⟩, ⟨c, hcX⟩, rfl⟩, mem_longInv_subgroup_iff.mpr
    (inducedHom_mem_longInv hX hodd h3 (x := ⟨c, hcX⟩) hc),
    Equiv.ext fun γ => Subtype.ext (hcγ γ γ.2)⟩

omit [Finite G] [FaithfulSMul G Ω] in
private theorem card_fibre_blockRes_eq_of_section {Γ : Set Ω} (hodd : Odd (Nat.card Γ))
    (h3 : 3 ≤ Nat.card Γ) {X : Subgroup G} (hX : X ≤ stabilizer G Γ)
    (hY : IsStarGroup ↥(inducedPerm X Γ hX) Γ)
    (hBY : HoltTheorem1Below (Nat.card (inducedPerm X Γ hX)) (Nat.card Γ + 1))
    (hext : ∀ y ∈ longInv G Ω, y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ X ∧ ∀ γ ∈ Γ, c • γ = y • γ) (a₀ a₁ : BlockInv G Γ) :
    Nat.card {a : BlockInv G Γ // blockRes Γ a = blockRes Γ a₀} =
      Nat.card {a : BlockInv G Γ // blockRes Γ a = blockRes Γ a₁} := by
  obtain ⟨y₀, hy₀, hya₀⟩ := exists_longInv_eq_blockRes hodd h3 hX hext a₀
  obtain ⟨y₁, hy₁, hya₁⟩ := exists_longInv_eq_blockRes hodd h3 hX hext a₁
  obtain ⟨w, -, hw⟩ := exists_mem_jHull_conj_eq hY hBY hy₀ hy₁
  obtain ⟨x, hxX, hxw⟩ := mem_inducedPerm.mp w.2
  have hxw' : inducedHom (stabilizer G Γ) Γ le_rfl ⟨x, hX hxX⟩ = (w : Equiv.Perm Γ) :=
    Equiv.ext fun γ => Subtype.ext (hxw γ).symm
  refine card_fibre_blockRes_eq_of_conj (hX hxX) ?_
  rw [hxw', ← hya₀, ← hya₁]
  exact congrArg Subtype.val hw

omit [Finite G] [FaithfulSMul G Ω] in
private theorem longInvAt_inter_eq_image {Γ : Set Ω} (hodd : Odd (Nat.card Γ))
    (h3 : 3 ≤ Nat.card Γ) {X : Subgroup G} (hX : X ≤ stabilizer G Γ)
    (hext : ∀ y ∈ longInv G Ω, y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ X ∧ ∀ γ ∈ Γ, c • γ = y • γ) {α : Ω} (hα : α ∈ Γ) :
    longInvAt G Ω α ∩ (stabilizer G Γ : Set G) = (fun a : BlockInv G Γ => a.1) '' (blockRes Γ ⁻¹'
      (Subtype.val '' longInvAt ↥(inducedPerm X Γ hX) Γ ⟨α, hα⟩)) := by
  ext s
  constructor
  · rintro ⟨hs, hsΓ⟩
    obtain ⟨y, hy, hya⟩ := exists_longInv_eq_blockRes hodd h3 hX hext ⟨s, hs.1, hsΓ⟩
    refine ⟨⟨s, hs.1, hsΓ⟩, ⟨y, ⟨hy, Subtype.ext ?_⟩, hya⟩, rfl⟩
    show ((y : Equiv.Perm Γ) ⟨α, hα⟩ : Ω) = α
    rw [hya]
    exact hs.2
  · rintro ⟨a, ⟨y, hy, hya⟩, rfl⟩
    have h1 : ((y : Equiv.Perm Γ) ⟨α, hα⟩ : Ω) = α := congrArg Subtype.val hy.2
    rw [hya] at h1
    exact ⟨⟨a.2.1, h1⟩, a.2.2⟩

omit [Finite G] [FaithfulSMul G Ω] in
private theorem longInvSwap_inter_eq_image {Γ : Set Ω} (hodd : Odd (Nat.card Γ))
    (h3 : 3 ≤ Nat.card Γ) {X : Subgroup G} (hX : X ≤ stabilizer G Γ)
    (hext : ∀ y ∈ longInv G Ω, y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ X ∧ ∀ γ ∈ Γ, c • γ = y • γ) {α β : Ω} (hα : α ∈ Γ)
    (hβ : β ∈ Γ) :
    longInvSwap G Ω α β ∩ (stabilizer G Γ : Set G) = (fun a : BlockInv G Γ => a.1) ''
      (blockRes Γ ⁻¹' (Subtype.val '' longInvSwap ↥(inducedPerm X Γ hX) Γ ⟨α, hα⟩ ⟨β, hβ⟩)) := by
  ext s
  constructor
  · rintro ⟨hs, hsΓ⟩
    obtain ⟨y, hy, hya⟩ := exists_longInv_eq_blockRes hodd h3 hX hext ⟨s, hs.1, hsΓ⟩
    refine ⟨⟨s, hs.1, hsΓ⟩, ⟨y, ⟨hy, Subtype.ext ?_⟩, hya⟩, rfl⟩
    show ((y : Equiv.Perm Γ) ⟨α, hα⟩ : Ω) = β
    rw [hya]
    exact hs.2
  · rintro ⟨a, ⟨y, hy, hya⟩, rfl⟩
    have h1 : ((y : Equiv.Perm Γ) ⟨α, hα⟩ : Ω) = β := congrArg Subtype.val hy.2
    rw [hya] at h1
    exact ⟨⟨a.2.1, h1⟩, a.2.2⟩

omit [FaithfulSMul G Ω] in
theorem card_longInvSwap_inter_eq_of_section (hG : IsStarGroup G Ω) {Γ : Set Ω}
    (hodd : Odd (Nat.card Γ)) (h3 : 3 ≤ Nat.card Γ) {X : Subgroup G} (hX : X ≤ stabilizer G Γ)
    (hY : IsStarGroup ↥(inducedPerm X Γ hX) Γ)
    (hBY : HoltTheorem1Below (Nat.card (inducedPerm X Γ hX)) (Nat.card Γ + 1))
    (hne : ∃ x ∈ X, x ∈ longInv G Ω)
    (hext : ∀ y ∈ longInv G Ω, y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ X ∧ ∀ γ ∈ Γ, c • γ = y • γ) {α β : Ω} (hα : α ∈ Γ)
    (hβ : β ∈ Γ) (h27 : Lemma27iAt ↥(inducedPerm X Γ hX) Γ ⟨α, hα⟩ ⟨β, hβ⟩) :
    Nat.card ↥(longInvSwap G Ω α β ∩ (stabilizer G Γ : Set G)) =
      Nat.card ↥(longInvAt G Ω α ∩ (stabilizer G Γ : Set G)) := by
  obtain ⟨x₀, hx₀X, hx₀⟩ := hne
  set a₀ : BlockInv G Γ := ⟨x₀, hx₀, hX hx₀X⟩
  have hl : ∀ σ ∈ Subtype.val '' longInv ↥(inducedPerm X Γ hX) Γ,
      Nat.card {a : BlockInv G Γ // blockRes Γ a = σ} =
        Nat.card {a : BlockInv G Γ // blockRes Γ a = blockRes Γ a₀} := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := (mem_longInv_inducedPerm_iff hG hX hY hBY ⟨x₀, hx₀X, hx₀⟩ y).mp hy
    rw [← show blockRes (G := G) Γ ⟨(x : G), hx, hX x.2⟩ = y from hxy]
    exact card_fibre_blockRes_eq_of_section hodd h3 hX hY hBY hext _ _
  have hinj : Function.Injective (fun a : BlockInv G Γ => a.1) := Subtype.val_injective
  rw [longInvSwap_inter_eq_image hodd h3 hX hext hα hβ, longInvAt_inter_eq_image hodd h3 hX hext hα,
    Nat.card_image_of_injective hinj, Nat.card_image_of_injective hinj,
    card_preimage_eq_mul _ fun σ hσ => hl σ (Set.image_mono (fun _ hy => hy.1) hσ),
    card_preimage_eq_mul _ fun σ hσ => hl σ (Set.image_mono (fun _ hy => hy.1) hσ),
    Nat.card_image_of_injective Subtype.val_injective,
    Nat.card_image_of_injective Subtype.val_injective, h27.1]

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_smul_eq_of_section {Γ : Set Ω} (hodd : Odd (Nat.card Γ)) (h3 : 3 ≤ Nat.card Γ)
    {X : Subgroup G} (hX : X ≤ stabilizer G Γ)
    (hext : ∀ y ∈ longInv G Ω, y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ X ∧ ∀ γ ∈ Γ, c • γ = y • γ) {α β : Ω} (hα : α ∈ Γ)
    (hβ : β ∈ Γ) (h27 : Lemma27iAt ↥(inducedPerm X Γ hX) Γ ⟨α, hα⟩ ⟨β, hβ⟩) {s₁ s₂ : G}
    (hs₁ : s₁ ∈ longInvAt G Ω α) (hs₁Γ : s₁ ∈ stabilizer G Γ) (hs₂ : s₂ ∈ longInvAt G Ω α)
    (hs₂Γ : s₂ ∈ stabilizer G Γ) :
    ∃ g ∈ X ⊓ (stabilizer G α ⊓ stabilizer G β), g • s₁ • β = s₂ • β := by
  have hmem : ∀ {s : G}, s ∈ longInvAt G Ω α → (hsΓ : s ∈ stabilizer G Γ) →
      ∃ hsβ : s • β ∈ Γ, (⟨s • β, hsβ⟩ : Γ) ∈ holtDelta' ↥(inducedPerm X Γ hX) Γ ⟨α, hα⟩
        ⟨β, hβ⟩ := by
    intro s hs hsΓ
    obtain ⟨y, hy, hya⟩ := exists_longInv_eq_blockRes hodd h3 hX hext ⟨s, hs.1, hsΓ⟩
    have hsβ : s • β ∈ Γ := by
      rw [← mem_stabilizer_iff.mp hsΓ]
      exact Set.smul_mem_smul_set hβ
    refine ⟨hsβ, y, ⟨hy, Subtype.ext ?_⟩, Subtype.ext ?_⟩
    · show ((y : Equiv.Perm Γ) ⟨α, hα⟩ : Ω) = α
      rw [hya]
      exact hs.2
    · show ((y : Equiv.Perm Γ) ⟨β, hβ⟩ : Ω) = s • β
      rw [hya]
      rfl
  obtain ⟨hβ₁, h₁⟩ := hmem hs₁ hs₁Γ
  obtain ⟨hβ₂, h₂⟩ := hmem hs₂ hs₂Γ
  rw [h27.2 _ h₁] at h₂
  obtain ⟨⟨w, hwα, hwβ⟩, hw⟩ := h₂
  obtain ⟨x, hxX, hxw⟩ := mem_inducedPerm.mp w.2
  have hxα : x • α = α := by
    rw [← hxw ⟨α, hα⟩]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp hwα)
  have hxβ : x • β = β := by
    rw [← hxw ⟨β, hβ⟩]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp hwβ)
  refine ⟨x, Subgroup.mem_inf.mpr ⟨hxX, Subgroup.mem_inf.mpr ⟨hxα, hxβ⟩⟩, ?_⟩
  rw [← hxw ⟨s₁ • β, hβ₁⟩]
  exact congrArg Subtype.val hw

end Section

end CFSG.Holt.H78
