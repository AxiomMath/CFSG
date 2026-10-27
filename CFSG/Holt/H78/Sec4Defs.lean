module

public import CFSG.Holt.H78.Section4Defs
public import CFSG.Holt.H78.Count
public import CFSG.Holt.Induced

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Setting

variable (G : Type*) [Group G] [Finite G] (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

structure Sec4Hyp : Prop where
  star : IsStarGroup G Ω
  preprimitive : IsPreprimitive G Ω
  jHull_eq_top : jHull G Ω = ⊤
  pPrimeCore_eq_bot : CFSG.pPrimeCore 2 G = ⊥
  below : HoltTheorem1Below (Nat.card G) (Nat.card Ω)
  not_conclusion : ¬ HoltPrimitiveConclusion G Ω

end Setting

theorem holtSection4Statement_of_false
    (h : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Hyp G Ω → False) :
    HoltSection4Statement := by
  intro G _ _ Ω _ _ _ _ hG hP hJ hO hB
  by_contra hc
  exact h G Ω ⟨hG, hP, hJ, hO, hB, hc⟩

section TwoPoint

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

abbrev twoPointHom (α β : Ω) :
    stabilizer G ({α, β} : Set Ω) →* Equiv.Perm (holtDelta G Ω α β) :=
  inducedHom _ _ (stabilizer_pair_le α β)

@[expose] def twoPointSection (α β : Ω) : Subgroup (Equiv.Perm (holtDelta G Ω α β)) :=
  inducedPerm (stabilizer G ({α, β} : Set Ω)) (holtDelta G Ω α β) (stabilizer_pair_le α β)

@[expose] def twoPointJ (α β : Ω) : Subgroup (Equiv.Perm (holtDelta G Ω α β)) :=
  inducedPerm (Subgroup.closure (longInvSwap G Ω α β)) (holtDelta G Ω α β)
    (closure_longInvSwap_le_stabilizer α β)

@[expose] def twoPointKernel (α β : Ω) : Subgroup G :=
  stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G (holtDelta G Ω α β)

@[expose] def twoPointNormalizer (α β : Ω) (L : Subgroup (twoPointSection G Ω α β)) :
    Subgroup G :=
  ((Subgroup.normalizer (L : Set (twoPointSection G Ω α β))).comap
    (twoPointHom G Ω α β).rangeRestrict).map (stabilizer G ({α, β} : Set Ω)).subtype

@[expose] def IsTypeL (α : Ω) (v : G) : Prop :=
  ∃ t ∈ longInvAt G Ω α, ∃ u ∈ longInvAt G Ω α, t ≠ u ∧ Commute t u ∧ t * u = v ∧
    v ∉ longInv G Ω

abbrev typeLSection (v : G) : Subgroup (Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) :=
  centralizerImage Ω (Subgroup.zpowers v)

end TwoPoint

section TwoPointAPI

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {α β : Ω}

theorem stabilizer_inf_le_stabilizer_pair (α β : Ω) :
    stabilizer G α ⊓ stabilizer G β ≤ stabilizer G ({α, β} : Set Ω) := fun g hg => by
  obtain ⟨hα, hβ⟩ := Subgroup.mem_inf.mp hg
  rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, mem_stabilizer_iff.mp hα,
    mem_stabilizer_iff.mp hβ]

theorem closure_longInvSwap_le_stabilizer_pair (α β : Ω) :
    Subgroup.closure (longInvSwap G Ω α β) ≤ stabilizer G ({α, β} : Set Ω) :=
  (Subgroup.closure_le _).mpr fun _ ht => by
    rw [SetLike.mem_coe, mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, ht.2,
      smul_eq_of_mem_longInvSwap ht, Set.pair_comm]

theorem coe_twoPointHom_apply (g : stabilizer G ({α, β} : Set Ω)) (δ : holtDelta G Ω α β) :
    ((twoPointHom G Ω α β g δ : holtDelta G Ω α β) : Ω) = (g : G) • (δ : Ω) := rfl

theorem twoPointSection_eq_range :
    twoPointSection G Ω α β = (twoPointHom G Ω α β).range := rfl

theorem twoPointHom_mem_twoPointSection (g : stabilizer G ({α, β} : Set Ω)) :
    twoPointHom G Ω α β g ∈ twoPointSection G Ω α β :=
  ⟨g, rfl⟩

theorem mem_twoPointJ {π : Equiv.Perm (holtDelta G Ω α β)} :
    π ∈ twoPointJ G Ω α β ↔ ∃ g ∈ Subgroup.closure (longInvSwap G Ω α β),
      ∀ δ : holtDelta G Ω α β, (π δ : Ω) = g • (δ : Ω) :=
  mem_inducedPerm

theorem twoPointJ_le_twoPointSection (α β : Ω) :
    twoPointJ G Ω α β ≤ twoPointSection G Ω α β :=
  inducedPerm_mono (closure_longInvSwap_le_stabilizer_pair α β)

@[simp] theorem mem_twoPointKernel {g : G} :
    g ∈ twoPointKernel G Ω α β ↔ g • α = α ∧ g • β = β ∧ ∀ δ ∈ holtDelta G Ω α β, g • δ = δ := by
  simp only [twoPointKernel, Subgroup.mem_inf, mem_stabilizer_iff, mem_fixingSubgroup_iff,
    and_assoc]

theorem twoPointKernel_le_inf : twoPointKernel G Ω α β ≤ stabilizer G α ⊓ stabilizer G β :=
  inf_le_left

theorem twoPointKernel_le_fixingSubgroup :
    twoPointKernel G Ω α β ≤ fixingSubgroup G (holtDelta G Ω α β) :=
  inf_le_right

theorem mem_twoPointNormalizer {L : Subgroup (twoPointSection G Ω α β)} {g : G} :
    g ∈ twoPointNormalizer G Ω α β L ↔ ∃ hg : g ∈ stabilizer G ({α, β} : Set Ω),
      (⟨twoPointHom G Ω α β ⟨g, hg⟩, twoPointHom_mem_twoPointSection _⟩ :
        twoPointSection G Ω α β) ∈ Subgroup.normalizer (L : Set (twoPointSection G Ω α β)) := by
  constructor
  · rintro ⟨⟨g, hg⟩, hN, rfl⟩
    exact ⟨hg, hN⟩
  · rintro ⟨hg, hN⟩
    exact ⟨⟨g, hg⟩, hN, rfl⟩

theorem twoPointNormalizer_le_stabilizer_pair (L : Subgroup (twoPointSection G Ω α β)) :
    twoPointNormalizer G Ω α β L ≤ stabilizer G ({α, β} : Set Ω) :=
  Subgroup.map_subtype_le _

theorem IsTypeL.smul_eq {v : G} (hv : IsTypeL G Ω α v) : v • α = α := by
  obtain ⟨t, ht, u, hu, -, -, rfl, -⟩ := hv
  rw [mul_smul, hu.2, ht.2]

theorem IsTypeL.orderOf_eq_two {v : G} (hv : IsTypeL G Ω α v) : orderOf v = 2 := by
  obtain ⟨t, ht, u, hu, htu, hc, rfl, -⟩ := hv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := ht.1.1 ▸ pow_orderOf_eq_one t
  have hu2 : u ^ 2 = 1 := hu.1.1 ▸ pow_orderOf_eq_one u
  refine orderOf_eq_prime (by rw [hc.mul_pow, ht2, hu2, one_mul]) fun h1 => htu ?_
  rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right (by rwa [← sq])]

end TwoPointAPI

section Card

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem card_twoPointSection_le (α β : Ω) :
    Nat.card (twoPointSection G Ω α β) ≤ Nat.card (stabilizer G ({α, β} : Set Ω)) :=
  card_inducedPerm_le

theorem card_stabilizer_pair_lt [IsPretransitive G Ω] (h3 : 3 ≤ Nat.card Ω) (α β : Ω) :
    Nat.card (stabilizer G ({α, β} : Set Ω)) < Nat.card G := by
  obtain ⟨γ, hγα, hγβ⟩ : ∃ γ : Ω, γ ≠ α ∧ γ ≠ β := by
    by_contra! h
    have hsub : (Set.univ : Set Ω) ⊆ {α, β} := fun γ _ =>
      (em (γ = α)).elim Or.inl fun hγ => Or.inr (h γ hγ)
    have := (Set.ncard_le_ncard hsub).trans (Set.ncard_insert_le α {β})
    rw [Set.ncard_univ, Set.ncard_singleton] at this
    omega
  obtain ⟨g, hg⟩ := exists_smul_eq G α γ
  refine (Subgroup.card_le_card_group _).lt_of_ne fun h => ?_
  have hg' : g • ({α, β} : Set Ω) = {α, β} := by
    rw [← mem_stabilizer_iff, Subgroup.eq_top_of_card_eq _ h]
    exact Subgroup.mem_top g
  have hγ : γ ∈ ({α, β} : Set Ω) := hg ▸ hg' ▸ Set.smul_mem_smul_set (Set.mem_insert α _)
  rcases hγ with h1 | h1
  exacts [hγα h1, hγβ h1]

theorem card_twoPoint_lt [IsPretransitive G Ω] (h3 : 3 ≤ Nat.card Ω) (α β : Ω) :
    Nat.card (twoPointSection G Ω α β) < Nat.card G :=
  (card_twoPointSection_le α β).trans_lt (card_stabilizer_pair_lt h3 α β)

theorem IsStarGroup.card_twoPoint_lt (hG : IsStarGroup G Ω) (α β : Ω) :
    Nat.card (twoPointSection G Ω α β) < Nat.card G :=
  have := hG.isPretransitive
  CFSG.Holt.H78.card_twoPoint_lt hG.three_le_card α β

end Card

section Kernel

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {α β γ : Ω}

theorem twoPointKernel_le_of_mem (hγ : γ ∈ holtDelta G Ω α β) :
    twoPointKernel G Ω α β ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ := fun _ hg =>
  Subgroup.mem_inf.mpr ⟨twoPointKernel_le_inf hg,
    mem_stabilizer_iff.mpr ((mem_fixingSubgroup_iff G).mp (twoPointKernel_le_fixingSubgroup hg)
      γ hγ)⟩

theorem conj_mem_twoPointKernel {g k : G} (hg : g ∈ stabilizer G α ⊓ stabilizer G β)
    (hk : k ∈ twoPointKernel G Ω α β) : g * k * g⁻¹ ∈ twoPointKernel G Ω α β := by
  have hgΔ := stabilizer_pair_le α β (stabilizer_inf_le_stabilizer_pair α β hg)
  obtain ⟨hgα, hgβ⟩ := Subgroup.mem_inf.mp hg
  rw [mem_stabilizer_iff] at hgα hgβ
  obtain ⟨hkα, hkβ, hkΔ⟩ := mem_twoPointKernel.mp hk
  refine mem_twoPointKernel.mpr ⟨?_, ?_, fun δ hδ => ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hgα.symm, hkα, hgα]
  · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hgβ.symm, hkβ, hgβ]
  · have hδ' : g⁻¹ • δ ∈ holtDelta G Ω α β := by
      rw [← mem_stabilizer_iff.mp (inv_mem hgΔ)]
      exact Set.smul_mem_smul_set hδ
    rw [mul_smul, mul_smul, hkΔ _ hδ', smul_inv_smul]

theorem normal_twoPointKernel_subgroupOf (hγ : γ ∈ holtDelta G Ω α β) :
    ((twoPointKernel G Ω α β).subgroupOf
      (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)).Normal :=
  (Subgroup.normal_subgroupOf_iff (twoPointKernel_le_of_mem hγ)).mpr fun _ _ hk hg =>
    conj_mem_twoPointKernel (Subgroup.mem_inf.mp hg).1 hk

variable [Finite G]

private theorem fusionIsSylowIn_inf_of_normal_aux {S H N : Subgroup G}
    (hS : fusionIsSylowIn 2 S H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    fusionIsSylowIn 2 (S ⊓ N) N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNH)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    have := hN.conj_mem ⟨x, hNH (hPN hx)⟩ (Subgroup.mem_subgroupOf.mpr (hPN hx))
      ⟨k⁻¹, inv_mem hk⟩
    simpa [Subgroup.mem_subgroupOf] using this⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

private theorem eq_bot_iff_odd_of_fusionIsSylowIn {T K : Subgroup G}
    (hT : fusionIsSylowIn 2 T K) : T = ⊥ ↔ Odd (Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro rfl
    by_contra hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    have hP : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
    have h1 := hT.2.2 _ (Subgroup.zpowers_le.mpr x.2) hP bot_le
    have hx1 : (x : G) = 1 := by
      rw [← Subgroup.mem_bot, ← h1]
      exact Subgroup.mem_zpowers _
    rw [← Subgroup.orderOf_coe, hx1, orderOf_one] at hx
    omega
  · intro hodd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT.2.1
    have h2 : Odd (2 ^ n) := hodd.of_dvd_nat (hn ▸ Subgroup.card_dvd_of_le hT.1)
    have hn0 : n = 0 := by
      by_contra h0
      exact Nat.not_even_iff_odd.mpr h2 (Nat.even_pow.mpr ⟨even_two, h0⟩)
    rw [← Subgroup.card_eq_one, hn, hn0, pow_zero]

theorem fusionIsSylowIn_inf_twoPointKernel {α β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β)
    {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)) :
    fusionIsSylowIn 2 (S ⊓ twoPointKernel G Ω α β) (twoPointKernel G Ω α β) :=
  fusionIsSylowIn_inf_of_normal_aux hS (twoPointKernel_le_of_mem hγ)
    (normal_twoPointKernel_subgroupOf hγ)

theorem inf_twoPointKernel_eq_bot_iff {α β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β)
    {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)) :
    S ⊓ twoPointKernel G Ω α β = ⊥ ↔ Odd (Nat.card (twoPointKernel G Ω α β)) :=
  eq_bot_iff_odd_of_fusionIsSylowIn (fusionIsSylowIn_inf_twoPointKernel hγ hS)

end Kernel

section Config

variable (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

structure AltConfig (α β : Ω) where
  D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)
  oddCore_eq_bot : jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥
  i₁ : D.ι
  alt : ∀ i, factorImage _ _ (D.L i) (D.ρ i) = alternatingGroup (D.Ψc i)
  mod4 : ∀ i, i ≠ i₁ → Fintype.card (D.Ψc i) % 4 = 1
  γ : holtDelta G Ω α β
  S : Subgroup G
  sylow : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (γ : Ω))
  w : G
  w_mem : w ∈ longInvSwap G Ω α β
  w_fix : w • (γ : Ω) = γ
  w_comm : w ∈ Subgroup.centralizer (S : Set G)
  fix_three : Nat.card (fixSet Ω (S ⊓ twoPointNormalizer G Ω α β (D.L i₁))) = 3
  fix_five : Fintype.card (D.Ψc i₁) % 4 = 3 → ∃ W : Subgroup G,
    W ≤ S ⊓ twoPointNormalizer G Ω α β (D.L i₁) ∧ Nat.card (fixSet Ω W) = 5 ∧
      fixSet Ω W ⊆ {α, β} ∪ ((↑) '' {δ : holtDelta G Ω α β | ∀ i ≠ i₁, D.coord δ i = D.coord γ i})
  five : Fintype.card D.ι = 1 → Fintype.card (D.Ψc i₁) = 5 →
    ¬ Odd (Nat.card (twoPointKernel G Ω α β))

end Config

section Interface

variable (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

structure Sec4Setting : Prop extends Sec4Hyp G Ω where
  known_inducedPerm : ∀ {X : Subgroup G} {Δ : Set Ω} (hX : X ≤ stabilizer G Δ),
    Nat.card (inducedPerm X Δ hX) < Nat.card G → IsStarGroup (inducedPerm X Δ hX) Δ →
      HoltTheorem1Below (Nat.card (inducedPerm X Δ hX)) (Nat.card Δ + 1)
  star_centralizerImage : ∀ {P : Subgroup G}, IsPGroup 2 P → 3 ≤ Nat.card (fixSet Ω P) →
    IsStarGroup (centralizerImage Ω P) (fixSet Ω P)
  star_twoPoint : ∀ {α β : Ω}, α ≠ β → 3 ≤ Nat.card (holtDelta G Ω α β) →
    IsStarGroup (twoPointSection G Ω α β) (holtDelta G Ω α β)
  card_twoPoint_lt : ∀ α β : Ω, α ≠ β → Nat.card (twoPointSection G Ω α β) < Nat.card G
  longInv_inducedPerm : ∀ {X : Subgroup G} {Δ : Set Ω} (hX : X ≤ stabilizer G Δ),
    Nat.card (inducedPerm X Δ hX) < Nat.card G → IsStarGroup (inducedPerm X Δ hX) Δ →
      (∃ x ∈ X, x ∈ longInv G Ω) → ∀ y : inducedPerm X Δ hX,
        y ∈ longInv (inducedPerm X Δ hX) Δ ↔
          ∃ x : X, (x : G) ∈ longInv G Ω ∧ inducedHom X Δ hX x = (y : Equiv.Perm Δ)
  frattini : ∀ {Γ : Set Ω}, 3 ≤ Nat.card Γ → ∀ {V : Subgroup G}, IsPGroup 2 V →
    V ≤ fixingSubgroup G Γ → ∀ {y : G}, y ∈ longInv G Ω → y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ Subgroup.centralizer (V : Set G) ∧ ∀ γ ∈ Γ, c • γ = y • γ
  sylow_twoPoint : ∀ {α β γ : Ω}, α ≠ β → γ ∈ holtDelta G Ω α β → ∀ {T : Subgroup G},
    fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ) →
      fusionIsSylowIn 2 T (stabilizer G α ⊓ stabilizer G β) ∧
        ∃ u ∈ longInvSwap G Ω α β, u • γ = γ ∧ u ∈ Subgroup.centralizer (T : Set G)
  odd_fixingSubgroup_orbit : ∀ {α : Ω} {Γ : Set Ω},
    (∃ β ∈ Γ, β ≠ α ∧ Γ = orbit (stabilizer G α) β) →
      Odd (Nat.card ↥(stabilizer G α ⊓ fixingSubgroup G Γ))
  holtDelta'_eq_orbit : ∀ {α β γ : Ω}, α ≠ β → γ ∈ holtDelta' G Ω α β →
    holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ
  centralizer_twoPoint : ∀ {α β : Ω}, α ≠ β → ∀ {S : Subgroup G},
    fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β) →
      ∃ u ∈ longInvAt G Ω α, u ∈ Subgroup.centralizer (S : Set G)
  card_longInvSwap_typeL : ∀ {v : G}, orderOf v = 2 →
    ∀ (D : HoltData ↥(typeLSection G Ω v) ↥(fixSet Ω (Subgroup.zpowers v))),
      jOddCore ↥(typeLSection G Ω v) ↥(fixSet Ω (Subgroup.zpowers v)) = ⊥ →
        ∀ {i : D.ι} {a b : fixSet Ω (Subgroup.zpowers v)},
          (∀ j, j ≠ i → D.coord b j = D.coord a j) →
            Nat.card (longInvSwap G Ω a b) = Nat.card (longInvAt G Ω a)
  exists_one_lt_card_holtDelta : ∀ {α : Ω} {v : G}, orderOf v = 2 → v • α = α →
    ∀ {P : Subgroup (typeLSection G Ω v)}, P.Normal → Odd (Nat.card P) → P ≠ ⊥ →
      ∃ β : Ω, β ≠ α ∧ (∃ p ∈ P, ∃ a : fixSet Ω (Subgroup.zpowers v), (a : Ω) = α ∧
        ((p • a : _) : Ω) = β) ∧ 1 < Nat.card (holtDelta G Ω α β)

end Interface

end CFSG.Holt.H78
