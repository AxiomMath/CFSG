module

public import CFSG.Holt.H78.OddCore
public import CFSG.Holt.H78.SectionsStar
public import CFSG.Holt.General.OddOrbits
public import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section CentralKernel

variable {A : Type*} [Group A] [Finite A]

private theorem not_two_dvd_card_pPrimeCore : ¬ 2 ∣ Nat.card (CFSG.pPrimeCore 2 A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp CFSG.pPrimeCore_coprime_card

private theorem pPrimeCore_quotient_eq_bot' :
    CFSG.pPrimeCore 2 (A ⧸ CFSG.pPrimeCore 2 A) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (CFSG.pPrimeCore 2 A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact not_two_dvd_card_pPrimeCore
  have h := (CFSG.prime_complement_kernel_core_preimage (QuotientGroup.mk' (CFSG.pPrimeCore 2 A))
    (QuotientGroup.mk'_surjective _) hk).2
  rw [← h, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem exists_pow_two_pow_mem_pPrimeCore {K : Subgroup A}
    (hc : ∀ k ∈ K, ∀ a : A, k * a * k⁻¹ * a⁻¹ ∈ CFSG.pPrimeCore 2 A) {k : A} (hk : k ∈ K) :
    ∃ n : ℕ, k ^ 2 ^ n ∈ CFSG.pPrimeCore 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 A
  obtain ⟨n, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  refine ⟨n, ?_⟩
  set y := k ^ 2 ^ n with hy_def
  have hyK : y ∈ K := K.pow_mem hk _
  have hy : orderOf y = m := by
    rw [hy_def, orderOf_pow_of_dvd (by positivity) (hkm ▸ dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  set q := QuotientGroup.mk' O
  have hcen : Subgroup.zpowers (q y) ≤ Subgroup.center (A ⧸ O) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro b
    induction b using QuotientGroup.induction_on with
    | H a =>
      have h1 := hc y⁻¹ (K.inv_mem hyK) a⁻¹
      rw [inv_inv, inv_inv] at h1
      change ((a : A ⧸ O) * (y : A ⧸ O)) = (y : A ⧸ O) * (a : A ⧸ O)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using h1
  have hodd : Nat.Coprime 2 (Nat.card (Subgroup.zpowers (q y))) := by
    rw [Nat.card_zpowers, Nat.coprime_two_left]
    exact Odd.of_dvd_nat hm (hy ▸ orderOf_map_dvd q y)
  have hle : Subgroup.zpowers (q y) ≤ CFSG.pPrimeCore 2 (A ⧸ O) :=
    le_sSup ⟨Subgroup.normal_of_le_center hcen, hodd⟩
  have hqy : q y = 1 := by
    have h1 := hle (Subgroup.mem_zpowers (q y))
    rwa [pPrimeCore_quotient_eq_bot', Subgroup.mem_bot] at h1
  rwa [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]

theorem pPrimeCore_eq_bot_of_ker {B : Type*} [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hO : CFSG.pPrimeCore 2 A ≤ f.ker)
    (hc : ∀ k ∈ f.ker, ∀ a : A, k * a * k⁻¹ * a⁻¹ ∈ CFSG.pPrimeCore 2 A) :
    CFSG.pPrimeCore 2 B = ⊥ := by
  have : Finite B := Finite.of_surjective f hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 A
  set fb := QuotientGroup.lift O f hO
  have hfb : Function.Surjective fb := fun b => by
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, QuotientGroup.lift_mk _ _ _⟩
  have hker : fb.ker = f.ker.map (QuotientGroup.mk' O) := QuotientGroup.ker_lift O f hO
  have hcen : fb.ker ≤ Subgroup.center (A ⧸ O) := by
    rw [hker]
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro b
    induction b using QuotientGroup.induction_on with
    | H a =>
      have h1 := hc k⁻¹ (f.ker.inv_mem hk) a⁻¹
      rw [inv_inv, inv_inv] at h1
      change ((a : A ⧸ O) * (k : A ⧸ O)) = (k : A ⧸ O) * (a : A ⧸ O)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using h1
  have hp : IsPGroup 2 fb.ker := by
    rintro ⟨x, hx⟩
    rw [hker] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨n, hn⟩ := exists_pow_two_pow_mem_pPrimeCore hc hk
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk']
    exact hn
  rw [CFSG.central_p_kernel_prime_core_image fb hfb hcen hp, pPrimeCore_quotient_eq_bot',
    Subgroup.map_bot]

end CentralKernel

section Blocks

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem eq_one_of_pow_two_pow_eq_one_of_mem {P : Subgroup G} (hP : Odd (Nat.card P)) {x : G}
    (hx : x ∈ P) {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxn
  have h2 : orderOf x ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hx
  have hcop : Nat.Coprime (2 ^ n) (Nat.card P) := Nat.Coprime.pow_left n
    (Nat.coprime_two_left.mpr hP)
  have h3 := Nat.dvd_gcd h1 h2
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem mem_oddOrbitsStabilizer_iff {α : Ω} {x : G} :
    x ∈ oddOrbitsStabilizer G α ↔ x • α ∈ orbit (CFSG.pPrimeCore 2 G) α := by
  have := CFSG.pPrimeCore_normal (p := 2) (G := G)
  rw [oddOrbitsStabilizer, sup_comm, Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨n, hn, s, hs, rfl⟩
    rw [mul_smul, mem_stabilizer_iff.mp hs]
    exact ⟨⟨n, hn⟩, rfl⟩
  · rintro ⟨⟨n, hn⟩, hnx⟩
    change n • α = x • α at hnx
    refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
    rw [mem_stabilizer_iff, mul_smul, ← hnx, inv_smul_smul]

theorem orbit_oddOrbitsStabilizer (α : Ω) :
    orbit (oddOrbitsStabilizer G α) α = orbit (CFSG.pPrimeCore 2 G) α := by
  ext ω
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact mem_oddOrbitsStabilizer_iff.mp hx
  · rintro ⟨⟨n, hn⟩, rfl⟩
    exact ⟨⟨n, (le_sup_right : CFSG.pPrimeCore 2 G ≤ oddOrbitsStabilizer G α) hn⟩, rfl⟩

theorem blockCoset_eq_blockCoset_iff [IsPretransitive G Ω] {α ω ω' : Ω} :
    blockCoset α (oddOrbitsStabilizer G α) ω = blockCoset α (oddOrbitsStabilizer G α) ω' ↔
      ω' ∈ orbit (CFSG.pPrimeCore 2 G) ω := by
  have := CFSG.pPrimeCore_normal (p := 2) (G := G)
  have hK : stabilizer G α ≤ oddOrbitsStabilizer G α := le_sup_left
  obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
  obtain ⟨g', rfl⟩ := exists_smul_eq G α ω'
  rw [blockCoset_smul_self hK, blockCoset_smul_self hK, QuotientGroup.eq,
    mem_oddOrbitsStabilizer_iff, ← smul_orbit_eq_orbit_smul, Set.mem_smul_set_iff_inv_smul_mem,
    mul_smul]

theorem mem_oddOrbitsKernel_iff [IsPretransitive G Ω] {α : Ω} {g : G} :
    g ∈ oddOrbitsKernel G α ↔ ∀ ω : Ω, g • ω ∈ orbit (CFSG.pPrimeCore 2 G) ω := by
  have hK : stabilizer G α ≤ oddOrbitsStabilizer G α := le_sup_left
  rw [MonoidHom.mem_ker]
  constructor
  · intro h ω
    have h1 : g • blockCoset α (oddOrbitsStabilizer G α) ω =
        blockCoset α (oddOrbitsStabilizer G α) ω := by
      simpa using congrArg (fun π : Equiv.Perm (OddOrbits G α) =>
        π (blockCoset α (oddOrbitsStabilizer G α) ω)) h
    rw [← blockCoset_smul hK] at h1
    exact blockCoset_eq_blockCoset_iff.mp h1.symm
  · intro h
    refine Equiv.ext fun c => ?_
    obtain ⟨ω, rfl⟩ := blockCoset_surjective hK c
    simp only [toPermHom_apply, toPerm_apply, Equiv.Perm.one_apply]
    rw [← blockCoset_smul hK]
    exact (blockCoset_eq_blockCoset_iff.mpr (h ω)).symm

theorem oddOrbitsKernel_eq [IsPretransitive G Ω] (α β : Ω) :
    oddOrbitsKernel G α = oddOrbitsKernel G β := by
  ext g
  rw [mem_oddOrbitsKernel_iff, mem_oddOrbitsKernel_iff]

theorem mem_stabilizer_orbit_of_mem_oddOrbitsKernel [IsPretransitive G Ω] {α β : Ω} {g : G}
    (hg : g ∈ oddOrbitsKernel G α) : g ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β) := by
  have := CFSG.pPrimeCore_normal (p := 2) (G := G)
  rw [mem_stabilizer_iff, smul_orbit_eq_orbit_smul, orbit_eq_iff]
  exact mem_oddOrbitsKernel_iff.mp hg β

theorem mem_stabilizer_orbit_of_mem_longInvAt {β : Ω} {u : G} (hu : u ∈ longInvAt G Ω β) :
    u ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β) := by
  have := CFSG.pPrimeCore_normal (p := 2) (G := G)
  rw [mem_stabilizer_iff, smul_orbit_eq_orbit_smul, hu.2]

variable [Finite G]

theorem fixingSubgroup_inf_oddOrbitsKernel_le [Finite Ω] [FaithfulSMul G Ω]
    (hG : IsStarGroup G Ω) (α β : Ω) :
    fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) β) ⊓ oddOrbitsKernel G α ≤
      CFSG.pPrimeCore 2 G := by
  have := hG.isPretransitive
  have h := fixingSubgroup_inf_kernel_le_pPrimeCore hG
    (le_sup_left : stabilizer G β ≤ oddOrbitsStabilizer G β)
  rwa [orbit_oddOrbitsStabilizer, ← oddOrbitsKernel_eq_normalCore, oddOrbitsKernel_eq β α] at h

theorem odd_card_orbit_pPrimeCore (β : Ω) : Odd (Nat.card (orbit (CFSG.pPrimeCore 2 G) β)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_coe_set_eq, ← index_stabilizer]
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
    (Subgroup.index_dvd_card _)

omit [Finite G] in
theorem card_orbit_pPrimeCore_eq [IsPretransitive G Ω] (β γ : Ω) :
    Nat.card (orbit (CFSG.pPrimeCore 2 G) β) = Nat.card (orbit (CFSG.pPrimeCore 2 G) γ) := by
  have := CFSG.pPrimeCore_normal (p := 2) (G := G)
  obtain ⟨g, rfl⟩ := exists_smul_eq G β γ
  rw [← smul_orbit_eq_orbit_smul, ← Set.image_smul,
    Nat.card_image_of_injective (MulAction.injective g)]

theorem three_le_card_orbit_pPrimeCore [FaithfulSMul G Ω] [IsPretransitive G Ω]
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (β : Ω) : 3 ≤ Nat.card (orbit (CFSG.pPrimeCore 2 G) β) := by
  by_contra h3
  have h1 : ∀ γ : Ω, Nat.card (orbit (CFSG.pPrimeCore 2 G) γ) = 1 := fun γ => by
    have h := odd_card_orbit_pPrimeCore (G := G) γ
    rw [card_orbit_pPrimeCore_eq γ β] at h ⊢
    obtain ⟨m, hm⟩ := h
    omega
  refine hO ((Subgroup.eq_bot_iff_forall _).mpr fun n hn => eq_of_smul_eq_smul (α := Ω) fun ω => ?_)
  have hs := (Nat.card_eq_one_iff_unique.mp (h1 ω)).1
  have := congrArg Subtype.val (hs.elim ⟨n • ω, ⟨⟨n, hn⟩, rfl⟩⟩ ⟨ω, mem_orbit_self ω⟩)
  rw [one_smul]
  exact this

end Blocks

section BlockGroup

variable {G : Type*} [Group G] {Ω : Type} [MulAction G Ω]

variable (G) in
abbrev blockGroup (β : Ω) : Subgroup (Equiv.Perm (orbit (CFSG.pPrimeCore 2 G) β)) :=
  inducedPerm (stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) (orbit (CFSG.pPrimeCore 2 G) β) le_rfl

variable (G) in
abbrev blockRestrict (β : Ω) : stabilizer G (orbit (CFSG.pPrimeCore 2 G) β) →* blockGroup G β :=
  (inducedHom (stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) (orbit (CFSG.pPrimeCore 2 G) β)
    le_rfl).rangeRestrict

theorem blockRestrict_eq_one_iff {β : Ω} {g : stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)} :
    blockRestrict G β g = 1 ↔ (g : G) ∈ fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) β) := by
  rw [← inducedHom_eq_one_iff, Subtype.ext_iff]
  rfl

variable [Finite G]

theorem blockRestrict_mem_pPrimeCore {β : Ω} {n : G} (hn : n ∈ CFSG.pPrimeCore 2 G) :
    blockRestrict G β ⟨n, le_stabilizer_orbit _ β hn⟩ ∈ CFSG.pPrimeCore 2 (blockGroup G β) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := CFSG.pPrimeCore_normal (p := 2) (G := G)
  set E := stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)
  set NZ := ((CFSG.pPrimeCore 2 G).subgroupOf E).map (blockRestrict G β)
  have hnorm : NZ.Normal :=
    (hN.subgroupOf E).map _ (MonoidHom.rangeRestrict_surjective _)
  have hcop : Nat.Coprime 2 (Nat.card NZ) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) ?_
    rw [← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      CFSG.pPrimeCore_coprime_card
  have hle : NZ ≤ CFSG.pPrimeCore 2 (blockGroup G β) := le_sSup ⟨hnorm, hcop⟩
  exact hle ⟨⟨n, le_stabilizer_orbit _ β hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩

theorem isPretransitive_pPrimeCore_blockGroup (β : Ω) :
    IsPretransitive (CFSG.pPrimeCore 2 (blockGroup G β)) (orbit (CFSG.pPrimeCore 2 G) β) := by
  refine ⟨fun δ δ' => ?_⟩
  obtain ⟨⟨n₁, hn₁⟩, h₁⟩ := δ.2
  obtain ⟨⟨n₂, hn₂⟩, h₂⟩ := δ'.2
  have hn : n₂ * n₁⁻¹ ∈ CFSG.pPrimeCore 2 G := mul_mem hn₂ (inv_mem hn₁)
  refine ⟨⟨_, blockRestrict_mem_pPrimeCore hn⟩, Subtype.ext ?_⟩
  change (n₂ * n₁⁻¹) • (δ : Ω) = δ'
  rw [← h₁, ← h₂, mul_smul]
  change n₂ • n₁⁻¹ • n₁ • β = n₂ • β
  rw [inv_smul_smul]

variable [Finite Ω]

theorem blockRestrict_mem_longInv [FaithfulSMul G Ω] [IsPretransitive G Ω]
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) {β : Ω} {u : G} (hu : u ∈ longInv G Ω)
    (huB : u ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) :
    blockRestrict G β ⟨u, huB⟩ ∈ longInv (blockGroup G β) (orbit (CFSG.pPrimeCore 2 G) β) :=
  mem_longInv_inducedPerm_of_eq (odd_card_orbit_pPrimeCore β)
    (three_le_card_orbit_pPrimeCore hO β) (x := ⟨u, huB⟩) hu rfl

theorem mul_mem_pPrimeCore_blockGroup [FaithfulSMul G Ω] [IsPretransitive G Ω]
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) {β : Ω} {u v : G} (hu : u ∈ longInv G Ω)
    (hv : v ∈ longInv G Ω) (huB : u ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β))
    (hvB : v ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) :
    blockRestrict G β ⟨u, huB⟩ * blockRestrict G β ⟨v, hvB⟩ ∈
      CFSG.pPrimeCore 2 (blockGroup G β) :=
  mul_mem_pPrimeCore_of_isPretransitive (isPretransitive_pPrimeCore_blockGroup β)
    (blockRestrict_mem_longInv hO hu huB) (blockRestrict_mem_longInv hO hv hvB)

end BlockGroup

section BlockEven

variable {G : Type*} [Group G] {Ω : Type} [MulAction G Ω]

variable (G) in
@[expose] def blockEven (β : Ω) : Subgroup G :=
  ((CFSG.pPrimeCore 2 (blockGroup G β)).comap (blockRestrict G β)).map
    (stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)).subtype

theorem mem_blockEven {β : Ω} {g : G} :
    g ∈ blockEven G β ↔ ∃ hg : g ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β),
      blockRestrict G β ⟨g, hg⟩ ∈ CFSG.pPrimeCore 2 (blockGroup G β) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem blockEven_le_stabilizer (β : Ω) :
    blockEven G β ≤ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β) := fun _ hg =>
  (mem_blockEven.mp hg).1

theorem conj_mem_blockEven {β : Ω} {h g : G}
    (hh : h ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) (hg : g ∈ blockEven G β) :
    h * g * h⁻¹ ∈ blockEven G β := by
  obtain ⟨hgB, hgO⟩ := mem_blockEven.mp hg
  refine mem_blockEven.mpr ⟨mul_mem (mul_mem hh hgB) (inv_mem hh), ?_⟩
  have e : (⟨h * g * h⁻¹, mul_mem (mul_mem hh hgB) (inv_mem hh)⟩ :
      stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) = ⟨h, hh⟩ * ⟨g, hgB⟩ * ⟨h, hh⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact CFSG.pPrimeCore_normal.conj_mem _ hgO _

variable [Finite G]

theorem pPrimeCore_le_blockEven (β : Ω) : CFSG.pPrimeCore 2 G ≤ blockEven G β := fun _ hn =>
  mem_blockEven.mpr ⟨_, blockRestrict_mem_pPrimeCore hn⟩

variable [Finite Ω]

omit [Finite G] in
theorem mem_fixingSubgroup_of_mem_blockEven {β : Ω} {g : G} (hg : g ∈ blockEven G β) {n : ℕ}
    (hgn : g ^ 2 ^ n = 1) : g ∈ fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) β) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hgB, hgO⟩ := mem_blockEven.mp hg
  have hpow : (⟨g, hgB⟩ : stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) ^ 2 ^ n = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hgn)
  have h1 : blockRestrict G β ⟨g, hgB⟩ = 1 :=
    eq_one_of_pow_two_pow_eq_one_of_mem (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
      hgO (n := n) (by rw [← map_pow, hpow, map_one])
  exact blockRestrict_eq_one_iff.mp h1

theorem mul_mem_blockEven [FaithfulSMul G Ω] [IsPretransitive G Ω]
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) {β : Ω} {u v : G} (hu : u ∈ longInv G Ω)
    (hv : v ∈ longInv G Ω) (huB : u ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β))
    (hvB : v ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) : u * v ∈ blockEven G β := by
  refine mem_blockEven.mpr ⟨mul_mem huB hvB, ?_⟩
  have e : (⟨u * v, mul_mem huB hvB⟩ : stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) =
      ⟨u, huB⟩ * ⟨v, hvB⟩ := rfl
  rw [e, map_mul]
  exact mul_mem_pPrimeCore_blockGroup hO hu hv huB hvB

end BlockEven

section Central

variable {G : Type*} [Group G] [Finite G]

theorem le_pPrimeCore_of_normal_subgroupOf {K P : Subgroup G} [K.Normal] (hPK : P ≤ K)
    (hP : (P.subgroupOf K).Normal) (hodd : Odd (Nat.card P)) : P ≤ CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (P.subgroupOf K)) := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hPK, Nat.coprime_two_left]
    exact hodd
  have hle : P.subgroupOf K ≤ CFSG.pPrimeCore 2 K := le_sSup ⟨hP, hcop⟩
  have hMO : P ≤ oddCoreOf K := by
    have h := Subgroup.map_mono (f := K.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPK] at h
  refine hMO.trans (le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, ?_⟩)
  rw [oddCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

variable {Ω : Type} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

theorem blockEven_inf_oddOrbitsKernel_le (hG : IsStarGroup G Ω) (α β : Ω) :
    blockEven G β ⊓ oddOrbitsKernel G α ≤ CFSG.pPrimeCore 2 G := by
  have := hG.isPretransitive
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oddOrbitsKernel G α
  set P := blockEven G β ⊓ K
  have hodd : Odd (Nat.card P) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2
    rw [Subgroup.orderOf_mk] at hx2
    have hxx : x ^ 2 ^ 1 = 1 := by rw [pow_one, ← hx2, pow_orderOf_eq_one]
    have hxN := fixingSubgroup_inf_oddOrbitsKernel_le hG α β
      ⟨mem_fixingSubgroup_of_mem_blockEven hx.1 hxx, hx.2⟩
    have h1 := eq_one_of_pow_two_pow_eq_one_of_mem
      (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) hxN hxx
    rw [h1, orderOf_one] at hx2
    omega
  have hnorm : (P.subgroupOf K).Normal := ⟨fun x hx k' => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨conj_mem_blockEven (mem_stabilizer_orbit_of_mem_oddOrbitsKernel k'.2) hx.1,
      (inferInstance : K.Normal).conj_mem _ hx.2 _⟩⟩
  exact le_pPrimeCore_of_normal_subgroupOf inf_le_right hnorm hodd

theorem commutator_mem_pPrimeCore_of_mem_longInv (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (α : Ω) {k u : G} (hk : k ∈ oddOrbitsKernel G α)
    (hu : u ∈ longInv G Ω) : k * u * k⁻¹ * u⁻¹ ∈ CFSG.pPrimeCore 2 G := by
  have := hG.isPretransitive
  obtain ⟨β, hβ⟩ := exists_mem_longInvAt hu
  set K := oddOrbitsKernel G α
  have huB := mem_stabilizer_orbit_of_mem_longInvAt hβ
  have hkB := mem_stabilizer_orbit_of_mem_oddOrbitsKernel (β := β) hk
  refine blockEven_inf_oddOrbitsKernel_le hG α β (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [inv_eq_self_of_mem_longInv hu]
    exact mul_mem_blockEven hO (conj_mem_longInv hu k) hu
      (mul_mem (mul_mem hkB huB) (inv_mem hkB)) huB
  · have h1 : u * k⁻¹ * u⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ (inv_mem hk) u
    have e : k * u * k⁻¹ * u⁻¹ = k * (u * k⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem hk h1

theorem commutator_mem_pPrimeCore (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (α : Ω) {k h : G} (hk : k ∈ oddOrbitsKernel G α) (hh : h ∈ jHull G Ω) :
    k * h * k⁻¹ * h⁻¹ ∈ CFSG.pPrimeCore 2 G := by
  have hN := CFSG.pPrimeCore_normal (p := 2) (G := G)
  have hh' : h ∈ Subgroup.closure (longInv G Ω) := hh
  clear hh
  induction hh' using Subgroup.closure_induction with
  | mem u hu => exact commutator_mem_pPrimeCore_of_mem_longInv hG hO α hk hu
  | one => simp
  | mul x y _ _ hx hy =>
    have e : k * (x * y) * k⁻¹ * (x * y)⁻¹ =
        (k * x * k⁻¹ * x⁻¹) * (x * (k * y * k⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact mul_mem hx (hN.conj_mem _ hy x)
  | inv x _ hx =>
    have e : k * x⁻¹ * k⁻¹ * x⁻¹⁻¹ = x⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact hN.conj_mem _ (inv_mem hx) x⁻¹

theorem commutator_mem_jOddCore (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (α : Ω)
    {k h : G} (hk : k ∈ jHull G Ω ⊓ oddOrbitsKernel G α) (hh : h ∈ jHull G Ω) :
    k * h * k⁻¹ * h⁻¹ ∈ jOddCore G Ω := by
  rw [jOddCore_eq_jHull_inf_pPrimeCore]
  have hkH := (Subgroup.mem_inf.mp hk).1
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hkH hh) (inv_mem hkH)) (inv_mem hh),
    commutator_mem_pPrimeCore hG hO α (Subgroup.mem_inf.mp hk).2 hh⟩

theorem exists_pow_two_pow_mem_jOddCore (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (α : Ω) {k : G} (hk : k ∈ jHull G Ω ⊓ oddOrbitsKernel G α) :
    ∃ n : ℕ, k ^ 2 ^ n ∈ jOddCore G Ω := by
  obtain ⟨n, hn⟩ := exists_pow_two_pow_mem_pPrimeCore (A := jHull G Ω)
    (K := (oddOrbitsKernel G α).subgroupOf (jHull G Ω)) (fun k hk a => by
      rw [← jOddCore_subgroupOf_jHull, Subgroup.mem_subgroupOf]
      exact commutator_mem_jOddCore hG hO α ⟨k.2, hk⟩ a.2) (k := ⟨k, hk.1⟩) hk.2
  refine ⟨n, ?_⟩
  rw [← jOddCore_subgroupOf_jHull, Subgroup.mem_subgroupOf] at hn
  exact hn

theorem pPrimeCore_map_jHull_eq_bot (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (α : Ω) :
    CFSG.pPrimeCore 2 ((jHull G Ω).map (toPermHom G (OddOrbits G α)).rangeRestrict) = ⊥ := by
  set π := (toPermHom G (OddOrbits G α)).rangeRestrict
  set f := π.subgroupMap (jHull G Ω)
  have hker : ∀ k : jHull G Ω, k ∈ f.ker ↔ (k : G) ∈ oddOrbitsKernel G α := fun k => by
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change π k = 1 ↔ _
    rw [← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict]
  refine pPrimeCore_eq_bot_of_ker f (π.subgroupMap_surjective _) (fun x hx => ?_)
    (fun k hk a => ?_)
  · rw [hker]
    exact pPrimeCore_le_oddOrbitsKernel α (jOddCore_le_pPrimeCore (mem_jOddCore.mpr ⟨x, hx, rfl⟩))
  · rw [← jOddCore_subgroupOf_jHull, Subgroup.mem_subgroupOf]
    exact commutator_mem_jOddCore hG hO α ⟨k.2, (hker k).mp hk⟩ a.2

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem jOrbitKernel_eq_inf_oddOrbitsKernel (hG : IsStarGroup G Ω) (α : Ω) :
    jOrbitKernel G Ω = jHull G Ω ⊓ oddOrbitsKernel G α := by
  have := hG.isPretransitive
  ext g
  rw [mem_jOrbitKernel_iff, Subgroup.mem_inf, mem_oddOrbitsKernel_iff]
  simp only [orbit_jOddCore_eq hG]

end Central

end CFSG.Holt.H78
