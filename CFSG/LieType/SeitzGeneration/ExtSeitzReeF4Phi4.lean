module

public import CFSG.RankThree.PartOne.SEITZ12.Final
public import CFSG.RankThree.PartOne.SEITZ7.PairN
public import CFSG.RankThree.PartOne.SEITZ3.PlanePair
public import CFSG.RankThree.PartOne.SEITZX.ReeSplit
public import CFSG.RankThree.PartOne.K128.ReeShape

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ12
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Generic

variable {G G' : Type*} [Group G] [Group G']

theorem reeF4c_cenGen_map (ε : G ≃* G') (E : Subgroup G) :
    cenGen (E.map ε.toMonoidHom) = ε '' cenGen E := by
  ext k
  constructor
  · rintro ⟨x, ⟨x₀, hx₀, rfl⟩, hx1, hk⟩
    refine ⟨ε.symm k, ⟨x₀, hx₀, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · apply ε.injective
      simpa using hk
  · rintro ⟨k₀, ⟨x₀, hx₀, hx1, hk⟩, rfl⟩
    refine ⟨ε x₀, ⟨x₀, hx₀, rfl⟩, ?_, ?_⟩
    · intro h
      exact hx1 (ε.injective (by simpa using h))
    · rw [← map_mul, ← map_mul, hk]

theorem reeF4c_closure_cenGen_map_top (ε : G ≃* G') (E : Subgroup G)
    (h : Subgroup.closure (cenGen E) = ⊤) :
    Subgroup.closure (cenGen (E.map ε.toMonoidHom)) = ⊤ := by
  rw [reeF4c_cenGen_map]
  have h1 : (Subgroup.closure (cenGen E)).map ε.toMonoidHom =
      Subgroup.closure (⇑ε '' cenGen E) := MonoidHom.map_closure _ _
  rw [← h1, h]
  exact Subgroup.map_top_of_surjective _ ε.surjective

theorem reeF4c_closure_cenGen_subgroupOf (Γ E : Subgroup G) (hE : E ≤ Γ)
    (h : Subgroup.closure {k | k ∈ Γ ∧ ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = Γ) :
    Subgroup.closure (cenGen (E.subgroupOf Γ)) = ⊤ := by
  have hset : Γ.subtype '' cenGen (E.subgroupOf Γ) =
      {k | k ∈ Γ ∧ ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    ext k
    constructor
    · rintro ⟨k₀, ⟨x, hx, hx1, hk⟩, rfl⟩
      exact ⟨k₀.2, x, hx, fun h' => hx1 (Subtype.ext h'), congrArg Subtype.val hk⟩
    · rintro ⟨hkΓ, x, hxE, hx1, hk⟩
      exact ⟨⟨k, hkΓ⟩, ⟨⟨x, hE hxE⟩, hxE, fun h' => hx1 (congrArg Subtype.val h'),
        Subtype.ext hk⟩, rfl⟩
  have h1 : (Subgroup.closure (cenGen (E.subgroupOf Γ))).map Γ.subtype = Γ := by
    rw [MonoidHom.map_closure, hset, h]
  have h2 : (⊤ : Subgroup ↥Γ).map Γ.subtype = Γ := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective Γ.subtype_injective (h1.trans h2.symm)

theorem reeF4c_plane_of_commuting [Finite G] {p : ℕ} [Fact p.Prime] {a b : G}
    (ha : orderOf a = p) (hb : orderOf b = p) (hab : a * b = b * a)
    (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    (∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, x ^ p = 1) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = p ^ 2 := by
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute a b from hab).zpow_zpow m n).eq
  have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hbp : b ^ p = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hzp : ∀ {c : G}, c ^ p = 1 → ∀ y ∈ Subgroup.zpowers c, y ^ p = 1 := by
    intro c hc y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [← pairHom_range _ _ hcomm] at hx
    obtain ⟨⟨a', b'⟩, rfl⟩ := hx
    rw [pairHom_apply]
    have hc' : Commute (a' : G) (b' : G) := hcomm a' a'.2 b' b'.2
    rw [hc'.mul_pow, hzp hap a' a'.2, hzp hbp b' b'.2, one_mul]
  · rw [card_sup_pair hinf hcomm, Nat.card_zpowers, Nat.card_zpowers, ha, hb, sq]

end Generic

section Main

theorem reeF4_closure_cenGen_eq_top_of_phi4
    (hamb : ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], 1 ≤ m →
      Nat.card K = 2 ^ (2 * m + 1) → Phi4Ambient m K)
    {m : ℕ} {K : Type} [Group K] [Finite K] [IsSimpleGroup K] (hiso : IsoLie K (.reeF4 m))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)
    (E₁ : Subgroup K) (hE₁p : ∀ x ∈ E₁, x ^ p = 1) (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hm1, hX, ⟨e⟩⟩ := CFSG.RankThree.PartOne.SEITZX.exists_reeGamma_model hiso
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have hshape : SylowShape p 2 (((2 ^ (2 * m + 1)) ^ 2 + 1).factorization p) K :=
    (CFSG.RankThree.PartOne.K128.sylowShape_ree_phi4 hX hp hp5 hpq).of_mulEquiv e
  have hpR : p ∣ Nat.card (rankOneGroupTwo X m) := by
    rw [card_rankOneGroupTwo hm1 hX]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' p hpR
  obtain ⟨a, haR, hap⟩ : ∃ a ∈ rankOneGroupTwo X m, orderOf a = p :=
    ⟨a₀, a₀.2, by rw [Subgroup.orderOf_coe]; exact ha₀⟩
  have hbB : szNw X * a * (szNw X)⁻¹ ∈ szSubB X m := ⟨a, haR, rfl⟩
  have hbp : orderOf (szNw X * a * (szNw X)⁻¹) = p := by
    have := orderOf_injective (MulAut.conj (szNw X)).toMonoidHom
      (MulAut.conj (szNw X)).injective a
    rw [← hap]
    exact this
  have hab : a * (szNw X * a * (szNw X)⁻¹) = (szNw X * a * (szNw X)⁻¹) * a :=
    commute_rankOneGroupTwo_szSubB a haR _ hbB
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers (szNw X * a * (szNw X)⁻¹) = ⊥ := by
    have h := rankOneGroupTwo_inf_szSubB hm1 hX
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ rankOneGroupTwo X m ⊓ szSubB X m :=
      ⟨Subgroup.zpowers_le.mpr haR hx.1, Subgroup.zpowers_le.mpr hbB hx.2⟩
    rw [h] at h1
    exact h1
  have hplane : (∀ x ∈ phi4Plane X a, x ^ p = 1) ∧ Nat.card ↥(phi4Plane X a) = p ^ 2 :=
    reeF4c_plane_of_commuting (p := p) hap hbp hab hinf
  have hplane_le : phi4Plane X a ≤ F4.reeGamma X m :=
    sup_le (Subgroup.zpowers_le.mpr (rankOneGroupTwo_le_reeGamma' hX haR))
      (Subgroup.zpowers_le.mpr (szSubB_le_reeGamma hX hbB))
  have hD : Subgroup.closure {k | k ∈ F4.reeGamma X m ∧
      ∃ x ∈ phi4Plane X a, x ≠ 1 ∧ k * x = x * k} = F4.reeGamma X m :=
    hamb m X hm1 hX p hp hp5 hpq a haR hap
  have hE'' := reeF4c_closure_cenGen_subgroupOf (F4.reeGamma X m) (phi4Plane X a) hplane_le hD
  have hE''c : Nat.card ↥((phi4Plane X a).subgroupOf (F4.reeGamma X m)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hplane_le).toEquiv]
    exact hplane.2
  have hE''p : ∀ x ∈ (phi4Plane X a).subgroupOf (F4.reeGamma X m), x ^ p = 1 := fun x hx =>
    Subtype.ext (by simpa using hplane.1 x hx)
  have hE₀top : Subgroup.closure
      (cenGen (((phi4Plane X a).subgroupOf (F4.reeGamma X m)).map e.symm.toMonoidHom)) = ⊤ :=
    reeF4c_closure_cenGen_map_top e.symm _ hE''
  have hE₀c : Nat.card ↥(((phi4Plane X a).subgroupOf (F4.reeGamma X m)).map
      e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE''c]
  have hE₀p : ∀ x ∈ ((phi4Plane X a).subgroupOf (F4.reeGamma X m)).map e.symm.toMonoidHom,
      x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    show (e.symm y) ^ p = 1
    rw [← map_pow, hE''p y hy, map_one]
  obtain ⟨S, hS⟩ := (IsPGroup.of_card hE₀c : IsPGroup p ↥(((phi4Plane X a).subgroupOf
    (F4.reeGamma X m)).map e.symm.toMonoidHom)).exists_le_sylow
  obtain ⟨φ⟩ := hshape _ S.isPGroup' S.not_dvd_index
  exact closure_cenGen_eq_top_of_plane S _ φ hS hE₀p hE₀c hE₀top E₁ hE₁p hE₁c

theorem extSeitzAtInnerFor_reeF4_phi4 (m : ℕ) :
    ExtSeitzAtInnerFor (.reeF4 m) fun p => p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  refine closure_fixUnion_eq_top_of_inner_equiv hnab (MulEquiv.refl K) (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  exact reeF4_closure_cenGen_eq_top_of_phi4
    (fun m K _ _ _ hm hK => phi4_ambient_holds hm hK) hiso hp hp5 hP E₁ hE₁p hcard₁

end Main

end CFSG.LieType.SeitzGeneration
