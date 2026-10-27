module

public import CFSG.Holt.H78.Dihedral
public import CFSG.Holt.H78.SEModel
public import CFSG.Timmesfeld.Bridge.Asc73Central
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender

section Normal


variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

theorem eq_bot_of_normal_of_isPGroup_two [IsPreprimitive G Ω] (hΩ : Odd (Nat.card Ω))
    (h1 : 1 < Nat.card Ω) {P : Subgroup G} (hP : P.Normal) (h2 : IsPGroup 2 P) : P = ⊥ := by
  by_contra hne
  have : Nonempty Ω := (Nat.card_pos_iff.mp (by omega)).1
  have := CFSG.GroupActions.isPretransitive_of_normal_ne_bot (Ω := Ω) P hne
  obtain ⟨α, hα⟩ := fixSet_nonempty_of_odd hΩ h2
  have hsub : ∀ ω : Ω, ω = α := fun ω => by
    obtain ⟨p, rfl⟩ := exists_smul_eq P α ω
    exact hα p p.2
  have : Subsingleton Ω := ⟨fun a b => (hsub a).trans (hsub b).symm⟩
  have := Nat.card_of_subsingleton α
  omega

private theorem pPrimeCore_eq_bot_of_normal {X : Type*} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 2 X = ⊥) {L : Subgroup X} (hL : L.Normal) :
    CFSG.pPrimeCore 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ((CFSG.pPrimeCore 2 L).map L.subtype).Normal := inferInstance
  have hc : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 L).map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hle : (CFSG.pPrimeCore 2 L).map L.subtype ≤ CFSG.pPrimeCore 2 X := le_sSup ⟨hn, hc⟩
  rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hle

omit [Finite Ω] in
private theorem eq_one_of_forall_commute_of_smul_eq [IsPretransitive G Ω] {v : G} {α : Ω}
    (hα : v • α = α) (hv : ∀ g : G, g * v = v * g) : v = 1 :=
  eq_of_smul_eq_smul fun ω => by
    obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
    rw [smul_smul, ← hv g, mul_smul, hα, one_smul]

end Normal

section Commute


variable {G : Type} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [FaithfulSMul G Ω]

omit [Finite G] [FaithfulSMul G Ω] in
theorem mem_longInvAt_of_commute {t u : G} {α : Ω} (ht : t ∈ longInvAt G Ω α)
    (hu : u ∈ longInv G Ω) (htu : Commute t u) : u ∈ longInvAt G Ω α :=
  ⟨hu, (smul_eq_iff_of_mem_longInvAt ht (u • α)).mp (by rw [smul_smul, htu.eq, mul_smul, ht.2])⟩

theorem exists_commute_ne_of_pPrimeCore_eq_bot (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G = ⊥) :
    ∃ t ∈ longInv G Ω, ∃ u ∈ longInv G Ω, t ≠ u ∧ Commute t u := by
  by_contra h
  push Not at h
  have : Fintype G := Fintype.ofFinite G
  have := hG.isPretransitive
  obtain ⟨t, ht⟩ := hG.longInv_nonempty
  obtain ⟨α, htα⟩ := exists_mem_longInvAt ht
  have ht1 : t ≠ 1 := fun h1 => by
    have h2 := ht.1
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G t ht1
    (mul_self_eq_one_of_mem_longInv ht) fun g hg => by
      by_contra hne
      exact h _ (conj_mem_longInv ht g) t ht hne hg
  have hNO : N ≤ CFSG.pPrimeCore 2 G := le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
  rw [hO, le_bot_iff] at hNO
  refine ht1 (eq_one_of_forall_commute_of_smul_eq htα.2 fun g => ?_)
  have hg := hN g
  rw [hNO, Subgroup.mem_bot, mul_inv_eq_one] at hg
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [hg]

end Commute

section Bender

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Finite Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

private theorem exists_benderType_of_fusionIsBenderGroup {X : Type*} [Group X]
    (h : fusionIsBenderGroup X) : ∃ n i e : ℕ, BenderType X n i e := by
  rcases h with ⟨f, hf, ⟨φ⟩⟩ | ⟨f, hf, ⟨φ⟩⟩ | ⟨a, ha, ⟨φ⟩⟩
  · exact ⟨f, 1, 1, .linear f hf φ⟩
  · have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
        CFSG.Models.benderPSU3Model_eq_psu3 f
    exact ⟨f, 3, _, .unitary f hf (φ.trans (MulEquiv.subgroupCongr hmodel.symm))⟩
  · exact ⟨2 * a + 1, 2, 1,
      .suzuki a ha (φ.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))⟩

private theorem false_of_not_twoRankAtLeastTwo (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G = ⊥) {L : Subgroup G} (hL : L.Normal) {v : G} (hvL : v ∈ L)
    (hv : orderOf v = 2) (hlow : ¬ CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo L) :
    False := by
  have : Fintype L := Fintype.ofFinite L
  have := hG.isPretransitive
  have key : ∀ a b : L, a * a = 1 → b * b = 1 → Commute a b → a ≠ 1 → b ≠ 1 → a = b :=
    fun a b ha hb hab ha1 hb1 => by
      by_contra hne
      exact hlow (CFSG.Timmesfeld.Bridge.twoRankAtLeastTwo_of_commute ha hb hab ha1 hb1 hne)
  have hvv : v * v = 1 := by rw [← sq, ← hv, pow_orderOf_eq_one]
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hv
    omega
  have hconj : ∀ {X : Type} [Group X] (g y : X), y * y = 1 → g * y * g⁻¹ * (g * y * g⁻¹) = 1 :=
    fun g y hy => by
      rw [show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, hy, mul_one,
        mul_inv_cancel]
  have hconj1 : ∀ {X : Type} [Group X] (g y : X), y ≠ 1 → g * y * g⁻¹ ≠ 1 :=
    fun g y hy h => hy (by rw [show y = g⁻¹ * (g * y * g⁻¹) * g by group, h, mul_one,
      inv_mul_cancel])
  set w : L := ⟨v, hvL⟩ with hw
  have hww : w * w = 1 := Subtype.ext hvv
  have hw1 : w ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar L w hw1 hww fun g hg =>
    key _ _ (hconj g w hww) hww hg (hconj1 g w hw1) hw1
  have hNO : N ≤ CFSG.pPrimeCore 2 L := le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
  rw [pPrimeCore_eq_bot_of_normal hO hL, le_bot_iff] at hNO
  have hcen : ∀ g : L, g * w = w * g := fun g => by
    have h := hN g
    rw [hNO, Subgroup.mem_bot, mul_inv_eq_one] at h
    calc g * w = g * w * g⁻¹ * g := by group
      _ = w * g := by rw [h]
  have hcomm : ∀ g : G, g * v = v * g := fun g => by
    let x : L := ⟨g * v * g⁻¹, hL.conj_mem v hvL g⟩
    have hx : x = w := key x w (Subtype.ext (hconj g v hvv)) hww (hcen x)
      (fun h => hconj1 g v hv1 (congrArg Subtype.val h)) hw1
    have h := congrArg Subtype.val hx
    change g * v * g⁻¹ = v at h
    calc g * v = g * v * g⁻¹ * g := by group
      _ = v * g := by rw [h]
  obtain ⟨α, hα⟩ := fixSet_nonempty_of_odd hG.odd_card (isPGroup_zpowers_of_orderOf_eq_two hv)
  exact hv1 (eq_one_of_forall_commute_of_smul_eq (hα v (Subgroup.mem_zpowers v)) hcomm)

private theorem existsUnique_fixed_of_benderType [IsPreprimitive G Ω] (hG : IsStarGroup G Ω)
    {N : Subgroup G} (hN : N.Normal) {n i e : ℕ} (hBT : BenderType N n i e) {x : G}
    (hxN : x ∈ N) (hx : orderOf x = 2) : ∃! ω : Ω, x • ω = ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : 1 < Nat.card Ω := by have := hG.three_le_card; omega
  have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp h1
  have hxN' : orderOf (⟨x, hxN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hNbot : N ≠ ⊥ := fun h => by
    have h' : x ∈ (⊥ : Subgroup G) := h ▸ hxN
    rw [Subgroup.mem_bot] at h'
    rw [h', orderOf_one] at hx
    omega
  have : IsPretransitive N Ω := CFSG.GroupActions.isPretransitive_of_normal_ne_bot N hNbot
  obtain ⟨Q⟩ : Nonempty (Sylow 2 N) := inferInstance
  obtain ⟨α, hQα⟩ := fixSet_nonempty_of_odd hG.odd_card Q.isPGroup'
  rw [mem_fixSet_iff_le_stabilizer] at hQα
  have hne : stabilizer N α ≠ ⊤ := by
    intro htop
    obtain ⟨β, hβ⟩ := exists_ne α
    obtain ⟨y, rfl⟩ := exists_smul_eq N α β
    have hy : y ∈ stabilizer N α := htop ▸ Subgroup.mem_top y
    exact hβ (mem_stabilizer_iff.mp hy)
  have hle : stabilizer N α ≤ borel (Q : Subgroup N) := hBT.le_borel_of_sylow_le Q hQα hne
  set P : Subgroup G := (Q : Subgroup N).map N.subtype with hP
  have hincl : ∀ g ∈ stabilizer G α, ∀ h ∈ P, g * h * g⁻¹ ∈ P := by
    rintro g hg _ ⟨y, hy, rfl⟩
    set R : Subgroup N := (Q : Subgroup N).map (MulAut.conjNormal g).toMonoidHom with hR
    have hR2 : IsPGroup 2 R := Q.isPGroup'.map _
    have hRα : R ≤ stabilizer N α := by
      rintro _ ⟨z, hz, rfl⟩
      rw [mem_stabilizer_iff, Subgroup.smul_def]
      change (MulAut.conjNormal g z : G) • α = α
      have hg' : g⁻¹ • α = α := inv_smul_eq_iff.mpr (mem_stabilizer_iff.mp hg).symm
      rw [MulAut.conjNormal_apply, mul_smul, mul_smul, hg', ← Subgroup.smul_def,
        mem_stabilizer_iff.mp (hQα hz), mem_stabilizer_iff.mp hg]
    have hRQ : R ≤ Q := fun r hr => by
      have hr' : r ∈ R ⊓ Subgroup.normalizer (Q : Set N) := ⟨hr, hle (hRα hr)⟩
      rw [hR2.inf_normalizer_sylow Q] at hr'
      exact hr'.2
    exact ⟨_, hRQ ⟨y, hy, rfl⟩, by simp [MulAut.conjNormal_apply]⟩
  have hnorm : stabilizer G α ≤ Subgroup.normalizer (P : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hincl g hg h, fun hh => ?_⟩
    have := hincl g⁻¹ (inv_mem hg) _ hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  have hPtop : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
    intro htop
    have hPbot := eq_bot_of_normal_of_isPGroup_two hG.odd_card h1
      (Subgroup.normalizer_eq_top_iff.mp htop) (Q.isPGroup'.map N.subtype)
    rw [hP, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hPbot
    exact Q.ne_bot_of_dvd_card (hxN' ▸ orderOf_dvd_natCard _) hPbot
  have heq : stabilizer G α = Subgroup.normalizer (P : Set G) := by
    rcases hnorm.lt_or_eq with hlt | h
    · exact absurd ((IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G α).lt_iff.mp hlt)
        hPtop
    · exact h
  have hge : borel (Q : Subgroup N) ≤ stabilizer N α := fun y hy => by
    have hy' : (y : G) ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_map N.subtype ⟨y, hy, rfl⟩
    rw [← heq, mem_stabilizer_iff] at hy'
    exact mem_stabilizer_iff.mpr hy'
  obtain ⟨t, hc⟩ := hBT.exists_benderCore Q
  have hcard : Nat.card Ω = (2 ^ n) ^ i + 1 := by
    rw [← index_stabilizer_of_transitive N α, le_antisymm hle hge, hc.index_eq]
  exact (IsBenderAction.mk hBT inferInstance hcard).existsUnique_fixed hxN'

theorem mem_longInv_of_mem_of_fusionStronglyEmbedded (hG : IsStarGroup G Ω) [IsPreprimitive G Ω]
    (hO : CFSG.pPrimeCore 2 G = ⊥) {L : Subgroup G} (hL : L.Normal)
    (hSE : ∃ M : Subgroup L, fusionStronglyEmbedded M) {v : G} (hvL : v ∈ L)
    (hv : orderOf v = 2) : v ∈ longInv G Ω := by
  obtain ⟨M, hM⟩ := hSE
  refine ⟨hv, ?_⟩
  rcases CFSG.BenderSuzuki.theorem_SE M hM.to_native with hlow | ⟨hB, -, -⟩
  · exact (false_of_not_twoRankAtLeastTwo hG hO hL hvL hv fun h =>
      hlow (CFSG.BenderSuzuki.twoRankAtLeastTwo_involutionCore_iff.mpr h)).elim
  · set K := CFSG.BenderSuzuki.involutionCore L with hK
    have hK0 : CFSG.pPrimeCore 2 K = ⊥ :=
      pPrimeCore_eq_bot_of_normal (pPrimeCore_eq_bot_of_normal hO hL) inferInstance
    let φ : K ⧸ CFSG.BenderSuzuki.twoPrimeCore K ≃* K.map L.subtype :=
      (QuotientGroup.quotientMulEquivOfEq hK0).trans
        (QuotientGroup.quotientBot.trans (K.equivMapOfInjective L.subtype L.subtype_injective))
    obtain ⟨n, i, e, hBT⟩ := exists_benderType_of_fusionIsBenderGroup
      (fusionIsBenderGroup_of_isSimpleBenderGroup (hB.map_mulEquiv φ))
    have hvK : (⟨v, hvL⟩ : L) ∈ K := Subgroup.subset_closure
      ⟨fun h => by
        rw [show v = 1 from congrArg Subtype.val h, orderOf_one] at hv
        omega, Subtype.ext (by rw [SubgroupClass.coe_pow, ← hv, pow_orderOf_eq_one]; rfl)⟩
    exact existsUnique_fixed_of_benderType hG inferInstance hBT ⟨_, hvK, rfl⟩ hv

end Bender

end CFSG.Holt.H78
