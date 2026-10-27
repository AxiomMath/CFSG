module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUSylow
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsPerfect
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.LieType.Chevalley.ExceptionalSmallRankSchreier
public import CFSG.LieType.Chevalley.DiagramFixedModelSchreier

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_perfect_twoSubgroup_of_conj {C : Type*} [Group C] {p : ℕ} {w z c : C}
    (hc : c * w * c⁻¹ = z) {P Q : Subgroup C} (hP : ⁅P, P⁆ = P)
    (hPz : P ≤ centralizer ({z} : Set C)) (hQP : Q ≤ P) (hQ : IsPGroup p Q) :
    ∃ P' Q' : Subgroup C, ⁅P', P'⁆ = P' ∧ P' ≤ centralizer ({w} : Set C) ∧ Q' ≤ P' ∧
      IsPGroup p Q' ∧ Nat.card Q' = Nat.card Q := by
  refine ⟨P.map (MulAut.conj c⁻¹).toMonoidHom, Q.map (MulAut.conj c⁻¹).toMonoidHom,
    by rw [← map_commutator, hP], ?_, map_mono hQP, hQ.map _,
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective⟩
  rintro _ ⟨p, hp, rfl⟩
  have h := mem_centralizer_singleton_iff.1 (hPz hp)
  rw [mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hw : w = c⁻¹ * z * c := by rw [← hc]; group
  rw [hw]
  calc c⁻¹ * p * c * (c⁻¹ * z * c) = c⁻¹ * (p * z) * c := by group
    _ = c⁻¹ * (z * p) * c := by rw [h]
    _ = c⁻¹ * z * c * (c⁻¹ * p * c) := by group


section TwoParts

variable {K : Type} [Field K]

theorem natCard_sylow_two_F4 [Finite K] [CharP K 2] (S : Sylow 2 (adjointGroup .F4 K)) :
    Nat.card S = Nat.card K ^ 24 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq_posUnipotent (K := K)
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S₀]
  change Nat.card (S₀ : Subgroup (adjointGroup .F4 K)) = _
  rw [hS₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup).toEquiv,
    card_posUnipotent, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4]

theorem natCard_le_of_isPGroup_two_F4 [Finite K] [CharP K 2]
    {Q : Subgroup (adjointGroup .F4 K)} (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card K ^ 24 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  calc Nat.card Q ≤ Nat.card S := Subgroup.card_le_of_le hS
    _ = Nat.card K ^ 24 := natCard_sylow_two_F4 S

theorem natCard_le_of_le_of_isPGroup_two_F4 [Finite K] [CharP K 2] {G : Type*} [Group G]
    {L : Subgroup G} (e : L ≃* adjointGroup .F4 K) {Q : Subgroup G} (hQL : Q ≤ L)
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card K ^ 24 := by
  have hQ' : IsPGroup 2 ((Q.subgroupOf L).map e.toMonoidHom) :=
    (hQ.comap_of_injective L.subtype L.subtype_injective).map _
  have h := natCard_le_of_isPGroup_two_F4 hQ'
  rwa [Subgroup.card_map_of_injective e.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv] at h

end TwoParts

section Perfect

variable {K : Type} [Field K]

theorem u0_subgroupOf_le_centralizer_frameRep [CharP K 2] {z : adjointGroup .F4 K}
    (hz : z ∈ ClassReps.frameReps K) :
    (ClassReps.u0 K).subgroupOf (adjointGroup .F4 K) ≤
      centralizer ({z} : Set (adjointGroup .F4 K)) := by
  intro x hx
  have h := mem_centralizer_singleton_iff.1
    (ClassReps.u0_le_centralizer_frameRep hz (Subgroup.mem_subgroupOf.1 hx))
  exact mem_centralizer_singleton_iff.2 (Subtype.ext h)

theorem natCard_u0_subgroupOf :
    Nat.card ((ClassReps.u0 K).subgroupOf (adjointGroup .F4 K)) = Nat.card K ^ 20 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe ClassReps.u0_le_adjointGroup).toEquiv).trans
    ClassReps.natCard_u0

theorem isPGroup_u0_subgroupOf [Finite K] [CharP K 2] :
    IsPGroup 2 ((ClassReps.u0 K).subgroupOf (adjointGroup .F4 K)) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  refine IsPGroup.of_card (n := n * 20) ?_
  rw [natCard_u0_subgroupOf, Nat.card_eq_fintype_card, hn, ← pow_mul]

theorem exists_perfect_le_centralizer_frameRep [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {z : adjointGroup .F4 K} (hz : z ∈ ClassReps.frameReps K) :
    ∃ P : Subgroup (adjointGroup .F4 K), ⁅P, P⁆ = P ∧
      P ≤ centralizer ({z} : Set (adjointGroup .F4 K)) ∧
      (ClassReps.u0 K).subgroupOf (adjointGroup .F4 K) ≤ P := by
  have hU := u0_subgroupOf_le_centralizer_frameRep hz
  have hz' := hz
  simp only [ClassReps.frameReps, Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
  rcases hz' with rfl | rfl | rfl | rfl
  · exact ⟨_, commutator_centralizer_zT hq, le_rfl, hU⟩
  · exact ⟨_, commutator_centralizer_zU hq, le_rfl, hU⟩
  · exact ⟨_, commutator_centralizer_zTU hq, le_rfl, hU⟩
  · refine ⟨(ClassReps.lambdaV K).subgroupOf (adjointGroup .F4 K), ?_, ?_, ?_⟩
    · rw [ClassReps.commutator_subgroupOf_of_le ClassReps.lambdaV_le_adjointGroup,
        ClassReps.commutator_lambdaV hq]
    · intro x hx
      have h := mem_centralizer_singleton_iff.1
        (ClassReps.lambdaV_le_centralizer (Subgroup.mem_subgroupOf.1 hx))
      exact mem_centralizer_singleton_iff.2 (Subtype.ext h)
    · intro x hx
      refine Subgroup.mem_subgroupOf.2 ?_
      have hle : ClassReps.u0 K ≤ ClassReps.lambdaV K := by
        refine biSup_mono fun γ hγ => ?_
        obtain ⟨p, hp, rfl⟩ := hγ
        exact ⟨p, List.mem_append_left _ hp, rfl⟩
      exact hle (Subgroup.mem_subgroupOf.1 hx)

theorem exists_perfect_twoSubgroup_le_centralizer_F4 [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {w : adjointGroup .F4 K} (hw : orderOf w = 2) :
    ∃ P Q : Subgroup (adjointGroup .F4 K), ⁅P, P⁆ = P ∧
      P ≤ centralizer ({w} : Set (adjointGroup .F4 K)) ∧ Q ≤ P ∧ IsPGroup 2 Q ∧
      Nat.card Q = Nat.card K ^ 20 := by
  obtain ⟨g, hg⟩ := ClassReps.exists_conj_mem_frameReps hw
  obtain ⟨P, hP, hPz, hUP⟩ := exists_perfect_le_centralizer_frameRep hq hg
  obtain ⟨P', Q', hP', hP'w, hQP', hQ', hcard⟩ :=
    exists_perfect_twoSubgroup_of_conj rfl hP hPz hUP isPGroup_u0_subgroupOf
  exact ⟨P', Q', hP', hP'w, hQP', hQ', hcard.trans natCard_u0_subgroupOf⟩

end Perfect

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_involution_centralizer_le_of_inner {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] (eM : M ≃* adjointGroup .F4 K₂) {m₀ : G}
    (hm₀M : m₀ ∈ M) (hm₀ : ∀ x ∈ M, t * x * t⁻¹ = m₀ * x * m₀⁻¹) :
    ∃ w ∈ M, orderOf w = 2 ∧ ∀ x ∈ M, x * w = w * x → x * t = t * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  by_cases h1 : m₀ = 1
  ·
    set z : adjointGroup .F4 K₂ := ⟨pinnedX .F4 K₂ root0122 1, pinnedX_mem_adjointGroup _ _⟩
    have hz : orderOf z = 2 := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
      · change pinnedX .F4 K₂ root0122 1 ^ 2 = 1
        rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
      · have h' : pinnedX .F4 K₂ root0122 1 = pinnedX .F4 K₂ root0122 0 := by
          rw [pinnedX_zero]
          exact congrArg Subtype.val h
        exact one_ne_zero (pinnedX_injective .F4 K₂ root0122 h')
    refine ⟨(eM.symm z : G), (eM.symm z).2, ?_, fun x hx _ => ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz]
    · have h := hm₀ x hx
      rw [h1, one_mul, inv_one, mul_one] at h
      calc x * t = t * x * t⁻¹ * t := by rw [h]
        _ = t * x := by group
  · refine ⟨m₀, hm₀M, ?_, fun x hx hxw => ?_⟩
    ·
      have hcomm : ∀ x ∈ M, m₀ * m₀ * x = x * (m₀ * m₀) := by
        intro x hx
        have hx' : t * x * t⁻¹ ∈ M := by
          rw [hm₀ x hx]
          exact mul_mem (mul_mem hm₀M hx) (inv_mem hm₀M)
        have h2 := hm₀ _ hx'
        have h3 : t * (t * x * t⁻¹) * t⁻¹ = x := by
          calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
            _ = x := by rw [ht2, one_mul, inv_one, mul_one]
        rw [h3, hm₀ x hx] at h2
        calc m₀ * m₀ * x = m₀ * (m₀ * x * m₀⁻¹) * m₀⁻¹ * (m₀ * m₀) := by group
          _ = x * (m₀ * m₀) := by rw [← h2]
      have hcen : eM ⟨m₀ * m₀, mul_mem hm₀M hm₀M⟩ ∈ center (adjointGroup .F4 K₂) := by
        rw [Subgroup.mem_center_iff]
        intro y
        rw [← eM.apply_symm_apply y, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm _ (eM.symm y).2).symm
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hcen
      have hsq : m₀ ^ 2 = 1 := by
        rw [sq]
        exact congrArg Subtype.val hcen
      exact orderOf_eq_prime hsq h1
    · have h := hm₀ x hx
      have hx' : m₀ * x * m₀⁻¹ = x := by
        calc m₀ * x * m₀⁻¹ = (x * m₀) * m₀⁻¹ := by rw [← hxw]
          _ = x := by group
      rw [hx'] at h
      calc x * t = t * x * t⁻¹ * t := by rw [h]
        _ = t * x := by group

theorem not_exists_inner_of_card_lt (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {M : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2]
    (hq₂ : 4 ≤ Nat.card K₂) (eM : M ≃* adjointGroup .F4 K₂)
    (hL2 : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 2 Q → Nat.card Q < Nat.card K₂ ^ 20) :
    ¬ ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹ := by
  rintro ⟨m₀, hm₀M, hm₀⟩
  obtain ⟨w, hwM, hw2, hwC⟩ := exists_involution_centralizer_le_of_inner ht eM hm₀M hm₀
  have hw' : orderOf (eM ⟨w, hwM⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw2]
  obtain ⟨P, Q, hP, hPw, hQP, hQ, hQcard⟩ := exists_perfect_twoSubgroup_le_centralizer_F4 hq₂ hw'
  set φ : adjointGroup .F4 K₂ →* G := M.subtype.comp eM.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := M.subtype_injective.comp eM.symm.injective
  have hφw : φ (eM ⟨w, hwM⟩) = w := by simp [hφ]
  have hPG : ⁅P.map φ, P.map φ⁆ = P.map φ := by rw [← map_commutator, hP]
  have hPt : P.map φ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    have hpw := mem_centralizer_singleton_iff.1 (hPw hp)
    have hpw' : φ p * w = w * φ p := by
      rw [← hφw, ← map_mul, ← map_mul, hpw]
    exact mem_centralizer_singleton_iff.2 (hwC _ (eM.symm p).2 hpw')
  have hQL : Q.map φ ≤ L := (map_mono hQP).trans (std_perfect_le hset hOut htC ht hPG hPt)
  have h := hL2 _ hQL (hQ.map φ)
  rw [Subgroup.card_map_of_injective hφinj, hQcard] at h
  exact lt_irrefl _ h

theorem not_exists_inner_F4_field (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G} {K₂ : Type}
    [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .F4 K₂) :
    ¬ ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹ := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₂
  have := charP_two_of_natCard_eq_two_pow hK₂
  have hf : 1 ≤ f := one_le_of_natCard_eq_two_pow hK
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨5, derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_ordinary_small_rank_Schreier .F4 K).2 (Or.inl rfl))⟩⟩
  have hq₂ : 4 ≤ Nat.card K₂ := by
    rw [hK₂]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine not_exists_inner_of_card_lt hset hOut htC ht hq₂ eM fun Q hQL hQ => ?_
  calc Nat.card Q ≤ Nat.card K ^ 24 := natCard_le_of_le_of_isPGroup_two_F4 e hQL hQ
    _ = 2 ^ (24 * f) := by rw [hK, ← pow_mul, mul_comm]
    _ < 2 ^ (40 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ = Nat.card K₂ ^ 20 := by rw [hK₂, ← pow_mul]; ring_nf

theorem not_mem_F4_field (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G} {K₂ : Type}
    [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .F4 K₂) : t ∉ M :=
  fun htM => not_exists_inner_F4_field hset hK e htC ht hK₂ eM ⟨t, htM, fun _ _ => rfl⟩

end Standard

end CFSG.SeitzReduction.F4Pilot
