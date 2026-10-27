module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageChainStep

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 goldschmidt1974_of_milestone)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Defs

variable {G : Type*} [Group G]

@[expose] def pushNormalizer (C : ℕ → Subgroup G) (k : ℕ) : Subgroup G :=
  ⨅ j ∈ Finset.range k, normalizer (C j : Set G)

structure LinearPushChain (t d : G) (T A : Subgroup G) (f m : ℕ) (C : ℕ → Subgroup G) :
    Prop where
  zero : C 0 = ⊥
  base : C 1 = A
  mono : ∀ j ≤ m, C j ≤ C (j + 1)
  card : ∀ j ≤ m + 1, Nat.card (C j) = 2 ^ (f * j)
  normal : ∀ j ≤ m, C (j + 1) ≤ normalizer (C j : Set G)
  layer_sq : ∀ j ≤ m, ∀ x ∈ C (j + 1), x * x ∈ C j
  layer_comm : ∀ j ≤ m, ∀ x ∈ C (j + 1), ∀ y ∈ C (j + 1), x * y * x⁻¹ * y⁻¹ ∈ C j
  t_norm : ∀ j ≤ m + 1, t ∈ normalizer (C j : Set G)
  t_not_mem : t ∉ C (m + 1)
  comm_t : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ C (j + 1), x * t * x⁻¹ * t⁻¹ ∈ C j
  comm_t_ker : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ C (j + 1), x * t * x⁻¹ * t⁻¹ ∈ C (j - 1) → x ∈ C j
  comm_t_onto : ∀ j, 1 ≤ j → j ≤ m → ∀ u ∈ C j, ∃ x ∈ C (j + 1),
    u⁻¹ * (x * t * x⁻¹ * t⁻¹) ∈ C (j - 1)
  centralizer_t : C (m + 1) ⊓ centralizer ({t} : Set G) = A
  d_comm : d * t = t * d
  d_order : orderOf d = 2 ^ f - 1
  d_norm : ∀ j ≤ m + 1, d ∈ normalizer (C j : Set G)
  d_reg : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, d ^ k * a * (d ^ k)⁻¹ = b
  T_norm : ∀ j ≤ m + 1, T ≤ normalizer (C j : Set G)

end Defs

@[expose] def SmallRootRegularNormalInput : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (R X U P : Subgroup D) (n : ℕ),
    SmallRootStage R X U P n → 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard →
    (∀ S : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      S ≤ (gmsRootConjugateAction (U ⊔ R) R).range →
      (S.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal → IsSimpleGroup S →
      (∃ a b : S, a * b ≠ b * a) → CFSG.Blueprint.Catalog S) →
    GMSHasRegularNormal U R ∨ (n = 3 ∧ GMSProjectiveEight U R)

section PushNormalizer

variable {G : Type*} [Group G]

theorem mem_pushNormalizer_iff {C : ℕ → Subgroup G} {k : ℕ} {g : G} :
    g ∈ pushNormalizer C k ↔ ∀ j < k, g ∈ normalizer (C j : Set G) := by
  simp only [pushNormalizer, mem_iInf, Finset.mem_range]

theorem pushNormalizer_succ (C : ℕ → Subgroup G) (k : ℕ) :
    pushNormalizer C (k + 1) = pushNormalizer C k ⊓ normalizer (C k : Set G) := by
  ext g
  simp only [mem_inf, mem_pushNormalizer_iff]
  constructor
  · exact fun h => ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h j hj
    · exact hk

theorem pushNormalizer_one {C : ℕ → Subgroup G} (h0 : C 0 = ⊥) : pushNormalizer C 1 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [mem_pushNormalizer_iff]
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [h0]
  exact mem_normalizer_iff.mpr fun x => by simp

theorem pushNormalizer_congr {C C' : ℕ → Subgroup G} {k : ℕ} (h : ∀ j < k, C j = C' j) :
    pushNormalizer C k = pushNormalizer C' k := by
  ext g
  simp only [mem_pushNormalizer_iff]
  exact forall₂_congr fun j hj => by rw [h j hj]

theorem pushNormalizer_antitone (C : ℕ → Subgroup G) {k l : ℕ} (hkl : k ≤ l) :
    pushNormalizer C l ≤ pushNormalizer C k := fun g hg =>
  mem_pushNormalizer_iff.mpr fun j hj => mem_pushNormalizer_iff.mp hg j (by omega)

end PushNormalizer

section Extend

variable {G : Type*} [Group G]

theorem LinearPushChain.extend {t d : G} {T A : Subgroup G} {f m : ℕ} {C : ℕ → Subgroup G}
    (h : LinearPushChain t d T A f m C) (Up : Subgroup G) (hmono : C (m + 1) ≤ Up)
    (hcard : Nat.card Up = 2 ^ (f * (m + 2))) (hnormal : Up ≤ normalizer (C (m + 1) : Set G))
    (hsq : ∀ x ∈ Up, x * x ∈ C (m + 1))
    (hcomm : ∀ x ∈ Up, ∀ y ∈ Up, x * y * x⁻¹ * y⁻¹ ∈ C (m + 1))
    (ht : t ∈ normalizer (Up : Set G)) (hct : ∀ x ∈ Up, x * t * x⁻¹ * t⁻¹ ∈ C (m + 1))
    (hker : ∀ x ∈ Up, x * t * x⁻¹ * t⁻¹ ∈ C m → x ∈ C (m + 1))
    (honto : ∀ u ∈ C (m + 1), ∃ x ∈ Up, u⁻¹ * (x * t * x⁻¹ * t⁻¹) ∈ C m)
    (hd : d ∈ normalizer (Up : Set G)) (hT : T ≤ normalizer (Up : Set G))
    (C' : ℕ → Subgroup G) (hC' : ∀ j, j ≠ m + 2 → C' j = C j) (hC'2 : C' (m + 2) = Up) :
    LinearPushChain t d T A f (m + 1) C' := by
  have hcen : ∀ x ∈ Up, x * t = t * x → x ∈ C (m + 1) := fun x hx hxt =>
    hker x hx (by rw [hxt, mul_inv_cancel_right, mul_inv_cancel]; exact one_mem _)
  refine ⟨by rw [hC' 0 (by omega)]; exact h.zero, by rw [hC' 1 (by omega)]; exact h.base,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, ?_, fun j h1 hj => ?_, fun j h1 hj => ?_, fun j h1 hj => ?_, ?_, h.d_comm,
    h.d_order, fun j hj => ?_, h.d_reg, fun j hj => ?_⟩
  ·
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · rw [hC' j (by omega), hC' (j + 1) (by omega)]
      exact h.mono j (by omega)
    · obtain rfl : j = m + 1 := by omega
      rw [hC' (m + 1) (by omega), hC'2]
      exact hmono
  ·
    rcases Nat.lt_or_ge j (m + 2) with hj' | hj'
    · rw [hC' j (by omega)]
      exact h.card j (by omega)
    · obtain rfl : j = m + 2 := by omega
      rw [hC'2]
      exact hcard
  ·
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · rw [hC' j (by omega), hC' (j + 1) (by omega)]
      exact h.normal j (by omega)
    · obtain rfl : j = m + 1 := by omega
      rw [hC' (m + 1) (by omega), hC'2]
      exact hnormal
  ·
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · rw [hC' j (by omega), hC' (j + 1) (by omega)]
      exact h.layer_sq j (by omega)
    · obtain rfl : j = m + 1 := by omega
      rw [hC' (m + 1) (by omega), hC'2]
      exact hsq
  ·
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · rw [hC' j (by omega), hC' (j + 1) (by omega)]
      exact h.layer_comm j (by omega)
    · obtain rfl : j = m + 1 := by omega
      rw [hC' (m + 1) (by omega), hC'2]
      exact hcomm
  ·
    rcases Nat.lt_or_ge j (m + 2) with hj' | hj'
    · rw [hC' j (by omega)]
      exact h.t_norm j (by omega)
    · obtain rfl : j = m + 2 := by omega
      rw [hC'2]
      exact ht
  ·
    rw [hC'2]
    exact fun htU => h.t_not_mem (hcen t htU rfl)
  ·
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · rw [hC' j (by omega), hC' (j + 1) (by omega)]
      exact h.comm_t j h1 (by omega)
    · obtain rfl : j = m + 1 := by omega
      rw [hC' (m + 1) (by omega), hC'2]
      exact hct
  ·
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · rw [hC' j (by omega), hC' (j + 1) (by omega), hC' (j - 1) (by omega)]
      exact h.comm_t_ker j h1 (by omega)
    · obtain rfl : j = m + 1 := by omega
      rw [hC' (m + 1) (by omega), hC'2, Nat.add_sub_cancel, hC' m (by omega)]
      exact hker
  ·
    rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
    · rw [hC' j (by omega), hC' (j + 1) (by omega), hC' (j - 1) (by omega)]
      exact h.comm_t_onto j h1 (by omega)
    · obtain rfl : j = m + 1 := by omega
      rw [hC' (m + 1) (by omega), hC'2, Nat.add_sub_cancel, hC' m (by omega)]
      exact honto
  ·
    rw [hC'2]
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨hxU, hxt⟩ := mem_inf.mp hx
      have hxt' : x * t = t * x :=
        (mem_centralizer_iff.mp hxt t (Set.mem_singleton t)).symm
      rw [← h.centralizer_t]
      exact mem_inf.mpr ⟨hcen x hxU hxt', hxt⟩
    · rw [← h.centralizer_t]
      exact inf_le_inf_right _ hmono
  ·
    rcases Nat.lt_or_ge j (m + 2) with hj' | hj'
    · rw [hC' j (by omega)]
      exact h.d_norm j (by omega)
    · obtain rfl : j = m + 2 := by omega
      rw [hC'2]
      exact hd
  ·
    rcases Nat.lt_or_ge j (m + 2) with hj' | hj'
    · rw [hC' j (by omega)]
      exact h.T_norm j (by omega)
    · obtain rfl : j = m + 2 := by omega
      rw [hC'2]
      exact hT

end Extend

section TopBot

variable {G : Type*} [Group G] [Finite G]

theorem relSmallRootStage_top_bot {R X U P : Subgroup G} {n : ℕ} (h : SmallRootStage R X U P n) :
    RelSmallRootStage ⊤ ⊥ R X U P n := by
  refine ⟨inferInstance, bot_le, bot_le, bot_le, bot_le, le_top, le_top, le_top, le_top, ?_⟩
  intro _
  let ψ : G →* ↥(⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf ⊤ :=
    (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom)
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 := (QuotientGroup.eq_iff_div_mem).mp hxy
      rw [mem_subgroupOf, mem_bot] at h1
      have h2 : ((Subgroup.topEquiv.symm x : ↥(⊤ : Subgroup G)) : G) =
          (Subgroup.topEquiv.symm y : ↥(⊤ : Subgroup G)) := by
        rw [← div_eq_one]
        simpa using h1
      simpa using h2
    · obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ z
      exact ⟨z, congrArg (QuotientGroup.mk' _) (Subtype.ext rfl)⟩
  let e := MulEquiv.ofBijective ψ hψ
  have himg : ∀ K : Subgroup G, K.map e.toMonoidHom = relImg ⊤ ⊥ K := by
    intro K
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact relMk_mem_relImg ⟨x, mem_top x⟩ hx
    · intro hz
      obtain ⟨x, hx, rfl⟩ := exists_of_mem_relImg hz
      exact ⟨x, hx, rfl⟩
  have h1 := h.map_mulEquiv e
  rwa [himg, himg, himg, himg] at h1

end TopBot

section State

variable {G : Type} [Group G] [Finite G]

structure PushState (t : G) (T A : Subgroup G) (f k : ℕ) (d : G) (C : ℕ → Subgroup G)
    (X : Subgroup G) : Prop where
  chain : LinearPushChain t d T A f k C
  d_mem : d ∈ X
  stage : RelSmallRootStage (pushNormalizer C (k + 1)) (C k) (C k ⊔ zpowers t) X (C (k + 1))
    (C (k + 1) ⊔ T) f

theorem pushState_zero {L T : Subgroup G} {f : ℕ} {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) (h0 : SmallRootStage (zpowers t) L (T ⊓ L) T f) :
    ∃ (d : G) (C : ℕ → Subgroup G), PushState t T (T ⊓ L) f 0 d C L ∧
      ∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1 := by
  obtain ⟨d, hdNX, hdord, -, hdtr, hdfix⟩ := h0.exists_singer
  obtain ⟨-, -, -, ⟨-, -, hXC⟩, ⟨hUel, -, -, hUcard⟩, -,
    ⟨-, -, hUP, hRP, hPU, hUR, -, -⟩⟩ := h0.1
  set C : ℕ → Subgroup G := fun j => if j = 1 then T ⊓ L else ⊥ with hCdef
  have hC0 : C 0 = ⊥ := by simp [hCdef]
  have hC1 : C 1 = T ⊓ L := by simp [hCdef]
  have htT : t ∈ T := hRP (mem_zpowers t)
  have htL : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.mp htC x hx
  have hnbot : ∀ g : G, g ∈ normalizer ((⊥ : Subgroup G) : Set G) := fun g =>
    mem_normalizer_iff.mpr fun x => by simp
  have hUsq : ∀ x ∈ T ⊓ L, x * x = 1 := fun x hx => by
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hUcomm : ∀ x ∈ T ⊓ L, ∀ y ∈ T ⊓ L, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have htU : t ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => htL x (mem_inf.mp hx).2)
  refine ⟨d, C, ⟨⟨hC0, hC1, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj x hx => ?_,
    fun j hj x hx y hy => ?_, fun j hj => ?_, ?_, fun j h1 h2 => by omega, fun j h1 h2 => by omega,
    fun j h1 h2 => by omega, ?_, ?_, hdord, fun j hj => ?_, hdtr, fun j hj => ?_⟩,
    (mem_inf.mp hdNX).1, ?_⟩, hdfix⟩
  · obtain rfl : j = 0 := by omega
    rw [hC0]
    exact bot_le
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · rw [hC0, card_bot, mul_zero, pow_zero]
    · rw [hC1, hUcard, mul_one]
  · obtain rfl : j = 0 := by omega
    rw [hC0]
    exact fun g _ => hnbot g
  · obtain rfl : j = 0 := by omega
    rw [hC1] at hx
    rw [hC0, hUsq x hx]
    exact one_mem _
  · obtain rfl : j = 0 := by omega
    rw [hC1] at hx hy
    rw [hC0, hUcomm x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · rw [hC0]
      exact hnbot t
    · rw [hC1]
      exact htU
  · rw [zero_add, hC1]
    intro htU'
    have : t ∈ (T ⊓ L) ⊓ zpowers t := mem_inf.mpr ⟨htU', mem_zpowers t⟩
    rw [hUR, mem_bot] at this
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · rw [zero_add, hC1]
    refine inf_eq_left.mpr fun x hx => ?_
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (htL x (mem_inf.mp hx).2).symm
  · exact htL d (mem_inf.mp hdNX).1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · rw [hC0]
      exact hnbot d
    · rw [hC1]
      exact (mem_inf.mp hdNX).2
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · rw [hC0]
      exact fun g _ => hnbot g
    · rw [hC1]
      exact hPU
  ·
    rw [zero_add, pushNormalizer_one hC0, hC0, hC1, bot_sup_eq,
      sup_eq_right.mpr (inf_le_left : T ⊓ L ≤ T)]
    exact relSmallRootStage_top_bot h0

end State

section Step

variable {G : Type} [Group G] [Finite G]

theorem PushState.next [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hHKS : SmallRootRegularNormalInput)
    {t : G} (ht : orderOf t = 2) {T A : Subgroup G} {f k : ℕ} {d : G} {C : ℕ → Subgroup G}
    {X : Subgroup G} (hT2 : IsPGroup 2 T) (hT0 : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T)
    (hAT : A ≤ T) (h : PushState t T A f k d C X) :
    ((1 ≤ k ∧ ABGLocalTools.IsSylowOf 2 (C (k + 1) ⊔ T) (pushNormalizer C (k + 1))) ∨
      (f = 3 ∧ ∀ [((C k).subgroupOf (pushNormalizer C (k + 1))).Normal],
        GMSProjectiveEight
          (((C (k + 1)).subgroupOf (pushNormalizer C (k + 1))).map
            (QuotientGroup.mk' ((C k).subgroupOf (pushNormalizer C (k + 1)))))
          (((C k ⊔ zpowers t).subgroupOf (pushNormalizer C (k + 1))).map
            (QuotientGroup.mk' ((C k).subgroupOf (pushNormalizer C (k + 1))))))) ∨
    ∃ (C' : ℕ → Subgroup G) (X' : Subgroup G), PushState t T A f (k + 1) d C' X' := by
  obtain ⟨hch, hdX, hst⟩ := h
  have : ((C k).subgroupOf (pushNormalizer C (k + 1))).Normal := hst.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hWR, hWX, hWU, hWP, hRN, hXN, hUN, hPN, hS⟩ := id hst
  have hS := @hS inferInstance
  have hW2 : IsPGroup 2 (C k) := IsPGroup.of_card (hch.card k (by omega))
  have hU2 : IsPGroup 2 (C (k + 1)) := IsPGroup.of_card (hch.card (k + 1) le_rfl)
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; exact absurd ht (by norm_num)
  have htU : t ∉ C (k + 1) := hch.t_not_mem
  have htW : t ∉ C k := fun h1 => htU (hch.mono k (by omega) h1)
  have htR : t ∈ C k ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  rcases (smallRoot_sylow_alternative hS).2 with ⟨hsyl, -⟩ | ⟨hnsyl, h3⟩
  ·
    left; left
    have hP := isSylowOf_of_relImg hW2 hWP hPN hsyl
    refine ⟨?_, hP⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      apply hT0
      rw [zero_add, pushNormalizer_one hch.zero, hch.base, sup_eq_right.mpr hAT,
        ABGLocalTools.isSylowOf_iff, relIndex_top_right] at hP
      exact ⟨hT2.toSylow hP.2.2, IsPGroup.toSylow_coe _ _⟩
    · exact hk
  ·
    have hz2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hVeq : C (k + 1) ⊔ (C k ⊔ zpowers t) = C (k + 1) ⊔ zpowers t := by
      rw [← sup_assoc, sup_eq_left.mpr (hch.mono k (by omega))]
    have hV2 : IsPGroup 2 (C (k + 1) ⊔ (C k ⊔ zpowers t) : Subgroup G) := by
      rw [hVeq]
      exact IsPGroup.to_sup_of_normal_left' hU2 hz2 (zpowers_le.mpr (hch.t_norm (k + 1) le_rfl))
    have hV1 : C (k + 1) ⊔ (C k ⊔ zpowers t) ≠ ⊥ := fun h1 =>
      ht1 (by
        have h2 : t ∈ C (k + 1) ⊔ (C k ⊔ zpowers t) := mem_sup_right htR
        rwa [h1, mem_bot] at h2)
    have hcat := catalog_of_relImg (N := pushNormalizer C (k + 1)) (W := C k)
      (V := C (k + 1) ⊔ (C k ⊔ zpowers t)) hnab hK (le_sup_left.trans le_sup_right)
      (sup_le hUN hRN) hV2 hV1
      (R' := relImg (pushNormalizer C (k + 1)) (C k) (C k ⊔ zpowers t)) (relImg_sup hUN hRN).symm
    rcases hHKS _ _ _ _ _ _ hS h3 hcat with hE | ⟨hf3, hproj⟩
    · right
      obtain ⟨Up, hUUp, hUpN, hUpNU, hsq, hcomm, hc, hker, honto, hRUp, hPUp, hXUp, hnext⟩ :=
        hst.step hnsyl hE
      have hnew := hnext _ rfl
      have hN'le : Up ≤ pushNormalizer C (k + 1) ⊓ normalizer (C (k + 1) : Set G) :=
        le_inf hUpN hUpNU
      have hUpcard : Nat.card Up = 2 ^ (f * (k + 2)) := by
        obtain ⟨hinst', -, -, -, -, -, -, -, -, hS'⟩ := id hnew
        have hS'' := @hS' hinst'
        have h1 := card_relImg_mul (N := pushNormalizer C (k + 1) ⊓ normalizer (C (k + 1) : Set G))
          (W := C (k + 1)) hUUp hN'le
        rw [hS''.1.2.2.2.2.1.2.2.2, hch.card (k + 1) le_rfl, ← pow_add] at h1
        rw [← h1]
        congr 1
        ring
      have hdXU : d ∈ X ⊓ normalizer (C (k + 1) : Set G) :=
        mem_inf.mpr ⟨hdX, hch.d_norm (k + 1) le_rfl⟩
      obtain ⟨C', hC', hC'2⟩ : ∃ C' : ℕ → Subgroup G,
          (∀ j, j ≠ k + 2 → C' j = C j) ∧ C' (k + 2) = Up :=
        ⟨fun j => if j = k + 2 then Up else C j, fun j hj => by simp [hj], by simp⟩
      have hext := hch.extend Up hUUp hUpcard hUpNU hsq hcomm (hRUp htR) (hc t htR htW)
        (hker t htR htW) (honto t htR htW) (hXUp hdXU) (le_sup_right.trans hPUp) C' hC' hC'2
      refine ⟨C', Up ⊔ (X ⊓ normalizer (C (k + 1) : Set G)), hext, mem_sup_right hdXU, ?_⟩
      have hN' : pushNormalizer C' (k + 1 + 1) =
          pushNormalizer C (k + 1) ⊓ normalizer (C (k + 1) : Set G) := by
        rw [pushNormalizer_congr (C' := C) (fun j hj => hC' j (by omega)), pushNormalizer_succ]
      rw [show k + 1 + 1 = k + 2 from rfl, hC'2, hC' (k + 1) (by omega), hN']
      have hP' : Up ⊔ (C (k + 1) ⊔ T) = Up ⊔ T := by rw [← sup_assoc, sup_eq_left.mpr hUUp]
      rw [hVeq, hP'] at hnew
      exact hnew
    · left; right
      exact ⟨hf3, by intro _; exact hproj⟩

end Step

end CFSG.SeitzReduction.RankOne
