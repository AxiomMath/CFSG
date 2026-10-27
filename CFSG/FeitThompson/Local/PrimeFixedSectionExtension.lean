module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.InvariantMaximalPrimeSubgroupsConjugate
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.FixedFreeComplementsInvariantSections
import CFSG.FeitThompson.Foundations.NormalContainsMinimalNormal
import CFSG.FeitThompson.Local.SolvableKernelFixedFreePrimeNilpotent
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise

variable {X : Type*} [Group X] {I S : Subgroup X}

abbrev normalizerQuotient (I : Subgroup X) : Type _ :=
  ↥(normalizer (I : Set X)) ⧸ I.subgroupOf (normalizer (I : Set X))

def normalizerQuotientMap (I S : Subgroup X) : Subgroup (normalizerQuotient I) :=
  (S.subgroupOf (normalizer (I : Set X))).map (mk' (I.subgroupOf (normalizer (I : Set X))))

def ofNormalizerQuotient (I : Subgroup X) (M : Subgroup (normalizerQuotient I)) : Subgroup X :=
  (M.comap (mk' (I.subgroupOf (normalizer (I : Set X))))).map (normalizer (I : Set X)).subtype

theorem mem_ofNormalizerQuotient_iff {M : Subgroup (normalizerQuotient I)} {x : X} :
    x ∈ ofNormalizerQuotient I M ↔ ∃ hxN : x ∈ normalizer (I : Set X),
      (QuotientGroup.mk ⟨x, hxN⟩ : normalizerQuotient I) ∈ M :=
  ⟨fun ⟨⟨_, hyN⟩, hy, hyx⟩ => hyx ▸ ⟨hyN, hy⟩, fun ⟨hxN, hx⟩ => ⟨⟨x, hxN⟩, hx, rfl⟩⟩

theorem mk_mem_ofNormalizerQuotient_iff {M : Subgroup (normalizerQuotient I)} {x : X}
    (hxN : x ∈ normalizer (I : Set X)) :
    x ∈ ofNormalizerQuotient I M ↔ (QuotientGroup.mk ⟨x, hxN⟩ : normalizerQuotient I) ∈ M := by
  rw [mem_ofNormalizerQuotient_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hxN, h⟩⟩

theorem ofNormalizerQuotient_le_normalizer (I : Subgroup X) (M : Subgroup (normalizerQuotient I)) :
    ofNormalizerQuotient I M ≤ normalizer (I : Set X) :=
  Subgroup.map_subtype_le _

theorem le_ofNormalizerQuotient (I : Subgroup X) (M : Subgroup (normalizerQuotient I)) :
    I ≤ ofNormalizerQuotient I M := fun x hx =>
  (mk_mem_ofNormalizerQuotient_iff (le_normalizer hx)).2 <| by
    rw [show (QuotientGroup.mk ⟨x, le_normalizer hx⟩ : normalizerQuotient I) = 1 from
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hx)]
    exact one_mem _

theorem mk_mem_normalizerQuotientMap_iff {x : X} (hxN : x ∈ normalizer (I : Set X)) :
    (QuotientGroup.mk ⟨x, hxN⟩ : normalizerQuotient I) ∈ normalizerQuotientMap I S ↔
      ∃ y ∈ S, ∃ hyN : y ∈ normalizer (I : Set X),
        (QuotientGroup.mk ⟨y, hyN⟩ : normalizerQuotient I) = QuotientGroup.mk ⟨x, hxN⟩ :=
  ⟨fun ⟨⟨y, hyN⟩, hy, hyz⟩ => ⟨y, mem_subgroupOf.1 hy, hyN, hyz⟩,
    fun ⟨y, hy, hyN, hyz⟩ => ⟨⟨y, hyN⟩, mem_subgroupOf.2 hy, hyz⟩⟩

theorem normalizerQuotientMap_eq_bot_iff (hSN : S ≤ normalizer (I : Set X)) :
    normalizerQuotientMap I S = ⊥ ↔ S ≤ I := by
  rw [normalizerQuotientMap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact ⟨fun hle x hx =>
      mem_subgroupOf.1 (hle (mem_subgroupOf.2 hx : (⟨x, hSN hx⟩ : ↥(normalizer (I : Set X))) ∈ _)),
    fun hle _ hx => mem_subgroupOf.2 (hle (mem_subgroupOf.1 hx))⟩

theorem normalizerQuotientMap_mono {S₁ S₂ : Subgroup X} (h : S₁ ≤ S₂) :
    normalizerQuotientMap I S₁ ≤ normalizerQuotientMap I S₂ :=
  Subgroup.map_mono fun _ hx => h hx

theorem normalizerQuotientMap_ofNormalizerQuotient (M : Subgroup (normalizerQuotient I)) :
    normalizerQuotientMap I (ofNormalizerQuotient I M) = M := by
  ext z
  induction z using QuotientGroup.induction_on with
  | _ y =>
    rw [show (QuotientGroup.mk y : normalizerQuotient I) = QuotientGroup.mk ⟨(y : X), y.2⟩ from rfl,
      mk_mem_normalizerQuotientMap_iff y.2]
    exact ⟨fun ⟨_, hw, hwN, hwz⟩ => hwz ▸ (mk_mem_ofNormalizerQuotient_iff hwN).1 hw,
      fun hy => ⟨(y : X), (mk_mem_ofNormalizerQuotient_iff y.2).2 hy, y.2, rfl⟩⟩

theorem ofNormalizerQuotient_le_of_le {T : Subgroup X} {M : Subgroup (normalizerQuotient I)}
    (h : M ≤ normalizerQuotientMap I T) (hIT : I ≤ T) : ofNormalizerQuotient I M ≤ T := by
  intro x hx
  obtain ⟨hxN, hxM⟩ := mem_ofNormalizerQuotient_iff.1 hx
  obtain ⟨y, hy, _, hyz⟩ := (mk_mem_normalizerQuotientMap_iff hxN).1 (h hxM)
  rw [QuotientGroup.eq, mem_subgroupOf] at hyz
  have hmem : y⁻¹ * x ∈ I := hyz
  rw [show x = y * (y⁻¹ * x) by group]
  exact T.mul_mem hy (hIT hmem)

theorem lt_ofNormalizerQuotient {M : Subgroup (normalizerQuotient I)} (hM : M ≠ ⊥) :
    I < ofNormalizerQuotient I M := by
  refine (le_ofNormalizerQuotient I M).lt_of_ne fun heq => hM ?_
  rw [← normalizerQuotientMap_ofNormalizerQuotient M, ← heq, normalizerQuotientMap,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem normalizer_le_normalizer_ofNormalizerQuotient {M : Subgroup (normalizerQuotient I)}
    (hM : M.Normal) :
    normalizer (I : Set X) ≤ normalizer ((ofNormalizerQuotient I M : Subgroup X) : Set X) := by
  refine le_normalizer_iff.2 fun g hg x hx => ?_
  obtain ⟨hxN, hxM⟩ := mem_ofNormalizerQuotient_iff.1 hx
  have hgxN : g * x * g⁻¹ ∈ normalizer (I : Set X) := mul_mem (mul_mem hg hxN) (inv_mem hg)
  refine (mk_mem_ofNormalizerQuotient_iff hgxN).2 ?_
  have heq : (QuotientGroup.mk ⟨g * x * g⁻¹, hgxN⟩ : normalizerQuotient I)
      = (QuotientGroup.mk ⟨g, hg⟩ : normalizerQuotient I) *
        (QuotientGroup.mk ⟨x, hxN⟩ : normalizerQuotient I) *
        (QuotientGroup.mk ⟨g, hg⟩ : normalizerQuotient I)⁻¹ := by
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    rfl
  rw [heq]
  exact hM.conj_mem _ hxM _

theorem isPGroup_normalizerQuotientMap {q : ℕ} (hSN : S ≤ normalizer (I : Set X))
    (hS : IsPGroup q ↥S) : IsPGroup q ↥(normalizerQuotientMap I S) := by
  have h1 : IsPGroup q ↥(S.subgroupOf (normalizer (I : Set X))) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  intro z
  obtain ⟨y, hy, hyz⟩ := z.2
  obtain ⟨k, hk⟩ := h1 ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hval : (y : ↥(normalizer (I : Set X))) ^ q ^ k = 1 := by
    simpa using congrArg (Subtype.val (p := (· ∈ S.subgroupOf (normalizer (I : Set X))))) hk
  rw [SubgroupClass.coe_pow, ← hyz, ← map_pow, hval, map_one]
  rfl

theorem lt_inf_normalizer_of_isPGroup [Finite X] {q : ℕ} (hq : q.Prime) {Q : Subgroup X}
    (hQ : IsPGroup q ↥Q) (hIQ : I < Q) : I < Q ⊓ normalizer (I : Set X) := by
  have h := card_lt_card_inf_normalizer_of_isPGroup hq hQ hIQ
  refine lt_of_le_of_ne (le_inf hIQ.le le_normalizer) fun heq => ?_
  rw [← heq] at h
  exact absurd h (lt_irrefl _)

theorem subgroupOf_inf_normalizer_eq {Q : Subgroup X} :
    (Q ⊓ normalizer (I : Set X)).subgroupOf (normalizer (I : Set X))
      = Q.subgroupOf (normalizer (I : Set X)) := by
  ext x
  simp [mem_subgroupOf]

instance normal_subgroupOf_inf_normalizer {Q : Subgroup X} [Q.Normal] :
    ((Q ⊓ normalizer (I : Set X)).subgroupOf (normalizer (I : Set X))).Normal := by
  rw [subgroupOf_inf_normalizer_eq]
  infer_instance

theorem isElementaryAbelian_of_isPGroup_of_forall_normal_lt_eq_bot {G : Type*} [Group G] [Finite G]
    {q : ℕ} (hq : q.Prime) {M : Subgroup G} [M.Normal] [Group.IsSolvable ↥M] (hMbot : M ≠ ⊥)
    (hMmin : ∀ K : Subgroup G, K.Normal → K < M → K = ⊥) (hMq : IsPGroup q ↥M) :
    IsElementaryAbelian q M := by
  have hcomm : IsMulCommutative ↥M :=
    isMulCommutative_of_isSolvable_of_forall_normal_lt_eq_bot hMbot hMmin
  obtain ⟨p, hp, hexp⟩ :=
    exists_prime_forall_pow_eq_one_of_isSolvable_of_forall_normal_lt_eq_bot hMbot hMmin
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).2 hMbot
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥M)
  have hord : orderOf x = p :=
    ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hexp x))).resolve_left
      (by simpa [orderOf_eq_one_iff] using hx)
  obtain ⟨k, hk⟩ := hMq x
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1
    (hp.dvd_of_dvd_pow (hord ▸ orderOf_dvd_of_pow_eq_one hk))
  rw [isElementaryAbelian_iff]
  refine ⟨hcomm, fun y hy => ?_⟩
  rw [← hpq]
  simpa using congrArg (Subtype.val (p := fun z : G => z ∈ M)) (hexp ⟨y, hy⟩)

theorem mem_of_forall_inv_mul_conj_mem_of_inf_centralizer_le [Finite X] {T I R : Subgroup X}
    [Group.IsSolvable ↥T] [Group.IsSolvable ↥R] (hcop : (Nat.card ↥R).Coprime (Nat.card ↥T))
    (hTI : T ≤ normalizer (I : Set X)) (hRT : R ≤ normalizer (T : Set X))
    (hRI : R ≤ normalizer (I : Set X)) (hC : T ⊓ centralizer (R : Set X) ≤ I) {x : X} (hx : x ∈ T)
    (hfix : ∀ r ∈ R, x⁻¹ * (r * x * r⁻¹) ∈ I) : x ∈ I := by
  have hIn : (I.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTI
  have hinv : IsInvariantSubgroup (conjOnNormalized T hRT) (I.subgroupOf T) :=
    isInvariantSubgroup_subgroupOf hRT hRI
  have hfixed : FixedPoints.subgroup (conjOnNormalized T hRT).range ↥T ≤ I.subgroupOf T := by
    intro y hy
    rw [mem_fixedPoints_range_iff] at hy
    rw [mem_subgroupOf]
    refine hC (Subgroup.mem_inf.2 ⟨y.2, ?_⟩)
    rw [mem_centralizer_iff]
    intro g hg
    have h := congrArg (Subtype.val (p := fun z : X => z ∈ T)) (hy ⟨g, hg⟩)
    rw [conjOnNormalized_apply_coe] at h
    calc g * (y : X) = g * (y : X) * g⁻¹ * g := by group
      _ = (y : X) * g := by rw [h]
  have hbot : FixedPoints.subgroup hinv.quotientAut.range (↥T ⧸ I.subgroupOf T) = ⊥ := by
    rw [fixedPoints_quotientAut_range hinv hcop, eq_bot_iff]
    calc Subgroup.map (mk' (I.subgroupOf T)) (FixedPoints.subgroup _ ↥T)
        ≤ Subgroup.map (mk' (I.subgroupOf T)) (I.subgroupOf T) := Subgroup.map_mono hfixed
      _ = ⊥ := by rw [QuotientGroup.map_mk'_self]
  have hmem : (QuotientGroup.mk ⟨x, hx⟩ : ↥T ⧸ I.subgroupOf T) ∈
      FixedPoints.subgroup hinv.quotientAut.range (↥T ⧸ I.subgroupOf T) := by
    rw [mem_fixedPoints_range_iff]
    intro b
    rw [hinv.quotientAut_mk, QuotientGroup.eq, mem_subgroupOf]
    have h : ((conjOnNormalized T hRT b ⟨x, hx⟩ : ↥T)⁻¹ * ⟨x, hx⟩ : ↥T)
        = (x⁻¹ * ((b : X) * x * (b : X)⁻¹))⁻¹ := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, conjOnNormalized_apply_coe]
      group
    rw [h]
    exact I.inv_mem (hfix b b.2)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_subgroupOf] at hmem
  exact hmem

theorem exists_lt_le_inf_normalizer_minimal_normal [Finite X] [Group.IsSolvable X] {q : ℕ}
    (hq : q.Prime) {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup q ↥Q) (hIQ : I < Q) :
    ∃ T : Subgroup X, T ≤ Q ⊓ normalizer (I : Set X) ∧ I < T ∧
      normalizer (I : Set X) ≤ normalizer (T : Set X) ∧
      (normalizerQuotientMap I T).Normal ∧ normalizerQuotientMap I T ≠ ⊥ ∧
      IsElementaryAbelian q (normalizerQuotientMap I T) ∧
      (∀ M : Subgroup (normalizerQuotient I), M.Normal →
        M < normalizerQuotientMap I T → M = ⊥) := by
  have hIN : I < Q ⊓ normalizer (I : Set X) := lt_inf_normalizer_of_isPGroup hq hQ hIQ
  set N0 : Subgroup (normalizerQuotient I) :=
    normalizerQuotientMap I (Q ⊓ normalizer (I : Set X)) with hN0
  have hN0normal : N0.Normal := by
    rw [hN0, normalizerQuotientMap]
    exact (normal_subgroupOf_inf_normalizer (Q := Q) (I := I)).map _ (mk'_surjective _)
  have hN0q : IsPGroup q ↥N0 :=
    isPGroup_normalizerQuotientMap inf_le_right (hQ.to_le inf_le_left)
  have hN0bot : N0 ≠ ⊥ := by
    rw [hN0, Ne, normalizerQuotientMap_eq_bot_iff inf_le_right]
    exact fun h => hIN.ne (le_antisymm hIN.le h)
  obtain ⟨M, hMnormal, hMbot, hMN0, hMmin⟩ :=
    exists_normal_ne_bot_le_forall_lt_eq_bot hN0normal hN0bot
  have : M.Normal := hMnormal
  have hMq : IsPGroup q ↥M := hN0q.to_le hMN0
  refine ⟨ofNormalizerQuotient I M, ofNormalizerQuotient_le_of_le hMN0 hIN.le,
    lt_ofNormalizerQuotient hMbot, normalizer_le_normalizer_ofNormalizerQuotient hMnormal,
    ?_, ?_, ?_, ?_⟩
  · rw [normalizerQuotientMap_ofNormalizerQuotient]; exact hMnormal
  · rw [normalizerQuotientMap_ofNormalizerQuotient]; exact hMbot
  · rw [normalizerQuotientMap_ofNormalizerQuotient]
    exact isElementaryAbelian_of_isPGroup_of_forall_normal_lt_eq_bot hq hMbot hMmin hMq
  · rw [normalizerQuotientMap_ofNormalizerQuotient]; exact hMmin

structure IsPrimeFixedSectionSetup (X : Type*) [Group X] (q : ℕ) (Q D K Z : Subgroup X) : Prop where
  prime : q.Prime
  odd_natCard : Odd (Nat.card X)
  isSolvable : Group.IsSolvable X
  normal_Q : Q.Normal
  isPGroup_Q : IsPGroup q ↥Q
  coe_mul_coe : (Q : Set X) * ((D ⊔ K : Subgroup X) : Set X) = Set.univ
  inf_Q_sup : Q ⊓ (D ⊔ K) = ⊥
  normal_D : (D.subgroupOf (D ⊔ K)).Normal
  inf_D_K : D ⊓ K = ⊥
  coprime_Q : (Nat.card ↥Q).Coprime (Nat.card ↥(D ⊔ K))
  coprime_D_K : (Nat.card ↥D).Coprime (Nat.card ↥K)
  D_ne_bot : D ≠ ⊥
  K_ne_bot : K ≠ ⊥
  inf_centralizer_D : ∀ k ∈ K, k ≠ 1 → D ⊓ centralizer ({k} : Set X) = ⊥
  inf_centralizer_Q : ∀ k ∈ K, k ≠ 1 → Q ⊓ centralizer ({k} : Set X) = Z
  Z_eq : Z = Q ⊓ centralizer (K : Set X)
  natCard_Z : Nat.card ↥Z = q

namespace IsPrimeFixedSectionSetup

variable {q : ℕ} {Q D K Z : Subgroup X}

theorem finite (h : IsPrimeFixedSectionSetup X q Q D K Z) : Finite X :=
  Nat.finite_of_card_ne_zero fun h0 => by simpa [h0, Nat.odd_iff] using h.odd_natCard

theorem Z_le_Q (h : IsPrimeFixedSectionSetup X q Q D K Z) : Z ≤ Q := by
  rw [h.Z_eq]
  exact inf_le_left

theorem Z_ne_bot (h : IsPrimeFixedSectionSetup X q Q D K Z) : Z ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card ↥Z = q := h.natCard_Z
  rw [hbot] at hcard
  simp only [Subgroup.card_bot] at hcard
  have := h.prime.one_lt
  omega

theorem sup_le_normalizer_Q (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    (D ⊔ K : Subgroup X) ≤ normalizer (Q : Set X) := by
  have := h.normal_Q
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem coe_sup_D_K (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    ((D ⊔ K : Subgroup X) : Set X) = (D : Set X) * (K : Set X) :=
  haveI := h.normal_D
  Subgroup.coe_mul_of_right_le_normalizer_left D K
    (le_trans le_sup_right
      (Subgroup.le_normalizer_of_normal_subgroupOf (H := D) (K := D ⊔ K) le_sup_left))

theorem sup_le_normalizer_D (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    (D ⊔ K : Subgroup X) ≤ normalizer (D : Set X) :=
  haveI := h.normal_D
  Subgroup.le_normalizer_of_normal_subgroupOf (H := D) (K := D ⊔ K) le_sup_left

theorem eq_one_of_mem_Q_of_mem_sup (h : IsPrimeFixedSectionSetup X q Q D K Z) {g : X}
    (hgQ : g ∈ Q) (hg : g ∈ (D ⊔ K : Subgroup X)) : g = 1 := by
  have hmem : g ∈ Q ⊓ (D ⊔ K) := Subgroup.mem_inf.2 ⟨hgQ, hg⟩
  rwa [h.inf_Q_sup, Subgroup.mem_bot] at hmem

theorem inf_sup_Q_D_K_eq_bot (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    (Q ⊔ D : Subgroup X) ⊓ K = ⊥ := by
  have := h.normal_Q
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  obtain ⟨hgQD, hgK⟩ := Subgroup.mem_inf.1 hg
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgQD
  obtain ⟨u, hu, d, hd, rfl⟩ := hgQD
  simp only [SetLike.mem_coe] at hu hd
  have hu1 : u = 1 := by
    refine h.eq_one_of_mem_Q_of_mem_sup hu ?_
    have hrw : u = (u * d) * d⁻¹ := by group
    rw [hrw]
    exact mul_mem (Subgroup.mem_sup_right hgK) (inv_mem (Subgroup.mem_sup_left hd))
  subst hu1
  have hmem : d ∈ D ⊓ K := Subgroup.mem_inf.2 ⟨hd, by simpa using hgK⟩
  rw [h.inf_D_K, Subgroup.mem_bot] at hmem
  simp [hmem]

theorem exists_mem_K_prime_orderOf (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    ∃ (r : X) (p : ℕ), r ∈ K ∧ p.Prime ∧ orderOf r = p := by
  have : Finite X := h.finite
  have hK : Nat.card ↥K ≠ 1 := fun hcon => h.K_ne_bot (Subgroup.card_eq_one.1 hcon)
  obtain ⟨p, hp, hpd⟩ := (Nat.card ↥K).exists_prime_and_dvd hK
  obtain ⟨r, hr, hro⟩ := exists_mem_orderOf_eq_of_dvd (H := K) hp hpd
  exact ⟨r, p, hr, hp, hro⟩

end IsPrimeFixedSectionSetup

theorem inf_eq_bot_or_le_of_natCard_eq_prime {q : ℕ} (hq : q.Prime) {Z : Subgroup X}
    (hZ : Nat.card ↥Z = q) (S : Subgroup X) : Z ⊓ S = ⊥ ∨ Z ≤ S := by
  have : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZ]; exact hq.pos.ne')
  have hdvd : Nat.card ↥(Z ⊓ S) ∣ q := hZ ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hq).1 hdvd with h1 | h1
  · exact Or.inl (Subgroup.card_eq_one.1 h1)
  · exact Or.inr ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZ, h1])) ▸ inf_le_right)

theorem commutator_le_of_inf_centralizer_le_of_natCard_eq_prime [Finite X] [Group.IsSolvable X]
    {T D I R : Subgroup X} {p : ℕ} (hp : p.Prime) (hRcard : Nat.card ↥R = p)
    (hIT : I ≤ T) (hTNI : T ≤ normalizer (I : Set X)) (hDNI : D ≤ normalizer (I : Set X))
    (hRNI : R ≤ normalizer (I : Set X)) (hDNT : D ≤ normalizer (T : Set X))
    (hRNT : R ≤ normalizer (T : Set X)) (hRND : R ≤ normalizer (D : Set X))
    (hTD : T ⊓ D = ⊥) (hTDR : (T ⊔ D) ⊓ R = ⊥) (hDR : D ⊓ centralizer (R : Set X) = ⊥)
    (hcop : (Nat.card ↥T).Coprime (Nat.card ↥D))
    (hcopR : (Nat.card ↥R).Coprime (Nat.card ↥T))
    (hTR : T ⊓ centralizer (R : Set X) ≤ I) :
    ⁅T, D⁆ ≤ I := by
  set A : Subgroup X := T ⊔ D with hAdef
  set V : Subgroup X := A ⊔ R with hVdef
  have hTA : T ≤ A := le_sup_left
  have hDA : D ≤ A := le_sup_right
  have hAV : A ≤ V := le_sup_left
  have hRV : R ≤ V := le_sup_right
  have hTV : T ≤ V := hTA.trans hAV
  have hDV : D ≤ V := hDA.trans hAV
  have hIA : I ≤ A := hIT.trans hTA
  have hRNA : R ≤ normalizer (A : Set X) := le_normalizer_sup hRNT hRND
  have hVNI : V ≤ normalizer (I : Set X) := sup_le (sup_le hTNI hDNI) hRNI
  have hVNA : V ≤ normalizer (A : Set X) := sup_le le_normalizer hRNA
  have hconjT : ∀ g ∈ R, ∀ t ∈ T, g * t * g⁻¹ ∈ T := le_normalizer_iff.1 hRNT
  have hconjD : ∀ g ∈ R, ∀ d ∈ D, g * d * g⁻¹ ∈ D := le_normalizer_iff.1 hRND
  have hconjDT : ∀ g ∈ D, ∀ t ∈ T, g * t * g⁻¹ ∈ T := le_normalizer_iff.1 hDNT
  have hIn : (I.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer hVNI
  set W := ↥V ⧸ I.subgroupOf V with hW
  set φ : ↥V →* W := mk' (I.subgroupOf V) with hφ
  have hφsurj : Function.Surjective φ := mk'_surjective _
  have hker : ∀ v : ↥V, φ v = 1 ↔ (v : X) ∈ I := fun v => by
    rw [hφ, mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have heqφ : ∀ u v : ↥V, φ u = φ v ↔ ((u : X))⁻¹ * (v : X) ∈ I := by
    intro u v
    rw [hφ, mk'_apply, mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    push_cast
    rfl
  set Abar : Subgroup W := (A.subgroupOf V).map φ with hAbar
  set Tbar : Subgroup W := (T.subgroupOf V).map φ with hTbar
  set Dbar : Subgroup W := (D.subgroupOf V).map φ with hDbar
  set Rbar : Subgroup W := (R.subgroupOf V).map φ with hRbar
  have hAbarNormal : Abar.Normal := (normal_subgroupOf_of_le_normalizer hVNA).map φ hφsurj
  have hCbot : Abar ⊓ centralizer (Rbar : Set W) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 ?_
    rintro z ⟨⟨v, hv, hvz⟩, hzC⟩
    simp only [SetLike.mem_coe, mem_subgroupOf] at hv
    have hvTD : (v : X) ∈ (T : Set X) * (D : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left T D hDNT]; exact hv
    obtain ⟨t, ht, d, hd, htd⟩ := hvTD
    simp only [SetLike.mem_coe] at ht hd
    simp only at htd
    have hfix : ∀ r ∈ R, ((v : X))⁻¹ * (r * (v : X) * r⁻¹) ∈ I := by
      intro r hr
      have hrV : r ∈ V := hRV hr
      have hrRbar : φ ⟨r, hrV⟩ ∈ Rbar := ⟨⟨r, hrV⟩, mem_subgroupOf.2 hr, rfl⟩
      have hcomm : φ (⟨r, hrV⟩ : ↥V) * z = z * φ (⟨r, hrV⟩ : ↥V) :=
        (mem_centralizer_iff.1 hzC) _ hrRbar
      have hrvr : (r : X) * (v : X) * r⁻¹ ∈ V := mul_mem (mul_mem hrV v.2) (inv_mem hrV)
      have hstep : φ v = φ (⟨r * (v : X) * r⁻¹, hrvr⟩ : ↥V) := by
        have hcast : (⟨r * (v : X) * r⁻¹, hrvr⟩ : ↥V)
            = (⟨r, hrV⟩ : ↥V) * v * (⟨r, hrV⟩ : ↥V)⁻¹ := by ext; push_cast; rfl
        rw [hcast, map_mul, map_mul, map_inv, hvz, hcomm]
        simp
      simpa using (heqφ v ⟨r * (v : X) * r⁻¹, hrvr⟩).1 hstep
    have hdfix : d ∈ centralizer (R : Set X) := by
      rw [mem_centralizer_iff]
      intro r hr
      have hmem := hfix r hr
      rw [← htd] at hmem
      have hrt : r * t * r⁻¹ ∈ T := hconjT r hr t ht
      have hrd : r * d * r⁻¹ ∈ D := hconjD r hr d hd
      have hcd : d⁻¹ * (t⁻¹ * (r * t * r⁻¹)) * d ∈ T := by
        simpa using hconjDT d⁻¹ (inv_mem hd) _ (mul_mem (inv_mem ht) hrt)
      have hkey : d⁻¹ * (r * d * r⁻¹) ∈ T := by
        have hrw : d⁻¹ * (r * d * r⁻¹)
            = (d⁻¹ * (t⁻¹ * (r * t * r⁻¹)) * d)⁻¹ * ((t * d)⁻¹ * (r * (t * d) * r⁻¹)) := by
          group
        rw [hrw]
        exact mul_mem (inv_mem hcd) (hIT hmem)
      have hbot : d⁻¹ * (r * d * r⁻¹) ∈ T ⊓ D :=
        Subgroup.mem_inf.2 ⟨hkey, mul_mem (inv_mem hd) hrd⟩
      rw [hTD, Subgroup.mem_bot] at hbot
      have hrdr : r * d * r⁻¹ = d := by
        have h2 := congrArg (fun x => d * x) hbot
        simpa only [mul_inv_cancel_left, mul_one] using h2
      calc r * d = (r * d * r⁻¹) * r := by group
        _ = d * r := by rw [hrdr]
    have hd1 : d = 1 := by
      have hmem : d ∈ D ⊓ centralizer (R : Set X) := Subgroup.mem_inf.2 ⟨hd, hdfix⟩
      rwa [hDR, Subgroup.mem_bot] at hmem
    have hvT : (v : X) ∈ T := by rw [← htd, hd1, mul_one]; exact ht
    have hvI : (v : X) ∈ I :=
      mem_of_forall_inv_mul_conj_mem_of_inf_centralizer_le hcopR hTNI hRNT hRNI hTR hvT hfix
    rw [← hvz]
    exact (hker v).2 hvI
  have hsup : Abar ⊔ Rbar = ⊤ := by
    rw [hAbar, hRbar, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hAV hRV, ← hVdef,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ hφsurj]
  have hprod : (Abar : Set W) * (Rbar : Set W) = Set.univ := by
    rw [← Subgroup.normal_mul Abar Rbar, hsup]; rfl
  have hAbarRbar : Abar ⊓ Rbar = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 ?_
    rintro z ⟨hzA, ⟨s, hs, hzs⟩⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hs
    rw [← hzs] at hzA ⊢
    obtain ⟨u, hu, huz⟩ := hzA
    rw [SetLike.mem_coe, mem_subgroupOf] at hu
    have heq : ((u : X))⁻¹ * (s : X) ∈ I := (heqφ u s).1 huz
    have hsA : (s : X) ∈ A := by
      have hrw : (s : X) = (u : X) * (((u : X))⁻¹ * (s : X)) := by group
      rw [hrw]; exact mul_mem hu (hIA heq)
    have hmem : (s : X) ∈ A ⊓ R := Subgroup.mem_inf.2 ⟨hsA, hs⟩
    rw [hAdef, hTDR, Subgroup.mem_bot] at hmem
    exact (hker s).2 (hmem ▸ one_mem I)
  have hRbarcard : Nat.card ↥Rbar = p := by
    have hdvd : Nat.card ↥Rbar ∣ p := by
      rw [← hRcard, hRbar]
      exact dvd_trans (Subgroup.card_map_dvd _ _)
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv ▸ dvd_rfl)
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exfalso
      rw [Subgroup.card_eq_one] at h1
      have hRbot : R = ⊥ := by
        refine le_antisymm (fun x hx => ?_) bot_le
        have hxI : φ ⟨x, hRV hx⟩ ∈ Rbar := ⟨⟨x, hRV hx⟩, mem_subgroupOf.2 hx, rfl⟩
        rw [h1, Subgroup.mem_bot] at hxI
        have hmm : x ∈ A ⊓ R := Subgroup.mem_inf.2 ⟨hIA ((hker _).1 hxI), hx⟩
        rw [hAdef, hTDR] at hmm
        exact hmm
      rw [hRbot, Subgroup.card_bot] at hRcard
      exact hp.one_lt.ne hRcard
    · exact h1
  have hnil : Group.IsNilpotent ↥Abar :=
    isNilpotent_of_isSolvable_of_natCard_eq_prime hprod hAbarRbar hp hRbarcard hCbot
  have hTAbar : Tbar ≤ Abar :=
    Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hTA (mem_subgroupOf.1 hx))
  have hDAbar : Dbar ≤ Abar :=
    Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hDA (mem_subgroupOf.1 hx))
  have hTbardvd : Nat.card ↥Tbar ∣ Nat.card ↥T :=
    dvd_trans (Subgroup.card_map_dvd _ _)
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTV).toEquiv ▸ dvd_rfl)
  have hDbardvd : Nat.card ↥Dbar ∣ Nat.card ↥D :=
    dvd_trans (Subgroup.card_map_dvd _ _)
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDV).toEquiv ▸ dvd_rfl)
  have hcent : Tbar ≤ centralizer (Dbar : Set W) :=
    le_centralizer_of_coprime_natCard_of_isNilpotent Abar hnil hTAbar hDAbar
      ((hcop.coprime_dvd_left hTbardvd).coprime_dvd_right hDbardvd)
  rw [Subgroup.commutator_le]
  intro t ht d hd
  rw [commutatorElement_def]
  have hφt : φ ⟨t, hTV ht⟩ ∈ Tbar := ⟨⟨t, hTV ht⟩, mem_subgroupOf.2 ht, rfl⟩
  have hφd : φ ⟨d, hDV hd⟩ ∈ Dbar := ⟨⟨d, hDV hd⟩, mem_subgroupOf.2 hd, rfl⟩
  have hcomm := (mem_centralizer_iff.1 (hcent hφt)) _ hφd
  have htd : t * d * t⁻¹ * d⁻¹ ∈ V :=
    mul_mem (mul_mem (mul_mem (hTV ht) (hDV hd)) (inv_mem (hTV ht))) (inv_mem (hDV hd))
  refine (hker ⟨t * d * t⁻¹ * d⁻¹, htd⟩).1 ?_
  have hcast : (⟨t * d * t⁻¹ * d⁻¹, htd⟩ : ↥V)
      = ⟨t, hTV ht⟩ * ⟨d, hDV hd⟩ * (⟨t, hTV ht⟩)⁻¹ * (⟨d, hDV hd⟩)⁻¹ := by
    ext; push_cast; rfl
  rw [hcast, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
  group

private theorem Z_le_and_inf_eq_bot_of_isPrimeFixedSectionSetup {q : ℕ} {Q D K Z : Subgroup X}
    (h : IsPrimeFixedSectionSetup X q Q D K Z) (hQ0 : Q ⊓ centralizer (D : Set X) < Q)
    {I : Subgroup X} (hIQ : I < Q) (hQ0I : Q ⊓ centralizer (D : Set X) ≤ I)
    (hDKI : (D ⊔ K : Subgroup X) ≤ normalizer (I : Set X)) {T : Subgroup X}
    (hTQ : T ≤ Q ⊓ normalizer (I : Set X)) (hIT : I < T)
    (hDKT : (D ⊔ K : Subgroup X) ≤ normalizer (T : Set X)) : Z ≤ T ∧ Z ⊓ I = ⊥ := by
  have hfin : Finite X := h.finite
  have hsolv : Group.IsSolvable X := h.isSolvable
  obtain ⟨r, p, hrK, hp, hro⟩ := h.exists_mem_K_prime_orderOf
  set R : Subgroup X := zpowers r with hRdef
  have hr1 : r ≠ 1 := fun hcon => hp.one_lt.ne' (by rw [← hro, hcon, orderOf_one])
  have hRK : R ≤ K := zpowers_le.2 hrK
  have hRcard : Nat.card ↥R = p := by rw [hRdef, Nat.card_zpowers, hro]
  have hRcentr : centralizer (R : Set X) = centralizer ({r} : Set X) := by
    rw [hRdef, zpowers_eq_closure, centralizer_closure]
  have hTQle : T ≤ Q := hTQ.trans inf_le_left
  have hTNI : T ≤ normalizer (I : Set X) := hTQ.trans inf_le_right
  have hDNI : D ≤ normalizer (I : Set X) := le_sup_left.trans hDKI
  have hKNI : K ≤ normalizer (I : Set X) := le_sup_right.trans hDKI
  have hDNT : D ≤ normalizer (T : Set X) := le_sup_left.trans hDKT
  have hKNT : K ≤ normalizer (T : Set X) := le_sup_right.trans hDKT
  have hKND : K ≤ normalizer (D : Set X) := le_sup_right.trans h.sup_le_normalizer_D
  have hRNI : R ≤ normalizer (I : Set X) := hRK.trans hKNI
  have hRNT : R ≤ normalizer (T : Set X) := hRK.trans hKNT
  have hRND : R ≤ normalizer (D : Set X) := hRK.trans hKND
  have hTD : T ⊓ D = ⊥ :=
    le_antisymm ((inf_le_inf hTQle (le_sup_left : D ≤ D ⊔ K)).trans h.inf_Q_sup.le) bot_le
  have hTDR : (T ⊔ D) ⊓ R = ⊥ :=
    le_antisymm ((inf_le_inf (sup_le (hTQle.trans le_sup_left) le_sup_right) hRK).trans
      h.inf_sup_Q_D_K_eq_bot.le) bot_le
  have hDR : D ⊓ centralizer (R : Set X) = ⊥ := by
    rw [hRcentr]; exact h.inf_centralizer_D r hrK hr1
  have hcop : (Nat.card ↥T).Coprime (Nat.card ↥D) :=
    (h.coprime_Q.coprime_dvd_left (Subgroup.card_dvd_of_le hTQle)).coprime_dvd_right
      (Subgroup.card_dvd_of_le le_sup_left)
  have hcopR : (Nat.card ↥R).Coprime (Nat.card ↥T) :=
    (h.coprime_Q.symm.coprime_dvd_left
      (Subgroup.card_dvd_of_le (hRK.trans le_sup_right))).coprime_dvd_right
      (Subgroup.card_dvd_of_le hTQle)
  have hTRZ : T ⊓ centralizer (R : Set X) ≤ Z := by
    rw [hRcentr, ← h.inf_centralizer_Q r hrK hr1]
    exact inf_le_inf_right _ hTQle
  have hkey : ¬ (T ⊓ centralizer (R : Set X) ≤ I) := by
    intro hTR
    have hcomm : ⁅T, D⁆ ≤ I :=
      commutator_le_of_inf_centralizer_le_of_natCard_eq_prime hp hRcard hIT.le hTNI hDNI hRNI
        hDNT hRNT hRND hTD hTDR hDR hcop hcopR hTR
    have hTI : T ≤ I :=
      le_of_commutator_le_of_inf_centralizer_le_of_coprime hDNT hcop.symm hcomm
        ((inf_le_inf_right _ hTQle).trans hQ0I)
    exact absurd (le_antisymm hTI hIT.le) hIT.ne'
  have hZI : Z ⊓ I = ⊥ := by
    rcases inf_eq_bot_or_le_of_natCard_eq_prime h.prime h.natCard_Z I with hbot | hle
    · exact hbot
    · exact absurd (hTRZ.trans hle) hkey
  have hZT : Z ≤ T := by
    rcases inf_eq_bot_or_le_of_natCard_eq_prime h.prime h.natCard_Z T with hbot | hle
    · refine absurd (fun x hx => ?_) hkey
      have hmem : x ∈ Z ⊓ T := Subgroup.mem_inf.2 ⟨hTRZ hx, (Subgroup.mem_inf.1 hx).1⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      rw [hmem]
      exact one_mem I
    · exact hle
  exact ⟨hZT, hZI⟩

theorem exists_le_inf_normalizer_isElementaryAbelian_minimal_normal {q : ℕ} {Q D K Z : Subgroup X}
    (h : IsPrimeFixedSectionSetup X q Q D K Z) (hQ0 : Q ⊓ centralizer (D : Set X) < Q)
    {I : Subgroup X} (hIQ : I < Q) (hQ0I : Q ⊓ centralizer (D : Set X) ≤ I)
    (hDKI : (D ⊔ K : Subgroup X) ≤ normalizer (I : Set X)) :
    ∃ T : Subgroup X, T ≤ Q ⊓ normalizer (I : Set X) ∧
      (D ⊔ K : Subgroup X) ≤ normalizer (T : Set X) ∧ I < T ∧ (I.subgroupOf T).Normal ∧
      (normalizerQuotientMap I T).Normal ∧ normalizerQuotientMap I T ≠ ⊥ ∧
      IsElementaryAbelian q (normalizerQuotientMap I T) ∧
      (∀ M : Subgroup (normalizerQuotient I), M.Normal →
        M < normalizerQuotientMap I T → M = ⊥) ∧
      Z ≤ T ∧ Z ⊓ I = ⊥ := by
  have : Finite X := h.finite
  have : Group.IsSolvable X := h.isSolvable
  have : Q.Normal := h.normal_Q
  obtain ⟨T, hTQ, hIT, hNT, hTnormal, hTbot, hTelem, hTmin⟩ :=
    exists_lt_le_inf_normalizer_minimal_normal h.prime h.isPGroup_Q hIQ
  have hDKT : (D ⊔ K : Subgroup X) ≤ normalizer (T : Set X) := le_trans hDKI hNT
  have hITnormal : (I.subgroupOf T).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_trans hTQ inf_le_right)
  obtain ⟨hZT, hZI⟩ :=
    Z_le_and_inf_eq_bot_of_isPrimeFixedSectionSetup h hQ0 hIQ hQ0I hDKI hTQ hIT hDKT
  exact ⟨T, hTQ, hDKT, hIT, hITnormal, hTnormal, hTbot, hTelem, hTmin, hZT, hZI⟩

end CFSG.FeitThompson
