module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
public import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
import CFSG.FeitThompson.OddOrder.PConfigChiefFactorLinearModel
import CFSG.FeitThompson.Local.FrobeniusWielandtKernelFixedFree
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.HighRankAbelianUniquenessCentralizers
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G}

section Transport

omit [Finite G]

variable {A B : Subgroup G}

private theorem disjoint_subgroupOf (M : Subgroup G) (h : Disjoint A B) :
    Disjoint (A.subgroupOf M) (B.subgroupOf M) := by
  rw [disjoint_iff, Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
    disjoint_iff.1 h]
  simp

private theorem subgroupOf_ne_bot (hAM : A ≤ M) (hA : A ≠ ⊥) : A.subgroupOf M ≠ ⊥ := by
  rw [Ne, Subgroup.subgroupOf_eq_bot]
  exact fun h => hA (by simpa [inf_eq_left.2 hAM] using h.eq_bot)

private theorem commutator_subgroupOf (hAM : A ≤ M) (hBM : B ≤ M) :
    ⁅A.subgroupOf M, B.subgroupOf M⁆ = (⁅A, B⁆ : Subgroup G).subgroupOf M := by
  have h : (⁅A.subgroupOf M, B.subgroupOf M⁆).map M.subtype = (⁅A, B⁆ : Subgroup G) := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAM,
      Subgroup.map_subgroupOf_eq_of_le hBM]
  have h2 := Subgroup.comap_map_eq_self_of_injective M.subtype_injective
    (⁅A.subgroupOf M, B.subgroupOf M⁆)
  rw [h] at h2
  exact h2.symm

private theorem centralizer_singleton_subgroupOf (b : M) :
    (Subgroup.centralizer {(b : G)}).subgroupOf M = Subgroup.centralizer {b} := by
  ext x
  simp [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subtype.ext_iff]

private theorem le_normalizer_subgroupOf (h : B ≤ Subgroup.normalizer (A : Set G)) :
    B.subgroupOf M ≤ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) := by
  intro b hb
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  have := (Subgroup.mem_set_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hb))) (y : G)
  simpa [Subgroup.mem_subgroupOf] using this

private theorem isNilpotent_subgroupOf (hAM : A ≤ M) [Group.IsNilpotent A] :
    Group.IsNilpotent (A.subgroupOf M) :=
  Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAM).symm

private theorem isCyclic_subgroupOf (hAM : A ≤ M) (h : IsCyclic A) :
    IsCyclic (A.subgroupOf M) :=
  isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hAM).symm.surjective

private theorem hallCore_subgroupOf (M : Subgroup G) :
    ((hallCore M).map M.subtype).subgroupOf M = hallCore M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

private theorem fittingRaw_subgroupOf [Finite G] (M : Subgroup G) :
    ((fittingRaw M).map M.subtype).subgroupOf M = fittingRaw M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

private theorem inf_centralizer_subgroupOf_eq_bot {K : Subgroup M} (hAM : A ≤ M)
    (h : K.map M.subtype ⊓ Subgroup.centralizer (A : Set G) = ⊥) :
    K ⊓ Subgroup.centralizer ((A.subgroupOf M : Subgroup M) : Set M) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxc⟩ := Subgroup.mem_inf.1 hx
  have h1 : (x : G) ∈ K.map M.subtype ⊓ Subgroup.centralizer (A : Set G) := by
    refine Subgroup.mem_inf.2 ⟨⟨x, hxK, rfl⟩, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxc (⟨g, hAM hg⟩ : M)
      (by simpa [Subgroup.mem_subgroupOf] using hg))
  rw [h, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (Subtype.ext h1)

end Transport

section PTypeConfig

open ChiefFactorFixedLine

variable {X : Type*} [Group X] {H J V B F W : Subgroup X}

theorem IsPTypeConfig.natCard_eq_natCard_pow_natCard (hc : IsPTypeConfig H J V B F W)
    (hCV : H ⊓ Subgroup.centralizer (V : Set X) = ⊥) :
    Nat.card H = Nat.card W ^ Nat.card B := by
  have := hc.finite
  have := hc.isSolvable
  have := hc.normal_H
  set A : Subgroup X := V ⊔ B with hA
  set ρ : ↥A →* MulAut ↥H := (MulAut.conjNormal (H := H)).comp A.subtype with hρ
  have hC : ∀ w ∈ B.subgroupOf A, w ≠ 1 →
      V.subgroupOf A ⊓ Subgroup.centralizer {w} = ⊥ := by
    intro w hw hw1
    rw [Subgroup.mem_subgroupOf] at hw
    rw [show w = (⟨(w : X), w.2⟩ : ↥A) from rfl, centralizer_subgroupOf w.2,
      hc.inf_centralizer_U_eq_bot (w : X) hw (fun hwe => hw1 (Subtype.ext hwe)),
      Subgroup.bot_subgroupOf]
  have hrange : ∀ D : Subgroup X, D ≤ A →
      FixedPoints.subgroup (ρ.comp (D.subgroupOf A).subtype).range ↥H
        = (H ⊓ Subgroup.centralizer (D : Set X)).subgroupOf H := fun D hD => by
    rw [hρ, range_comp_subgroupOf_subtype _ hD, fixedPoints_conjNormal_comp_subtype]
  have hCV' : FixedPoints.subgroup (ρ.comp (V.subgroupOf A).subtype).range ↥H = ⊥ := by
    rw [hrange V le_sup_left, hCV, Subgroup.bot_subgroupOf]
  have key := natCard_eq_natCard_fixedPoints_range_pow_natCard ρ hc.coprime_natCard_H_sup.symm
    hc.normal_subgroupOf_U_sup hc.isComplement'_subgroupOf_U_sup hC hCV'
  rwa [hrange B le_sup_right, hc.inf_centralizer_B_eq_W2, natCard_subgroupOf hc.le_H_W2,
    natCard_subgroupOf le_sup_right] at key

theorem IsPTypeConfig.nonempty_mulEquiv_pi_of_natCard_eq (hc : IsPTypeConfig H J V B F W) {p q : ℕ}
    (hp : p.Prime) (hq : Nat.card B = q) (hcard : Nat.card H = p ^ q) :
    Nonempty (↥H ≃* (Fin q → Multiplicative (ZMod p))) := by
  have := hc.finite
  obtain ⟨hHn, H₀, hH₀n, p', hfp', hfq, b, e, -, -, -, -, -, -, -, -⟩ := hc.exists_linearModel hq
  have hnorm : (H₀.subgroupOf H).Normal := hH₀n.subgroupOf H
  have hp' : p'.Prime := hfp'.out
  have hquot : Nat.card (↥H ⧸ H₀.subgroupOf H) = p' ^ q := by
    rw [Nat.card_congr e.toEquiv]; simp
  have hmul : Nat.card (H₀.subgroupOf H) * Nat.card (↥H ⧸ H₀.subgroupOf H) = Nat.card H := by
    rw [← Subgroup.index_eq_card, Subgroup.card_mul_index]
  have hp'p : p' = p := by
    have h1 : p' ∣ p ^ q :=
      Dvd.dvd.trans (calc p' ∣ p' ^ q := dvd_pow_self _ hfq.out.pos.ne'
        _ = Nat.card (↥H ⧸ H₀.subgroupOf H) := hquot.symm
        _ ∣ Nat.card H := Subgroup.card_quotient_dvd_card _)
        (hcard ▸ dvd_refl (Nat.card H))
    exact (Nat.prime_dvd_prime_iff_eq hp' hp).1 (hp'.dvd_of_dvd_pow h1)
  have hcard' : Nat.card H = p' ^ q := by rw [hp'p]; exact hcard
  have hbot : H₀.subgroupOf H = ⊥ := by
    refine Subgroup.card_eq_one.1 ?_
    rw [hquot, hcard'] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp'.pos) (by rw [one_mul]; exact hmul)
  have eH : ↥H ≃* Multiplicative (Fin q → ZMod p') :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e
  rw [← hp'p]
  exact nonempty_mulEquiv_pi_of_isElementaryAbelian hp'
    (isElementaryAbelian_of_nonempty_mulEquiv_multiplicative_pi ⟨eH⟩) hcard'

end PTypeConfig

theorem IsWitnessedPConfiguration.isPTypeConfig
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hsolv : Group.IsSolvable M)
    (hq : (Nat.card W₁).Prime) (hU : U ≠ ⊥) :
    IsPTypeConfig (hallCore M) ((⁅M, M⁆ : Subgroup G).subgroupOf M) (U.subgroupOf M)
      (W₁.subgroupOf M) (fittingRaw M) (W₂.subgroupOf M) where
  finite := inferInstance
  isSolvable := hsolv
  eq_commutator := (commutator_eq_subgroupOf_commutator M).symm
  normal_H := hallCore_normal
  isNilpotent_H := hallCore_isNilpotent
  hall_H := coprime_natCard_index_hallCore
  max_H _ hK1 hK2 hK3 := le_hallCore_of_normal_of_isNilpotent_of_coprime hK2 hK1 hK3
  normal_F := fittingRaw_normal M
  isNilpotent_F := fittingRaw_isNilpotent M
  max_F _ hK1 hK2 := (normal_isNilpotent_iff_le_fittingRaw hK2).1 hK1
  isComplement'_J_B := hc.isComplement'_subgroupOf_commutator_W₁
  sup_eq_J := by
    rw [← hallCore_subgroupOf M,
      ← Subgroup.subgroupOf_sup (Subgroup.map_subtype_le _) hc.le_M_E, hc.sup_hallCore_E]
  disjoint_H_U := by
    rw [← hallCore_subgroupOf M]; exact disjoint_subgroupOf M hc.disjoint_hallCore_E
  ne_bot_U := subgroupOf_ne_bot hc.le_M_E hU
  isNilpotent_U := have := hc.isNilpotent_E; isNilpotent_subgroupOf hc.le_M_E
  prime_natCard_B := by rwa [natCard_subgroupOf hc.le_M_W₁]
  hall_B := by
    have := hc.hall_W₁
    rwa [natCard_subgroupOf hc.le_M_W₁]
  le_normalizer_U := le_normalizer_subgroupOf hc.le_normalizer_E
  ne_bot_H := hc.hallCore_ne_bot'
  commutator_J_le_F := by
    rw [commutator_subgroupOf (Subgroup.commutator_le_self M) (Subgroup.commutator_le_self M),
      ← fittingRaw_subgroupOf M]
    exact Subgroup.subgroupOf_mono M hc.commutator_commutator_le_fittingRaw
  isCyclic_W2 := isCyclic_subgroupOf hc.le_M_W₂ hc.isCyclic_W₂
  ne_bot_W2 := subgroupOf_ne_bot hc.le_M_W₂ hc.ne_bot_W₂
  le_H_W2 := by
    rw [← hallCore_subgroupOf M]; exact Subgroup.subgroupOf_mono M hc.le_hallCore_W₂
  inf_centralizer_eq_W2 := by
    intro b hb hb1
    rw [← centralizer_singleton_subgroupOf b, Subgroup.subgroupOf, Subgroup.subgroupOf,
      ← Subgroup.comap_inf, hc.inf_centralizer_eq_W₂ (b : G) (Subgroup.mem_subgroupOf.1 hb)
      (fun h => hb1 (Subtype.ext h))]
    rfl

theorem isTIWithNormalizer_hallCoreSharp_of_fittingRawSharp
    (hTI : IsTIWithNormalizer (fittingRawSharp M) M) (hne : (hallCoreSharp M).Nonempty) :
    IsTIWithNormalizer (hallCoreSharp M) M where
  nonempty := hne
  one_notMem := by simp
  normalizer_eq := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    ·
      by_contra hgM
      have h1 : MulAut.conj g '' hallCoreSharp M = hallCoreSharp M :=
        Subgroup.mem_normalizer_iff_conj_image_eq.1 hg
      obtain ⟨x, hx⟩ := hne
      have hx1 : x ∈ fittingRawSharp M := hallCoreSharp_subset_fittingRawSharp M hx
      have hx2 : x ∈ MulAut.conj g '' fittingRawSharp M := by
        rw [← h1] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨y, hallCoreSharp_subset_fittingRawSharp M hy, rfl⟩
      exact Set.disjoint_left.1 (hTI.disjoint_conj_image g hgM) hx1 hx2
    ·
      rw [Subgroup.mem_normalizer_iff_conj_image_eq, hallCoreSharp_eq]
      have hH : MulAut.conj g '' (((hallCore M).map M.subtype : Subgroup G) : Set G)
          = (((hallCore M).map M.subtype : Subgroup G) : Set G) :=
        Subgroup.mem_normalizer_iff_conj_image_eq.1 (le_normalizer_map_subtype_hallCore M hg)
      rw [Set.image_diff (MulAut.conj g).injective, hH, Set.image_singleton]
      simp
  disjoint_conj_image g hg :=
    ((hTI.disjoint_conj_image g hg).mono_left (hallCoreSharp_subset_fittingRawSharp M)).mono_right
      (Set.image_mono (hallCoreSharp_subset_fittingRawSharp M))

theorem IsTypeII.primes_of_isWitnessedPConfiguration (hsimple : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hp : (Nat.card W₂).Prime) :
    (Nat.card W₁).Prime ∧ Odd (Nat.card W₁) ∧ Odd (Nat.card W₂) ∧
      Nat.card W₂ ≠ Nat.card W₁ := by
  obtain ⟨hcIIToIV, -⟩ :=
    h.clauses_of_isWitnessedPConfiguration_of_minimalSimple hsimple hna hodd hsolv hM hc
  refine ⟨hcIIToIV.prime_natCard_W₁, Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card W₁),
    Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card W₂), fun hpq => ?_⟩
  have hdvd : Nat.card W₂ ∣ Nat.card (⁅M, M⁆ : Subgroup G) :=
    Subgroup.card_dvd_of_le
      (hc.le_commutator_commutator_W₂.trans (Subgroup.commutator_le_self _))
  have hcop := hc.coprime_natCard_W₁_natCard_commutator
  rw [← hpq] at hcop
  exact hp.one_lt.ne' (hcop.eq_one_of_dvd hdvd)

theorem IsTypeII.isTIWithNormalizer_hallCoreSharp_of_isWitnessedPConfiguration
    (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsTIWithNormalizer (hallCoreSharp M) M := by
  obtain ⟨hcIIToIV, -⟩ :=
    h.clauses_of_isWitnessedPConfiguration_of_minimalSimple hsimple hna hodd hsolv hM hc
  exact isTIWithNormalizer_hallCoreSharp_of_fittingRawSharp
    hcIIToIV.isTIWithNormalizer_fittingRawSharp hc.hallCoreSharp_nonempty

theorem IsTypeII.inf_centralizer_hallCore_eq_bot_of_isWitnessedPConfiguration
    (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ((hallCore M).map M.subtype) ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
  obtain ⟨-, -, -, -, hfrob, hhall⟩ :=
    h.clauses_of_isWitnessedPConfiguration_of_minimalSimple hsimple hna hodd hsolv hM hc
  obtain ⟨e, heU, -, hcent⟩ := hfrob.exists_ne_one_inf_centralizer_eq_bot
  have heG : (e : G) ∈ U := Subgroup.mem_subgroupOf.1 heU
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.1 hx
  rw [← hhall] at hxH
  obtain ⟨y, hy, rfl⟩ := hxH
  have hcomm : (e : G) * (y : G) = (y : G) * (e : G) :=
    Subgroup.mem_centralizer_iff.1 hxc _ heG
  have hy1 : y ∈ hallCore ↥(⁅M, M⁆ : Subgroup G) ⊓ Subgroup.centralizer {e} :=
    Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hcomm.symm)⟩
  rw [hcent, Subgroup.mem_bot] at hy1
  simp [hy1]

theorem IsTypeII.core_elementary_abelian_of_isWitnessedPConfiguration
    (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (hM : IsCoatom M) (h : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hp : (Nat.card W₂).Prime) :
    Nat.card ((hallCore M).map M.subtype) = Nat.card W₂ ^ Nat.card W₁ ∧
      Nonempty (((hallCore M).map M.subtype) ≃*
        (Fin (Nat.card W₁) → Multiplicative (ZMod (Nat.card W₂)))) := by
  obtain ⟨hcIIToIV, hUne, -⟩ :=
    h.clauses_of_isWitnessedPConfiguration_of_minimalSimple hsimple hna hodd hsolv hM hc
  have hcfg := hc.isPTypeConfig (hsolv M hM.1) hcIIToIV.prime_natCard_W₁ hUne
  have hCU : hallCore ↥M ⊓ Subgroup.centralizer ((U.subgroupOf M : Subgroup M) : Set M) = ⊥ :=
    inf_centralizer_subgroupOf_eq_bot hc.le_M_E
      (h.inf_centralizer_hallCore_eq_bot_of_isWitnessedPConfiguration hsimple hna hodd hsolv hM hc)
  have hcard : Nat.card (hallCore ↥M) = Nat.card W₂ ^ Nat.card W₁ := by
    have := hcfg.natCard_eq_natCard_pow_natCard hCU
    rwa [natCard_subgroupOf hc.le_M_W₂, natCard_subgroupOf hc.le_M_W₁] at this
  have hmap : Nat.card ((hallCore ↥M).map M.subtype) = Nat.card (hallCore ↥M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  refine ⟨by rw [hmap, hcard], ?_⟩
  obtain ⟨e⟩ := hcfg.nonempty_mulEquiv_pi_of_natCard_eq hp (natCard_subgroupOf hc.le_M_W₁) hcard
  exact ⟨((hallCore ↥M).equivMapOfInjective M.subtype M.subtype_injective).symm.trans e⟩

end

end CFSG.FeitThompson
