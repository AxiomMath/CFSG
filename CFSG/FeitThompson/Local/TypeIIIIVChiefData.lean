module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.TypeIIHallCoreElementaryAbelian
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
import CFSG.FeitThompson.OddOrder.PConfigComplementCentralizer
public import CFSG.FeitThompson.OddOrder.FittingSplitsOverHallCore
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.OddOrder.PConfigChiefFactorLinearModel
public import CFSG.FeitThompson.OddOrder.ChiefFactorIrreducibleComplementModule
import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
import CFSG.FeitThompson.Local.RankTwoSectionChiefFactorCentralization

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise ChiefFactorLinearAction CFSG.FeitThompson.Prep05

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G}

omit [Finite G] in
theorem subgroupOf_centralizer (M A : Subgroup G) (hA : A ≤ M) :
    (centralizer (A : Set G)).subgroupOf M
      = centralizer ((A.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  refine ⟨fun h y hy => Subtype.ext (h (y : G) (Subgroup.mem_subgroupOf.1 hy)),
    fun h y hy => ?_⟩
  exact congrArg Subtype.val (h ⟨y, hA hy⟩ (Subgroup.mem_subgroupOf.2 (by simpa using hy)))

omit [Finite G] in
theorem inf_subgroupOf_self (M A : Subgroup G) :
    (M ⊓ A).subgroupOf M = A.subgroupOf M := by
  rw [Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_inf,
    show (M.comap M.subtype) = M.subgroupOf M from rfl, Subgroup.subgroupOf_self, top_inf_eq]

theorem inf_eq_bot_of_natCard_map_eq {X : Type*} [Group X] [Finite X] (A B : Subgroup X)
    [B.Normal] (hcard : Nat.card ↥(A.map (QuotientGroup.mk' B)) = Nat.card ↥A) : A ⊓ B = ⊥ := by
  set f : X →* X ⧸ B := QuotientGroup.mk' B with hf
  set g : ↥A →* X ⧸ B := f.comp A.subtype with hg
  have hrange : g.range = A.map f := by rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : g.ker = (A ⊓ B).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, Subgroup.coe_subtype, hf,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hmul : Nat.card ↥g.ker * Nat.card ↥g.range = Nat.card ↥A := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv,
      ← Subgroup.index_eq_card g.ker, Subgroup.card_mul_index]
  rw [hrange, hcard, hker] at hmul
  have h2 : (A ⊓ B).subgroupOf A = ⊥ :=
    Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul, one_mul]))
  rw [Subgroup.subgroupOf_eq_bot] at h2
  exact le_antisymm (fun x hx => Subgroup.mem_bot.2
    (Subgroup.disjoint_def.1 h2 hx (Subgroup.mem_inf.1 hx).1)) bot_le

theorem IsWitnessedPConfiguration.isPrescribedFitting
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hsolvM : Group.IsSolvable ↥M)
    (hqprime : (Nat.card ↥W₁).Prime) (hUne : U ≠ ⊥) :
    IsPrescribedFitting (hallCore ↥M) (U.subgroupOf M) ((⁅M, M⁆ : Subgroup G).subgroupOf M)
      (fittingRaw ↥M) ((centralizerIn U (hallCoreOf M)).subgroupOf M) := by
  have hcfg := hc.isPTypeConfig hsolvM hqprime hUne
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hHsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := by
    rw [hallCoreOf_eq]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hcent : (centralizer ((hallCoreOf M : Subgroup G) : Set G)).subgroupOf M
      = centralizer ((hallCore ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [subgroupOf_centralizer M _ hHle, hHsub]
  have hFsub : (fittingOf M).subgroupOf M = fittingRaw ↥M := by
    rw [fittingOf_eq]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hMC : M ⊓ centralizer ((hallCoreOf M : Subgroup G) : Set G) ≤ M := inf_le_left
  have hFeqG : fittingOf M
      = hallCoreOf M ⊔ (M ⊓ centralizer ((hallCoreOf M : Subgroup G) : Set G)) := by
    rw [fittingOf_eq, hallCoreOf_eq]; exact hc.fittingRaw_eq_sup
  exact
    { normal_H := hallCore_normal
      coprime_index_H := coprime_natCard_index_hallCore
      sup_H_U := hcfg.sup_eq_J
      disjoint_H_U := hcfg.disjoint_H_U
      normal_F := fittingRaw_normal ↥M
      nilpotent_F := fittingRaw_isNilpotent ↥M
      le_H_F := hallCore_le_fittingRaw
      eq_F := by
        rw [← hFsub, ← hcent, ← hHsub, hFeqG, Subgroup.subgroupOf_sup hHle hMC,
          inf_subgroupOf_self]
      le_F_K := by rw [← hFsub]; exact Subgroup.subgroupOf_mono M hc.fittingRaw_le_commutator
      eq_C := by
        rw [centralizerIn_eq, Subgroup.subgroupOf, Subgroup.comap_inf, ← hcent]
        rfl }

theorem chiefData_fitting_product (hsolvM : Group.IsSolvable ↥M)
    (hqprime : (Nat.card ↥W₁).Prime) (hUne : U ≠ ⊥)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    centralizerIn U (hallCoreOf M) < U ∧
      IsInternalDirectProduct (fittingOf M) (hallCoreOf M) (centralizerIn U (hallCoreOf M)) ∧
      M ≤ normalizer ((centralizerIn U (hallCoreOf M) : Subgroup G) : Set G) := by
  have hcfg := hc.isPTypeConfig hsolvM hqprime hUne
  have hpf := hc.isPrescribedFitting hsolvM hqprime hUne
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hCle : centralizerIn U (hallCoreOf M) ≤ M := (centralizerIn_le _ _).trans hc.le_M_E
  have hHsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := by
    rw [hallCoreOf_eq]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hcent : (centralizer ((hallCoreOf M : Subgroup G) : Set G)).subgroupOf M
      = centralizer ((hallCore ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [subgroupOf_centralizer M _ hHle, hHsub]
  have hsupHC : hallCoreOf M ⊔ centralizerIn U (hallCoreOf M) = fittingOf M := by
    have h := congrArg (Subgroup.map M.subtype) hpf.sup_C_eq_F
    rw [Subgroup.map_sup, ← hHsub, Subgroup.map_subgroupOf_eq_of_le hHle,
      Subgroup.map_subgroupOf_eq_of_le hCle, ← fittingOf_eq] at h
    exact h
  have hcomm : ∀ x ∈ hallCoreOf M, ∀ y ∈ centralizerIn U (hallCoreOf M), Commute x y :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x hx
  have hinfHC : hallCoreOf M ⊓ centralizerIn U (hallCoreOf M) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_bot.2 (Subgroup.disjoint_def.1
      (hallCoreOf_eq M ▸ hc.disjoint_hallCore_E) hxH (Subgroup.mem_inf.1 hxC).1)
  have := hpf.normal_C
  refine ⟨lt_of_le_of_ne (centralizerIn_le _ _) (fun heq => ?_), ?_,
    Subgroup.le_normalizer_of_normal_subgroupOf hCle⟩
  · refine hcfg.not_le_centralizer_H fun x hx => ?_
    have hxG : (x : G) ∈ U := Subgroup.mem_subgroupOf.1 hx
    have h1 : (x : G) ∈ centralizerIn U (hallCoreOf M) := by rw [heq]; exact hxG
    rw [← hcent]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 h1).2
  · exact
      { left_le := hsupHC ▸ le_sup_left
        right_le := hsupHC ▸ le_sup_right
        coe_eq_mul := by rw [← hsupHC]; exact coe_sup_eq_mul_of_commute hcomm
        inf_eq_bot := hinfHC
        commutator_eq_bot := by
          rw [eq_bot_iff]
          refine Subgroup.commutator_le.2 fun x hx y hy => ?_
          exact Subgroup.mem_bot.2
            (commutatorElement_eq_one_iff_commute.2 (hcomm x hx y hy)) }

theorem chiefData_exists_chief_layer (hsolvM : Group.IsSolvable ↥M)
    (hqprime : (Nat.card ↥W₁).Prime) (hUne : U ≠ ⊥)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ∃ H₀ : Subgroup G, centralizerIn (hallCoreOf M) U ≤ H₀ ∧
      IsChiefLayer M H₀ (hallCoreOf M) := by
  have hcfg := hc.isPTypeConfig hsolvM hqprime hUne
  have hUleM : U ≤ M := hc.le_M_E
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hHsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := by
    rw [hallCoreOf_eq]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  obtain ⟨H₀', hchief, hCU⟩ := hcfg.exists_isChiefFactor
  have hH₀le : H₀'.map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hH₀sub : (H₀'.map M.subtype).subgroupOf M = H₀' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hnorm : M ≤ normalizer ((H₀'.map M.subtype : Subgroup G) : Set G) := by
    have hd : ((H₀'.map M.subtype).subgroupOf M).Normal := by
      rw [hH₀sub]; exact hchief.normal_den
    exact Subgroup.le_normalizer_of_normal_subgroupOf hH₀le
  refine ⟨H₀'.map M.subtype, ?_, hnorm, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxM : x ∈ M := hHle hxH
    have h1 : (⟨x, hxM⟩ : ↥M) ∈ hallCore ↥M := by
      rw [← hHsub]; exact Subgroup.mem_subgroupOf.2 hxH
    have h2 : (⟨x, hxM⟩ : ↥M) ∈ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      rw [← subgroupOf_centralizer M U hUleM]; exact Subgroup.mem_subgroupOf.2 hxc
    exact ⟨⟨x, hxM⟩, hCU (Subgroup.mem_inf.2 ⟨h1, h2⟩), rfl⟩
  · rw [hallCoreOf_eq]
    exact (Subgroup.map_lt_map_iff_of_injective M.subtype_injective).2 hchief.lt
  · intro N hN hH₀N hNH
    have hNM : N ≤ M := hNH.trans hHle
    have hNnormal : (N.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hN
    have h1 : H₀' ≤ N.subgroupOf M := by
      have h := Subgroup.subgroupOf_mono M hH₀N
      rwa [hH₀sub] at h
    have h2 : N.subgroupOf M ≤ hallCore ↥M := by
      rw [← hHsub]; exact Subgroup.subgroupOf_mono M hNH
    rcases hchief.eq_or_eq hNnormal h1 h2 with h | h
    · left; rw [← h, Subgroup.map_subgroupOf_eq_of_le hNM]
    · right; rw [hallCoreOf_eq, ← h, Subgroup.map_subgroupOf_eq_of_le hNM]

omit [Finite G] in
theorem isChiefFactor_of_isChiefLayer {H₀ : Subgroup G}
    (hlayer : IsChiefLayer M H₀ (hallCoreOf M)) :
    IsChiefFactor (hallCore ↥M) (H₀.subgroupOf M) := by
  obtain ⟨hH₀norm, hH₀lt, hmax⟩ := hlayer
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hH₀leM : H₀ ≤ M := hH₀lt.le.trans hHle
  have hHsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := by
    rw [hallCoreOf_eq]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hHmap : (hallCore ↥M).map M.subtype = hallCoreOf M := (hallCoreOf_eq M).symm
  refine { normal_num := hallCore_normal
           normal_den := (Subgroup.normal_subgroupOf_iff_le_normalizer hH₀leM).2 hH₀norm
           lt := ?_
           not_lt_lt := ?_ }
  · rw [← hHsub]
    refine lt_of_le_of_ne (Subgroup.subgroupOf_mono M hH₀lt.le) fun heq => ?_
    have h1 := congrArg (Subgroup.map M.subtype) heq
    rw [Subgroup.map_subgroupOf_eq_of_le hH₀leM, Subgroup.map_subgroupOf_eq_of_le hHle] at h1
    exact hH₀lt.ne h1
  · intro Z hZ h₁ h₃
    have hZM : Z.map M.subtype ≤ M := Subgroup.map_subtype_le _
    have hZcomap : (Z.map M.subtype).subgroupOf M = Z :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    have hZnorm : M ≤ normalizer ((Z.map M.subtype : Subgroup G) : Set G) := by
      have : ((Z.map M.subtype).subgroupOf M).Normal := by rw [hZcomap]; exact hZ
      exact Subgroup.le_normalizer_of_normal_subgroupOf hZM
    have hle1 : H₀ ≤ Z.map M.subtype := by
      have h := Subgroup.map_mono (f := M.subtype) h₁.le
      rwa [Subgroup.map_subgroupOf_eq_of_le hH₀leM] at h
    have hle2 : Z.map M.subtype ≤ hallCoreOf M := by
      have h := Subgroup.map_mono (f := M.subtype) h₃.le
      rwa [hHmap] at h
    rcases hmax (Z.map M.subtype) hZnorm hle1 hle2 with h | h
    · exact absurd (by rw [← hZcomap, h] : Z = H₀.subgroupOf M) h₁.ne'
    · refine absurd (?_ : Z = hallCore ↥M) h₃.ne
      rw [← hZcomap, h, ← hHmap]
      exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem chiefData_layer_products (hsolvM : Group.IsSolvable ↥M)
    (hqprime : (Nat.card ↥W₁).Prime) (hUne : U ≠ ⊥)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (H₀ : Subgroup G) (hlayer : IsChiefLayer M H₀ (hallCoreOf M)) :
    M ≤ normalizer ((H₀ ⊔ centralizerIn U (hallCoreOf M) : Subgroup G) : Set G) ∧
      IsInternalDirectProduct (H₀ ⊔ centralizerIn U (hallCoreOf M)) H₀
        (centralizerIn U (hallCoreOf M)) ∧
      (H₀.subgroupOf (hallCoreOf M)).Normal ∧
      ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf (fittingOf M)).Normal := by
  have hpf := hc.isPrescribedFitting hsolvM hqprime hUne
  obtain ⟨hH₀norm, hH₀lt, -⟩ := hlayer
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hH₀leH : H₀ ≤ hallCoreOf M := hH₀lt.le
  have hH₀leM : H₀ ≤ M := hH₀leH.trans hHle
  have hCle : centralizerIn U (hallCoreOf M) ≤ M := (centralizerIn_le _ _).trans hc.le_M_E
  have hsupCleM : H₀ ⊔ centralizerIn U (hallCoreOf M) ≤ M := sup_le hH₀leM hCle
  have hH₀Nm : (H₀.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH₀leM).2 hH₀norm
  have hsub : (H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M
      = H₀.subgroupOf M ⊔ (centralizerIn U (hallCoreOf M)).subgroupOf M :=
    Subgroup.subgroupOf_sup hH₀leM hCle
  have hnormsupC := hpf.normal_sup_C (H0 := H₀.subgroupOf M)
  have hsupCnorm : ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M).Normal := by
    rw [hsub]; exact hnormsupC
  have hMnorm : M ≤ normalizer ((H₀ ⊔ centralizerIn U (hallCoreOf M) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hsupCleM
  have hcomm : ∀ x ∈ H₀, ∀ y ∈ centralizerIn U (hallCoreOf M), Commute x y :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x (hH₀leH hx)
  have hHleF : hallCoreOf M ≤ fittingOf M := by
    rw [fittingOf_eq, hallCoreOf_eq]; exact hc.hallCore_le_fittingRaw_map
  have hCleF : centralizerIn U (hallCoreOf M) ≤ fittingOf M := by
    have h := Subgroup.map_mono (f := M.subtype) hpf.C_le_F
    rw [Subgroup.map_subgroupOf_eq_of_le hCle] at h
    exact h.trans (le_of_eq (fittingOf_eq M).symm)
  refine ⟨hMnorm, ?_, (Subgroup.normal_subgroupOf_iff_le_normalizer hH₀leH).2
      (hHle.trans hH₀norm), ?_⟩
  · refine { left_le := le_sup_left
             right_le := le_sup_right
             coe_eq_mul := coe_sup_eq_mul_of_commute hcomm
             inf_eq_bot := ?_
             commutator_eq_bot := ?_ }
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxH₀, hxC⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_bot.2 (Subgroup.disjoint_def.1
        (hallCoreOf_eq M ▸ hc.disjoint_hallCore_E) (hH₀leH hxH₀) (Subgroup.mem_inf.1 hxC).1)
    · rw [eq_bot_iff]
      refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_commute.2 (hcomm x hx y hy))
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer ?_).2 ((fittingOf_le M).trans hMnorm)
    exact sup_le (hH₀leH.trans hHleF) hCleF

theorem chiefData_layer_natCard_quotient (hsolvM : Group.IsSolvable ↥M)
    (hqprime : (Nat.card ↥W₁).Prime) (hpprime : (Nat.card ↥W₂).Prime) (hUne : U ≠ ⊥)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup G} (hchief : IsChiefFactor (hallCore ↥M) (H₀.subgroupOf M))
    (hCU : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M)
      ≤ H₀.subgroupOf M)
    (hH₀leH : H₀ ≤ hallCoreOf M) :
    Nat.card (↥(hallCore ↥M) ⧸ (H₀.subgroupOf M).subgroupOf (hallCore ↥M))
        = Nat.card ↥W₂ ^ Nat.card ↥W₁ ∧ H₀ ⊓ W₂ = ⊥ := by
  have hcfg := hc.isPTypeConfig hsolvM hqprime hUne
  have hH₀norm := hchief.normal_den
  have hW₂M := hc.le_M_W₂
  have hcard2 : Nat.card ↥(W₂.subgroupOf M) = Nat.card ↥W₂ := natCard_subgroupOf hW₂M
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ := natCard_subgroupOf hc.le_M_W₁
  obtain ⟨b, hbB, hb1, -⟩ := exists_zpowers_eq_of_prime_natCard hcfg.prime_natCard_B
  have hs := hcfg.isFaithfulImageSetup rfl hchief hCU hbB hb1
  obtain ⟨r, d, hr, hd, ⟨e⟩⟩ := exists_prime_nonempty_mulEquiv_of_isChiefFactor hchief
  have hcard : Nat.card (↥(hallCore ↥M) ⧸ (H₀.subgroupOf M).subgroupOf (hallCore ↥M))
      = r ^ Nat.card ↥(W₁.subgroupOf M) := hs.natCard_quotient_eq r e hr
  have hCE : Nat.card ↥(ChiefFactorFixedLine.factorCentralizer (hallCore ↥M) (H₀.subgroupOf M)
      (W₁.subgroupOf M)) = r := hs.natCard_factorCentralizer_B_eq e hr
  have hCEmap := hs.toIsFixedLineSetup.factorCentralizer_B
  rw [hcfg.inf_centralizer_B_eq_W2] at hCEmap
  have hWmcard : Nat.card ↥((W₂.subgroupOf M).subgroupOf (hallCore ↥M)) = Nat.card ↥W₂ := by
    rw [natCard_subgroupOf hcfg.le_H_W2, hcard2]
  have hdvd : r ∣ Nat.card ↥W₂ := by
    rw [← hCE, hCEmap, ← hWmcard]
    exact Subgroup.card_map_dvd _ _
  have hrp : r = Nat.card ↥W₂ := (Nat.prime_dvd_prime_iff_eq hr hpprime).1 hdvd
  refine ⟨by rw [hcard, hrp, hcard1], ?_⟩
  have hcardimg : Nat.card ↥(((W₂.subgroupOf M).subgroupOf (hallCore ↥M)).map
        (QuotientGroup.mk' ((H₀.subgroupOf M).subgroupOf (hallCore ↥M))))
      = Nat.card ↥((W₂.subgroupOf M).subgroupOf (hallCore ↥M)) := by
    rw [← hCEmap, hCE, hrp, hWmcard]
  have hbotm := inf_eq_bot_of_natCard_map_eq _ _ hcardimg
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH₀, hxW₂⟩ := Subgroup.mem_inf.1 hx
  have hxM : x ∈ M := hW₂M hxW₂
  have hHsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := by
    rw [hallCoreOf_eq]; exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hxHm : (⟨x, hxM⟩ : ↥M) ∈ hallCore ↥M := by
    rw [← hHsub]; exact Subgroup.mem_subgroupOf.2 (hH₀leH hxH₀)
  have hmem : (⟨⟨x, hxM⟩, hxHm⟩ : ↥(hallCore ↥M))
      ∈ ((W₂.subgroupOf M).subgroupOf (hallCore ↥M))
        ⊓ ((H₀.subgroupOf M).subgroupOf (hallCore ↥M)) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hxW₂),
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hxH₀)⟩
  rw [hbotm, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (by simpa [Subtype.ext_iff] using hmem)

theorem chiefData_layer_elementary (hsolvM : Group.IsSolvable ↥M)
    (hqprime : (Nat.card ↥W₁).Prime) (hpprime : (Nat.card ↥W₂).Prime) (hUne : U ≠ ⊥)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (p q : ℕ) (hp : p = Nat.card ↥W₂) (hq : q = Nat.card ↥W₁)
    (H₀ : Subgroup G) (hH₀ : centralizerIn (hallCoreOf M) U ≤ H₀)
    (hlayer : IsChiefLayer M H₀ (hallCoreOf M)) :
    IsElemAbelianLayer p q H₀ (hallCoreOf M) ∧
      H₀ ⊓ W₂ = ⊥ ∧
      ∀ (_ : (H₀.subgroupOf (hallCoreOf M)).Normal)
        (_ : ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf (fittingOf M)).Normal),
        Nonempty
          ((↥(fittingOf M) ⧸
              (H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf (fittingOf M)) ≃*
            (↥(hallCoreOf M) ⧸ H₀.subgroupOf (hallCoreOf M))) := by
  have hsolv := hsolvM
  subst hp hq
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hH₀leH : H₀ ≤ hallCoreOf M := hlayer.2.1.le
  have hH₀leM : H₀ ≤ M := hH₀leH.trans hHle
  have hUleM : U ≤ M := hc.le_M_E
  have hCle : centralizerIn U (hallCoreOf M) ≤ M := (centralizerIn_le _ _).trans hc.le_M_E
  have hHsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := by
    rw [hallCoreOf_eq]; exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hchief : IsChiefFactor (hallCore ↥M) (H₀.subgroupOf M) :=
    isChiefFactor_of_isChiefLayer hlayer
  have hH₀mN := hchief.normal_den
  have hCUm : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M)
      ≤ H₀.subgroupOf M := by
    rw [centralizerIn_eq] at hH₀
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rw [← hHsub, Subgroup.mem_subgroupOf] at hx1
    rw [← subgroupOf_centralizer M U hUleM, Subgroup.mem_subgroupOf] at hx2
    exact Subgroup.mem_subgroupOf.2 (hH₀ (Subgroup.mem_inf.2 ⟨hx1, hx2⟩))
  have hnq := chiefData_layer_natCard_quotient hsolvM hqprime hpprime hUne hc hchief hCUm hH₀leH
  have hrel : H₀.relIndex (hallCoreOf M) = Nat.card ↥W₂ ^ Nat.card ↥W₁ := by
    rw [← Subgroup.relIndex_subgroupOf hHle, hHsub]
    change (((H₀.subgroupOf M).subgroupOf (hallCore ↥M)).index) = _
    rw [Subgroup.index_eq_card]
    exact hnq.1
  have hcomm : ⁅hallCoreOf M, hallCoreOf M⁆ ≤ H₀ := by
    have h := Subgroup.map_mono (f := M.subtype) hchief.commutator_num_le_den
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hH₀leM, ← hallCoreOf_eq] at h
    exact h
  obtain ⟨r, d, hr, hd, ⟨e⟩⟩ := exists_prime_nonempty_mulEquiv_of_isChiefFactor hchief
  have hcardq : Nat.card (↥(hallCore ↥M) ⧸ (H₀.subgroupOf M).subgroupOf (hallCore ↥M))
      = r ^ d := by
    rw [Nat.card_congr e.toEquiv]
    have : NeZero r := ⟨hr.ne_zero⟩
    simp [Nat.card_eq_fintype_card]
  have hrp : r = Nat.card ↥W₂ := by
    have hdvd : r ∣ Nat.card ↥W₂ ^ Nat.card ↥W₁ := by
      rw [← hnq.1, hcardq]; exact dvd_pow_self r (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hr hpprime).1 (hr.dvd_of_dvd_pow hdvd)
  have hpowMult : ∀ g : Multiplicative (Fin d → ZMod r), g ^ r = 1 := by
    intro g
    have h0 : (r • Multiplicative.toAdd g) = 0 := by funext i; simp
    change Multiplicative.ofAdd (r • Multiplicative.toAdd g) = 1
    rw [h0]; rfl
  have hpow : ∀ h ∈ hallCoreOf M, h ^ Nat.card ↥W₂ ∈ H₀ := by
    intro h hh
    have hhM : h ∈ M := hHle hh
    have hhm : (⟨h, hhM⟩ : ↥M) ∈ hallCore ↥M := by
      rw [← hHsub]; exact Subgroup.mem_subgroupOf.2 hh
    set x : ↥(hallCore ↥M) := ⟨⟨h, hhM⟩, hhm⟩ with hxdef
    have h1 : (QuotientGroup.mk x :
        ↥(hallCore ↥M) ⧸ (H₀.subgroupOf M).subgroupOf (hallCore ↥M)) ^ Nat.card ↥W₂ = 1 := by
      refine e.injective ?_
      rw [map_pow, map_one, ← hrp]
      exact hpowMult _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf] at h1
    simpa [hxdef, SubmonoidClass.coe_pow] using h1
  refine ⟨⟨hH₀leH, hcomm, hpow, hrel⟩, hnq.2, ?_⟩
  intro hnorm1 hnorm2
  have hpf := hc.isPrescribedFitting hsolvM hqprime hUne
  set S : Subgroup ↥M := H₀.subgroupOf M ⊔ (centralizerIn U (hallCoreOf M)).subgroupOf M with hS
  have hSmap : Subgroup.map M.subtype S = H₀ ⊔ centralizerIn U (hallCoreOf M) := by
    rw [hS, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hH₀leM,
      Subgroup.map_subgroupOf_eq_of_le hCle]
  have hH₀map : Subgroup.map M.subtype (H₀.subgroupOf M) = H₀ :=
    Subgroup.map_subgroupOf_eq_of_le hH₀leM
  have hFeq : Subgroup.map M.subtype (fittingRaw ↥M) = fittingOf M := (fittingOf_eq M).symm
  have hHeq : Subgroup.map M.subtype (hallCore ↥M) = hallCoreOf M := (hallCoreOf_eq M).symm
  have hSN : S.Normal := hpf.normal_sup_C
  have hSN2 : ((Subgroup.map M.subtype S).subgroupOf
      (Subgroup.map M.subtype (fittingRaw ↥M))).Normal := by
    rw [hSmap, hFeq]; exact hnorm2
  have hH₀N2 : ((Subgroup.map M.subtype (H₀.subgroupOf M)).subgroupOf
      (Subgroup.map M.subtype (hallCore ↥M))).Normal := by
    rw [hH₀map, hHeq]; exact hnorm1
  have hH₀leHm : H₀.subgroupOf M ≤ hallCore ↥M := by
    rw [← hHsub]; exact Subgroup.subgroupOf_mono M hH₀leH
  have E1 := hpf.quotientSupCMulEquiv (H0 := H₀.subgroupOf M) hH₀leHm
  have E2 := factorMulEquivMapSubtype M S (fittingRaw ↥M)
  have E3 := QuotientGroup.equivQuotientSubgroupOfOfEq (G := G)
    (A' := Subgroup.map M.subtype S) (A := Subgroup.map M.subtype (fittingRaw ↥M))
    (B' := H₀ ⊔ centralizerIn U (hallCoreOf M)) (B := fittingOf M) hSmap hFeq
  have E4 := factorMulEquivMapSubtype M (H₀.subgroupOf M) (hallCore ↥M)
  have E5 := QuotientGroup.equivQuotientSubgroupOfOfEq (G := G)
    (A' := Subgroup.map M.subtype (H₀.subgroupOf M))
    (A := Subgroup.map M.subtype (hallCore ↥M)) (B' := H₀) (B := hallCoreOf M) hH₀map hHeq
  exact ⟨E3.symm.trans (E2.symm.trans (E1.trans (E4.trans E5)))⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_type_iii_iv_chief_data
    (hprime : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_chief_data.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc p q hpdef hqdef
  obtain ⟨hcIIToIV, hUne⟩ : IsPConfigurationIIToIV M U W₁ W₂ ∧ U ≠ ⊥ := by
    rcases htype with h | h
    · obtain ⟨h1, h2, -, -⟩ := h.clauses_of_isWitnessedPConfiguration_of_minimalSimple
        hG.isSimpleGroup hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hc
      exact ⟨h1, h2⟩
    · obtain ⟨h1, h2, -⟩ := h.clauses_of_isWitnessedPConfiguration_of_minimalSimple
        hG.isSimpleGroup hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hc
      refine ⟨h1, fun hb => h2 ?_⟩
      subst hb
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 a.2)
      have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 b.2)
      rw [ha, hb, one_mul]
  have hqprime : q.Prime := hqdef ▸ hcIIToIV.prime_natCard_W₁
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hpprime : p.Prime := by
    haveI : Fintype G := Fintype.ofFinite G
    have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    have h := hprime G hG6 M U W₁ W₂ hM (by tauto) hc
    rw [hpdef]
    exact h
  have hoddp : Odd p := hpdef ▸ Odd.of_dvd_nat hG.odd_natCard (Subgroup.card_subgroup_dvd_card W₂)
  have hoddq : Odd q := hqdef ▸ Odd.of_dvd_nat hG.odd_natCard (Subgroup.card_subgroup_dvd_card W₁)
  have hpq : p ≠ q := by
    intro hpq
    have hdvd : Nat.card ↥W₂ ∣ Nat.card ↥(⁅M, M⁆ : Subgroup G) :=
      Subgroup.card_dvd_of_le
        (hc.le_commutator_commutator_W₂.trans (Subgroup.commutator_le_self _))
    have hcop := hc.coprime_natCard_W₁_natCard_commutator
    rw [← hqdef, ← hpq, hpdef] at hcop
    exact hpprime.one_lt.ne' (hpdef ▸ hcop.eq_one_of_dvd hdvd)
  have hUle : U ≤ M := hc.le_M_E
  have hW₁le : W₁ ≤ M := hc.le_M_W₁
  have hUW₁le : U ⊔ W₁ ≤ M := sup_le hUle hW₁le
  have hsup : hallCoreOf M ⊔ (U ⊔ W₁) = M := by
    rw [hallCoreOf_eq, ← sup_assoc, hc.sup_hallCore_E, hc.sup_commutator_W₁]
  have hmul : ((U ⊔ W₁ : Subgroup G) : Set G) = (U : Set G) * (W₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U W₁ hc.le_normalizer_E
  have hdisjHU : Disjoint ((hallCore ↥M).map M.subtype) U := hc.disjoint_hallCore_E
  have hdisj : Disjoint (hallCoreOf M) (U ⊔ W₁) := by
    rw [hallCoreOf_eq, Subgroup.disjoint_def]
    intro x hxH hxUW
    have hx : x ∈ (U : Set G) * (W₁ : Set G) :=
      hmul ▸ (hxUW : x ∈ ((U ⊔ W₁ : Subgroup G) : Set G))
    obtain ⟨u, hu, w, hw, hxeq⟩ := hx
    have hxeq' : u * w = x := hxeq
    have hxM' : x ∈ (⁅M, M⁆ : Subgroup G) := hc.hallCore_le_commutator hxH
    have hwM' : w ∈ (⁅M, M⁆ : Subgroup G) := by
      have h := (⁅M, M⁆ : Subgroup G).mul_mem
        (Subgroup.inv_mem _ (hc.le_commutator_E hu)) hxM'
      rw [← hxeq'] at h
      simpa [mul_assoc] using h
    have hw1 : w = 1 := Subgroup.disjoint_def.1 hc.disjoint_commutator_W₁ hwM' hw
    have hxu : x = u := by rw [← hxeq', hw1, mul_one]
    rw [hxu] at hxH
    exact hxu.trans (Subgroup.disjoint_def.1 hdisjHU hxH hu)
  have hcfg := hc.isPTypeConfig hsolvM hcIIToIV.prime_natCard_W₁ hUne
  have hcardH : Nat.card ↥(hallCoreOf M) = Nat.card ↥(hallCore ↥M) := by
    rw [hallCoreOf_eq]
    exact Subgroup.card_map_of_injective M.subtype_injective
  have hcardUW : Nat.card ↥(U.subgroupOf M ⊔ W₁.subgroupOf M) = Nat.card ↥(U ⊔ W₁) := by
    rw [← Subgroup.subgroupOf_sup hUle hW₁le]
    exact natCard_subgroupOf hUW₁le
  have hcop : Nat.Coprime (Nat.card ↥(hallCoreOf M)) (Nat.card ↥(U ⊔ W₁)) := by
    rw [hcardH, ← hcardUW]
    exact hcfg.coprime_natCard_H_sup
  have hfpf : IsFixedPointFreeOn U W₁ := by
    intro b hb hb1
    rw [centralizerIn_eq, centralizer_coe_eq_centralizer_singleton (rfl : zpowers b = zpowers b)]
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.1 hx
    have h1 : x ∈ (⁅M, M⁆ : Subgroup G) ⊓ centralizer ({b} : Set G) :=
      Subgroup.mem_inf.2 ⟨hc.le_commutator_E hxU, hxc⟩
    rw [hc.inf_centralizer_eq_W₂ b hb hb1] at h1
    exact Subgroup.mem_bot.2
      (Subgroup.disjoint_def.1 hdisjHU (hc.le_hallCore_W₂ h1) hxU)
  have hcentH : centralizerIn (hallCoreOf M) W₁ = W₂ := by
    rw [centralizerIn_eq, hallCoreOf_eq]
    refine le_antisymm ?_ (le_inf hc.le_hallCore_W₂ hc.le_centralizer_W₁)
    calc (hallCore ↥M).map M.subtype ⊓ centralizer (W₁ : Set G)
        ≤ (⁅M, M⁆ : Subgroup G) ⊓ centralizer (W₁ : Set G) :=
          inf_le_inf_right _ hc.hallCore_le_commutator
      _ = W₂ := hc.inf_centralizer_W₁_eq_W₂
  obtain ⟨hCU, hIDP, hnormC⟩ :=
    chiefData_fitting_product hsolvM hcIIToIV.prime_natCard_W₁ hUne hc
  refine ⟨hpprime, hqprime, hoddp, hoddq, hpq, hUne,
    { sup_eq := hsup
      le_normalizer := by
        rw [hallCoreOf_eq]; exact le_normalizer_map_subtype_hallCore M
      disjoint := hdisj },
    { sup_eq := rfl
      le_normalizer := sup_le Subgroup.le_normalizer hc.le_normalizer_E
      disjoint := hc.disjoint_commutator_W₁.mono_left hc.le_commutator_E },
    hcop, hfpf, hcentH, hCU, hIDP, hnormC,
    chiefData_exists_chief_layer hsolvM hcIIToIV.prime_natCard_W₁ hUne hc, ?_⟩
  intro H₀ hH₀ hlayer
  obtain ⟨hElem, hinfW₂, hquot⟩ :=
    chiefData_layer_elementary hsolvM hcIIToIV.prime_natCard_W₁ (hpdef ▸ hpprime) hUne hc
      p q hpdef hqdef H₀ hH₀ hlayer
  obtain ⟨hnorm, hprod, hnorm1, hnorm2⟩ :=
    chiefData_layer_products hsolvM hcIIToIV.prime_natCard_W₁ hUne hc H₀ hlayer
  exact ⟨hElem, hinfW₂, hnorm, hprod, hnorm1, hnorm2, hquot⟩

end CFSG.FeitThompson.Proofs

end
