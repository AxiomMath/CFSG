module

public import CFSG.FeitThompson.Local.ReducedKernelExponentPrimeSpecial
import CFSG.FeitThompson.Local.TwoPrimeComplementFaithfulAction
public import CFSG.FeitThompson.Local.CoprimeDisplacementFixedInDerived
public import Mathlib.RepresentationTheory.Invariants
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition
import CFSG.FeitThompson.Local.InvariantComplementFittingSelfCentralizing
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
import CFSG.FeitThompson.Representations.PrimeComplementNoFixedVectorCentralizes

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

section Aux

variable {W : Type*} [Group W]

theorem natCard_map_mk'_frattini_mul_natCard_inf (S : Subgroup W) :
    Nat.card ↥(S.map (QuotientGroup.mk' (frattini W))) * Nat.card ↥(S ⊓ frattini W)
      = Nat.card ↥S := by
  set f := (QuotientGroup.mk' (frattini W)).comp S.subtype with hf
  have hrange : f.range = S.map (QuotientGroup.mk' (frattini W)) := by
    rw [hf, MonoidHom.range_comp, Subgroup.subtype_range]
  have hker : Nat.card ↥f.ker = Nat.card ↥(S ⊓ frattini W) := by
    have he : f.ker = (frattini W).subgroupOf S := by
      ext x
      simp [hf, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [he, ← Subgroup.card_map_of_injective (f := S.subtype) S.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← hrange, ← hker]
  exact natCard_range_mul_natCard_ker f

variable [Finite W]

theorem index_eq_natCard_of_sup_eq_top_of_inf_eq_bot (S T : Subgroup W)
    (hnorm : T ≤ normalizer (S : Set W)) (hsup : S ⊔ T = ⊤) (hinf : S ⊓ T = ⊥) :
    S.index = Nat.card ↥T := by
  have h := natCard_sup_mul_natCard_inf_of_le_normalizer hnorm
  rw [hsup, hinf] at h
  simp only [Subgroup.card_top] at h
  have h2 : Nat.card ↥S * S.index = Nat.card ↥S * Nat.card ↥T := by
    rw [Subgroup.card_mul_index]; simpa using h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2

theorem isCyclic_of_isZGroup_of_isPGroup [IsZGroup W] {q : ℕ} (hq : q.Prime)
    (hW : IsPGroup q W) : IsCyclic W :=
  have := Fact.mk hq
  have : Group.IsNilpotent W := hW.isNilpotent
  inferInstance

end Aux

section AuxCyclic

variable {W : Type*} [Group W] [IsCyclic W] [Nontrivial W]

theorem natCard_eq_of_isCyclic_of_pow_eq_one {q : ℕ} (hq : q.Prime)
    (hexp : ∀ x : W, x ^ q = 1) : Nat.card W = q := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  have hcard : orderOf g = Nat.card W := orderOf_eq_card_of_forall_mem_zpowers hg
  rcases (Nat.dvd_prime hq).1 (orderOf_dvd_of_pow_eq_one (hexp g)) with h1 | h1
  · exfalso
    rw [h1] at hcard
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial W)
    exact hab (Subsingleton.elim (h := (Nat.card_eq_one_iff_unique.1 hcard.symm).1) a b)
  · rw [← hcard, h1]

end AuxCyclic

section Dictionary

variable {A W : Type*} [Group A] [Group W] (ρ : A →* MulAut W) (D : Subgroup A)
  [MulDistribMulAction ↥D W] (hsmul : ∀ (d : ↥D) (v : W), (d • v : W) = ρ (d : A) v)

include hsmul

theorem fixedPoints_subgroup_eq_actionCentralizer :
    FixedPoints.subgroup ↥D W = actionCentralizer ρ D := by
  ext v
  rw [FixedPoints.mem_subgroup, mem_actionCentralizer]
  refine ⟨fun h d hd => ?_, fun h m => ?_⟩
  · rw [← hsmul ⟨d, hd⟩ v]; exact h ⟨d, hd⟩
  · rw [hsmul]; exact h (m : A) m.2

theorem smulDisplacementSubgroup_eq_actionCommutator :
    smulDisplacementSubgroup ↥D W = actionCommutator ρ D := by
  rw [smulDisplacementSubgroup_eq_closure, actionCommutator_eq_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨a, v, rfl⟩; exact ⟨v, (a : A), a.2, by rw [hsmul]⟩
  · rintro ⟨x, d, hd, rfl⟩; exact ⟨⟨d, hd⟩, x, by rw [hsmul]⟩

end Dictionary

section Coprime

variable {A W : Type*} [Group A] [Group W] (ρ : A →* MulAut W) (D : Subgroup A)

theorem normal_actionCommutator : (actionCommutator ρ D).Normal := by
  let _ : MulDistribMulAction ↥D W := MulDistribMulAction.compHom W (ρ.comp D.subtype)
  rw [← smulDisplacementSubgroup_eq_actionCommutator ρ D (fun _ _ => rfl)]
  infer_instance

theorem isCompl_actionCentralizer_actionCommutator [Finite W] [Finite ↥D]
    (hW : IsMulCommutative W) (hcop : (Nat.card ↥D).Coprime (Nat.card W)) :
    IsCompl (actionCentralizer ρ D) (actionCommutator ρ D) := by
  let _ : MulDistribMulAction ↥D W := MulDistribMulAction.compHom W (ρ.comp D.subtype)
  rw [← smulDisplacementSubgroup_eq_actionCommutator ρ D (fun _ _ => rfl),
    ← fixedPoints_subgroup_eq_actionCentralizer ρ D (fun _ _ => rfl)]
  exact isCompl_fixedPoints_smulDisplacementSubgroup hW hcop

theorem sup_actionCentralizer_actionCommutator_eq_top [Finite W] [Finite ↥D]
    [Group.IsSolvable W] [Group.IsSolvable ↥D] (hcop : (Nat.card ↥D).Coprime (Nat.card W)) :
    actionCentralizer ρ D ⊔ actionCommutator ρ D = ⊤ := by
  let _ : MulDistribMulAction ↥D W := MulDistribMulAction.compHom W (ρ.comp D.subtype)
  rw [← smulDisplacementSubgroup_eq_actionCommutator ρ D (fun _ _ => rfl),
    ← fixedPoints_subgroup_eq_actionCentralizer ρ D (fun _ _ => rfl), sup_comm]
  exact smulDisplacementSubgroup_sup_fixedPoints_subgroup ↥D W hcop

end Coprime

section Lifting

variable {A W : Type*} [Group A] [Group W] [Finite A] [Finite W] [Group.IsSolvable W]

theorem actionCentralizer_frattiniQuotientAction_eq_map (ρ : A →* MulAut W) (D : Subgroup A)
    [Group.IsSolvable ↥D] (hcop : (Nat.card ↥D).Coprime (Nat.card W)) :
    actionCentralizer (frattiniQuotientAction ρ) D
      = (actionCentralizer ρ D).map (QuotientGroup.mk' (frattini W)) := by
  set ρ' : ↥D →* MulAut W := ρ.comp D.subtype with hρ'
  have hN : IsInvariantSubgroup ρ' (frattini W) := isInvariantSubgroup_of_characteristic _ _
  have hquot : ∀ (b : ↥D) (x : W ⧸ frattini W),
      hN.quotientAut b x = frattiniQuotientAction ρ (b : A) x := by
    intro b x
    induction x using QuotientGroup.induction_on with
    | H v => rw [hN.quotientAut_mk, frattiniQuotientAction_mk]; rfl
  refine le_antisymm (fun t ht => ?_) ?_
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini W) t
    have hfix : ∀ b : ↥D, hN.quotientAut b (QuotientGroup.mk x : W ⧸ frattini W)
        = QuotientGroup.mk x := fun b => by
      rw [hquot]; exact mem_actionCentralizer.1 ht (b : A) b.2
    obtain ⟨v, hv, hvx⟩ := exists_mem_fixedPoints_range_mk_eq hN hcop hfix
    refine ⟨v, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_actionCentralizer]
      intro d hd
      exact (mem_fixedPoints_range_iff ρ').1 hv ⟨d, hd⟩
    · simpa using hvx
  · rintro _ ⟨x, hx, rfl⟩
    rw [QuotientGroup.mk'_apply, mem_actionCentralizer]
    intro d hd
    rw [frattiniQuotientAction_mk, mem_actionCentralizer.1 hx d hd]

end Lifting

section Linear

variable {M : Type*} [Group M] {A : Type*} [Group A] {W : Type*} [AddCommGroup W]
  (r : ℕ) [Module (ZMod r) W] (σ : M →* MulAut A) (e : A ≃* Multiplicative W)

theorem representationOfMulAut_eq_one_iff (m : M) :
    representationOfMulAut r σ e m = 1 ↔ σ m = 1 := by
  refine ⟨fun h => MulEquiv.ext fun a => ?_, fun h => LinearMap.ext fun v => ?_⟩
  · have h2 := congrArg (fun f : W →ₗ[ZMod r] W => f (Multiplicative.toAdd (e a))) h
    simp only [representationOfMulAut_apply_toAdd, Module.End.one_apply] at h2
    simpa using e.injective (by simpa using congrArg Multiplicative.ofAdd h2)
  · rw [representationOfMulAut_apply, h]
    simp

theorem mem_invariants_representationOfMulAut_comp_subtype_iff (D : Subgroup M) (v : W) :
    v ∈ Representation.invariants ((representationOfMulAut r σ e).comp D.subtype) ↔
      e.symm (Multiplicative.ofAdd v) ∈ actionCentralizer σ D := by
  rw [Representation.mem_invariants, mem_actionCentralizer]
  constructor
  · intro h d hd
    have h2 := h ⟨d, hd⟩
    simp only [MonoidHom.comp_apply, representationOfMulAut_apply] at h2
    exact e.injective (by simpa using congrArg Multiplicative.ofAdd h2)
  · intro h d
    simp only [MonoidHom.comp_apply, representationOfMulAut_apply]
    rw [show (D.subtype d : M) = (d : M) from rfl, h (d : M) d.2]
    simp

theorem invariants_representationOfMulAut_comp_subtype_eq_bot_iff (D : Subgroup M) :
    Representation.invariants ((representationOfMulAut r σ e).comp D.subtype) = ⊥ ↔
      actionCentralizer σ D = ⊥ := by
  constructor
  · intro h
    refine le_bot_iff.1 fun a ha => ?_
    have hv : Multiplicative.toAdd (e a) ∈
        Representation.invariants ((representationOfMulAut r σ e).comp D.subtype) := by
      rw [mem_invariants_representationOfMulAut_comp_subtype_iff]
      simpa using ha
    rw [h, Submodule.mem_bot] at hv
    rw [Subgroup.mem_bot]
    simpa using e.injective (by simpa using congrArg Multiplicative.ofAdd hv)
  · intro h
    refine le_bot_iff.1 fun v hv => ?_
    rw [mem_invariants_representationOfMulAut_comp_subtype_iff, h, Subgroup.mem_bot] at hv
    have h1 : Multiplicative.ofAdd v = 1 := by simpa using congrArg (fun x => e x) hv
    simpa using congrArg Multiplicative.toAdd h1

end Linear

variable {G : Type u} [Group G] [Finite G]

namespace IsReducedPrimeCentralizerKernel

variable {p q : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsReducedPrimeCentralizerKernel p q H R R0 V K U N P)

include hc

theorem P_le_H : P ≤ H := le_of_le_of_eq le_sup_right hc.sup_V_K_P

theorem inf_P_R : P ⊓ R = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_right _ hc.P_le_H).trans_eq hc.admissible.inf_eq_bot)

theorem isSolvable_K : Group.IsSolvable ↥K :=
  haveI := hc.admissible.isSolvable
  isSolvable_of_le (le_top : K ≤ ⊤)

theorem isSolvable_R_subgroupOf : Group.IsSolvable ↥(R.subgroupOf (P ⊔ R)) :=
  haveI := hc.admissible.isSolvable
  isSolvable_of_le (le_top : R.subgroupOf (P ⊔ R) ≤ ⊤)

theorem isMulCommutative_quotient_frattini : IsMulCommutative (↥K ⧸ frattini ↥K) := by
  obtain ⟨d, -, ⟨e⟩⟩ := hc.exists_mulEquiv_quotient_frattini
  exact ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

theorem coprime_natCard_P_R : (Nat.card ↥P).Coprime (Nat.card ↥R) := by
  have hpr : p ≠ Nat.card ↥R0 :=
    have : Fact p.Prime := ⟨hc.prime_p⟩
    ne_natCard_of_minimal hc.admissible hc.not_hasPLengthLeOne hc.minimal
  rw [hc.card_P, hc.R_eq]
  exact ((Nat.coprime_primes hc.prime_p hc.admissible.prime_card).2 hpr).pow_left _

theorem coprime_natCard_R_subgroupOf_K :
    (Nat.card ↥(R.subgroupOf (P ⊔ R))).Coprime (Nat.card ↥K) := by
  have := Fact.mk hc.prime_q
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hc.isPGroup_K
  rw [natCard_subgroupOf_of_le (le_sup_right : R ≤ P ⊔ R), hn, hc.R_eq]
  exact ((Nat.coprime_primes hc.admissible.prime_card hc.prime_q).2
    (fun h => hc.q_ne_r h.symm)).pow_right _

theorem coprime_natCard_R_subgroupOf_quotient :
    (Nat.card ↥(R.subgroupOf (P ⊔ R))).Coprime (Nat.card (↥K ⧸ frattini ↥K)) := by
  have := Fact.mk hc.prime_q
  obtain ⟨d, hd, -⟩ := hc.exists_mulEquiv_quotient_frattini
  rw [natCard_subgroupOf_of_le (le_sup_right : R ≤ P ⊔ R), hd, hc.R_eq]
  exact ((Nat.coprime_primes hc.admissible.prime_card hc.prime_q).2
    (fun h => hc.q_ne_r h.symm)).pow_right _

theorem normal_P_subgroupOf : (P.subgroupOf (P ⊔ R)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hc.R_le_normalizer_P)

theorem isComplement'_subgroupOf :
    (P.subgroupOf (P ⊔ R)).IsComplement' (R.subgroupOf (P ⊔ R)) := by
  have hn := hc.normal_P_subgroupOf
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, ← subgroupOf_inf, hc.inf_P_R, Subgroup.bot_subgroupOf]
  · have hmul := Subgroup.normal_mul (P.subgroupOf (P ⊔ R)) (R.subgroupOf (P ⊔ R))
    rw [← hmul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self,
      Subgroup.coe_top]

theorem commutator_subgroupOf_eq :
    ⁅P.subgroupOf (P ⊔ R), R.subgroupOf (P ⊔ R)⁆ = P.subgroupOf (P ⊔ R) := by
  rw [commutator_subgroupOf le_sup_left le_sup_right, ← hc.P_eq_commutator]

theorem odd_natCard_sup : Odd (Nat.card ↥(P ⊔ R)) :=
  hc.admissible.odd_card.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)

theorem map_subtype_actionCentralizer_R :
    (actionCentralizer hc.action (R.subgroupOf (P ⊔ R))).map K.subtype
      = K ⊓ centralizer (R : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_iff, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun g hg => ?_⟩
    have hgm : g ∈ P ⊔ R := (le_sup_right : R ≤ P ⊔ R) hg
    have h := mem_actionCentralizer.1 hy ⟨g, hgm⟩ (Subgroup.mem_subgroupOf.2 hg)
    have h2 := congrArg (fun z : ↥K => (z : G)) h
    rw [hc.coe_action_apply] at h2
    calc g * (y : G) = g * (y : G) * g⁻¹ * g := by group
      _ = (y : G) * g := by rw [h2]
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [mem_actionCentralizer]
    intro d hd
    refine Subtype.ext ?_
    rw [hc.coe_action_apply]
    have hcomm := hx (d : G) (Subgroup.mem_subgroupOf.1 hd)
    calc (d : G) * x * (d : G)⁻¹ = x * (d : G) * (d : G)⁻¹ := by rw [← hcomm]
      _ = x := by group

theorem map_subtype_actionCommutator_R :
    (actionCommutator hc.action (R.subgroupOf (P ⊔ R))).map K.subtype = ⁅K, R⁆ := by
  rw [actionCommutator_eq_closure, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, coe_subtype]
  constructor
  · rintro ⟨y, ⟨x, d, hd, rfl⟩, rfl⟩
    refine ⟨(x : G)⁻¹, K.inv_mem x.2, (d : G), Subgroup.mem_subgroupOf.1 hd, ?_⟩
    rw [commutatorElement_def, Subgroup.coe_mul, InvMemClass.coe_inv, hc.coe_action_apply]
    group
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hbm : b ∈ P ⊔ R := (le_sup_right : R ≤ P ⊔ R) hb
    set x : ↥K := (⟨a, ha⟩ : ↥K)⁻¹ with hx
    refine ⟨x⁻¹ * hc.action ⟨b, hbm⟩ x, ⟨x, ⟨b, hbm⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩, ?_⟩
    rw [Subgroup.coe_mul, InvMemClass.coe_inv, hc.coe_action_apply, hx, InvMemClass.coe_inv,
      commutatorElement_def]
    group

theorem natCard_actionCentralizer_R :
    Nat.card ↥(actionCentralizer hc.action (R.subgroupOf (P ⊔ R)))
      = Nat.card ↥(K ⊓ centralizer (R : Set G)) := by
  rw [← hc.map_subtype_actionCentralizer_R, Subgroup.card_map_of_injective K.subtype_injective]

theorem natCard_actionCommutator_R :
    Nat.card ↥(actionCommutator hc.action (R.subgroupOf (P ⊔ R)))
      = Nat.card ↥(⁅K, R⁆ : Subgroup G) := by
  rw [← hc.map_subtype_actionCommutator_R, Subgroup.card_map_of_injective K.subtype_injective]

theorem commutator_K_R_le : (⁅K, R⁆ : Subgroup G) ≤ K :=
  hc.map_subtype_actionCommutator_R ▸ Subgroup.map_subtype_le _

theorem actionCentralizer_frattiniQuotientAction_R_ne_bot :
    actionCentralizer (frattiniQuotientAction hc.action) (R.subgroupOf (P ⊔ R)) ≠ ⊥ := by
  intro hbot
  have hq := Fact.mk hc.prime_q
  obtain ⟨d, -, ⟨e0⟩⟩ := hc.exists_mulEquiv_quotient_frattini
  set e : (↥K ⧸ frattini ↥K) ≃* Multiplicative (Fin d → ZMod q) :=
    e0.trans (MulEquiv.piMultiplicative (fun _ : Fin d => ZMod q)).symm with he
  set σ := frattiniQuotientAction hc.action with hσ
  set ρ := representationOfMulAut q σ e with hρ
  have hsolv : Group.IsSolvable ↥(P ⊔ R) :=
    haveI := hc.admissible.isSolvable
    isSolvable_of_le (le_top : (P ⊔ R) ≤ ⊤)
  have hn := hc.normal_P_subgroupOf
  have hCV : Representation.invariants (ρ.comp (R.subgroupOf (P ⊔ R)).subtype) = ⊥ :=
    (invariants_representationOfMulAut_comp_subtype_eq_bot_iff q σ e _).2 hbot
  have hcop : (Nat.card ↥(P.subgroupOf (P ⊔ R))).Coprime
      (Nat.card ↥(R.subgroupOf (P ⊔ R))) := by
    rw [natCard_subgroupOf_of_le (le_sup_left : P ≤ P ⊔ R),
      natCard_subgroupOf_of_le (le_sup_right : R ≤ P ⊔ R)]
    exact hc.coprime_natCard_P_R
  have hr : (Nat.card ↥(R.subgroupOf (P ⊔ R))).Prime := by
    rw [natCard_subgroupOf_of_le (le_sup_right : R ≤ P ⊔ R), hc.R_eq]
    exact hc.admissible.prime_card
  have hkey : ∀ x ∈ P.subgroupOf (P ⊔ R), σ x = 1 := by
    intro x hx
    rw [← representationOfMulAut_eq_one_iff q σ e]
    refine eq_one_of_mem_commutator_of_invariants_eq_bot_zmod hc.odd_natCard_sup
      hc.isComplement'_subgroupOf hcop hr hc.not_dvd_natCard_sup ρ hCV ?_
    rw [hc.commutator_subgroupOf_eq]
    exact hx
  refine hc.P_ne_bot (le_bot_iff.1 fun x hx => ?_)
  have hxm : x ∈ P ⊔ R := (le_sup_left : P ≤ P ⊔ R) hx
  have h1 : σ (⟨x, hxm⟩ : ↥(P ⊔ R)) = 1 := hkey _ (Subgroup.mem_subgroupOf.2 hx)
  have h2 := (injective_iff_map_eq_one _).1 hc.injective_frattiniQuotientAction _ h1
  rw [Subgroup.mem_bot]
  simpa using congrArg (fun z : ↥(P ⊔ R) => (z : G)) h2

theorem actionCentralizer_frattiniQuotientAction_R_eq_map :
    actionCentralizer (frattiniQuotientAction hc.action) (R.subgroupOf (P ⊔ R))
      = (actionCentralizer hc.action (R.subgroupOf (P ⊔ R))).map
          (QuotientGroup.mk' (frattini ↥K)) :=
  haveI := hc.isSolvable_K
  haveI := hc.isSolvable_R_subgroupOf
  actionCentralizer_frattiniQuotientAction_eq_map _ _ hc.coprime_natCard_R_subgroupOf_K

theorem map_mk'_actionCentralizer_R_ne_bot :
    (actionCentralizer hc.action (R.subgroupOf (P ⊔ R))).map
      (QuotientGroup.mk' (frattini ↥K)) ≠ ⊥ :=
  hc.actionCentralizer_frattiniQuotientAction_R_eq_map ▸
    hc.actionCentralizer_frattiniQuotientAction_R_ne_bot

theorem natCard_actionCentralizer_R_eq :
    Nat.card ↥(actionCentralizer hc.action (R.subgroupOf (P ⊔ R))) = q := by
  set C := actionCentralizer hc.action (R.subgroupOf (P ⊔ R)) with hC
  have hZamb : IsZGroup ↥(centralizer (R0 : Set G) ⊓ H : Subgroup G) :=
    hc.admissible.isZGroup_centralizer
  have hZ : IsZGroup ↥C := by
    refine isZGroup_of_map_subtype_le (W := (centralizer (R0 : Set G) ⊓ H : Subgroup G)) _ ?_
    rw [hC, hc.map_subtype_actionCentralizer_R]
    refine le_inf ?_ (inf_le_left.trans hc.K_le_H)
    rw [← hc.R_eq]
    exact inf_le_right
  have hcyc : IsCyclic ↥C :=
    isCyclic_of_isZGroup_of_isPGroup hc.prime_q (hc.isPGroup_K.to_subgroup _)
  have hnt : Nontrivial ↥C := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun hbot => ?_
    refine hc.map_mk'_actionCentralizer_R_ne_bot ?_
    rw [← hC, hbot, Subgroup.map_bot]
  refine natCard_eq_of_isCyclic_of_pow_eq_one hc.prime_q fun x => ?_
  refine Subtype.ext (Subtype.ext ?_)
  simpa using hc.pow_eq_one (x : ↥K).2

theorem inf_centralizer_R_inf_frattini_eq_bot :
    actionCentralizer hc.action (R.subgroupOf (P ⊔ R)) ⊓ frattini ↥K = ⊥ := by
  set C := actionCentralizer hc.action (R.subgroupOf (P ⊔ R)) with hC
  have hcount := natCard_map_mk'_frattini_mul_natCard_inf (W := ↥K) C
  have hcard : Nat.card ↥C = q := hc.natCard_actionCentralizer_R_eq
  have hgt : 1 < Nat.card ↥(C.map (QuotientGroup.mk' (frattini ↥K))) :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 hc.map_mk'_actionCentralizer_R_ne_bot
  rw [hcard] at hcount
  have hdvd : Nat.card ↥(C ⊓ frattini ↥K) ∣ q := Dvd.intro_left _ hcount
  rcases (Nat.dvd_prime hc.prime_q).1 hdvd with h1 | h1
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    rw [h1] at hcount
    have h2 : Nat.card ↥(C.map (QuotientGroup.mk' (frattini ↥K))) = 1 := by
      have hq : 0 < q := hc.prime_q.pos
      nlinarith [hcount, hgt]
    omega

theorem natCard_inf_centralizer_R : Nat.card ↥(K ⊓ centralizer (R : Set G)) = q := by
  rw [← hc.natCard_actionCentralizer_R, hc.natCard_actionCentralizer_R_eq]

theorem isCompl_quotient_frattini :
    IsCompl (actionCentralizer (frattiniQuotientAction hc.action) (R.subgroupOf (P ⊔ R)))
      (actionCommutator (frattiniQuotientAction hc.action) (R.subgroupOf (P ⊔ R))) :=
  isCompl_actionCentralizer_actionCommutator _ _ hc.isMulCommutative_quotient_frattini
    hc.coprime_natCard_R_subgroupOf_quotient

theorem ne_sup_commutator_frattini :
    actionCommutator hc.action (R.subgroupOf (P ⊔ R)) ⊔ frattini ↥K ≠ ⊤ := by
  intro htop
  have hmap : (actionCommutator hc.action (R.subgroupOf (P ⊔ R))).map
      (QuotientGroup.mk' (frattini ↥K)) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' (frattini ↥K))) htop
    rwa [Subgroup.map_sup, show (frattini ↥K).map (QuotientGroup.mk' (frattini ↥K)) = ⊥ by simp,
      sup_bot_eq, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  have hC := hc.isCompl_quotient_frattini
  rw [map_actionCommutator] at hmap
  have hbot : actionCentralizer (frattiniQuotientAction hc.action) (R.subgroupOf (P ⊔ R)) = ⊥ := by
    refine le_bot_iff.1 ?_
    have := hC.disjoint
    rw [disjoint_iff] at this
    rw [← this, hmap]
    exact le_inf le_rfl le_top
  exact hc.actionCentralizer_frattiniQuotientAction_R_ne_bot hbot

theorem inf_commutator_centralizer_R_eq_bot :
    actionCentralizer hc.action (R.subgroupOf (P ⊔ R))
      ⊓ actionCommutator hc.action (R.subgroupOf (P ⊔ R)) = ⊥ := by
  refine le_bot_iff.1 ?_
  rw [← hc.inf_centralizer_R_inf_frattini_eq_bot]
  refine le_inf inf_le_left fun x hx => ?_
  have h1 : (QuotientGroup.mk x : ↥K ⧸ frattini ↥K)
      ∈ actionCentralizer (frattiniQuotientAction hc.action) (R.subgroupOf (P ⊔ R)) := by
    rw [hc.actionCentralizer_frattiniQuotientAction_R_eq_map]
    exact ⟨x, hx.1, rfl⟩
  have h2 : (QuotientGroup.mk x : ↥K ⧸ frattini ↥K)
      ∈ actionCommutator (frattiniQuotientAction hc.action) (R.subgroupOf (P ⊔ R)) := by
    rw [← map_actionCommutator]
    exact ⟨x, hx.2, rfl⟩
  have hdisj := hc.isCompl_quotient_frattini.disjoint
  rw [disjoint_iff] at hdisj
  have h3 : (QuotientGroup.mk x : ↥K ⧸ frattini ↥K) = 1 := by
    have := hdisj ▸ Subgroup.mem_inf.2 ⟨h1, h2⟩
    rwa [Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).1 h3

theorem normal_actionCommutator_R :
    (actionCommutator hc.action (R.subgroupOf (P ⊔ R))).Normal :=
  normal_actionCommutator _ _

theorem index_actionCommutator_R :
    (actionCommutator hc.action (R.subgroupOf (P ⊔ R))).index = q := by
  have := hc.isSolvable_K
  have := hc.isSolvable_R_subgroupOf
  have hsup : actionCommutator hc.action (R.subgroupOf (P ⊔ R))
      ⊔ actionCentralizer hc.action (R.subgroupOf (P ⊔ R)) = ⊤ := by
    rw [sup_comm]
    exact sup_actionCentralizer_actionCommutator_eq_top _ _ hc.coprime_natCard_R_subgroupOf_K
  have hinf : actionCommutator hc.action (R.subgroupOf (P ⊔ R))
      ⊓ actionCentralizer hc.action (R.subgroupOf (P ⊔ R)) = ⊥ := by
    rw [inf_comm]; exact hc.inf_commutator_centralizer_R_eq_bot
  have hnorm : actionCentralizer hc.action (R.subgroupOf (P ⊔ R))
      ≤ normalizer ((actionCommutator hc.action (R.subgroupOf (P ⊔ R)) : Subgroup ↥K) : Set ↥K) :=
    haveI := hc.normal_actionCommutator_R
    le_normalizer_of_normal
  rw [index_eq_natCard_of_sup_eq_top_of_inf_eq_bot _ _ hnorm hsup hinf,
    hc.natCard_actionCentralizer_R_eq]

theorem index_commutator_K_R : ((⁅K, R⁆ : Subgroup G).subgroupOf K).index = q := by
  have he : (⁅K, R⁆ : Subgroup G).subgroupOf K
      = actionCommutator hc.action (R.subgroupOf (P ⊔ R)) := by
    refine Subgroup.map_injective K.subtype_injective ?_
    rw [Subgroup.subgroupOf_map_subtype, hc.map_subtype_actionCommutator_R,
      inf_eq_left.2 hc.commutator_K_R_le]
  rw [he, hc.index_actionCommutator_R]

theorem primeCentralizerSpecialFixedLine :
    Nat.card ↥(K ⊓ centralizer (R : Set G)) = q ∧
      actionCentralizer hc.action (R.subgroupOf (P ⊔ R)) ⊓ frattini ↥K = ⊥ ∧
      actionCommutator hc.action (R.subgroupOf (P ⊔ R)) ⊔ frattini ↥K ≠ ⊤ ∧
      ((⁅K, R⁆ : Subgroup G).subgroupOf K).index = q ∧
      actionCentralizer hc.action (R.subgroupOf (P ⊔ R))
        ⊓ actionCommutator hc.action (R.subgroupOf (P ⊔ R)) = ⊥ :=
  ⟨hc.natCard_inf_centralizer_R, hc.inf_centralizer_R_inf_frattini_eq_bot,
    hc.ne_sup_commutator_frattini, hc.index_commutator_K_R,
    hc.inf_commutator_centralizer_R_eq_bot⟩

end IsReducedPrimeCentralizerKernel

end CFSG.FeitThompson

end
