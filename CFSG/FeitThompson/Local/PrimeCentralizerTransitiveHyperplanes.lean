module

public import CFSG.FeitThompson.Local.ReducedKernelExponentPrimeSpecial
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
public import CFSG.FeitThompson.Local.TwoQuadraticElementsPrimePowerAutomorphisms
public import CFSG.FeitThompson.Local.FittingModuleHyperplaneDecomposition
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.Local.PrimeCentralizerAbelianCommutatorConjugates
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
import CFSG.FeitThompson.Local.MinimalCounterexampleUniqueMinimalNormal
import CFSG.FeitThompson.Local.FittingMonoNormal

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] {p q : ℕ}

section Aux

theorem conjAct_smul_centralizer (a : ConjAct G) (S : Set G) :
    a • centralizer S = centralizer (a • S) := by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_centralizer_iff,
    Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro h m hm
    have h1 := h (a⁻¹ • m) hm
    have h2 : a • ((a⁻¹ • m) * a⁻¹ • x) = a • (a⁻¹ • x * (a⁻¹ • m)) := congrArg _ h1
    simpa [smul_mul'] using h2
  · intro h m hm
    have h1 := h (a • m) (by simpa using hm)
    have h2 : a⁻¹ • ((a • m) * x) = a⁻¹ • (x * (a • m)) := congrArg _ h1
    simpa [smul_mul'] using h2

theorem conjAct_smul_inf_centralizer (a : ConjAct G) (V L : Subgroup G) :
    a • (V ⊓ centralizer (L : Set G)) = (a • V) ⊓ centralizer ((a • L : Subgroup G) : Set G) := by
  rw [Subgroup.smul_inf, conjAct_smul_centralizer, Subgroup.coe_pointwise_smul]

theorem natCard_conjAct_smul (a : ConjAct G) (L : Subgroup G) :
    Nat.card ↥(a • L) = Nat.card ↥L := (Nat.card_congr (Subgroup.equivSMul a L).toEquiv).symm

theorem relIndex_conjAct_smul [Finite G] (a : ConjAct G) {L K : Subgroup G} (h : L ≤ K) :
    (a • L).relIndex (a • K) = L.relIndex K := by
  have hle : (a • L : Subgroup G) ≤ a • K := Subgroup.pointwise_smul_le_pointwise_smul_iff.2 h
  have h1 := natCard_mul_relIndex hle
  rw [natCard_conjAct_smul, natCard_conjAct_smul] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥L)) (h1.trans (natCard_mul_relIndex h).symm)

theorem le_inv_smul_iff_smul_le {a : ConjAct G} {X Y : Subgroup G} :
    X ≤ a⁻¹ • Y ↔ a • X ≤ Y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a).2 h
    rwa [smul_inv_smul] at h2
  · have h2 := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a⁻¹).2 h
    rwa [inv_smul_smul] at h2

theorem smul_iSup_eq_of_permutes {S : Set (Subgroup G)} {a : ConjAct G}
    (h : ∀ W ∈ S, a • W ∈ S) (hinv : ∀ W ∈ S, a⁻¹ • W ∈ S) :
    a • (⨆ W ∈ S, W) = ⨆ W ∈ S, W := by
  set T : Subgroup G := ⨆ W ∈ S, W with hT
  have key : ∀ b : ConjAct G, (∀ W ∈ S, b • W ∈ S) → b • T ≤ T := by
    intro b hb
    rw [← le_inv_smul_iff_smul_le, hT]
    refine iSup₂_le fun W hW => ?_
    rw [le_inv_smul_iff_smul_le]
    exact le_iSup₂ (f := fun W (_ : W ∈ S) => W) (b • W) (hb W hW)
  refine le_antisymm (key a h) ?_
  have h3 := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a).2 (key a⁻¹ hinv)
  rwa [smul_inv_smul] at h3

end Aux

section Dictionary

variable {A Q : Type*} [CommGroup A] [Group Q] [Module (ZMod p) (Additive A)]

theorem subgroupOrderIsoSubmodule_actionCentralizer (ρ : Q →* MulAut A) (D : Subgroup Q) :
    subgroupOrderIsoSubmodule p A (actionCentralizer ρ D) = fixedSpace (autRep p ρ) D := by
  ext x
  simp only [mem_subgroupOrderIsoSubmodule, mem_actionCentralizer, mem_fixedSpace, autRep_apply]
  refine ⟨fun h d hd => ?_, fun h d hd => congrArg Additive.toMul (h d hd)⟩
  change Additive.ofMul (ρ d (Additive.toMul x)) = x
  rw [h d hd]
  rfl

theorem symm_subgroupOrderIsoSubmodule_fixedSpace (ρ : Q →* MulAut A) (D : Subgroup Q) :
    (subgroupOrderIsoSubmodule p A).symm (fixedSpace (autRep p ρ) D) = actionCentralizer ρ D := by
  rw [← subgroupOrderIsoSubmodule_actionCentralizer, OrderIso.symm_apply_apply]

end Dictionary

theorem map_subtype_actionCentralizer_conjOnNormalized {V K : Subgroup G}
    (hKV : K ≤ normalizer (V : Set G)) (L : Subgroup ↥K) :
    (actionCentralizer (conjOnNormalized V hKV) L).map V.subtype
      = V ⊓ centralizer ((L.map K.subtype : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, mem_actionCentralizer, Subgroup.mem_inf,
    mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, ?_⟩
    rintro g ⟨k, hk, rfl⟩
    have h2 := congrArg (fun y : ↥V => (y : G)) (hv k hk)
    simp only [conjOnNormalized_apply_coe] at h2
    conv_rhs => rw [← h2]
    group
  · rintro ⟨hxV, hx⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    intro k hk
    have h1 : (k : G) * x = x * (k : G) := hx (k : G) ⟨k, hk, rfl⟩
    refine Subtype.ext ?_
    rw [conjOnNormalized_apply_coe]
    simp only
    rw [h1]
    group

theorem relIndex_map_subtype {K : Subgroup G} (L : Subgroup ↥K) :
    (L.map K.subtype).relIndex K = L.index := by
  rw [Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

theorem map_biSup {N : Type*} [Group N] {ι : Type*} (f : G →* N) (S : Set ι)
    (g : ι → Subgroup G) : (⨆ i ∈ S, g i).map f = ⨆ i ∈ S, (g i).map f := by
  simp only [Subgroup.map_iSup]

theorem orderIso_map_biSup {α β : Type*} [CompleteLattice α] [CompleteLattice β] (e : α ≃o β)
    {ι : Type*} (S : Set ι) (g : ι → α) : e (⨆ i ∈ S, g i) = ⨆ i ∈ S, e (g i) := by
  simp only [OrderIso.map_iSup]

def hyperplaneFixedSubgroups (q : ℕ) (V K : Subgroup G) : Set (Subgroup G) :=
  {W | W ≠ ⊥ ∧ ∃ L : Subgroup G, L ≤ K ∧ L.relIndex K = q ∧ W = V ⊓ centralizer (L : Set G)}

theorem mem_hyperplaneFixedSubgroups {V K W : Subgroup G} :
    W ∈ hyperplaneFixedSubgroups q V K ↔ W ≠ ⊥ ∧
      ∃ L : Subgroup G, L ≤ K ∧ L.relIndex K = q ∧ W = V ⊓ centralizer (L : Set G) :=
  Iff.rfl

theorem ne_bot_of_mem_hyperplaneFixedSubgroups {V K W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) : W ≠ ⊥ := hW.1

theorem le_of_mem_hyperplaneFixedSubgroups {V K W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) : W ≤ V := by
  obtain ⟨-, L, -, -, rfl⟩ := hW
  exact inf_le_left

structure IsTransitiveHyperplaneSetup [Finite G] (p q d : ℕ)
    (H R R0 V K U N P : Subgroup G) : Prop where
  reduced : IsReducedPrimeCentralizerKernel p q H R R0 V K U N P
  isElementaryAbelian_K : IsElementaryAbelian q K
  card_K : Nat.card ↥K = q ^ d
  three_le : 3 ≤ d
  card_inf_centralizer_R : Nat.card ↥(V ⊓ centralizer (R : Set G)) = p
  relIndex_commutator : (⁅K, R⁆ : Subgroup G).relIndex K = q

namespace IsTransitiveHyperplaneSetup

variable [Finite G] {d : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsTransitiveHyperplaneSetup p q d H R R0 V K U N P)

include hc

theorem prime_p : p.Prime := hc.reduced.prime_p

theorem prime_q : q.Prime := hc.reduced.prime_q

theorem K_le_H : K ≤ H := hc.reduced.K_le_H

theorem sup_le_normalizer_K : P ⊔ R ≤ normalizer (K : Set G) := hc.reduced.sup_le_normalizer_K

theorem normal_V : V.Normal := by
  rw [hc.reduced.V_eq]; exact normal_map_subtype_fittingRaw hc.reduced.admissible.normal

theorem V_le_H : V ≤ H := hc.reduced.V_eq ▸ Subgroup.map_subtype_le _

theorem isElementaryAbelian_V : IsElementaryAbelian p V := by
  have := Fact.mk hc.prime_p
  rw [hc.reduced.V_eq]
  exact isElementaryAbelian_map_subtype_fittingRaw_of_minimal hc.reduced.admissible
    hc.reduced.not_hasPLengthLeOne hc.reduced.minimal

theorem isMulCommutative_V : IsMulCommutative ↥V := hc.isElementaryAbelian_V.isMulCommutative

theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have hp := hc.prime_p
  have hcard := hc.card_inf_centralizer_R
  rw [h, bot_inf_eq] at hcard
  simp only [Subgroup.card_bot] at hcard
  exact hp.one_lt.ne hcard

theorem inf_K_centralizer_V : K ⊓ centralizer (V : Set G) = ⊥ :=
  hc.reduced.isPrimeCentralizerKernelSetup.inf_K_centralizer_V

theorem sup_sup_sup_eq_top : V ⊔ K ⊔ P ⊔ R = ⊤ := by
  rw [hc.reduced.sup_V_K_P]; exact hc.reduced.admissible.sup_eq_top

theorem smul_mem_hyperplaneFixedSubgroups {a : G} (ha : a ∈ P ⊔ R) {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) :
    ConjAct.toConjAct a • W ∈ hyperplaneFixedSubgroups q V K := by
  obtain ⟨hWne, L, hLK, hLidx, rfl⟩ := hW
  have hVn := hc.normal_V
  have hVfix : ConjAct.toConjAct a • V = V :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer_of_normal ha)
  have hKfix : ConjAct.toConjAct a • K = K :=
    Subgroup.conjAct_pointwise_smul_eq_self (hc.sup_le_normalizer_K ha)
  refine ⟨?_, ConjAct.toConjAct a • L, ?_, ?_, ?_⟩
  · intro h
    refine hWne ?_
    have h2 := congrArg (fun S : Subgroup G => (ConjAct.toConjAct a)⁻¹ • S) h
    simpa using h2
  · rw [← hKfix]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hLK
  · rw [← hKfix, relIndex_conjAct_smul _ hLK, hLidx]
  · rw [conjAct_smul_inf_centralizer, hVfix]

theorem smul_eq_self_of_mem_K {k : G} (hk : k ∈ K) {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) : ConjAct.toConjAct k • W = W := by
  obtain ⟨-, L, hLK, -, rfl⟩ := hW
  have hVn := hc.normal_V
  have hVfix : ConjAct.toConjAct k • V = V :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer_of_normal hk)
  have hLfix : ConjAct.toConjAct k • L = L :=
    Subgroup.conjAct_pointwise_smul_eq_self
      (Subgroup.centralizer_le_normalizer _ (hc.isElementaryAbelian_K.le_centralizer hLK hk))
  rw [conjAct_smul_inf_centralizer, hVfix, hLfix]

private theorem hyperplaneDecomposition_aux :
    (⨆ W ∈ hyperplaneFixedSubgroups q V K, W) = V ∧
      ∀ S T : Set (Subgroup G), S ⊆ hyperplaneFixedSubgroups q V K →
        T ⊆ hyperplaneFixedSubgroups q V K → Disjoint S T →
        (⨆ W ∈ S, W) ⊓ (⨆ W ∈ T, W) = ⊥ := by
  classical
  have hp := hc.prime_p
  have hq := hc.prime_q
  have hqp : q ≠ p := hc.reduced.q_ne_p
  have hVea := hc.isElementaryAbelian_V
  have hKea := hc.isElementaryAbelian_K
  have _instFactp := Fact.mk hp
  have _instVcomm : IsMulCommutative ↥V := hVea.isMulCommutative
  have _instKcomm : IsMulCommutative ↥K := hKea.isMulCommutative
  have hVn := hc.normal_V
  have hKV : K ≤ normalizer (V : Set G) := fun _ hk => Subgroup.le_normalizer_of_normal hk
  let _instCG : CommGroup ↥V := IsMulCommutative.instCommGroup
  have _instMod : Module (ZMod p) (Additive ↥V) :=
    AddCommGroup.zmodModule (G := Additive ↥V) (n := p) fun (x : Additive ↥V) => by
      have h1 : (Additive.toMul x) ^ p = 1 :=
        Subtype.ext (by simpa using hVea.pow_eq_one (Additive.toMul x).2)
      calc p • x = Additive.ofMul ((Additive.toMul x) ^ p) := by simp
        _ = 0 := by rw [h1]; rfl
  have _instfinV : Finite (Additive ↥V) := (inferInstance : Finite ↥V)
  have _instfd : FiniteDimensional (ZMod p) (Additive ↥V) := Module.Finite.of_finite
  have hexp : ∀ x : ↥K, x ^ q = 1 := fun x => Subtype.ext (by simpa using hKea.pow_eq_one x.2)
  set ρ := conjOnNormalized V hKV
  set σ := autRep p ρ
  set e := subgroupOrderIsoSubmodule p ↥V
  have hmapL : ∀ L : Subgroup ↥K, (actionCentralizer ρ L).map V.subtype
      = V ⊓ centralizer ((L.map K.subtype : Subgroup G) : Set G) := fun L =>
    map_subtype_actionCentralizer_conjOnNormalized hKV L
  have hfix : ∀ L : Subgroup ↥K, e (actionCentralizer ρ L) = fixedSpace σ L := fun L =>
    subgroupOrderIsoSubmodule_actionCentralizer ρ L
  have hinv : σ.invariants = ⊥ := by
    have h0 : actionCentralizer ρ (⊤ : Subgroup ↥K) = ⊥ := by
      refine Subgroup.map_injective V.subtype_injective ?_
      rw [hmapL, map_subtype_top', hc.reduced.inf_V_centralizer_K, Subgroup.map_bot]
    have h1 : fixedSpace σ ⊤ = ⊥ := by rw [← hfix, h0, OrderIso.map_bot]
    rwa [fixedSpace_top] at h1
  set ι := {L : Subgroup ↥K // L.index = q ∧ fixedSpace σ L ≠ ⊥}
  set f : ι → Subgroup G := fun L => (actionCentralizer ρ L.1).map V.subtype with hf
  have hne_iff : ∀ L : Subgroup ↥K,
      (actionCentralizer ρ L).map V.subtype ≠ ⊥ ↔ fixedSpace σ L ≠ ⊥ := by
    intro L
    rw [← hfix]
    constructor
    · intro h hbot
      exact h (by rw [e.injective (hbot.trans (OrderIso.map_bot e).symm), Subgroup.map_bot])
    · intro h hbot
      refine h ?_
      rw [Subgroup.map_eq_bot_iff, (MonoidHom.ker_eq_bot_iff _).2 V.subtype_injective,
        le_bot_iff] at hbot
      rw [hbot, OrderIso.map_bot]
  have hrange : hyperplaneFixedSubgroups q V K = Set.range f := by
    ext W
    rw [mem_hyperplaneFixedSubgroups]
    constructor
    · rintro ⟨hWne, L, hLK, hLidx, rfl⟩
      have hmap : (actionCentralizer ρ (L.subgroupOf K)).map V.subtype
          = V ⊓ centralizer (L : Set G) := by
        rw [hmapL, Subgroup.map_subgroupOf_eq_of_le hLK]
      exact ⟨⟨L.subgroupOf K, hLidx, (hne_iff _).1 (by rw [hmap]; exact hWne)⟩, hmap⟩
    · rintro ⟨L, rfl⟩
      exact ⟨(hne_iff _).2 L.2.2, L.1.map K.subtype, Subgroup.map_subtype_le _,
        by rw [relIndex_map_subtype, L.2.1], hmapL L.1⟩
  have hKq : IsPGroup q ↥K := hKea.isPGroup
  have hindep : iSupIndep fun L : ι => fixedSpace σ L.1 :=
    iSupIndep_fixedSpace_hyperplane hq hqp hKq hinv
  have htop : (⨆ L : ι, fixedSpace σ L.1) = ⊤ :=
    iSup_fixedSpace_hyperplane_eq_top hq hqp hKq hinv hexp
  refine ⟨?_, ?_⟩
  ·
    rw [hrange, iSup_range, hf]
    simp only
    rw [← Subgroup.map_iSup]
    have h1 : (⨆ L : ι, actionCentralizer ρ L.1) = ⊤ := by
      refine e.injective ?_
      rw [OrderIso.map_iSup, OrderIso.map_top]
      simpa only [hfix] using htop
    rw [h1, map_subtype_top']
  ·
    intro S T hS hT hdisj
    have hSim : f '' (f ⁻¹' S) = S := Set.image_preimage_eq_of_subset (hrange ▸ hS)
    have hTim : f '' (f ⁻¹' T) = T := Set.image_preimage_eq_of_subset (hrange ▸ hT)
    rw [← hSim, ← hTim, iSup_image, iSup_image]
    simp only [hf]
    rw [← map_biSup, ← map_biSup, ← Subgroup.map_inf _ _ _ V.subtype_injective]
    have hd := hindep.disjoint_biSup_biSup (hdisj.preimage f)
    rw [disjoint_iff] at hd
    have key : (⨆ L ∈ f ⁻¹' S, actionCentralizer ρ L.1)
        ⊓ (⨆ L ∈ f ⁻¹' T, actionCentralizer ρ L.1) = ⊥ := by
      refine e.injective ?_
      rw [OrderIso.map_inf, OrderIso.map_bot, orderIso_map_biSup, orderIso_map_biSup]
      simpa only [hfix] using hd
    rw [key, Subgroup.map_bot]

theorem hyperplaneDecomposition :
    (⨆ W ∈ hyperplaneFixedSubgroups q V K, W) = V ∧
      ∀ S T : Set (Subgroup G), S ⊆ hyperplaneFixedSubgroups q V K →
        T ⊆ hyperplaneFixedSubgroups q V K → Disjoint S T →
        (⨆ W ∈ S, W) ⊓ (⨆ W ∈ T, W) = ⊥ :=
  hyperplaneDecomposition_aux hc

theorem hyperplaneFixedSubgroups_nonempty : (hyperplaneFixedSubgroups q V K).Nonempty := by
  rcases Set.eq_empty_or_nonempty (hyperplaneFixedSubgroups q V K) with hemp | h
  · exfalso
    refine hc.V_ne_bot ?_
    rw [← hc.hyperplaneDecomposition.1, hemp]
    simp
  · exact h

theorem normal_iSup_of_smul_stable {S : Set (Subgroup G)}
    (hS : S ⊆ hyperplaneFixedSubgroups q V K)
    (hstable : ∀ a ∈ P ⊔ R, ∀ W ∈ S, ConjAct.toConjAct a • W ∈ S) :
    (⨆ W ∈ S, W).Normal := by
  set T : Subgroup G := ⨆ W ∈ S, W with hT
  have hTV : T ≤ V := by
    rw [hT]
    exact iSup₂_le fun W hW => le_of_mem_hyperplaneFixedSubgroups (hS hW)
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hc.sup_sup_sup_eq_top]
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  ·
    exact (hc.isElementaryAbelian_V.le_centralizer hTV).trans (Subgroup.centralizer_le_normalizer _)
  ·
    intro k hk
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    refine smul_iSup_eq_of_permutes (fun W hW => ?_) (fun W hW => ?_)
    · rw [hc.smul_eq_self_of_mem_K hk (hS hW)]; exact hW
    · rw [← map_inv, hc.smul_eq_self_of_mem_K (inv_mem hk) (hS hW)]; exact hW
  ·
    intro g hg
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    refine smul_iSup_eq_of_permutes
      (fun W hW => hstable g (Subgroup.mem_sup_left hg) W hW) fun W hW => ?_
    rw [← map_inv]
    exact hstable g⁻¹ (Subgroup.mem_sup_left (P.inv_mem hg)) W hW
  ·
    intro r hr
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    refine smul_iSup_eq_of_permutes
      (fun W hW => hstable r (Subgroup.mem_sup_right hr) W hW) fun W hW => ?_
    rw [← map_inv]
    exact hstable r⁻¹ (Subgroup.mem_sup_right (R.inv_mem hr)) W hW

theorem exists_smul_eq {W₁ W₂ : Subgroup G} (h₁ : W₁ ∈ hyperplaneFixedSubgroups q V K)
    (h₂ : W₂ ∈ hyperplaneFixedSubgroups q V K) :
    ∃ a ∈ P ⊔ R, ConjAct.toConjAct a • W₁ = W₂ := by
  classical
  by_contra hcon
  push_neg at hcon
  set O : Set (Subgroup G) := {W | ∃ a ∈ P ⊔ R, ConjAct.toConjAct a • W₁ = W} with hO
  have hOsub : O ⊆ hyperplaneFixedSubgroups q V K := by
    rintro W ⟨a, ha, rfl⟩
    exact hc.smul_mem_hyperplaneFixedSubgroups ha h₁
  have hW₁O : W₁ ∈ O := ⟨1, one_mem _, by simp⟩
  have hOstable : ∀ a ∈ P ⊔ R, ∀ W ∈ O, ConjAct.toConjAct a • W ∈ O := by
    rintro a ha W ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, by rw [map_mul, mul_smul]⟩
  set O' : Set (Subgroup G) := hyperplaneFixedSubgroups q V K \ O with hO'
  have hO'sub : O' ⊆ hyperplaneFixedSubgroups q V K := Set.diff_subset
  have hW₂O' : W₂ ∈ O' := ⟨h₂, fun ⟨a, ha, hae⟩ => hcon a ha hae⟩
  have hO'stable : ∀ a ∈ P ⊔ R, ∀ W ∈ O', ConjAct.toConjAct a • W ∈ O' := by
    rintro a ha W ⟨hW, hWO⟩
    refine ⟨hc.smul_mem_hyperplaneFixedSubgroups ha hW, fun hmem => hWO ?_⟩
    have := hOstable a⁻¹ (inv_mem ha) _ hmem
    rwa [map_inv, inv_smul_smul] at this
  have hdisj : Disjoint O O' := Set.disjoint_sdiff_right
  have hnormO : (⨆ W ∈ O, W).Normal := hc.normal_iSup_of_smul_stable hOsub hOstable
  have hnormO' : (⨆ W ∈ O', W).Normal := hc.normal_iSup_of_smul_stable hO'sub hO'stable
  have hinf : (⨆ W ∈ O, W) ⊓ (⨆ W ∈ O', W) = ⊥ :=
    hc.hyperplaneDecomposition.2 O O' hOsub hO'sub hdisj
  have hleH : ∀ S : Set (Subgroup G), S ⊆ hyperplaneFixedSubgroups q V K →
      (⨆ W ∈ S, W) ≤ H := by
    intro S hS
    exact iSup_le fun W => iSup_le fun hW =>
      (le_of_mem_hyperplaneFixedSubgroups (hS hW)).trans hc.V_le_H
  have _hp := Fact.mk hc.prime_p
  have hbot := eq_bot_or_eq_bot_of_inf_eq_bot_of_minimal hc.reduced.admissible
    hc.reduced.not_hasPLengthLeOne hc.reduced.minimal (hleH O hOsub) (hleH O' hO'sub) hinf
  have hne : ∀ S : Set (Subgroup G), S ⊆ hyperplaneFixedSubgroups q V K →
      ∀ W ∈ S, (⨆ W ∈ S, W) ≠ ⊥ := by
    intro S hS W hW hzero
    exact (hS hW).1 (le_bot_iff.1 (hzero ▸ le_iSup₂ (f := fun W (_ : W ∈ S) => W) W hW))
  rcases hbot with h | h
  · exact hne O hOsub W₁ hW₁O h
  · exact hne O' hO'sub W₂ hW₂O' h

private theorem hyperplaneFixedSubgroups_eq_orbit {W : Subgroup G}
    (hW : W ∈ hyperplaneFixedSubgroups q V K) :
    hyperplaneFixedSubgroups q V K =
      MulAction.orbit ↥((P ⊔ R).map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom) W := by
  ext W'
  constructor
  · intro hW'
    obtain ⟨a, ha, hae⟩ := hc.exists_smul_eq hW hW'
    exact ⟨⟨ConjAct.toConjAct a, ⟨a, ha, rfl⟩⟩, hae⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    exact hc.smul_mem_hyperplaneFixedSubgroups hb hW

theorem ncard_dvd : (hyperplaneFixedSubgroups q V K).ncard ∣ Nat.card ↥(P ⊔ R) := by
  classical
  obtain ⟨W, hW⟩ := hc.hyperplaneFixedSubgroups_nonempty
  set A' := (P ⊔ R).map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom with hA'
  have hcard : Nat.card ↥A' = Nat.card ↥(P ⊔ R) := by
    rw [hA']
    exact (Nat.card_congr
      ((P ⊔ R).equivMapOfInjective _ (ConjAct.toConjAct (G := G)).injective).toEquiv).symm
  rw [hc.hyperplaneFixedSubgroups_eq_orbit hW, ← hcard, ← MulAction.index_stabilizer ↥A' W]
  exact Subgroup.index_dvd_card _

theorem odd_ncard : Odd (hyperplaneFixedSubgroups q V K).ncard :=
  (hc.reduced.admissible.odd_card_subgroup (P ⊔ R)).of_dvd_nat hc.ncard_dvd

theorem ne_bot_of_relIndex_eq {L : Subgroup G} (hLK : L ≤ K) (hLidx : L.relIndex K = q) :
    L ≠ ⊥ := by
  rintro rfl
  have hq := hc.prime_q
  have h1 := natCard_mul_relIndex hLK
  rw [hLidx, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1, one_mem _⟩⟩, one_mul,
    hc.card_K] at h1
  have hd : q ^ 1 = q ^ d := by rw [pow_one]; exact h1
  have h2 : (1 : ℕ) = d := Nat.pow_right_injective hq.two_le hd
  have h3 := hc.three_le
  omega

theorem one_lt_ncard : 1 < (hyperplaneFixedSubgroups q V K).ncard := by
  classical
  have hfin : (hyperplaneFixedSubgroups q V K).Finite := Set.toFinite _
  obtain ⟨W, hW⟩ := hc.hyperplaneFixedSubgroups_nonempty
  have hpos : 1 ≤ (hyperplaneFixedSubgroups q V K).ncard := by
    rw [Nat.one_le_iff_ne_zero]
    exact fun h0 => (Set.nonempty_of_mem hW).ne_empty ((Set.ncard_eq_zero hfin).1 h0)
  rcases Nat.lt_or_ge 1 (hyperplaneFixedSubgroups q V K).ncard with h | h
  · exact h
  · exfalso
    have hone : (hyperplaneFixedSubgroups q V K).ncard = 1 := le_antisymm h hpos
    obtain ⟨W', hW'eq⟩ := Set.ncard_eq_one.1 hone
    have hWW' : W = W' := by rw [hW'eq] at hW; exact hW
    subst hWW'
    have hVW : V = W := by
      rw [← hc.hyperplaneDecomposition.1, hW'eq]
      simp
    obtain ⟨-, L, hLK, hLidx, hWL⟩ := hW
    have hVC : V ≤ centralizer (L : Set G) := by rw [hVW, hWL]; exact inf_le_right
    have hLC : L ≤ centralizer (V : Set G) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro v hv
      exact ((mem_centralizer_iff.1 (hVC hv)) x hx).symm
    refine hc.ne_bot_of_relIndex_eq hLK hLidx (le_bot_iff.1 ?_)
    rw [← hc.inf_K_centralizer_V]
    exact le_inf hLK hLC

omit hc in
def permutationKernel (q : ℕ) (V K P R : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ P ⊔ R ∧ ∀ W ∈ hyperplaneFixedSubgroups q V K,
    ConjAct.toConjAct a • W = W}
  one_mem' := ⟨one_mem _, fun W _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
    refine ⟨mul_mem haA hbA, fun W hW => ?_⟩
    show ConjAct.toConjAct (a * b) • W = W
    rw [map_mul, mul_smul, hb W hW, ha W hW]
  inv_mem' := by
    rintro a ⟨haA, ha⟩
    refine ⟨inv_mem haA, fun W hW => ?_⟩
    show ConjAct.toConjAct a⁻¹ • W = W
    rw [map_inv, eq_comm, ← smul_eq_iff_eq_inv_smul, ha W hW]

omit hc in
@[simp] theorem mem_permutationKernel {a : G} :
    a ∈ permutationKernel q V K P R ↔ a ∈ P ⊔ R ∧
      ∀ W ∈ hyperplaneFixedSubgroups q V K, ConjAct.toConjAct a • W = W := Iff.rfl

theorem exists_not_fixed :
    ∃ W ∈ hyperplaneFixedSubgroups q V K, ∃ r ∈ R, ConjAct.toConjAct r • W ≠ W := by
  classical
  by_contra hcon
  push_neg at hcon
  set Ker : Subgroup G := permutationKernel q V K P R with hKer
  have hRle : R ≤ Ker := fun r hr =>
    ⟨Subgroup.mem_sup_right hr, fun W hW => hcon W hW r hr⟩
  have hnorm : ∀ a ∈ P ⊔ R, ∀ x ∈ Ker, a * x * a⁻¹ ∈ Ker := by
    intro a haA x hx
    refine ⟨mul_mem (mul_mem haA hx.1) (inv_mem haA), fun W hW => ?_⟩
    have hWa : ConjAct.toConjAct a⁻¹ • W ∈ hyperplaneFixedSubgroups q V K :=
      hc.smul_mem_hyperplaneFixedSubgroups (inv_mem haA) hW
    show ConjAct.toConjAct (a * x * a⁻¹) • W = W
    calc ConjAct.toConjAct (a * x * a⁻¹) • W
        = ConjAct.toConjAct a • (ConjAct.toConjAct x • (ConjAct.toConjAct a⁻¹ • W)) := by
          simp only [map_mul, map_inv, mul_smul]
      _ = ConjAct.toConjAct a • (ConjAct.toConjAct a⁻¹ • W) :=
          congrArg _ ((mem_permutationKernel.1 hx).2 _ hWa)
      _ = W := by rw [map_inv, smul_inv_smul]
  have hPR : (⁅P, R⁆ : Subgroup G) ≤ Ker := by
    rw [Subgroup.commutator_le]
    intro g hg r hr
    have h1 : g * r * g⁻¹ ∈ Ker := hnorm g (Subgroup.mem_sup_left hg) r (hRle hr)
    have h2 : r⁻¹ ∈ Ker := Ker.inv_mem (hRle hr)
    have h3 : (⁅g, r⁆ : G) = (g * r * g⁻¹) * r⁻¹ := commutatorElement_def g r
    rw [show ⁅g, r⁆ = (g * r * g⁻¹) * r⁻¹ from h3]
    exact Ker.mul_mem h1 h2
  have hAle : P ⊔ R ≤ Ker := sup_le (hc.reduced.P_eq_commutator ▸ hPR) hRle
  have hn := hc.one_lt_ncard
  have _hfin : (hyperplaneFixedSubgroups q V K).Finite := Set.toFinite _
  obtain ⟨W₁, hW₁, W₂, hW₂, hne⟩ :=
    (Set.one_lt_ncard_iff_nontrivial (s := hyperplaneFixedSubgroups q V K)).1 hn
  obtain ⟨a, haA, hae⟩ := hc.exists_smul_eq hW₁ hW₂
  exact hne (((hAle haA).2 W₁ hW₁).symm.trans hae)

end IsTransitiveHyperplaneSetup

theorem transitiveHyperplanes [Finite G] {d : ℕ} {H R R0 V K U N P : Subgroup G}
    (hc : IsTransitiveHyperplaneSetup p q d H R R0 V K U N P) :
    (∀ a ∈ P ⊔ R, ∀ W ∈ hyperplaneFixedSubgroups q V K,
        ConjAct.toConjAct a • W ∈ hyperplaneFixedSubgroups q V K) ∧
      (∀ W₁ ∈ hyperplaneFixedSubgroups q V K, ∀ W₂ ∈ hyperplaneFixedSubgroups q V K,
        ∃ a ∈ P ⊔ R, ConjAct.toConjAct a • W₁ = W₂) ∧
      Odd (hyperplaneFixedSubgroups q V K).ncard ∧
      1 < (hyperplaneFixedSubgroups q V K).ncard ∧
      ∃ W ∈ hyperplaneFixedSubgroups q V K, ∃ r ∈ R, ConjAct.toConjAct r • W ≠ W :=
  ⟨fun _ ha _ hW => hc.smul_mem_hyperplaneFixedSubgroups ha hW,
    fun _ h₁ _ h₂ => hc.exists_smul_eq h₁ h₂, hc.odd_ncard, hc.one_lt_ncard, hc.exists_not_fixed⟩

end

end CFSG.FeitThompson
