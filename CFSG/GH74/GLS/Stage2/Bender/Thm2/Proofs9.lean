module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt9
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

theorem lemma_9_1 (h : IG_5_12) : Lemma9_1 := by
  intro G _ _ z p hp N X hN hXp hX hz hNX hnot hF
  apply hnot
  have hXN : X ≤ N := le_trans Subgroup.le_normalizer hNX
  have h1 := (h G p hp N X hXp hXN).1 hF
  rw [inf_eq_right.mpr hNX] at h1
  exact ⟨le_top, hX, hz, h1⟩

section Chain

variable {G : Type} [Group G] [Finite G]

theorem fstar_up (h : IG_5_12) {p : ℕ} (hp : p.Prime) {Y Y₁ : Subgroup G}
    (hY : Fs (normalizer (Y : Set G)) = Op p (normalizer (Y : Set G))) (hle : Y ≤ Y₁)
    (hn : Y₁ ≤ normalizer (Y : Set G)) (hpg : IsPGroup p ↥Y₁) :
    Fs (normalizer (Y₁ : Set G)) = Op p (normalizer (Y₁ : Set G)) := by
  have h1 := h G p hp (normalizer (Y : Set G)) Y₁ hpg hn
  have h3 := h1.2.mp (h1.1 hY)
  have hC : centralizer (Y₁ : Set G) ≤ normalizer (Y : Set G) :=
    le_trans (Subgroup.centralizer_le (fun x hx => hle hx)) (Subgroup.centralizer_le_normalizer _)
  rw [inf_eq_right.mpr hC] at h3
  have h4 := (h G p hp (normalizer (Y₁ : Set G)) Y₁ hpg Subgroup.le_normalizer).2
  rw [inf_idem, inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)] at h4
  exact h4.mpr h3

theorem fstar_chain (h : IG_5_12) {p : ℕ} (hp : p.Prime) {W : Subgroup G} (hW : IsPGroup p ↥W) :
    ∀ Y : Subgroup G, Y ≤ W → Fs (normalizer (Y : Set G)) = Op p (normalizer (Y : Set G)) →
      Fs (normalizer (W : Set G)) = Op p (normalizer (W : Set G)) := by
  intro Y
  induction Y using WellFoundedGT.induction with
  | _ Y ih =>
    intro hYW hY
    by_cases hEq : Y = W
    · rw [← hEq]
      exact hY
    · have hlt : Y < W ⊓ normalizer (Y : Set G) := lt_inf_normalizer_of_lt hp hW (lt_of_le_of_ne hYW hEq)
      have hY1 := fstar_up h hp hY hlt.le inf_le_right (hW.to_le inf_le_left)
      exact ih _ hlt inf_le_left hY1

end Chain

theorem lemma_9_3 (h : IG_5_12) : Lemma9_3 := by
  intro G _ _ z k S M p ctx N X Y hN hNX _hYN hY hW
  have hp := ctx.prime
  have hXW : X ≤ X ⊔ Y := le_sup_left
  have hYW : Y ≤ X ⊔ Y := le_sup_right
  have h1 := fstar_chain h hp hW Y hYW hY.2.2.2
  have h2 : Fs (centralizer ((X ⊔ Y : Subgroup G) : Set G)) =
      Op p (centralizer ((X ⊔ Y : Subgroup G) : Set G)) := by
    have := (h G p hp (normalizer ((X ⊔ Y : Subgroup G) : Set G)) (X ⊔ Y) hW Subgroup.le_normalizer).2
    rw [inf_idem, inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)] at this
    exact this.mp h1
  have hCN : centralizer ((X ⊔ Y : Subgroup G) : Set G) ≤ N :=
    le_trans (Subgroup.centralizer_le (fun x hx => hXW hx))
      (le_trans (Subgroup.centralizer_le_normalizer _) hNX)
  rw [inf_eq_right.mpr hCN]
  exact ⟨pPrimeCoreOf_inf_eq_bot hp hCN h2, Em_eq_bot_of_Fs_eq hp h2⟩

section Fstar27

variable {G : Type} [Group G] [Finite G]

theorem fitting_eq_pCore_of_inf_eq_bot {p : ℕ} (hp : p.Prime) {N : Subgroup G}
    (h : pPrimeCoreOf p N ⊓ centralizer ((Op p N : Subgroup G) : Set G) = ⊥) :
    fittingSubgroup ↥N = pCore p ↥N := by
  have : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    by_cases hqp : (q : ℕ) = p
    · rw [hqp]
    · have : Fact (q : ℕ).Prime := ⟨hq⟩
      have hZ : pCore (q : ℕ) ↥N = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        rw [Subgroup.mem_bot]
        have hcom := (CFSG.LocalCores.distinct_prime_cores_commute (G := ↥N) hq hp hqp).2
        have hcop : Nat.Coprime p (Nat.card ↥(pCore (q : ℕ) ↥N)) := by
          obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥N) (p := (q : ℕ)))
          rw [hn]
          exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hq).mpr (fun h' => hqp h'.symm))
        have hle : pCore (q : ℕ) ↥N ≤ CFSG.pPrimeCore p ↥N := le_sSup ⟨CFSG.pCore_normal, hcop⟩
        have hzO : (z : G) ∈ pPrimeCoreOf p N := ⟨z, hle hz, rfl⟩
        have hzC : (z : G) ∈ centralizer ((Op p N : Subgroup G) : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          rintro y ⟨y', hy', rfl⟩
          have h1 : ⁅z, y'⁆ ∈ ⁅pCore (q : ℕ) ↥N, pCore p ↥N⁆ := Subgroup.commutator_mem_commutator hz hy'
          rw [hcom, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
          exact congrArg Subtype.val h1.symm
        have h2 : (z : G) ∈ pPrimeCoreOf p N ⊓ centralizer ((Op p N : Subgroup G) : Set G) := ⟨hzO, hzC⟩
        rw [h, Subgroup.mem_bot] at h2
        exact Subtype.ext h2
      rw [hZ]
      exact bot_le
  · exact CFSG.pCore_le_fitting ↥N p

omit [Finite G] in
theorem no_component_of_Em_bot {N : Subgroup G} (Y' : Subgroup ↥N)
    (hE : Em (N ⊓ centralizer ((Y'.map N.subtype : Subgroup G) : Set G)) = ⊥) (K : Subgroup ↥N)
    (hK : IsComponent K) (hKC : K ≤ centralizer (Y' : Set ↥N)) : False := by
  set Y : Subgroup G := Y'.map N.subtype with hYdef
  have hDeq : (centralizer (Y' : Set ↥N)).map N.subtype = N ⊓ centralizer (Y : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro y ⟨b, hb, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp ha b hb
      exact congrArg Subtype.val this
    · rintro ⟨hxN, hxC⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro b hb
      have := Subgroup.mem_centralizer_iff.mp hxC (b : G) ⟨b, hb, rfl⟩
      exact Subtype.ext this
  have hcomp := CFSG.LocalCores.component_overgroup hK hKC
  let e : ↥(centralizer (Y' : Set ↥N)) ≃* ↥(N ⊓ centralizer (Y : Set G)) :=
    (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).trans (MulEquiv.subgroupCongr hDeq)
  have hc2 := CFSG.LocalCores.isComponent_map_mulEquiv e hcomp
  have hlayer : layer ↥(N ⊓ centralizer (Y : Set G)) = ⊥ := by
    have := hE
    rw [Em_def', Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  have hle := CFSG.LocalCores.component_le_layer hc2
  rw [hlayer] at hle
  have hbot := le_bot_iff.mp hle
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hc2.1
  rw [hbot] at hnt
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt rfl

theorem prop_9_27 (h : IG_5_12) : Prop9_27 := by
  intro G _ _ z k S M p ctx N X hN hX hXN hXO
  have hp := ctx.prime
  have : Fact p.Prime := ⟨hp⟩
  have hXne : X ≠ ⊥ := hX.2.1
  have hYne : Op p N ≠ ⊥ := fun hY => hXne (le_bot_iff.mp (hY ▸ hXO))
  have hOpN : Op p N ≤ N := Op_le' p N
  have hNY : normalizer ((Op p N : Subgroup G) : Set G) = N := by
    by_cases hNe : N = normalizer ((Op p N : Subgroup G) : Set G)
    · exact hNe.symm
    · exfalso
      have htop := hN.2 _ (lt_of_le_of_ne (le_normalizer_Op' p N) hNe)
      have hnorm : (Op p N).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      have : IsSimpleGroup G := ctx.ctx.std.kps.1
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Op p N) with hb | ht
      · exact hYne hb
      · exact hN.1 (top_le_iff.mp (ht ▸ hOpN))
  have hXNN : NN z p ⊤ X := ⟨le_top, hX.2.1, hX.2.2.1, hX.2.2.2⟩
  have hW : IsPGroup p ↥(Op p N ⊔ X) := by
    rw [sup_eq_left.mpr hXO]
    exact op_isPGroup N
  obtain ⟨h1, h2⟩ := lemma_9_3 h G z k S M p ctx N (Op p N) X hN hNY.le hXN hXNN hW
  rw [sup_eq_left.mpr hXO] at h1 h2
  have hF : fittingSubgroup ↥N = pCore p ↥N := fitting_eq_pCore_of_inf_eq_bot hp h1
  have hL : layer ↥N = ⊥ := by
    refine CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => ?_
    refine no_component_of_Em_bot (pCore p ↥N) h2 K hK ?_
    have hc := CFSG.LocalCores.fitting_layer_commute (G := ↥N)
    rw [hF] at hc
    exact le_trans (CFSG.LocalCores.component_le_layer hK) (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hc))
  rw [Fs_eq_Op_iff]
  show fittingSubgroup ↥N ⊔ layer ↥N = pCore p ↥N
  rw [hF, hL, sup_bot_eq]

end Fstar27

theorem prop_9_14c_of (h : Lemma9_15) : Prop9_14c := by
  intro G _ _ z k S M p ctx Q hQ X hXQ hX hz
  rcases h G z k S M p ctx Q hQ with ha | ⟨-, -, -, hrank⟩
  · exact ha X hXQ hX hz
  · exfalso
    have h3 := three_le_pRank_S ctx.ctx
    omega

end CFSG.GH74.GLS.Stage2.Bender.Thm2
