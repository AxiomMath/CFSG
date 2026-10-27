module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineGen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Coordinator

set_option linter.unusedSectionVars false

@[expose] def Bal209TwoUniqIn : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (a : X), CFSG.Open.IsQuasisimple ↥K →
    IsLieQuot ↥K Bal209TwoIndex → a ∈ Subgroup.normalizer (K : Set X) →
      a ^ 3 ∈ Subgroup.centralizer (K : Set X) → a ∉ Subgroup.centralizer (K : Set X) →
        Bal209F4Aux.InnerAt K a →
        ∀ J J' : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J' → J = J'

@[expose] def Bal209TwoSLOBIn : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B : Subgroup X) (a : X),
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      IsLieQuot ↥K Bal209TwoIndex → GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B →
        a ∈ B → a ∉ Subgroup.centralizer (K : Set X) → Bal209F4Aux.InnerAt K a →
        ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          B ≤ Subgroup.normalizer (J : Set X) →
            IsStronglyLocallyOneBalanced 3 B a J ∨
              CFSG.Open.pRank 3 B ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + 3

theorem bal209TwoUniqIn_of_uniq (h : Bal209TwoUniq) : Bal209TwoUniqIn :=
  fun X _ _ K a hq hK haN ha3 haC _ J J' hJ hJ' => h X K a hq hK haN ha3 haC J J' hJ hJ'

namespace Bal209TwoInnerAux

section Count

theorem card_le_card_mul_card_comap {B G : Type*} [Group B] [Group G] [Finite B] (f : B →* G)
    {N D : Subgroup G} [N.Normal] [Finite D] (hf : f.range ≤ N ⊔ D) :
    Nat.card B ≤ Nat.card D * Nat.card (N.comap f) := by
  have h1 := (N.comap f).card_mul_index
  rw [Subgroup.index_comap] at h1
  have hD0 : N.relIndex D ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_dvd_card N D
    rw [h0, zero_dvd_iff] at this
    exact Nat.card_pos.ne' this
  have h2 : N.relIndex f.range ≤ N.relIndex (N ⊔ D) :=
    Subgroup.relIndex_le_of_le_right hf (by rwa [Subgroup.relIndex_sup_left])
  rw [Subgroup.relIndex_sup_left] at h2
  have h3 : N.relIndex D ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card N D)
  calc Nat.card B = Nat.card (N.comap f) * N.relIndex f.range := h1.symm
    _ ≤ Nat.card (N.comap f) * Nat.card D := Nat.mul_le_mul_left _ (h2.trans h3)
    _ = Nat.card D * Nat.card (N.comap f) := mul_comm _ _

theorem autCenterQuot_conj {Y : Type*} [Group Y] (y : Y) :
    autCenterQuot Y (MulAut.conj y) = MulAut.conj (y : Y ⧸ Subgroup.center Y) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [autCenterQuot_mk, MulAut.conj_apply, MulAut.conj_apply]
    rfl

theorem congr_eq_conj_imp' {K C : Type*} [Group K] [Group C] (e : K ≃* C) (α : MulAut K) (g : C)
    (h : MulAut.congr e α = MulAut.conj g) : α = MulAut.conj (e.symm g) := by
  refine MulEquiv.ext fun k => ?_
  apply e.injective
  have hk := congrArg (fun φ : MulAut C => φ (e k)) h
  simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.symm_apply_apply] at hk
  rw [MulAut.conj_apply, map_mul, map_mul]
  simp only [MulEquiv.apply_symm_apply, map_inv]
  rw [← hk]
  simp

theorem innerAt_of_congr_mem_inner {X : Type} [Group X] {K : Subgroup X}
    (hperf : commutator ↥K = ⊤) {C : Type*} [Group C] (e : (↥K ⧸ Subgroup.center ↥K) ≃* C)
    {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X))
    (h : MulAut.congr e (autCenterQuot ↥K (K.normalizerMonoidHom ⟨b, hb⟩)) ∈
      (MulAut.conj : C →* MulAut C).range) : Bal209F4Aux.InnerAt K b := by
  obtain ⟨g, hg⟩ := h
  have h1 := congr_eq_conj_imp' e _ g hg.symm
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm g)
  rw [← hk, ← autCenterQuot_conj] at h1
  have h2 := autCenterQuot_injective_of_perfect hperf h1
  refine ⟨(k : X), k.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have key : b * x * b⁻¹ = (k : X) * x * (k : X)⁻¹ := by
    have := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : X)) h2
    simpa [MulAut.conj_apply] using this
  calc x * ((k : X)⁻¹ * b) = (k : X)⁻¹ * ((k : X) * x * (k : X)⁻¹) * b := by group
    _ = (k : X)⁻¹ * (b * x * b⁻¹) * b := by rw [key]
    _ = (k : X)⁻¹ * b * x := by group

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley in
theorem card_twistedE6Diag_le {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) : Nat.card (twistedE6Diag K σ) ≤ 9 := by
  classical
  obtain ⟨-, -, h2, h3, -⟩ := twisted_E6_all_characteristic_exact_automorphism_normal_form
    Nat.prime_two le_rfl K (by rw [hK]; norm_num) σ (fun c => by rw [hσ]; norm_num)
  set U := (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ
  have hrank : TwistTag.E6.foldedTag.rank = 4 := by decide
  have htriv : ∀ a : Fin TwistTag.E6.foldedTag.rank, 2 ≤ a.val →
      ∀ u : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ, u = 1 := by
    intro a ha u
    have hfix : σ ((u : orbitField TwistTag.E6 K σ.toRingHom a) : K) =
        ((u : orbitField TwistTag.E6 K σ.toRingHom a) : K) := by
      have hlt : a.val < 4 := hrank ▸ a.2
      have hmem := (u : orbitField TwistTag.E6 K σ.toRingHom a).2
      obtain ⟨n, hn⟩ := a
      simp only at ha hlt
      interval_cases n
      · exact (h2 _).1 hmem
      · exact (h3 _).1 hmem
    rw [hσ, sq] at hfix
    have hne : ((u : orbitField TwistTag.E6 K σ.toRingHom a) : K) ≠ 0 := by
      intro h0
      have : (u : orbitField TwistTag.E6 K σ.toRingHom a) = 0 := Subtype.ext h0
      exact u.ne_zero this
    have h1 : ((u : orbitField TwistTag.E6 K σ.toRingHom a) : K) = 1 := by
      have := mul_right_cancel₀ hne (hfix.trans (one_mul _).symm)
      exact this
    exact Units.ext (Subtype.ext h1)
  let a0 : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩
  let a1 : Fin TwistTag.E6.foldedTag.rank := ⟨1, by decide⟩
  let ι : U → Kˣ × Kˣ := fun u =>
    (Units.map (orbitField TwistTag.E6 K σ.toRingHom a0).subtype.toMonoidHom (u a0),
      Units.map (orbitField TwistTag.E6 K σ.toRingHom a1).subtype.toMonoidHom (u a1))
  have hι : Function.Injective ι := by
    intro u v huv
    simp only [ι, Prod.mk.injEq] at huv
    have hu0 : u a0 = v a0 := by
      apply Units.ext
      apply Subtype.ext
      have := congrArg Units.val huv.1
      rw [Units.coe_map, Units.coe_map] at this
      exact this
    have hu1 : u a1 = v a1 := by
      apply Units.ext
      apply Subtype.ext
      have := congrArg Units.val huv.2
      rw [Units.coe_map, Units.coe_map] at this
      exact this
    funext a
    obtain ⟨n, hn⟩ := a
    have hlt : n < 4 := hrank ▸ hn
    by_cases h01 : n < 2
    · interval_cases n
      · exact hu0
      · exact hu1
    · rw [htriv ⟨n, hn⟩ (by simp only; omega) (u _), htriv ⟨n, hn⟩ (by simp only; omega) (v _)]
  have hU : Nat.card U ≤ Nat.card (Kˣ × Kˣ) := Nat.card_le_card_of_injective ι hι
  have hKu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [Nat.card_prod, hKu] at hU
  haveI : Finite U := Finite.of_injective ι hι
  calc Nat.card (twistedE6Diag K σ) ≤ Nat.card U :=
        Nat.card_le_card_of_surjective _ (compatDiagAutHom TwistTag.E6 K σ.toRingHom).rangeRestrict_surjective
    _ ≤ 9 := hU

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley in
theorem card_le_nine_mul_inner_aux {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hperf : commutator ↥K = ⊤) {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 4)
    (σ : K' ≃+* K') (hσ : ∀ c, σ c = c ^ 2)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* twistedE6RootGroup K' σ)
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card B ≤ 9 * Nat.card ↥(B ⊓ Bal209F4Aux.innerSub K) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form
      Nat.prime_two le_rfl K' (by rw [hK']; norm_num) σ (fun c => by rw [hσ]; norm_num)
  let ρ : ↥B →* MulAut (twistedE6RootGroup K' σ) :=
    (MulAut.congr e).toMonoidHom.comp
      ((autCenterQuot ↥K).comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)))
  have hRA : Nat.card (RingAut K') = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K'
      (by rw [hK']; norm_num)).1
  haveI : Finite (RingAut K') := Nat.finite_of_card_ne_zero (by rw [hRA]; norm_num)
  have hrange : ρ.range ≤ twistedE6Inn K' σ ⊔ twistedE6Diag K' σ := by
    rintro _ ⟨b, rfl⟩
    rw [← hker, MonoidHom.mem_ker]
    have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hBel.2 (b : X) b.2)
    have h3 : Θ (ρ b) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hb3, map_one, map_one]
    have h2 : Θ (ρ b) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := RingAut K') (x := Θ (ρ b))
      rwa [hRA] at this
    calc Θ (ρ b) = Θ (ρ b) ^ 3 * (Θ (ρ b) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]
  haveI : Finite (twistedE6Diag K' σ) := by
    have hf : Finite ((a : Fin TwistTag.E6.foldedTag.rank) →
        (orbitField TwistTag.E6 K' σ.toRingHom a)ˣ) := inferInstance
    exact Finite.of_surjective _ (compatDiagAutHom TwistTag.E6 K' σ.toRingHom).rangeRestrict_surjective
  have hcount := card_le_card_mul_card_comap ρ hrange
  have hΔ := card_twistedE6Diag_le hK' σ hσ
  have hcomap : Nat.card ((twistedE6Inn K' σ).comap ρ) ≤ Nat.card ↥(B ⊓ Bal209F4Aux.innerSub K) := by
    rw [← Subgroup.card_map_of_injective (f := B.subtype) B.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨b.2, ?_⟩
    exact innerAt_of_congr_mem_inner hperf e (hBN b.2) hb
  calc Nat.card B ≤ Nat.card (twistedE6Diag K' σ) * Nat.card ((twistedE6Inn K' σ).comap ρ) := hcount
    _ ≤ 9 * Nat.card ↥(B ⊓ Bal209F4Aux.innerSub K) := Nat.mul_le_mul hΔ hcomap

theorem card_le_nine_mul_inner {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hK : IsLieQuot ↥K Bal209TwoIndex)
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card B ≤ 9 * Nat.card ↥(B ⊓ Bal209F4Aux.innerSub K) := by
  obtain ⟨d, hd, ⟨e₁⟩⟩ := hK
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 ∧ q.exponent = 1 := hd
    obtain ⟨K', hKf, σ, hcard, hσ, ⟨eC⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hcard4 : Nat.card K' = 4 := by
      rw [hcard, hq2.1, hq2.2]; norm_num
    haveI : Finite K' := Nat.finite_of_card_ne_zero (by rw [hcard4]; norm_num)
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by
      have := hσ c
      rwa [hq2.1, hq2.2, pow_one] at this
    exact card_le_nine_mul_inner_aux hq.1 hcard4 σ hσ2 (e₁.trans eC) hBel hBN
  | _ => exact absurd hd (by simp [Bal209TwoIndex])

end Count

section Local

theorem innerOneBalanceThree_of_quotient_center {Y : Type*} [Group Y] (hY : commutator Y = ⊤)
    (h : InnerOneBalanceThree (Y ⧸ Subgroup.center Y)) : InnerOneBalanceThree Y := by
  intro d hdin hd3 hd1 H hH
  set φ := autCenterQuot Y with hφdef
  have hφ : Function.Injective φ := autCenterQuot_injective_of_perfect hY
  have hinn : innerAut (Y ⧸ Subgroup.center Y) ≤ H.map φ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨MulAut.conj y, hH ⟨y, rfl⟩, autCenterQuot_conj y⟩
  have hφd : φ d ∈ innerAut (Y ⧸ Subgroup.center Y) := by
    obtain ⟨y, rfl⟩ := hdin
    exact ⟨(y : Y ⧸ Subgroup.center Y), (autCenterQuot_conj y).symm⟩
  have hφd3 : φ d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hφd1 : φ d ≠ 1 := fun h1 => hd1 (hφ (h1.trans (map_one φ).symm))
  have h0 := h (φ d) hφd hφd3 hφd1 (H.map φ) hinn
  rw [← map_inf_centralizer_of_injective φ hφ, ← map_glaPPrimeCoreOf_of_injective 3 φ hφ] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h0

theorem innerOneBalanceThree_quotient_of_central {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    {N : Subgroup Y} [N.Normal] (hN : N ≤ Subgroup.center Y)
    (h : InnerOneBalanceThree (Y ⧸ Subgroup.center Y)) : InnerOneBalanceThree (Y ⧸ N) := by
  have hperf' : commutator (Y ⧸ N) = ⊤ := by
    have := congrArg (Subgroup.map (QuotientGroup.mk' N)) hperf
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective N)] at this
    rw [commutator]
    exact this
  refine innerOneBalanceThree_of_quotient_center hperf' ?_
  refine Bal209TwoInAux.innerOneBalanceThree_of_mulEquiv ?_ h
  exact (QuotientGroup.quotientMulEquivOfEq (Bal209TwoInAux.center_quotient_eq_map hperf hN)).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center Y) hN)

theorem isCompLocallyBalanced_of_inner {X : Type} [Group X] {K A : Subgroup X}
    (hK3 : InnerOneBalanceThree (barOf 3 K)) (hA : ∀ a ∈ A, Bal209F4Aux.InnerAt K a) :
    IsCompLocallyBalanced 3 1 A K := by
  intro D hD H hH _
  obtain ⟨hDA, hDel, hDcard⟩ := hD
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hcon
    rw [hbot, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hdinn : d ∈ innerAut (barOf 3 K) := by
    obtain ⟨γ, hγA, hγd⟩ := hDA hdD
    have hγA' : (γ : X) ∈ A := (Subgroup.mem_subgroupOf.1 hγA).1
    obtain ⟨k, hk, hc⟩ := hA γ hγA'
    refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
    rw [← hγd]
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [barAut_mk, MulAut.conj_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      have hcx : ((k : X)⁻¹ * γ) * (x : X) = (x : X) * ((k : X)⁻¹ * γ) :=
        (Subgroup.mem_centralizer_iff.1 hc (x : X) x.2).symm
      symm
      show (γ : X) * (x : X) * (γ : X)⁻¹ = (k : X) * (x : X) * (k : X)⁻¹
      calc (γ : X) * (x : X) * (γ : X)⁻¹
          = (k : X) * (((k : X)⁻¹ * γ) * (x : X)) * ((k : X)⁻¹ * γ)⁻¹ * (k : X)⁻¹ := by group
        _ = (k : X) * ((x : X) * ((k : X)⁻¹ * γ)) * ((k : X)⁻¹ * γ)⁻¹ * (k : X)⁻¹ := by rw [hcx]
        _ = (k : X) * (x : X) * (k : X)⁻¹ := by group
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree hK3 hDel hdD hdinn hd1 hH

theorem innerOneBalanceThree_barOf {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hK : IsLieQuot ↥K Bal209TwoIndex) :
    InnerOneBalanceThree (barOf 3 K) := by
  have h3 : 3 ∣ Nat.card ↥K := (bal209TwoParabolic_holds X K hq hK).1
  have hNZ : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
    Bal209TwoInAux.pPrimeCore_le_center_of_quasisimple hq Nat.prime_three h3
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  exact innerOneBalanceThree_quotient_of_central hq.1 hNZ
    (innerOneBalanceThree_of_bal209TwoIndex d hd e)

end Local

end Bal209TwoInnerAux

open Bal209TwoInnerAux Bal209TwoAux

theorem bal209Two_of_inner (hU : Bal209TwoUniqIn) (hR : Bal209TwoSLOBIn) : Bal209Two := by
  intro X _ _ hX K B hcomp hSC hBN hm hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdvd, U, Q, hUK, hU1, hUp, hQK, hQel, hQcard, hQN, hQC⟩ :=
    bal209TwoParabolic_holds X K hcomp.2.2 hK
  have hBel : CFSG.Open.IsElemAbelian 3 B := hSC.2.1
  set C0 : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hC0def
  have hC0el : CFSG.Open.IsElemAbelian 3 C0 := CFSG.Open.IsElemAbelian.mono hBel inf_le_left
  have hC0N : C0 ≤ Subgroup.normalizer (U : Set X) := fun c hc =>
    mem_normalizer_of_mem_centralizer hUK hc.2
  have hQ0 : C0 ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQC : x ∈ Q ⊓ Subgroup.centralizer (K : Set X) := ⟨hx.2, hx.1.2⟩
    rw [hQC] at hxQC
    exact hxQC
  have hcomm : ∀ c ∈ C0, ∀ q ∈ Q, c * q = q * c := fun c hc q hq =>
    (Subgroup.mem_centralizer_iff.1 hc.2 q (hQK hq)).symm
  obtain ⟨E, hEN, hEel, hEcard⟩ :=
    exists_elemAb_normalizer hC0el hQel hcomm hQ0 hC0N hQN
  have hcount : CFSG.Open.pRank 3 C0 + 4 ≤ GLATwoLocalRank 3 X := by
    have hk : Nat.card E = 3 ^ (CFSG.Open.pRank 3 C0 + 4) := by
      rw [hEcard, card_eq_pow_pRank Nat.prime_three hC0el, hQcard, pow_add]
    exact le_glaTwoLocalRank_of_elemAb Nat.prime_three hU1 hUp hEN hEel hk
  have hBrk : CFSG.Open.pRank 3 C0 + 4 ≤ CFSG.Open.pRank 3 B := hcount.trans hm
  set BI : Subgroup X := B ⊓ Bal209F4Aux.innerSub K with hBIdef
  have hBIel : CFSG.Open.IsElemAbelian 3 BI := CFSG.Open.IsElemAbelian.mono hBel inf_le_left
  have hC0BI : C0 ≤ BI := fun x hx =>
    ⟨hx.1, Bal209F4Aux.mem_innerSub.2 ⟨1, K.one_mem, by simpa using hx.2⟩⟩
  have hB9 : Nat.card B ≤ 9 * Nat.card BI := card_le_nine_mul_inner hcomp.2.2 hK hBel hBN
  obtain ⟨A, hABI, hdisj, -, hcardBI⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i224_exists_complement hBIel hC0BI
  have hAB : A ≤ B := hABI.trans inf_le_left
  have hAin : ∀ a ∈ A, Bal209F4Aux.InnerAt K a := fun a ha =>
    Bal209F4Aux.mem_innerSub.1 (hABI ha).2
  have hAel : CFSG.Open.IsElemAbelian 3 A := CFSG.Open.IsElemAbelian.mono hBel hAB
  have hAC : A ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ C0 ⊓ A := ⟨⟨hAB hx.1, hx.2⟩, hx.1⟩
    rw [hdisj] at hx'
    exact hx'
  have hcardA : 3 ^ 2 ≤ Nat.card A := by
    have hB := card_eq_pow_pRank Nat.prime_three hBel
    have hC0c := card_eq_pow_pRank Nat.prime_three hC0el
    set c := CFSG.Open.pRank 3 C0
    have key : 3 ^ c * 81 ≤ 3 ^ c * (9 * Nat.card A) := by
      calc 3 ^ c * 81 = 3 ^ (c + 4) := by ring
        _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hBrk
        _ = Nat.card B := hB.symm
        _ ≤ 9 * Nat.card BI := hB9
        _ = 3 ^ c * (9 * Nat.card A) := by rw [hcardBI, hC0c]; ring
    have h81 : 81 ≤ 9 * Nat.card A := Nat.le_of_mul_le_mul_left key (by positivity)
    omega
  have hAnc : ¬ IsCyclic ↥A := not_isCyclic_of_card Nat.prime_three hAel hcardA
  have haC : ∀ a ∈ A, a ≠ 1 → a ∉ Subgroup.centralizer (K : Set X) := by
    intro a ha ha1 h
    have h' : a ∈ A ⊓ Subgroup.centralizer (K : Set X) := ⟨ha, h⟩
    rw [hAC, Subgroup.mem_bot] at h'
    exact ha1 h'
  have huniq : ∀ a ∈ A, a ≠ 1 → ∀ g ∈ Subgroup.normalizer (K : Set X),
      g * a * g⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X) → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          g ∈ Subgroup.normalizer (J : Set X) := by
    intro a ha ha1 g hg hga J hJ
    have haN : a ∈ Subgroup.normalizer (K : Set X) := hBN (hAB ha)
    have ha3 : a ^ 3 = 1 := hBel.2 a (hAB ha)
    have hJ' := Bal209TwoInAux.glaPComponent_conj_centralizer hg hga hJ
    have heq := hU X K a hcomp.2.2 hK haN (by rw [ha3]; exact Subgroup.one_mem _)
      (haC a ha ha1) (hAin a ha) _ _ hJ' hJ
    exact mem_normalizer_iff_gLBConj_eq.2 heq
  have hEH : EngineHyp 3 K B A :=
    { prime := Nat.prime_three
      odd := by decide
      quasi := hcomp.2.2
      dvd := hdvd
      norm := hBN
      elem := hBel
      sc := ⟨le_sup_right, hBel, fun E _ hEel hBE => hSC.2.2 E le_top hEel hBE⟩
      sub := hAB
      noncyc := hAnc
      loc := isCompLocallyBalanced_of_inner (innerOneBalanceThree_barOf hcomp.2.2 hK) hAin
      comp := fun a ha ha1 J hJ => by
        have hBJ : B ≤ Subgroup.normalizer (J : Set X) := by
          intro b hb
          have hba : b * a = a * b :=
            congrArg Subtype.val (hSC.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨a, hAB ha⟩)
          have hba' : b * a * b⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
            rw [hba]
            group
            exact Subgroup.one_mem _
          exact huniq a ha ha1 b (hBN hb) hba' J hJ
        refine ⟨hBJ, ?_⟩
        rcases hR X hX K B a hcomp hSC hBN hK hm (hAB ha) (haC a ha ha1) (hAin a ha) J hJ hBJ
          with h | h
        · exact h
        · exfalso
          have h' : CFSG.Open.pRank 3 B ≤ CFSG.Open.pRank 3 C0 + 3 := h
          omega }
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hAnc
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hcon
    subst hbot
    infer_instance
  exact engine_full hEH ⟨a, haA, ha1, fun w hwN _ hwB J hJ =>
    huniq a haA ha1 w hwN (hwB a (hAB haA)) J hJ⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
