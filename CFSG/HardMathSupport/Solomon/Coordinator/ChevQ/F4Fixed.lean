module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneUntw
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.CTP CFSG.TauCetiBridge.Even CFSG.Blueprint.Multiplier


namespace F4FixedAux

open scoped commutatorElement

theorem isQuasisimple_of_open_aux {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hc : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [hH, Subgroup.mem_bot] at hc
  exact e.injective (by rw [hc, map_one])

@[expose] noncomputable def adjointEquiv (τ : Tag) (K : Type) [Field K] [Finite K] :
    AdjointQuotient τ K ≃* adjointGroup τ K :=
  (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := K))).trans
    QuotientGroup.quotientBot

@[expose] noncomputable def conjOnNormal {X : Type} [Group X] (K : Subgroup X) (a : X)
    (ha : a ∈ Subgroup.normalizer (K : Set X)) : MulAut K where
  toFun k := ⟨a * k * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha k).1 k.2⟩
  invFun k := ⟨a⁻¹ * k * a, by
    refine (Subgroup.mem_normalizer_iff.1 ha (a⁻¹ * k * a)).2 ?_
    have e : a * (a⁻¹ * k * a) * a⁻¹ = k := by group
    rw [e]
    exact k.2⟩
  left_inv k := Subtype.ext (by
    show a⁻¹ * (a * k * a⁻¹) * a = k
    group)
  right_inv k := Subtype.ext (by
    show a * (a⁻¹ * k * a) * a⁻¹ = k
    group)
  map_mul' k l := Subtype.ext (by
    show a * (k * l) * a⁻¹ = (a * k * a⁻¹) * (a * l * a⁻¹)
    group)

theorem conjOnNormal_apply {X : Type} [Group X] (K : Subgroup X) (a : X)
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (k : K) :
    ((conjOnNormal K a ha k : K) : X) = a * k * a⁻¹ :=
  rfl

theorem conjOnNormal_pow_apply {X : Type} [Group X] (K : Subgroup X) (a : X)
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (n : ℕ) :
    ∀ k : K, ((conjOnNormal K a ha ^ n) k : X) = a ^ n * k * (a ^ n)⁻¹ := by
  induction n with
  | zero => intro k; simp
  | succ n ih =>
    intro k
    rw [pow_succ, MulAut.mul_apply, ih, conjOnNormal_apply, pow_succ]
    group

theorem conjOnNormal_pow_three {X : Type} [Group X] (K : Subgroup X) (a : X)
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hA : a ^ 3 = 1) :
    conjOnNormal K a ha ^ 3 = 1 := by
  refine MulEquiv.ext fun k => Subtype.ext ?_
  rw [conjOnNormal_pow_apply, hA]
  simp

theorem mem_centralizer_singleton_iff' {X : Type} [Group X] (a x : X) :
    x ∈ Subgroup.centralizer ({a} : Set X) ↔ a * x = x * a := by
  simp [Subgroup.mem_centralizer_iff]

theorem conjOnNormal_not_inner {X : Type} [Group X] (K : Subgroup X) (a : X)
    (ha : a ∈ Subgroup.normalizer (K : Set X))
    (hOut : ¬ Bal209F4Aux.InnerAt K a) :
    conjOnNormal K a ha ∉ (MulAut.conj : K →* MulAut K).range := by
  rintro ⟨g, hg⟩
  apply hOut
  refine ⟨(g : X), g.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have key : (g : X) * h * (g : X)⁻¹ = a * h * a⁻¹ := by
    have := congrArg (fun φ : MulAut K => ((φ ⟨h, hh⟩ : K) : X)) hg
    simpa [conjOnNormal_apply, MulAut.conj_apply] using this
  have e : (g : X)⁻¹ * a * h = h * ((g : X)⁻¹ * a) := by
    calc (g : X)⁻¹ * a * h = (g : X)⁻¹ * (a * h * a⁻¹) * a := by group
      _ = (g : X)⁻¹ * ((g : X) * h * (g : X)⁻¹) * a := by rw [key]
      _ = h * ((g : X)⁻¹ * a) := by group
  exact e.symm

theorem fixedSubgroup_conjOnNormal {X : Type} [Group X] (K : Subgroup X) (a : X)
    (ha : a ∈ Subgroup.normalizer (K : Set X)) :
    fixedSubgroup (conjOnNormal K a ha) =
      (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K := by
  ext k
  rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subtype.ext_iff,
    conjOnNormal_apply, mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff']
  exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩

theorem fixed_map_congr {G H : Type} [Group G] [Group H] (e : G ≃* H) (α : MulAut G) :
    (fixedSubgroup α).map e.toMonoidHom = fixedSubgroup (MulAut.congr e α) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixedSubgroup] at hx ⊢
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.coe_toMonoidHom, hx]
  · intro hy
    rw [mem_fixedSubgroup] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixedSubgroup]
    apply e.injective
    simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hy

theorem fixed_map_conj {G : Type} [Group G] (ψ γ : MulAut G) :
    (fixedSubgroup γ).map ψ.toMonoidHom = fixedSubgroup (ψ * γ * ψ⁻¹) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixedSubgroup] at hx
    rw [mem_fixedSubgroup, MulAut.mul_apply, MulAut.mul_apply, MulEquiv.coe_toMonoidHom]
    simp [hx]
  · intro hy
    rw [mem_fixedSubgroup, MulAut.mul_apply, MulAut.mul_apply] at hy
    refine ⟨ψ⁻¹ y, ?_, by simp⟩
    rw [mem_fixedSubgroup]
    apply ψ.injective
    rw [hy]
    simp

theorem congr_eq_conj_imp {K C : Type} [Group K] [Group C] (e : K ≃* C) (α : MulAut K) (g : C)
    (h : MulAut.congr e α = MulAut.conj g) : α = MulAut.conj (e.symm g) := by
  refine MulEquiv.ext fun k => ?_
  apply e.injective
  have hk := congrArg (fun φ : MulAut C => φ (e k)) h
  simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.symm_apply_apply] at hk
  rw [MulAut.conj_apply, map_mul, map_mul]
  simp only [MulEquiv.apply_symm_apply, map_inv]
  rw [← hk]
  simp

end F4FixedAux

theorem f4Fixed_holds : Bal209F4Aux.F4Fixed := by
  intro X _ _ K a hK hLie hNorm hA3 hOut
  classical
  have hKq : CFSG.IsQuasisimple K := F4FixedAux.isQuasisimple_of_open_aux hK.2.2
  obtain ⟨d, hdF, ⟨eL⟩⟩ := hLie
  obtain ⟨d1, hv⟩ := d
  have hq8 : ∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.F4 q ∧ IsTwoPow q 3 := by
    cases d1 with
    | F4 q => exact ⟨q, rfl, hdF⟩
    | _ => simp [IsF4EightIndex] at hdF
  obtain ⟨q, rfl, hq3⟩ := hq8
  obtain ⟨hq2, hqe⟩ := hq3
  have hLM : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.F4 q, hv⟩).Group
      .F4 0 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, rfl⟩, Or.inr ⟨rfl, ⟨TauCeti.LieTypeIndex.F4 q, hv⟩, ⟨hq2, hqe⟩,
      ⟨MulEquiv.refl _⟩⟩⟩
  have hZK : Subgroup.center K = ⊥ := by
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hKq eL hLM
    have h1 : (genericOrders .F4 0 2 3).1 * (genericOrders .F4 0 2 3).2 *
        ((exceptionalOrders .F4 0 2 3).1 * (exceptionalOrders .F4 0 2 3).2) = 1 := by
      decide
    rw [h1] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h)
  have hK'card : Nat.card (GaloisField 2 3) = q.card := by
    rw [GaloisField.card 2 3 (by norm_num), TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨eB⟩ := (chevalleyBridgesEven).f4 q hv hq2 (GaloisField 2 3) hK'card
  let eKq : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK.symm)
  let eK : K ≃* adjointGroup Tag.F4 (GaloisField 2 3) :=
    eKq.trans (eL.trans (eB.symm.trans (F4FixedAux.adjointEquiv Tag.F4 (GaloisField 2 3))))
  have hβ3 : MulAut.congr eK (F4FixedAux.conjOnNormal K a hNorm) ^ 3 = 1 := by
    rw [← map_pow, F4FixedAux.conjOnNormal_pow_three K a hNorm hA3, map_one]
  have hβconj : ∀ g : adjointGroup Tag.F4 (GaloisField 2 3),
      MulAut.congr eK (F4FixedAux.conjOnNormal K a hNorm) ≠ MulAut.conj g := by
    intro g hg
    exact F4FixedAux.conjOnNormal_not_inner K a hNorm hOut
      (MonoidHom.mem_range.2 ⟨eK.symm g, (F4FixedAux.congr_eq_conj_imp eK _ g hg).symm⟩)
  have hβne : MulAut.congr eK (F4FixedAux.conjOnNormal K a hNorm) ≠ 1 := by
    intro h
    apply hβconj 1
    rw [h, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hβout : CFSG.RankThree.PartOne.CTP.IsOuterOfOrder 3
      (MulAut.congr eK (F4FixedAux.conjOnNormal K a hNorm)) :=
    ⟨orderOf_eq_prime hβ3 hβne, hβconj⟩
  have hFD : CFSG.AGLEmbedding.SeitzEqTwo.FieldDescentAt Tag.F4 (GaloisField 2 3) 3 :=
    CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_F4 (ℓ := 2) (f := 3) Nat.prime_two (by norm_num)
      (GaloisField.card 2 3 (by norm_num)) Nat.prime_three (by norm_num)
  obtain ⟨ψ, σ, hσ3, hψ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.stdDescent_of_fieldDescentAt
      (K := GaloisField 2 3) Nat.prime_three hFD _ hβout
  have hqcard : q.card = 2 ^ 3 := by
    rw [TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨q₀, hq₀p, hq₀card, hq₀eq⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.exists_primePower_fixSubfield
      hK'card σ Nat.prime_three hσ3
  have hq₀two : q₀.card = 2 := by
    have h8 : q₀.card ^ 3 = 2 ^ 3 := by rw [← hq₀eq, hqcard]
    exact Nat.pow_left_injective (by norm_num) h8
  have hK''card : Nat.card (fixSubfield σ) = q₀.card := hq₀card.symm
  have hq₀exp : q₀.exponent = 1 := by
    have hc : q₀.card = 2 ^ q₀.exponent := by
      rw [TauCeti.PrimePower.card_def, hq₀p, hq2]
    have h2 : (2 : ℕ) ^ q₀.exponent = 2 ^ 1 := by rw [pow_one, ← hc, hq₀two]
    exact Nat.pow_right_injective (le_refl 2) h2
  have E1 : ↥(fixedSubgroup (F4FixedAux.conjOnNormal K a hNorm)) ≃*
      ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
    (MulEquiv.subgroupCongr (F4FixedAux.fixedSubgroup_conjOnNormal K a hNorm)).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have E2 : ↥(fixedSubgroup (F4FixedAux.conjOnNormal K a hNorm)) ≃*
      ↥(fixedSubgroup (MulAut.congr eK (F4FixedAux.conjOnNormal K a hNorm))) :=
    (Subgroup.equivMapOfInjective _ eK.toMonoidHom eK.injective).trans
      (MulEquiv.subgroupCongr (F4FixedAux.fixed_map_congr eK (F4FixedAux.conjOnNormal K a hNorm)))
  have E3 : ↥(fixedSubgroup (MulAut.congr eK (F4FixedAux.conjOnNormal K a hNorm))) ≃*
      ↥(fixedSubgroup (entrywiseAdjointAut Tag.F4 σ)) :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr ((F4FixedAux.fixed_map_conj ψ _).trans (congrArg fixedSubgroup hψ)))
  have E4 := CFSG.LieType.SeitzGeneration.ExcOuterLeOne.fixedEquivOfEq (τ := Tag.F4) σ
    (CFSG.LieType.SeitzGeneration.ExcOuterLeOne.entrywiseFixedGroup_F4_eq σ)
  let Ffix : ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ≃*
      adjointGroup Tag.F4 (fixSubfield σ) :=
    E1.symm.trans (E2.trans (E3.trans E4))
  have hsimpleFix : IsSimpleGroup (adjointGroup Tag.F4 (fixSubfield σ)) :=
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type
      (Or.inr (Or.inr (Or.inr rfl)))
  have hsimpleK : IsSimpleGroup ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
    (MulEquiv.isSimpleGroup_congr Ffix).2 hsimpleFix
  have hperfFix : Group.IsPerfect (adjointGroup Tag.F4 (fixSubfield σ)) :=
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (fixSubfield σ)).1
  have hperfK : Group.IsPerfect ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
    haveI := hperfFix
    Group.IsPerfect.ofSurjective (f := Ffix.symm.toMonoidHom) Ffix.symm.surjective
  have hZKC : Subgroup.center ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) = ⊥ :=
    F4FixedAux.center_eq_bot_of_mulEquiv Ffix center_adjointGroup_eq_bot
  have hquasiK : CFSG.Open.IsQuasisimple ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) := by
    refine ⟨hperfK.commutator_eq_top, ?_⟩
    exact (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hZKC).trans
      QuotientGroup.quotientBot)).2 hsimpleK
  have hcardK : Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) = 3311126603366400 := by
    rw [Nat.card_congr Ffix.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
      hK''card, hq₀two]
    norm_num [CFSG.Open.ordF4]
  have h3 : 3 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) := by
    rw [hcardK]
    norm_num
  have hv₀ : (TauCeti.LieTypeIndex.F4 q₀).Valid := by
    simp [TauCeti.LieTypeIndex.valid_iff]
  have hF4two : Bal209F4Aux.IsF4TwoIndex (TauCeti.LieTypeIndex.F4 q₀) := ⟨hq₀p.trans hq2, hq₀exp⟩
  obtain ⟨eB0⟩ := (chevalleyBridgesEven).f4 q₀ hv₀ (hq₀p.trans hq2) (fixSubfield σ) hK''card
  let eFix : (↥(K ⊓ Subgroup.centralizer ({a} : Set X))) ⧸
      Subgroup.center ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.F4 q₀, hv₀⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZKC).trans QuotientGroup.quotientBot).trans
      (Ffix.trans ((F4FixedAux.adjointEquiv Tag.F4 (fixSubfield σ)).symm.trans eB0))
  exact ⟨hsimpleK, hquasiK, h3, ⟨⟨TauCeti.LieTypeIndex.F4 q₀, hv₀⟩, hF4two, ⟨eFix⟩⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
