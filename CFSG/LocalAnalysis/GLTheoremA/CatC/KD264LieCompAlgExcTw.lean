module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutReeF4
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner Outer)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

theorem compAlgAt_of_isSolvable_fixSubgroup_kd264alg {S : Type} [Group S]
    (h : ∀ β : MulAut S, β ∈ innAutDerived S → β ^ 3 = 1 → β ≠ 1 →
      Group.IsSolvable ↥(fixSubgroup β)) : CompAlgAt S := by
  intro β hβ hβ3 hβ1 K hK
  exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isComponentOf_of_isSolvable
    (h β hβ hβ3 hβ1) hK).elim

theorem subgroupStabRestrict_conj_of_mem_kd264alg {G : Type*} [Group G] {K : Subgroup G} {w : G}
    (hw : w ∈ K) (hx : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut K) :
    CFSG.GroupActions.subgroupStabRestrict K ⟨MulAut.conj w, hx⟩ =
      MulAut.conj (⟨w, hw⟩ : K) := by
  ext k
  rw [CFSG.GroupActions.subgroupStabRestrict_apply]
  simp [MulAut.conj_apply]

theorem compAlgAt_of_inner_of_component_eq_fixSubgroup_kd264alg {S : Type} [Group S]
    (hZ : Subgroup.center S = ⊥) (hinn : innAutDerived S ≤ inner S)
    (hK : ∀ β : MulAut S, β ∈ innAutDerived S → β ^ 3 = 1 → β ≠ 1 →
      ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) → K = fixSubgroup β) :
    CompAlgAt S := by
  intro β hβ hβ3 hβ1 K hKc e he hiso x hx hx3 hβx hxK
  obtain ⟨b, rfl⟩ := hinn hβ
  obtain ⟨w, rfl⟩ := hinn hx
  have hbw : b * w = w * b := by
    apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
    rw [map_mul, map_mul]
    exact hβx
  have hwK : w ∈ K := by
    rw [hK _ hβ hβ3 hβ1 K hKc, CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
      MulAut.conj_apply, hbw, mul_inv_cancel_right]
  rw [subgroupStabRestrict_conj_of_mem_kd264alg hwK hxK,
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
  exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨_, rfl⟩

theorem compAlgAt_suzukiGroup {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) : CompAlgAt ↥(suzukiGroup a K) := by
  refine compAlgAt_of_isSolvable_fixSubgroup_kd264alg fun β hβ hβ3 hβ1 => ?_
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥(suzukiGroup a K) := (suzuki_simple ha hK).1
  have hinn : β ∈ inner ↥(suzukiGroup a K) := innAutDerived_le_inner_excTw_of_isCyclic
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).1 hβ
  obtain ⟨x, rfl, hxp, hx1⟩ :=
    exists_eq_conj_of_mem_range (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK) hinn hβ3 hβ1
  have hodd : Odd (orderOf x) := by
    rw [orderOf_eq_prime hxp hx1]
    decide
  obtain ⟨hcard, -⟩ :=
    (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).2 x hx1 hodd
  rw [fixSubgroup_conj]
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard

theorem compAlgAt_cat_suzuki (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    CompAlgAt (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group := by
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  exact compAlgAt_of_mulEquiv θ.symm (compAlgAt_suzukiGroup ha hK)

section ReeF4


theorem component_eq_fixSubgroup_reeGamma_F4_kd264alg {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = 3) {J : Subgroup ↥(ReeTag.F4.reeGamma K a)}
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj y))) :
    J = fixSubgroup (MulAut.conj y) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hy
  have hFcard : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hFcard (by omega)).1
  let E : ↥(fixSubgroup (MulAut.conj y)) ≃*
      ↥(StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) :=
    (MulEquiv.subgroupCongr (fixSubgroup_conj y)).trans e
  have hCq : CFSG.IsQuasisimple ↥(fixSubgroup (MulAut.conj y)) :=
    CFSG.IsQuasisimple.of_mulEquiv E hq
  exact CFSG.HardMathSupport.Solomon.Coordinator.component_eq_of_normal_quasisimple hJ le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) hCq fun H hH _ => hH

theorem compAlgAt_reeGamma_F4 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hinn : innAutDerived ↥(ReeTag.F4.reeGamma K a) ≤ inner ↥(ReeTag.F4.reeGamma K a)) :
    CompAlgAt ↥(ReeTag.F4.reeGamma K a) := by
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  refine compAlgAt_of_inner_of_component_eq_fixSubgroup_kd264alg hZ hinn ?_
  intro β hβ hβ3 hβ1 J hJ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, rfl, hy3, hy1⟩ := exists_eq_conj_of_mem_range hZ (hinn hβ) hβ3 hβ1
  exact component_eq_fixSubgroup_reeGamma_F4_kd264alg ha hK y (orderOf_eq_prime hy3 hy1) hJ

theorem compAlgAt_cat_reeF4 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    CompAlgAt (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group := by
  have hm : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm hR
  exact compAlgAt_of_mulEquiv e.symm (compAlgAt_reeGamma_F4 hm hK
    (innAutDerived_le_inner_excTw_of_mulEquiv e
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outreef4_innAutDerived_le_inner hR)))

end ReeF4

@[expose] def TwistedE6CompAlgEight : Prop :=
  LieCompAlg fun e => ∃ q : TauCeti.PrimePower, e = .twistedE6 q

theorem lieCompAlg_excTwisted_of_twistedE6
    (h : TwistedE6CompAlgEight) : LieCompAlg isExcTwistedIdx := by
  intro d hP hfield
  obtain ⟨e, hv⟩ := d
  cases e with
  | twistedE6 q => exact h ⟨.twistedE6 q, hv⟩ ⟨q, rfl⟩ hfield
  | suzuki m => exact compAlgAt_cat_suzuki m hv
  | reeF4 m => exact compAlgAt_cat_reeF4 m hv
  | reeG2 m =>
      exfalso
      have h1 : 3 ^ (2 * m + 1) = 8 := hfield
      have h2 : 3 ∣ 8 := h1 ▸ dvd_pow_self 3 (by omega)
      omega
  | tits => exact absurd hfield (by simp [fieldSize])
  | _ => exact absurd hP (by simp [isExcTwistedIdx])

section TwistedE6Lang

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

set_option linter.unusedSectionVars false


theorem exists_langSetup_of_toral_datum_conj_kd264alg {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L)
    (hDq : D.q = ℓ ^ f) {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q)
    {p : ℕ} (hfin : Finite D.model) {C : Type} [Group C] (ι₀ : C →* ModGL τ L)
    (hι₀ : Function.Injective ι₀) (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom)
    {u : ModGL τ L} (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1)
    (hu1 : u ≠ 1) :
    ∃ (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (ι : C →* ModGL τ L),
      S.D = D ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ rootDiagUnit τ a = D.g0⁻¹ * u * D.g0 ∧
      ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := by
  classical
  obtain ⟨y, hy, hyu⟩ := hmem
  have hyu' : y = D.g0⁻¹ * u * D.g0 := by
    have h : D.g0 * y * D.g0⁻¹ = u := hyu
    rw [← h]
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u) (i := p)
    rw [inv_inv] at h
    rw [hyu', h, hup]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [this, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have h1 : rootDiagUnit τ a ≠ 1 := by
    intro h
    apply hu1
    rw [← ha, hyu'] at h
    have : u = D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ := by group
    rw [this, h]
    group
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let ι : C →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, a, ι, rfl, ?_, hap, h1,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, by rw [← ha, hyu'], hι⟩
  · exact ha ▸ hy
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀

theorem exists_langSetup_of_inndiag_twE6_conj_kd264alg {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ twistedE6InndiagGL K σ) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
      (bc : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 (AlgebraicClosure K))
      (g : ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ rootDiagUnit Tag.E6 a = g⁻¹ * bc h * g ∧
      (∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ * bc c * g) ∧
      ∀ h' ∈ twistedE6InndiagGL K σ,
        S.D.step (g⁻¹ * bc h' * g) = g⁻¹ * bc h' * g ∧
          g⁻¹ * bc h' * g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h with hu
  have huF : u ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h, hh, rfl⟩
  have huG : u ∈ adjointGroup TwistTag.E6.tag L := huF.1
  have hufix : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) u = u := huF.2
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.E6 f hf hufix hconj
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    rw [hι₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hda, hι⟩ :=
    exists_langSetup_of_toral_datum_conj_kd264alg hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ hmem
      hup hu1
  refine ⟨S, a, ι, baseChangeGL ι₁, S.D.g0, hDq, hT, hap, h1, hinj, hrange, hda, fun c => hι c,
    fun h' hh' => ?_⟩
  have hvF : baseChangeGL ι₁ h' ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h', hh', rfl⟩
  have hΦv : S.D.Φ (baseChangeGL ι₁ h') = baseChangeGL ι₁ h' := by
    rw [hΦ]
    exact hvF.2
  have key : ∀ x : ModGL TwistTag.E6.tag L, S.D.Φ x = x →
      S.D.step (S.D.g0⁻¹ * x * S.D.g0) = S.D.g0⁻¹ * x * S.D.g0 := by
    intro x hx
    change (MulAut.conj S.D.n) (S.D.Φ (S.D.g0⁻¹ * x * S.D.g0)) = S.D.g0⁻¹ * x * S.D.g0
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hx, S.D.lang]
    group
  exact ⟨key _ hΦv, mul_mem (mul_mem (inv_mem S.D.g0_mem) hvF.1) S.D.g0_mem⟩


theorem compAlgAt_twistedE6Model_kd264alg {K : Type} [Field K] (hK : Nat.card K = (2 ^ 3) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 3)) (hR1 : E6D4OuterNotEight)
    (hR2 : E6EightCentralizerConn) : CompAlgAt ↥(twistedE6RootGroup K σ) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  intro β hβmem hβ3 hβ1 J hJ e he hiso x' hx'mem _ hβx' hx'stab
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two (by norm_num) K hK σ
      hσ
  have hKf : Nat.card K = 2 ^ (2 * 3) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcyc.isMulCommutative.is_comm.comm _ _
  have hrng : ∀ γ ∈ innAutDerived ↥(twistedE6RootGroup K σ),
      γ ∈ (twistedE6InndiagConj K σ).range := by
    intro γ hγ
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hγ
  obtain ⟨h, rfl⟩ := hrng β hβmem
  obtain ⟨h', rfl⟩ := hrng x' hx'mem
  have hinjc := twistedE6InndiagConj_injective Nat.prime_two (by norm_num) hK σ hσ
  have hp1 : h ^ 3 = 1 := hinjc (by rw [map_pow, hβ3, map_one])
  have hh1 : h ≠ 1 := fun h'' => hβ1 (by rw [h'', map_one])
  have hhh' : h * h' = h' * h := hinjc (by rw [map_mul, map_mul]; exact hβx')
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, bc, g, hSq, hT, hap, h1, hinj, hrange, hda, hι, hfix⟩ :=
    exists_langSetup_of_inndiag_twE6_conj_kd264alg Nat.prime_two (by norm_num) hK σ hσ
      Nat.prime_three (by norm_num) Nat.prime_three (by norm_num) (Or.inr (by norm_num)) hmon
      (h : ModGL TwistTag.E6.tag K) h.2 (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h'' => hh1 (Subtype.ext h''))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 3 * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hq8 : S.D.q = 8 := by rw [hSq]; norm_num
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_three hK (by norm_num)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL (fun h => absurd h (by decide)) hT
    hap h1
  have hN := card_eq_of_compAlgEight_kd264alg e he hiso
  have hβ : ∀ c, ι (twistedE6InndiagConj K σ h c) =
      rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹ := by
    intro c
    rw [hι, hι, twistedE6InndiagConj_apply, map_mul, map_mul, map_inv, hda]
    group
  have hφy : ∀ c, ι (twistedE6InndiagConj K σ h' c) =
      (g⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * g) * ι c *
        (g⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * g)⁻¹ := by
    intro c
    rw [hι, hι, twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
    group
  obtain ⟨hyF, hyG⟩ := hfix h' h'.2
  have hbc : bc (h : ModGL TwistTag.E6.tag K) * bc (h' : ModGL TwistTag.E6.tag K) =
      bc (h' : ModGL TwistTag.E6.tag K) * bc (h : ModGL TwistTag.E6.tag K) := by
    have hc : (h : ModGL TwistTag.E6.tag K) * h' = h' * h := congrArg Subtype.val hhh'
    rw [← map_mul, ← map_mul, hc]
  have hyd : rootDiagUnit Tag.E6 a * (g⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * g) *
      (rootDiagUnit Tag.E6 a)⁻¹ = g⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * g := by
    rw [hda]
    calc g⁻¹ * bc (h : ModGL TwistTag.E6.tag K) * g *
          (g⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * g) *
          (g⁻¹ * bc (h : ModGL TwistTag.E6.tag K) * g)⁻¹ =
        g⁻¹ * (bc (h : ModGL TwistTag.E6.tag K) * bc (h' : ModGL TwistTag.E6.tag K)) *
          (bc (h : ModGL TwistTag.E6.tag K))⁻¹ * g := by group
      _ = g⁻¹ * (bc (h' : ModGL TwistTag.E6.tag K) * bc (h : ModGL TwistTag.E6.tag K)) *
          (bc (h : ModGL TwistTag.E6.tag K))⁻¹ * g := by rw [hbc]
      _ = g⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * g := by group
  have hyC : g⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * g ∈
      toralCentralizer Tag.E6 (AlgebraicClosure K) a :=
    CFSG.LieType.Chevalley.mem_toralCentralizer.2 ⟨hyG, hyd⟩
  exact centerQuotientHom_mem_innAutDerived_of_langSetup_conj_kd264alg S hq8 ι hinj hrange hT hap
    h1 hTame
    (fun i hqs hNi => excAlgTypeAAt_E6_of_kd264alg hR1 (AlgebraicClosure K) 3 S hq8 a hT hap h1 i
      hqs hNi)
    hβ hJ hN hx'stab hφy hyF
    (fun i hqs hNi hyR => hR2 (AlgebraicClosure K) 3 S hq8 a hT hap h1 i hqs hNi _ hyC hyF hyR)

theorem twistedE6CompAlgEight_of_kd264alg (hR1 : E6D4OuterNotEight)
    (hR2 : E6EightCentralizerConn) : TwistedE6CompAlgEight := by
  intro d hP hfield
  obtain ⟨e, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  have hq8 : q.p ^ q.exponent = 2 ^ 3 := by
    have hfs : fieldSize (TauCeti.LieTypeIndex.twistedE6 q) = q.p ^ q.exponent := by
      simp only [fieldSize, TauCeti.PrimePower.card_def]
    rw [← hfs]
    exact hfield
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  rw [hq8] at hK hσ
  exact compAlgAt_of_mulEquiv eK.symm (compAlgAt_twistedE6Model_kd264alg hK σ hσ hR1 hR2)

theorem lieCompAlg_excTwisted_of_E6res_kd264alg (hR1 : E6D4OuterNotEight)
    (hR2 : E6EightCentralizerConn) : LieCompAlg isExcTwistedIdx :=
  lieCompAlg_excTwisted_of_twistedE6 (twistedE6CompAlgEight_of_kd264alg hR1 hR2)

end TwistedE6Lang

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
