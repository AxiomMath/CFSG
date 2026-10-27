module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Embedding

variable {C G : Type*} [Group C] [Group G]

theorem isComponentOf_map_of_injective (f : C →* G) (hf : Function.Injective f)
    {K X : Subgroup C} (h : IsComponentOf K X) : IsComponentOf (K.map f) (X.map f) := by
  refine ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map f h.2.1, ?_⟩
  set e : K ≃* K.map f := K.equivMapOfInjective f hf
  obtain ⟨hp, hs⟩ := h.2.2
  have hc : (Subgroup.center K).map (e : K →* K.map f) = Subgroup.center (K.map f) :=
    Subgroup.map_center_eq e
  let e' := QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : K →* K.map f) e.surjective,
    ← Subgroup.map_commutator, hp]

theorem map_fixSubgroup_eq_of_embedding (ι : C →* G) (hι : Function.Injective ι) (β : MulAut C)
    (z : G) (hβ : ∀ c, ι (β c) = z * ι c * z⁻¹) :
    (fixSubgroup β).map ι = ι.range ⊓ Subgroup.centralizer {z} := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h := hβ c
    rw [(mem_fixSubgroup).1 hc] at h
    calc ι c * z = (z * ι c * z⁻¹) * z := by rw [← h]
      _ = z * ι c := by group
  · rintro ⟨⟨c, rfl⟩, hz⟩
    refine ⟨c, (mem_fixSubgroup).2 (hι ?_), rfl⟩
    rw [hβ c]
    have hz' : ι c * z = z * ι c := Subgroup.mem_centralizer_singleton_iff.1 hz
    rw [← hz', mul_inv_cancel_right]

theorem isComponentOf_map_of_embedding (ι : C →* G) (hι : Function.Injective ι) (β : MulAut C)
    (z : G) (hβ : ∀ c, ι (β c) = z * ι c * z⁻¹) {J : Subgroup C}
    (hJ : IsComponentOf J (fixSubgroup β)) :
    IsComponentOf (J.map ι) (ι.range ⊓ Subgroup.centralizer {z}) := by
  rw [← map_fixSubgroup_eq_of_embedding ι hι β z hβ]
  exact isComponentOf_map_of_injective ι hι hJ

theorem commute_of_fixed_of_embedding (ι : C →* G) (β : MulAut C) (z : G)
    (hβ : ∀ c, ι (β c) = z * ι c * z⁻¹) {J : Subgroup C} (hJ : ∀ c ∈ J, β c = c) :
    ∀ y ∈ J.map ι, Commute z y := by
  rintro _ ⟨c, hc, rfl⟩
  have h := hβ c
  rw [hJ c hc] at h
  show z * ι c = ι c * z
  calc z * ι c = (z * ι c * z⁻¹) * z := by group
    _ = ι c * z := by rw [← h]

end Embedding

section Setups


theorem exists_langSetup_e6 {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    (hK4 : 4 ≤ Nat.card K) {w : WeylGroup Tag.E6}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) :
    ∃ S : LangSetup Tag.E6 (AlgebraicClosure K) 3, 4 ≤ S.D.q ∧
      S.D.torus = twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
        (Units.map (entrywiseHom Fr)) ∧
      S.Γ = (((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype).range).map
          (MulAut.conj g0⁻¹).toMonoidHom := by
  classical
  set L := AlgebraicClosure K with hL
  let D : LangDatum Tag.E6 L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hperf : commutator ↥(adjointGroup Tag.E6 K) = ⊤ :=
    single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))
  have hdesc := langDescent_untw (K := K) (L := L) 3 (Or.inl ⟨rfl, rfl⟩) hFr D rfl
    Nat.prime_seven (by norm_num) hperf
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 L D
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hKc : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    change IsPrimePow (Nat.card K) ∧ ((Nat.card K : ℕ) : L) = 0
    rw [hKc]
    exact ⟨hℓ.isPrimePow.pow f.pos.ne', (CharP.cast_eq_zero_iff L (ringChar K) _).2
      (dvd_pow_self _ f.pos.ne')⟩
  refine ⟨D.toSetup 3 ρ hρ Nat.prime_three (Or.inr hK4) hqpow hK3 hdesc.finite_model, hK4, rfl,
    ?_⟩
  exact hdesc.Γ_eq

theorem exists_langSetup_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq4 : 4 ≤ ℓ ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {w : WeylGroup TwistTag.E6.tag}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) :
    ∃ S : LangSetup Tag.E6 (AlgebraicClosure K) 3, 4 ≤ S.D.q ∧
      S.D.torus = twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      S.Γ = ((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).map
          (MulAut.conj g0⁻¹).toMonoidHom := by
  classical
  set L := AlgebraicClosure K with hL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  let D : LangDatum TwistTag.E6.tag L := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr w hg0C hg0
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 :=
    ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2 (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ 3 ∣ D.q := by
    change ¬ 3 ∣ ℓ ^ f
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hfin : Finite D.model := finite_model_twistedE6 hℓ hf hK hσ hFr D rfl
  refine ⟨D.toSetup 3 ρ hρ Nat.prime_three (Or.inr hq4) hqpow hpq hfin, hq4, rfl, ?_⟩
  exact Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D rfl

end Setups

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
