module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLemma44
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bActor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection2
public import CFSG.LocalAnalysis.OddStandard.GlueAlt
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main
import CFSG.Quasithin.Recognition.Stroth.BenderNoFF
public import CFSG.Quasithin.Background.B1MoreElevenD

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo isChevTwo_of_classicalTwoOrG2)

variable {W : Type} [CommGroup W] [Finite W]

namespace IsGomiQuad

section

variable {X A K : Subgroup (MulAut W)} (hQ : IsGomiQuad X A K)
include hQ

omit [Finite W] in
private theorem conj_mem : ∀ m ∈ X, ∀ l ∈ K, m * l * m⁻¹ ∈ K := by
  obtain ⟨-, hKX, hKn, -⟩ := hQ
  intro m hm l hl
  have := hKn.conj_mem ⟨l, hKX hl⟩ (by simpa [Subgroup.mem_subgroupOf] using hl) ⟨m, hm⟩
  simpa [Subgroup.mem_subgroupOf] using this

omit [Finite W] in
private theorem inf_centralizer_le : X ⊓ Subgroup.centralizer (K : Set (MulAut W)) ≤ K := by
  rw [hQ.2.2.2.2.2.1]
  exact Subgroup.map_subtype_le _

omit [Finite W] in
private theorem le_normalizer {Y : Subgroup (MulAut W)} (hYX : Y ≤ X) :
    Y ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
  intro a ha
  have haX : a ∈ X := hYX ha
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · exact conj_mem hQ a haX l
  · intro hl
    have := conj_mem hQ a⁻¹ (X.inv_mem haX) _ hl
    simpa [mul_assoc] using this

omit [Finite W] in
private theorem inf_le_centralizer_of_not_ge {N : Subgroup (MulAut W)}
    (hN : ∀ m ∈ X, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hKN : ¬ K ≤ N) :
    N ⊓ K ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
  have hKX : K ≤ X := hQ.2.1
  have hL : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
  have hLo : CFSG.Open.IsQuasisimple ↥K := ⟨Group.isPerfect_def.mp hL.1, hL.2.1⟩
  have hnorm : ((N ⊓ K).subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · have := hN (g : MulAut W) (hKX g.2) x hx.1
      simpa using this
    · exact K.mul_mem (K.mul_mem g.2 hx.2) (K.inv_mem g.2)
  have hne : (N ⊓ K).subgroupOf K ≠ ⊤ := by
    intro h'
    apply hKN
    intro l hl
    have : (⟨l, hl⟩ : K) ∈ (N ⊓ K).subgroupOf K := by rw [h']; trivial
    rw [Subgroup.mem_subgroupOf] at this
    exact this.1
  have hc := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLo _ hne
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hx' : (⟨x, hx.2⟩ : K) ∈ (N ⊓ K).subgroupOf K := hx
  have := Subgroup.mem_center_iff.mp (hc hx') ⟨l, hl⟩
  exact congrArg Subtype.val this

omit [Finite W] in
private theorem normal_le_of_not_ge {N : Subgroup (MulAut W)} (hNX : N ≤ X)
    (hN : ∀ m ∈ X, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hKN : ¬ K ≤ N) :
    N ≤ K ∧ N ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
  have hKX : K ≤ X := hQ.2.1
  have hL : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
  have hLn := conj_mem hQ
  have hCL := inf_centralizer_le hQ
  have hcentral := inf_le_centralizer_of_not_ge hQ hN hKN
  have hcomm : ⁅N, K⁆ ≤ N ⊓ K := by
    rw [Subgroup.commutator_le]
    intro n hn l hl
    refine ⟨?_, ?_⟩
    · have h1 := hN l (hKX hl) n⁻¹ (N.inv_mem hn)
      have : n * l * n⁻¹ * l⁻¹ = n * (l * n⁻¹ * l⁻¹) := by simp [mul_assoc]
      show n * l * n⁻¹ * l⁻¹ ∈ N
      rw [this]
      exact N.mul_mem hn h1
    · have h1 := hLn n (hNX hn) l hl
      show n * l * n⁻¹ * l⁻¹ ∈ K
      exact K.mul_mem h1 (K.inv_mem hl)
  have h1 : ⁅⁅N, K⁆, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hcentral)
  have h2 : ⁅⁅K, N⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm K N]; exact h1
  have h3 : ⁅⁅K, K⁆, N⁆ = ⊥ := three_subgroup_lemma h2 h1
  have hperf : Group.IsPerfect ↥K := hL.1
  rw [Subgroup.commutator_eq_self] at h3
  have h4 : N ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
    rw [Subgroup.commutator_comm] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  exact ⟨fun x hx => hCL ⟨hNX hx, h4 hx⟩, h4⟩

private theorem not_le_of_isPGroup {N : Subgroup (MulAut W)} (hN2 : IsPGroup 2 N) : ¬ K ≤ N := by
  intro hKN
  have hL : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
  have hK2 : IsPGroup 2 ↥K := hN2.to_le hKN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥K := hK2.isNilpotent
  have hperf : Group.IsPerfect ↥K := hL.1
  have hnt : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open hL)
  exact Group.IsPerfect.not_isNilpotent ↥K hnil

omit [Finite W] in
private theorem quot_isPGroup [(K.subgroupOf X).Normal] :
    IsPGroup 2 (↥X ⧸ K.subgroupOf X) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  have hXeq : X = K ⊔ A := hQ.2.2.2.2.2.2
  have hAN : A ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    le_normalizer hQ hQ.1.1
  have hm : (m : MulAut W) ∈ K ⊔ A := hXeq ▸ m.2
  obtain ⟨l, hl, a, ha, he⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAN).1 hm
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have ha2 : a ^ 2 = 1 := hQ.1.2.2.1.2 a ha
  have hal : a * l * a⁻¹ ∈ K := conj_mem hQ a (hQ.1.1 ha) l hl
  have : ((m ^ 2 : ↥X) : MulAut W) = l * (a * l * a⁻¹) * a ^ 2 := by
    rw [Subgroup.coe_pow, he, pow_two, pow_two]; group
  rw [this, ha2, mul_one]
  exact K.mul_mem hl hal

theorem genFitting_eq : CFSG.Open.quasithinGenFitting X = K := by
  have hKX : K ≤ X := hQ.2.1
  have hq : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
  have hKn : (K.subgroupOf X).Normal := hQ.2.2.1
  apply le_antisymm
  · refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨hNM, hNn, hNnil⟩
      by_cases hLN : K ≤ N
      · exfalso
        have hnil : Group.IsNilpotent (K.subgroupOf N) := inferInstance
        have hnilL : Group.IsNilpotent ↥K :=
          (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hLN)).mp hnil
        have hperf : Group.IsPerfect ↥K := hq.1
        have hnt : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial
          (B1Red.isQuasisimple_to_open hq)
        exact Group.IsPerfect.not_isNilpotent ↥K hnilL
      · refine (normal_le_of_not_ge hQ hNM ?_ hLN).1
        intro m hm n hn
        have := hNn.conj_mem ⟨n, hNM hn⟩ (by simpa [Subgroup.mem_subgroupOf] using hn) ⟨m, hm⟩
        simpa [Subgroup.mem_subgroupOf] using this
    · rintro K' ⟨hKM, hKsub, hKq⟩
      have hq2 : IsPGroup 2 (↥X ⧸ K.subgroupOf X) := quot_isPGroup hQ
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent (↥X ⧸ K.subgroupOf X) := IsPGroup.isNilpotent hq2
      have hKperf : Group.IsPerfect ↥K' := ⟨hKq.1⟩
      set f : ↥K' →* (↥X ⧸ K.subgroupOf X) :=
        (QuotientGroup.mk' (K.subgroupOf X)).comp (Subgroup.inclusion hKM) with hf
      have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
      have hrange : f.range = ⊥ := by
        by_contra hne
        have : Nontrivial ↥f.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
        exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance
      intro k hk
      have : f ⟨k, hk⟩ = 1 := by
        have hmem : f ⟨k, hk⟩ ∈ f.range := ⟨_, rfl⟩
        rw [hrange, Subgroup.mem_bot] at hmem
        exact hmem
      simpa [hf, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] using this
  · have hcomp : CFSG.Open.IsComponentOf K X := by
      refine ⟨hKX, ?_, B1Red.isQuasisimple_to_open hq⟩
      exact CFSG.Open.IsSubnormal.step hKX hKn (CFSG.Open.IsSubnormal.refl _)
    exact le_sup_of_le_right (le_sSup hcomp)

omit [Finite W] in
private theorem eq_bot_of_le_centralizer {N : Subgroup (MulAut W)} (hNK : N ≤ K)
    (hNC : N ≤ Subgroup.centralizer (K : Set (MulAut W))) (hN2 : IsPGroup 2 ↥N) : N = ⊥ := by
  have hK2 : CFSG.pCore 2 ↥K = ⊥ := hQ.2.2.2.2.1
  have hNKn : (N.subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hc : (g : MulAut W) * (x : MulAut W) = (x : MulAut W) * (g : MulAut W) :=
      Subgroup.mem_centralizer_iff.mp (hNC hx) g g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hNK2 : IsPGroup 2 ↥(N.subgroupOf K) := hN2.comap_subtype
  have hle : N.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hNKn, hNK2⟩
  rw [hK2] at hle
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hNK hx⟩ : ↥K) ∈ N.subgroupOf K := by rwa [Subgroup.mem_subgroupOf]
  have := hle this
  rw [Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem pCore_eq_bot : CFSG.pCore 2 ↥X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 ↥X with hPdef
  have hPn : P.Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 ↥P := CFSG.pCore_isPGroup
  set N : Subgroup (MulAut W) := P.map X.subtype with hNdef
  have hNX : N ≤ X := Subgroup.map_subtype_le P
  have hN2 : IsPGroup 2 ↥N := hP2.map X.subtype
  have hNn : ∀ m ∈ X, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
    intro m hm n hn
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    exact Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * x * ⟨m, hm⟩⁻¹, hPn.conj_mem x hx ⟨m, hm⟩, rfl⟩
  obtain ⟨hNK, hNC⟩ := normal_le_of_not_ge hQ hNX hNn (not_le_of_isPGroup hQ hN2)
  have hNbot := eq_bot_of_le_centralizer hQ hNK hNC hN2
  rw [hNdef, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective] at hNbot
  exact hNbot

omit [Finite W] in
theorem isFFModule : IsFFModule X :=
  ⟨A, hQ.1.1, hQ.1.2.1, hQ.1.2.2.1, hQ.1.2.2.2⟩

end

private theorem exists_isBestOffender_le {X A₀ : Subgroup (MulAut W)} (hA : A₀ ≤ X) (h1 : A₀ ≠ ⊥)
    (he : IsElemAbelian2 A₀) (hoff : Nat.card W ≤ Nat.card A₀ * Nat.card (fixV A₀)) :
    ∃ B, B ≤ A₀ ∧ CFSG.QuasithinUnique.Setup.Family.IsBestOffender X B := by
  classical
  have hex : ∃ n, ∃ B : Subgroup (MulAut W), (B ≤ A₀ ∧ B ≠ ⊥ ∧
      Nat.card W ≤ Nat.card B * Nat.card (fixV B)) ∧ Nat.card B = n :=
    ⟨_, A₀, ⟨le_rfl, h1, hoff⟩, rfl⟩
  obtain ⟨B, ⟨hBA, hB1, hBoff⟩, hBn⟩ := Nat.find_spec hex
  refine ⟨B, hBA, hBA.trans hA, hB1,
    ⟨fun a ha b hb => he.1 a (hBA ha) b (hBA hb), fun a ha => he.2 a (hBA ha)⟩, hBoff, ?_⟩
  intro B' hB'B hB'1 hB'ne
  by_contra hlt
  push Not at hlt
  have hlt' : Nat.card B' < Nat.card B :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hB'B hB'ne)
  have := Nat.find_min hex (hBn ▸ hlt')
  exact this ⟨B', ⟨hB'B.trans hBA, hB'1, hBoff.trans hlt⟩, rfl⟩

omit [Finite W] in
private theorem isFFStarOffender_of_isBestOffender {X B : Subgroup (MulAut W)}
    (hB : CFSG.QuasithinUnique.Setup.Family.IsBestOffender X B) : IsFFStarOffender X B := by
  refine ⟨hB.1, hB.2.1, hB.2.2.1, ?_⟩
  intro B' hB'B
  by_cases h1 : B' = ⊥
  · subst h1
    rw [CFSG.Quasithin.B1.fixV_bot]
    simp only [Subgroup.card_bot, one_mul, Subgroup.card_top]
    exact hB.2.2.2.1
  · by_cases h2 : B' = B
    · rw [h2]
    · exact (hB.2.2.2.2 B' hB'B h1 h2).le

section

variable {X A K : Subgroup (MulAut W)} (hQ : IsGomiQuad X A K)
include hQ

omit [Finite W] in
private theorem isComponentOf : CFSG.Open.IsComponentOf K X := by
  have hKX : K ≤ X := hQ.2.1
  have hq : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
  have hKn : (K.subgroupOf X).Normal := hQ.2.2.1
  exact ⟨hKX, CFSG.Open.IsSubnormal.step hKX hKn (CFSG.Open.IsSubnormal.refl _),
    B1Red.isQuasisimple_to_open hq⟩

omit [Finite W] in
private theorem commutator_ne_bot {B : Subgroup (MulAut W)}
    (hB : CFSG.QuasithinUnique.Setup.Family.IsBestOffender X B) : ⁅K, B⁆ ≠ ⊥ := by
  intro hKB
  have hBC : B ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
    rw [Subgroup.commutator_comm] at hKB
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKB
  have hBX : B ≤ X := hB.1
  have hB2 : IsPGroup 2 ↥B := by
    intro b
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hB.2.2.1.2 b b.2
  have hBK : B ≤ K := fun x hx => inf_centralizer_le hQ ⟨hBX hx, hBC hx⟩
  exact hB.2.1 (eq_bot_of_le_centralizer hQ hBK hBC hB2)

theorem false_of_suzuki
    (hSz : ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid),
      HardMathSupport.Cooperstein.Coordinator.NoIrrFFOffender
        (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group)
    (hW : ∀ w : W, w * w = 1) {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (α : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) :
    False :=
  CFSG.Quasithin.Stroth.not_isFFModule_of_noIrrFFOffender hW hQ.genFitting_eq.symm hQ.2.2.2.1
    hQ.pCore_eq_bot (hSz m hv) ⟨α⟩ hQ.isFFModule

theorem false_of_psu3 (hU3 : CFSG.QuasithinUnique.Setup.X5.EvenUnitaryThreeNoOffender)
    (hW : ∀ w : W, w * w = 1) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : CFSG.Open.StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSU 3 2 f) : False := by
  obtain ⟨B, -, hB⟩ := exists_isBestOffender_le hQ.1.1 hQ.1.2.1 hQ.1.2.2.1 hQ.1.2.2.2
  have hcomp := isComponentOf hQ
  obtain ⟨W', hWg, hWf, ρ, A₀, hW2, hWn, h0, hirr, hA0, hAe, hAn, hoff⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.sectionProductionProp W hW X K B hcomp hB
      (commutator_ne_bot hQ hB)
  have hq : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
  obtain ⟨hq0, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hq ρ h0
  have hmodel0 := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmodel
  have := hU3 f hf W' hW2 hWn ρ.range A₀ hq0.1 hirr hmodel0 hA0 hAe hAn
  omega

theorem odd_card_center : Odd (Nat.card (Subgroup.center ↥K)) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 2 h2
  set y : MulAut W := ((z : ↥K) : MulAut W) with hy
  have hyK : y ∈ K := (z : ↥K).2
  have hyC : ∀ l ∈ K, l * y = y * l := by
    intro l hl
    have := Subgroup.mem_center_iff.mp z.2 ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hord : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  set N := Subgroup.zpowers y
  have hNK : N ≤ K := (Subgroup.zpowers_le).mpr hyK
  have hNC : N ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hyC l hl
  have hN2 : IsPGroup 2 ↥N := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hbot := eq_bot_of_le_centralizer hQ hNK hNC hN2
  have : y ∈ N := Subgroup.mem_zpowers y
  rw [hbot, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hord
  omega

theorem card_center_eq_one_of_alt {n : ℕ} (hn : 8 ≤ n)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) :
    Nat.card (Subgroup.center ↥K) = 1 := by
  have hq : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
  have : Group.IsPerfect ↥K := hq.1
  have hle := CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt hn e
  have hodd := odd_card_center hQ
  have hpos : 0 < Nat.card (Subgroup.center ↥K) := Nat.card_pos
  obtain ⟨k, hk⟩ := hodd
  omega

theorem false_of_tripleA7 (hA7 : HardMathSupport.Cooperstein.Coordinator.GF2NoFFTripleA7)
    (hW : ∀ w : W, w ^ 2 = 1) (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨B, -, hB⟩ := exists_isBestOffender_le hQ.1.1 hQ.1.2.1 hQ.1.2.2.1 hQ.1.2.2.2
  exact hA7 W hW X K hQ.genFitting_eq.symm hQ.2.2.2.1 hZ ⟨e⟩ B
    (isFFStarOffender_of_isBestOffender hB)

end

section

variable {X A K : Subgroup (MulAut W)}

theorem not_isGomiU3 (hQ : IsGomiQuad X A K)
    (hU3 : CFSG.QuasithinUnique.Setup.X5.EvenUnitaryThreeNoOffender) (hW : ∀ w : W, w ^ 2 = 1) :
    ¬ IsGomiU3 (↥K ⧸ Subgroup.center ↥K) := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  rintro ⟨⟨d, hv⟩, ⟨q, hq2, rfl⟩, ⟨e⟩⟩
  have hmodel :=
    CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.statedClassicalModel_psu_of_twistedA q hv e
  rw [hq2] at hmodel
  have hf : 2 ≤ q.exponent := by
    have h3 : 3 ≤ q.card :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2 rfl
    have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    by_contra hlt
    have hle : q.exponent ≤ 1 := by omega
    have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
    omega
  exact hQ.false_of_psu3 hU3 hW' hf hmodel

theorem not_isGomiSz (hQ : IsGomiQuad X A K)
    (hSz : ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid),
      HardMathSupport.Cooperstein.Coordinator.NoIrrFFOffender
        (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group)
    (hW : ∀ w : W, w ^ 2 = 1) : ¬ IsGomiSz (↥K ⧸ Subgroup.center ↥K) := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  rintro ⟨⟨d, hv⟩, ⟨m, rfl⟩, ⟨e⟩⟩
  exact hQ.false_of_suzuki hSz hW' hv e

theorem ffConclusion (hQ : IsGomiQuad X A K)
    (hFF : HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) (hW : ∀ w : W, w ^ 2 = 1)
    (hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K)) :
    HardMathSupport.Cooperstein.Coordinator.FFConclusion (↥K ⧸ Subgroup.center ↥K) :=
  hFF W hW X K ⟨hQ.genFitting_eq.symm, hQ.2.2.2.1, hQ.pCore_eq_bot, hcat⟩ hQ.isFFModule

omit [Finite W] in
private theorem mulEquiv_alt_of_card_center {n : ℕ} (hZ : Nat.card (Subgroup.center ↥K) = 1)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) :
    Nonempty (↥K ≃* alternatingGroup (Fin n)) := by
  have hbot : Subgroup.center ↥K = ⊥ := Subgroup.card_eq_one.mp hZ
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e⟩

theorem isChevTwo_or_alt (hQ : IsGomiQuad X A K)
    (hFF : HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hA7 : HardMathSupport.Cooperstein.Coordinator.GF2NoFFTripleA7)
    (hSA : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hW : ∀ w : W, w ^ 2 = 1) (hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K)) :
    IsChevTwo (↥K ⧸ Subgroup.center ↥K) ∨
      ∃ n : ℕ, 7 ≤ n ∧ Nonempty (↥K ≃* alternatingGroup (Fin n)) := by
  rcases hQ.ffConclusion hFF hW hcat with hcl | ⟨m, hm, ⟨e⟩⟩
  · exact Or.inl (isChevTwo_of_classicalTwoOrG2 hcl)
  · by_cases h568 : m = 5 ∨ m = 6 ∨ m = 8
    · exact Or.inl (Or.inr (Or.inl ⟨m, h568, ⟨e⟩⟩))
    · right
      refine ⟨m, by omega, ?_⟩
      by_cases h7 : m = 7
      · subst h7
        have hq : CFSG.IsQuasisimple ↥K := hQ.2.2.2.1
        have : Group.IsPerfect ↥K := hq.1
        have h6 := card_center_dvd_six_of_schur hSA e
        have hodd := hQ.odd_card_center
        have hZ : Nat.card (Subgroup.center ↥K) = 1 := by
          have hpos : 0 < Nat.card (Subgroup.center ↥K) := Nat.card_pos
          have hle : Nat.card (Subgroup.center ↥K) ≤ 6 := Nat.le_of_dvd (by norm_num) h6
          interval_cases h : Nat.card (Subgroup.center ↥K)
          · rfl
          · exact absurd hodd (by decide)
          · exact (hQ.false_of_tripleA7 hA7 hW h e).elim
          · exact absurd hodd (by decide)
          · exact absurd h6 (by decide)
          · exact absurd hodd (by decide)
        exact mulEquiv_alt_of_card_center hZ e
      · exact mulEquiv_alt_of_card_center (hQ.card_center_eq_one_of_alt (by omega) e) e

end

end IsGomiQuad

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

private theorem isChevTwo_of_mulEquiv (e : Y ≃* Y') (h : IsChevTwo Y) : IsChevTwo Y' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

private theorem isGomiU3_of_mulEquiv (e : Y ≃* Y') (h : IsGomiU3 Y) : IsGomiU3 Y' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

private theorem isGomiSz_of_mulEquiv (e : Y ≃* Y') (h : IsGomiSz Y) : IsGomiSz Y' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

private noncomputable def centerQuotientEquiv (e : Y ≃* Y') :
    (Y ⧸ Subgroup.center Y) ≃* (Y' ⧸ Subgroup.center Y') :=
  QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y') e (Subgroup.map_center_eq e)

end Transport

theorem gomiHyp43OfKnown_of (hFF : HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hU3 : CFSG.QuasithinUnique.Setup.X5.EvenUnitaryThreeNoOffender)
    (hA7 : HardMathSupport.Cooperstein.Coordinator.GF2NoFFTripleA7)
    (hSA : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSz : ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid),
      HardMathSupport.Cooperstein.Coordinator.NoIrrFFOffender
        (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) :
    GomiHyp43OfKnown := by
  intro Ω _ _ G hev hct hknown
  refine ⟨hev, hct, ?_⟩
  intro K _ _ hK hsec hQ
  obtain ⟨W, _, _, hW, X, A, K₀, hquad, ⟨e⟩⟩ := hQ
  have eZ := centerQuotientEquiv e
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.1
  have hsec' : CFSG.SignalizerFunctorTheorem.IsSectionOf (K ⧸ Subgroup.center K) ↥G := by
    obtain ⟨K', f, hf⟩ := hsec
    exact ⟨K', (QuotientGroup.mk' (Subgroup.center K)).comp f,
      (QuotientGroup.mk'_surjective _).comp hf⟩
  have hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K) := hknown _ hsimple hsec'
  have hcat₀ : CFSG.Open.IsCatalogGroup (↥K₀ ⧸ Subgroup.center ↥K₀) := by
    obtain ⟨i, ⟨g⟩⟩ := hcat
    exact ⟨i, ⟨eZ.symm.trans g⟩⟩
  rcases hquad.isChevTwo_or_alt hFF hA7 hSA hW hcat₀ with hch | ⟨n, hn7, ⟨g⟩⟩
  · left
    refine ⟨⟨hK, ?_, isChevTwo_of_mulEquiv eZ.symm hch⟩,
      fun h => hquad.not_isGomiU3 hU3 hW (isGomiU3_of_mulEquiv eZ h),
      fun h => hquad.not_isGomiSz hSz hW (isGomiSz_of_mulEquiv eZ h)⟩
    have h := CFSG.pCore_map_iso 2 e.symm
    rw [hquad.2.2.2.2.1, Subgroup.map_bot] at h
    exact h.symm
  · exact Or.inr ⟨n, hn7, ⟨e.trans g⟩⟩

end CFSG.GroupTheory
