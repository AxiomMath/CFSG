module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1217Sigma
import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

namespace O1219SigmaProof

variable {G : Type*} [Group G]

theorem exists_zpowers_of_card_prime [Finite G] {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hY : Nat.card Y = p) : ∃ x : G, x ∈ Y ∧ orderOf x = p ∧ zpowers x = Y := by
  obtain ⟨x, hxY, hx1⟩ : ∃ x ∈ Y, x ≠ 1 := by
    by_contra! h
    have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr h
    rw [hbot, Subgroup.card_bot] at hY
    exact hp.one_lt.ne hY
  have hdvd : orderOf x ∣ p := hY ▸ Subgroup.orderOf_dvd_natCard Y hxY
  have hord : orderOf x = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  refine ⟨x, hxY, hord, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxY) ?_⟩
  rw [hY, Nat.card_zpowers, hord]

theorem card_eq_of_cyclic_exp [Finite G] {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hexp : ∀ y ∈ Y, y ^ p = 1) (hc : IsCyclic Y) (hne : Y ≠ ⊥) : Nat.card Y = p := by
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hcard : Nat.card Y = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hexp g g.2))
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exfalso
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hy' : (⟨y, hy⟩ : Y) ∈ zpowers g := hg ⟨y, hy⟩
    have hg1 : g = 1 := orderOf_eq_one_iff.mp h
    rw [hg1, Subgroup.zpowers_one_eq_bot] at hy'
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hy')
  · rw [hcard, h]

theorem le_normalizer_of_forall {F Y : Subgroup G}
    (h : ∀ f ∈ F, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) : F ≤ normalizer (Y : Set G) := by
  intro f hf
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h f hf y hy, fun hy => ?_⟩
  have := h f⁻¹ (F.inv_mem hf) _ hy
  simpa [mul_assoc] using this

theorem exists_elemAbelian_sq [Finite G] {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hexp : ∀ x ∈ X, x ^ p = 1) (hnc : ¬ IsCyclic X) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p X := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  have hne : X ≠ ⊥ := by
    rintro rfl
    exact hnc inferInstance
  obtain ⟨z, hzX, hz1, hzc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_central_of_normal hp hXp le_rfl
    (fun g hg u hu => X.mul_mem (X.mul_mem hg hu) (X.inv_mem hg)) hne
  obtain ⟨x, hxX, hxz⟩ : ∃ x ∈ X, x ∉ zpowers z := by
    by_contra! h
    have hzX' : zpowers z = X := le_antisymm (zpowers_le.mpr hzX) h
    exact hnc (hzX' ▸ (inferInstance : IsCyclic (zpowers z)))
  have hmem : ∀ a ∈ ({x, z} : Set G), a ∈ X := by
    intro a ha
    rcases ha with rfl | ha
    · exact hxX
    · rw [Set.mem_singleton_iff.mp ha]; exact hzX
  have hcomm : ∀ a ∈ ({x, z} : Set G), ∀ b ∈ ({x, z} : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hzc _ hxX
    · exact (hzc _ hxX).symm
    · rfl
  have hE₀ : IsElemAbelian p (Subgroup.closure ({x, z} : Set G)) :=
    IsElemAbelian.closure_of_commute hcomm fun a ha => hexp a (hmem a ha)
  have hE₀X : Subgroup.closure ({x, z} : Set G) ≤ X := (Subgroup.closure_le X).2 hmem
  obtain ⟨n, hn⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hE₀
  have hzE : zpowers z < Subgroup.closure ({x, z} : Set G) := by
    refine lt_of_le_of_ne (zpowers_le.mpr (Subgroup.subset_closure (by simp))) fun h => hxz ?_
    rw [h]
    exact Subgroup.subset_closure (by simp)
  have hzcard : Nat.card (zpowers z) = p := by
    have hord : orderOf z = p := by
      have hdvd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one (hexp z hzX)
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    rw [Nat.card_zpowers, hord]
  have hlt := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hzE
  rw [hzcard, hn] at hlt
  have hn2 : 2 ≤ n := by
    by_contra! h
    have : p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at this
    omega
  obtain ⟨E, hEle, hE, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card hp hE₀ hn2 hn
  exact ⟨E, hEle.trans hE₀X, hE, hEc⟩

theorem card_of_mem_hyperplanes {q : ℕ} (hq : q.Prime) {F B : Subgroup G}
    (hFc : Nat.card F = q ^ 3)
    (hB : B ≤ F ∧ Nat.card F = q * Nat.card B) : Nat.card B = q ^ 2 := by
  have hcard := hB.2
  rw [hFc, show q ^ 3 = q * q ^ 2 by ring] at hcard
  exact (Nat.eq_of_mul_eq_mul_left hq.pos hcard).symm

theorem le_normalizer_inf_centralizer {p : ℕ} {F X B : Subgroup G} (hF : IsElemAbelian p F)
    (hBF : B ≤ F) (hFX : F ≤ normalizer (X : Set G)) :
    F ≤ normalizer ((X ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall fun f hf y hy => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hFX hf) y).mp hy.1
  · have hfC : f ∈ centralizer (B : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => hF.comm (hBF hh) hf
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hfC hy.2) (Subgroup.inv_mem _ hfC)

theorem gen_dichotomy [Finite G] {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p)
    {F X : Subgroup G} (hF : IsElemAbelian q F) (hFc : Nat.card F = q ^ 3)
    (hFX : F ≤ normalizer (X : Set G)) (hX : ∀ x ∈ X, x ^ p = 1) (hnc : ¬ IsCyclic X) :
    (∃ B : Subgroup G, B ≤ F ∧ Nat.card B = q ^ 2 ∧
        ¬ IsCyclic ↥(X ⊓ centralizer (B : Set G))) ∨
      (∃ Y₁ Y₂ : Subgroup G, Y₁ ≤ X ∧ Y₂ ≤ X ∧ Nat.card Y₁ = p ∧ Nat.card Y₂ = p ∧ Y₁ ≠ Y₂ ∧
        F ≤ normalizer (Y₁ : Set G) ∧ F ≤ normalizer (Y₂ : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p X := fun g => ⟨1, Subtype.ext (by simpa using hX g g.2)⟩
  have hcop : Nat.Coprime q (Nat.card X) := by
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hq hp).mpr hqp)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes hq hF
    (by rw [hFc]; exact Nat.le_self_pow (by norm_num) q) hFX hcop
  by_cases hcyc : ∀ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes q F,
      IsCyclic ↥(X ⊓ centralizer (B : Set G))
  · right
    have key : ∃ B₁ ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes q F,
        ∃ B₂ ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes q F,
        X ⊓ centralizer (B₁ : Set G) ≠ ⊥ ∧ X ⊓ centralizer (B₂ : Set G) ≠ ⊥ ∧
          X ⊓ centralizer (B₁ : Set G) ≠ X ⊓ centralizer (B₂ : Set G) := by
      by_contra hcon
      push Not at hcon
      by_cases hall : ∀ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes q F,
          X ⊓ centralizer (B : Set G) = ⊥
      · apply hnc
        have hXbot : X = ⊥ := by rw [← hgen]; exact iSup₂_eq_bot.2 hall
        rw [hXbot]
        infer_instance
      · push Not at hall
        obtain ⟨B₀, hB₀, hne₀⟩ := hall
        have hle : (⨆ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes q F,
            X ⊓ centralizer (B : Set G)) ≤ X ⊓ centralizer (B₀ : Set G) :=
          iSup₂_le fun B hB => by
            by_cases h : X ⊓ centralizer (B : Set G) = ⊥
            · rw [h]; exact bot_le
            · exact (hcon B hB B₀ hB₀ h hne₀).le
        rw [hgen] at hle
        have heq : X ⊓ centralizer (B₀ : Set G) = X := le_antisymm inf_le_left hle
        exact hnc (heq ▸ hcyc B₀ hB₀)
    obtain ⟨B₁, hB₁, B₂, hB₂, h1, h2, h12⟩ := key
    exact ⟨_, _, inf_le_left, inf_le_left,
      card_eq_of_cyclic_exp hp (fun y hy => hX y hy.1) (hcyc B₁ hB₁) h1,
      card_eq_of_cyclic_exp hp (fun y hy => hX y hy.1) (hcyc B₂ hB₂) h2, h12,
      le_normalizer_inf_centralizer hF hB₁.1 hFX, le_normalizer_inf_centralizer hF hB₂.1 hFX⟩
  · left
    push Not at hcyc
    obtain ⟨B, hB, hncB⟩ := hcyc
    exact ⟨B, hB.1, card_of_mem_hyperplanes hq hFc hB, hncB⟩

theorem conj_mem_zpowers_pow {x f : G} {v : ℕ} (h : f * x * f⁻¹ = x ^ v) {a : G}
    (ha : a ∈ zpowers x) : f * a * f⁻¹ = a ^ v := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← conj_zpow, h, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem exists_char [Finite G] {p : ℕ} [Fact p.Prime] {x : G} (hx : orderOf x = p)
    {F : Subgroup G} (hF : F ≤ normalizer (zpowers x : Set G)) :
    ∃ c : ↥F →* (ZMod p)ˣ, ∀ f : F, ∀ a ∈ zpowers x,
      (f : G) * a * (f : G)⁻¹ = a ^ (((c f : (ZMod p)ˣ) : ZMod p).val) := by
  have hex : ∀ f : F, ∃ k : ℕ, (f : G) * x * (f : G)⁻¹ = x ^ k := fun f => by
    have hmem : (f : G) * x * (f : G)⁻¹ ∈ zpowers x :=
      (Subgroup.mem_normalizer_iff.mp (hF f.2) x).mp (Subgroup.mem_zpowers x)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
    exact ⟨k, hk.symm⟩
  choose k hk using hex
  have hmod : ∀ m n : ℕ, x ^ m = x ^ n → (m : ZMod p) = (n : ZMod p) := fun m n h => by
    rw [ZMod.natCast_eq_natCast_iff]
    rw [← hx]
    exact pow_eq_pow_iff_modEq.mp h
  have hone : (k 1 : ZMod p) = 1 := by
    have h1 : x ^ (k 1) = x ^ 1 := by rw [← hk 1, pow_one]; simp
    simpa using hmod _ _ h1
  have hmul : ∀ f g : F, (k (f * g) : ZMod p) = (k f : ZMod p) * (k g : ZMod p) := fun f g => by
    have h1 : x ^ (k (f * g)) = x ^ (k f * k g) := by
      rw [← hk (f * g), Subgroup.coe_mul]
      have hg := hk g
      have hf := hk f
      calc ((f : G) * (g : G)) * x * ((f : G) * (g : G))⁻¹
          = (f : G) * ((g : G) * x * (g : G)⁻¹) * (f : G)⁻¹ := by group
        _ = (f : G) * x ^ k g * (f : G)⁻¹ := by rw [hg]
        _ = ((f : G) * x * (f : G)⁻¹) ^ k g := by rw [conj_pow]
        _ = (x ^ k f) ^ k g := by rw [hf]
        _ = x ^ (k f * k g) := by rw [← pow_mul]
    simpa using hmod _ _ h1
  let ψ : ↥F →* ZMod p :=
    { toFun := fun f => (k f : ZMod p)
      map_one' := hone
      map_mul' := hmul }
  refine ⟨ψ.toHomUnits, fun f a ha => ?_⟩
  refine conj_mem_zpowers_pow ?_ ha
  have hval : (((ψ.toHomUnits f : (ZMod p)ˣ) : ZMod p)).val = k f % p :=
    ZMod.val_natCast p (k f)
  have hpow : x ^ (k f % p) = x ^ k f := by rw [← hx, pow_mod_orderOf]
  rw [hval, hpow]
  exact hk f

theorem index_ker_le {p q : ℕ} [Fact p.Prime] (hq : q.Prime) {F : Type*} [Group F] [Finite F]
    (hFq : ∀ f : F, f ^ q = 1) (c : F →* (ZMod p)ˣ) : c.ker.index ≤ q := by
  rw [Subgroup.index_ker]
  have hexp : Monoid.exponent ↥c.range ∣ q := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    obtain ⟨f, hf⟩ := g.2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hf, ← map_pow, hFq f, map_one]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd hq.pos hexp

def GoodPair (q p : ℕ) (F E : Subgroup G) : Prop :=
  IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ q ∣ Nat.card ↥(F ⊓ centralizer (E : Set G)) ∧
    ∀ A : Subgroup G, A ≤ E → Nat.card A = p →
      ∃ K : Subgroup G, K ≤ F ⊓ normalizer (A : Set G) ∧ IsElemAbelian q K ∧ Nat.card K = q ^ 2

theorem good_of_centralized [Finite G] {q p : ℕ} {F B E : Subgroup G}
    (hF : IsElemAbelian q F) (hBF : B ≤ F) (hBc : Nat.card B = q ^ 2)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) (hBE : E ≤ centralizer (B : Set G)) :
    GoodPair q p F E := by
  have hBE' : B ≤ centralizer (E : Set G) := Subgroup.le_centralizer_iff.mp hBE
  have hBFE : B ≤ F ⊓ centralizer (E : Set G) := le_inf hBF hBE'
  refine ⟨hE, hEc, ?_, fun A hAE _ => ⟨B, ?_, CFSG.Open.IsElemAbelian.mono hF hBF, hBc⟩⟩
  · have := Subgroup.card_dvd_of_le hBFE
    rw [hBc] at this
    exact dvd_trans (dvd_pow_self q two_ne_zero) this
  · exact le_inf hBF (hBE'.trans ((Subgroup.centralizer_le hAE).trans
      (Subgroup.centralizer_le_normalizer (A : Set G))))

theorem isElemAbelian_of_card_prime [Finite G] {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hY : Nat.card Y = p) : IsElemAbelian p Y := by
  haveI : IsCyclic Y := isCyclic_of_prime_card (p := p) (hp := ⟨hp⟩) hY
  refine ⟨inferInstance, fun a ha => ?_⟩
  have := pow_card_eq_one' (G := Y) (x := ⟨a, ha⟩)
  rw [hY] at this
  exact congrArg Subtype.val this

theorem card_sup_eq_sq [Finite G] {p : ℕ} (hp : p.Prime) {Y₁ Y₂ : Subgroup G}
    (h₁ : Nat.card Y₁ = p) (h₂ : Nat.card Y₂ = p) (hne : Y₁ ≠ Y₂)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) :
    IsElemAbelian p (Y₁ ⊔ Y₂) ∧ Nat.card ↥(Y₁ ⊔ Y₂) = p ^ 2 := by
  have hE : IsElemAbelian p (Y₁ ⊔ Y₂) :=
    IsElemAbelian.sup_of_commute (isElemAbelian_of_card_prime hp h₁)
      (isElemAbelian_of_card_prime hp h₂) hcomm
  refine ⟨hE, ?_⟩
  obtain ⟨n, hn⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hE
  have hlt' : Y₁ < Y₁ ⊔ Y₂ := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    have hle : Y₂ ≤ Y₁ := h ▸ le_sup_right
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h₁, h₂])).symm
  have hlt : p < p ^ n := by
    have := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt'
    rwa [h₁, hn] at this
  have hle : p ^ n ≤ p ^ 2 := by
    have := CFSG.GH74.Uniqueness.SU.SU1.card_sup_le_of_commute hcomm
    rw [hn, h₁, h₂] at this
    rwa [sq]
  have h1 : n ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have h2 : 2 ≤ n := by
    by_contra h
    have := Nat.pow_le_pow_right hp.pos (show n ≤ 1 by omega)
    rw [pow_one] at this
    omega
  rw [hn, show n = 2 by omega]

theorem diag_good [Finite G] {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    {F Y₁ Y₂ : Subgroup G} (hF : IsElemAbelian q F) (hFc : Nat.card F = q ^ 3)
    (h₁ : Nat.card Y₁ = p) (h₂ : Nat.card Y₂ = p) (hne : Y₁ ≠ Y₂)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hn₁ : F ≤ normalizer (Y₁ : Set G)) (hn₂ : F ≤ normalizer (Y₂ : Set G)) :
    GoodPair q p F (Y₁ ⊔ Y₂) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hE, hEc⟩ := card_sup_eq_sq hp h₁ h₂ hne hcomm
  obtain ⟨x₁, -, ho₁, e₁⟩ := exists_zpowers_of_card_prime hp h₁
  obtain ⟨x₂, -, ho₂, e₂⟩ := exists_zpowers_of_card_prime hp h₂
  obtain ⟨c₁, hc₁⟩ := exists_char (F := F) ho₁ (by rw [e₁]; exact hn₁)
  obtain ⟨c₂, hc₂⟩ := exists_char (F := F) ho₂ (by rw [e₂]; exact hn₂)
  have hact : ∀ f : F, c₁ f = c₂ f → ∀ y ∈ Y₁ ⊔ Y₂,
      (f : G) * y * (f : G)⁻¹ = y ^ (((c₁ f : (ZMod p)ˣ) : ZMod p).val) := by
    intro f hf y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hcomm hy
    have hfa := hc₁ f a (by rw [e₁]; exact ha)
    have hfb := hc₂ f b (by rw [e₂]; exact hb)
    rw [← hf] at hfb
    rw [show (f : G) * (a * b) * (f : G)⁻¹ = ((f : G) * a * (f : G)⁻¹) * ((f : G) * b * (f : G)⁻¹)
      by group, hfa, hfb]
    exact (Commute.mul_pow (hcomm a ha b hb) _).symm
  have hFq : ∀ f : F, f ^ q = 1 := fun f => Subtype.ext (hF.2 f f.2)
  have hker : ∀ d : ↥F →* (ZMod p)ˣ, q ^ 2 ≤ Nat.card d.ker := fun d => by
    have h := Subgroup.card_mul_index d.ker
    have hi := index_ker_le hq hFq d
    rw [hFc] at h
    have h' : q ^ 2 * q ≤ Nat.card d.ker * q := by
      calc q ^ 2 * q = q ^ 3 := by ring
        _ = Nat.card d.ker * d.ker.index := h.symm
        _ ≤ Nat.card d.ker * q := Nat.mul_le_mul_left _ hi
    exact Nat.le_of_mul_le_mul_right h' hq.pos
  let c : ↥F →* (ZMod p)ˣ := c₁ * c₂⁻¹
  set K₀ : Subgroup G := c.ker.map F.subtype with hK₀def
  have hK₀card : Nat.card K₀ = Nat.card c.ker :=
    Subgroup.card_map_of_injective F.subtype_injective
  have hK₀F : K₀ ≤ F := Subgroup.map_subtype_le _
  have hK₀e : IsElemAbelian q K₀ := CFSG.Open.IsElemAbelian.mono hF hK₀F
  obtain ⟨j, hj⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hq hK₀e
  have hj2 : 2 ≤ j := by
    have h := hker c
    rw [← hK₀card, hj] at h
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp h
  obtain ⟨K, hKK₀, hKe, hKc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card hq hK₀e hj2 hj
  have hK₀act : ∀ f ∈ K₀, ∀ a ∈ Y₁ ⊔ Y₂, ∃ v : ℕ, f * a * f⁻¹ = a ^ v := by
    intro f hf a ha
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf
    have hcc : c₁ f' = c₂ f' := by
      have h1 : c f' = 1 := MonoidHom.mem_ker.mp hf'
      have h2 : c₁ f' * (c₂ f')⁻¹ = 1 := h1
      exact mul_inv_eq_one.mp h2
    exact ⟨_, hact f' hcc a ha⟩
  refine ⟨hE, hEc, ?_, fun A hAE hAc => ⟨K, ?_, hKe, hKc⟩⟩
  · let C : Subgroup ↥F := c₁.ker ⊓ c₂.ker
    have hCidx : C.index ≤ q * q :=
      Subgroup.index_inf_le.trans
        (Nat.mul_le_mul (index_ker_le hq hFq c₁) (index_ker_le hq hFq c₂))
    have hCcard : q ≤ Nat.card C := by
      have h := Subgroup.card_mul_index C
      rw [hFc] at h
      have h' : q * q ^ 2 ≤ Nat.card C * q ^ 2 := by
        calc q * q ^ 2 = q ^ 3 := by ring
          _ = Nat.card C * C.index := h.symm
          _ ≤ Nat.card C * (q * q) := Nat.mul_le_mul_left _ hCidx
          _ = Nat.card C * q ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right h' (pow_pos hq.pos 2)
    have hC1 : 1 < Nat.card C := lt_of_lt_of_le hq.one_lt hCcard
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      ((Subgroup.one_lt_card_iff_ne_bot C).mp hC1)
    have hc1 : c₁ a.1 = 1 := MonoidHom.mem_ker.mp a.2.1
    have hc2 : c₂ a.1 = 1 := MonoidHom.mem_ker.mp a.2.2
    have hfE : ((a.1 : F) : G) ∈ F ⊓ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) := by
      refine ⟨a.1.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h := hact a.1 (hc1.trans hc2.symm) y hy
      rw [hc1] at h
      simp only [Units.val_one, ZMod.val_one, pow_one] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have hf1 : ((a.1 : F) : G) ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
    have hfq : ((a.1 : F) : G) ^ q = 1 := hF.2 _ a.1.2
    have hord : orderOf ((a.1 : F) : G) = q := by
      rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hfq) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hf1
      · exact h
    have := Subgroup.orderOf_dvd_natCard (F ⊓ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G)) hfE
    rw [hord] at this
    exact this
  · refine le_inf (hKK₀.trans hK₀F) (le_normalizer_of_forall fun f hf a ha => ?_)
    obtain ⟨v, hv⟩ := hK₀act f (hKK₀ hf) a (hAE ha)
    rw [hv]
    exact A.pow_mem ha v

theorem key_good [Finite G] {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p)
    {F D : Subgroup G} (hF : IsElemAbelian q F) (hFc : Nat.card F = q ^ 3)
    (hFD : F ≤ normalizer (D : Set G)) (hDexp : ∀ x ∈ D, x ^ p = 1) (hnc : ¬ IsCyclic D) :
    ∃ E : Subgroup G, E ≤ D ∧ GoodPair q p F E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hDp : IsPGroup p D := fun g => ⟨1, Subtype.ext (by simpa using hDexp g g.2)⟩
  have hDne : D ≠ ⊥ := by
    rintro rfl
    exact hnc inferInstance
  obtain ⟨z, hzD, hz1, hzc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_central_of_normal hp hDp le_rfl
    (fun g hg u hu => D.mul_mem (D.mul_mem hg hu) (D.inv_mem hg)) hDne
  set Z : Subgroup G := D ⊓ centralizer (D : Set G) with hZ
  have hZD : Z ≤ D := inf_le_left
  have hzZ : z ∈ Z := ⟨hzD, Subgroup.mem_centralizer_iff.mpr hzc⟩
  have hFZ : F ≤ normalizer (Z : Set G) := le_normalizer_of_forall fun f hf y hy => by
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hFD hf) y).mp hy.1,
      Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    have h1 : f⁻¹ * d * f ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hFD (F.inv_mem hf)) d).mp hd
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hy.2 _ h1
    calc d * (f * y * f⁻¹) = f * ((f⁻¹ * d * f) * y) * f⁻¹ := by group
      _ = f * (y * (f⁻¹ * d * f)) * f⁻¹ := by rw [h2]
      _ = (f * y * f⁻¹) * d := by group
  have hZcomm : ∀ a ∈ D, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ha
  by_cases hZc : IsCyclic Z
  · have hZ1 : Z ≠ ⊥ := fun h => hz1 (Subgroup.mem_bot.mp (h ▸ hzZ))
    have hZcard : Nat.card Z = p := card_eq_of_cyclic_exp hp (fun y hy => hDexp y hy.1) hZc hZ1
    rcases gen_dichotomy hq hp hqp hF hFc hFD hDexp hnc with
      ⟨B, hBF, hBc, hncB⟩ | ⟨Y₁, Y₂, hY₁, hY₂, hc₁, hc₂, hne, hn₁, hn₂⟩
    · obtain ⟨E, hEle, hE, hEc⟩ := exists_elemAbelian_sq
        (X := D ⊓ centralizer (B : Set G)) hp (fun x hx => hDexp x hx.1) hncB
      exact ⟨E, hEle.trans inf_le_left,
        good_of_centralized hF hBF hBc hE hEc (hEle.trans inf_le_right)⟩
    · obtain ⟨Y, hYD, hYc, hYZ, hnY⟩ : ∃ Y : Subgroup G, Y ≤ D ∧ Nat.card Y = p ∧ Y ≠ Z ∧
          F ≤ normalizer (Y : Set G) := by
        by_cases h : Y₁ = Z
        · exact ⟨Y₂, hY₂, hc₂, fun h2 => hne (h.trans h2.symm), hn₂⟩
        · exact ⟨Y₁, hY₁, hc₁, h, hn₁⟩
      exact ⟨Y ⊔ Z, sup_le hYD hZD,
        diag_good hq hp hF hFc hYc hZcard hYZ (fun a ha b hb => hZcomm a (hYD ha) b hb) hnY hFZ⟩
  · rcases gen_dichotomy hq hp hqp hF hFc hFZ (fun x hx => hDexp x hx.1) hZc with
      ⟨B, hBF, hBc, hncB⟩ | ⟨Y₁, Y₂, hY₁, hY₂, hc₁, hc₂, hne, hn₁, hn₂⟩
    · obtain ⟨E, hEle, hE, hEc⟩ := exists_elemAbelian_sq
        (X := Z ⊓ centralizer (B : Set G)) hp (fun x hx => hDexp x hx.1.1) hncB
      exact ⟨E, (hEle.trans inf_le_left).trans hZD,
        good_of_centralized hF hBF hBc hE hEc (hEle.trans inf_le_right)⟩
    · exact ⟨Y₁ ⊔ Y₂, sup_le (hY₁.trans hZD) (hY₂.trans hZD),
        diag_good hq hp hF hFc hc₁ hc₂ hne
          (fun a ha b hb => hZcomm a (hZD (hY₁ ha)) b (hY₂ hb)) hn₁ hn₂⟩

theorem three_le_pRank_of_mem_sigmaM {G : Type} [Group G] [Finite G] (hS : Standing G)
    (hUC : rankThreeUC G) {q : ℕ} {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hq : q ∈ sigmaM G M) : 3 ≤ CFSG.Open.pRank q M := by
  have hqq : q.Prime := sigmaA_prime q hq.1
  haveI : Fact q.Prime := ⟨hqq⟩
  obtain ⟨E, hEM, hE, hEc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hqq hq.2
  have hEp : IsPGroup q E := elementary_isPGroup q E hE
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨M₁, hcw⟩ := exists_isCoreWitness hUC hq.1 Q
  have hQM₁ : (Q : Subgroup G) ≤ M₁ := le_normalizer.trans (hcw.normalizer_le hS hq.1)
  have hk : 2 ≤ CFSG.Open.pRank q E := CFSG.SectionRank.le_pRank hqq.one_lt (le_refl E) hE hEc
  have hE2 : 2 ≤ CFSG.Open.pRank q (M ⊓ M₁) :=
    hk.trans (pRank_mono q hqq.one_lt (le_inf hEM (hEQ.trans hQM₁)))
  have hMM₁ : M ≤ M₁ := hcw.u2 M hM.1 hE2
  have heq : M₁ = M := hM.2 M₁ hcw.maxLocal.1 hMM₁
  have hQM : (Q : Subgroup G) ≤ M := heq ▸ hQM₁
  have h3 : 3 ≤ CFSG.Open.pRank q (Q : Subgroup G) :=
    selected_sylow_rank_at_least_three hS.rank q hq.1 Q
  exact h3.trans (pRank_mono q hqq.one_lt hQM)

end O1219SigmaProof

theorem O1219Sigma_of_O1217Sigma (h : O1217Sigma) : O1219Sigma := by
  intro G _ _ hS hUC M hM hw hst q p hq hp hp2 hpσ D hDM hDnc hDexp _ hrk
  have hqq : q.Prime := sigmaA_prime q hq.1
  have hqp : q ≠ p := fun hqp => hpσ (hqp ▸ hq)
  have h3 : 3 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (D : Set G)) := by
    rw [hrk]
    exact O1219SigmaProof.three_le_pRank_of_mem_sigmaM hS hUC hM hq
  obtain ⟨F, hFle, hF, hFc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hqq h3
  have hFM : F ≤ M := hFle.trans inf_le_left
  have hFD : F ≤ Subgroup.normalizer (D : Set G) := hFle.trans inf_le_right
  obtain ⟨E, hED, hEabel, hEcard, hqC, hA⟩ :=
    O1219SigmaProof.key_good hqq hp hqp hF hFc hFD hDexp hDnc
  refine ⟨E, hED, hEabel, hEcard, ?_⟩
  refine h G hS hUC M hM hw hst q p hq hp hp2 E (hED.trans hDM) hEabel hEcard ?_ ?_
  · exact dvd_trans hqC (Subgroup.card_dvd_of_le (inf_le_inf_right _ hFM))
  · intro A hAE hAc
    obtain ⟨K, hKle, hKe, hKc⟩ := hA A hAE hAc
    exact CFSG.SectionRank.le_pRank hqq.one_lt (hKle.trans (inf_le_inf_right _ hFM)) hKe hKc

end CFSG.LocalAnalysis.RankThreeUC.S15
