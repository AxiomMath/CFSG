module

public import CFSG.LieType.SeitzGeneration.CubeCoverLayer
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnCard
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6CoverTw
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5Even
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShellGl
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHKey
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenReps
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Reduce
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutMain
public import CFSG.LargeExtraspecial.S8CBFCrit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141f2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
public import CFSG.Quasithin.SteinbergCBGDTrace
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

open scoped Pointwise

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.CubeCoverLayer
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

namespace CFSG.LieType.SeitzGeneration.CubeCoverTwE6

theorem exists_lift_SU3 {G C : Type} [Group G] [Group C] {π : G →* C}
    {ℓ f : ℕ} {k : Type} [Field k] (h : UnitaryFieldData ℓ f k) (h2 : ℓ ^ f ≠ 2)
    [Finite G] (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (ρ₀ : unitarySU ℓ f k 3 →* C) :
    ∃ ρ : unitarySU ℓ f k 3 →* G, π.comp ρ = ρ₀ := by
  haveI : Finite k := h.finite
  have hF : Nat.card k = (ℓ ^ f) ^ 2 := by
    rw [h.card, Nat.mul_comm 2 f, pow_mul]
  have hq : (3, ℓ ^ f) ≠ (3, 2) := fun hh => h2 (Prod.mk.inj hh).2
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP k ℓ := h.charP
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (p := ℓ) (f := f) (F := k) hF h.one_le (n := 3) le_rfl (by norm_num) hq
      (π := CFSG.LieType.Steinberg.pullbackFst ρ₀ π)
      (CFSG.LieType.Steinberg.pullbackFst_surjective (β := ρ₀) (η := π) hπ)
      (CFSG.LieType.Steinberg.ker_pullbackFst_le_center (β := ρ₀) (η := π) hker)
  refine ⟨(MonoidHom.snd (unitarySU ℓ f k 3) G).comp
    ((CFSG.LieType.Steinberg.pullback ρ₀ π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : CFSG.LieType.Steinberg.pullback ρ₀ π) :
      unitarySU ℓ f k 3 × G).1 = x := hs x
  have h2' := CFSG.LieType.Steinberg.mem_pullback.1 (s x).2
  rw [h1] at h2'
  show π (((s x : CFSG.LieType.Steinberg.pullback ρ₀ π) :
    unitarySU ℓ f k 3 × G).2) = ρ₀ x
  exact h2'.symm

end CFSG.LieType.SeitzGeneration.CubeCoverTwE6

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

theorem TwE6ThreeA2Line.torus_pow_eq_one
    {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K}
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n) {m : ℕ} {t : ModGL TwistTag.E6.tag K}
    (ht : t ∈ T) (hpow : t ^ (ringChar K ^ m) = 1) : t = 1 := by
  classical
  obtain ⟨q, Fr, g₀, pic⟩ := hL.picture
  have hψ : twLinePsi K g₀ t ∈ torusGroup Tag.E6 (AlgebraicClosure K) :=
    (pic.mem_T t).1 ht |>.2
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hψ
  have hψpow : (twLinePsi K g₀ t) ^ (ringChar K ^ m) = 1 := by
    rw [← map_pow, hpow, map_one]
  rw [hb] at hψpow
  have hbpow : b ^ (ringChar K ^ m) = 1 := by
    apply rootDiagUnit_injective
    rw [← rootDiagUnit_pow, hψpow, rootDiagUnit_one]
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have hfield : ∀ c : AlgebraicClosure K, c ^ (ringChar K ^ m) = 1 → c = 1 := by
    intro c hc
    have h0 : (c - 1) ^ (ringChar K ^ m) = 0 := by
      rw [sub_pow_char_pow (p := ringChar K) (n := m), hc, one_pow, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)
  have hb1 : b = 1 := by
    funext i
    apply Units.ext
    apply hfield
    have hi := congrFun hbpow i
    simpa using congrArg Units.val hi
  apply twLinePsi_injective K g₀
  rw [hb, hb1, rootDiagUnit_one, map_one]

theorem TwE6ThreeA2Line.mem_iSup_of_charPow
    {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K}
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n) (hK3 : ringChar K ≠ 3)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ twistedE6RootGroup K σ ⊓
      Subgroup.centralizer {h₀}) {m : ℕ} (hxpow : x ^ (ringChar K ^ m) = 1) :
    x ∈ ⨆ i, L i := by
  classical
  set N : Subgroup (ModGL TwistTag.E6.tag K) := ⨆ i, L i with hN
  obtain ⟨k, hk⟩ := hL.conj_shift x hx
  have hk3all : ∀ k : Fin 3, k + k + k = (0 : Fin 3) := by decide
  have hx3norm : ∀ i, (L i).map (MulAut.conj (x ^ 3)).toMonoidHom = L i := by
    intro i
    have h3 : MulAut.conj (x ^ 3) = MulAut.conj x * MulAut.conj x * MulAut.conj x := by
      rw [pow_three, map_mul, map_mul]
      group
    have hcomp : (MulAut.conj x * MulAut.conj x * MulAut.conj x).toMonoidHom =
        (MulAut.conj x).toMonoidHom.comp ((MulAut.conj x).toMonoidHom.comp
          (MulAut.conj x).toMonoidHom) := rfl
    rw [h3, hcomp, ← Subgroup.map_map, ← Subgroup.map_map, hk, hk, hk]
    congr 1
    rw [show i + k + k + k = i + (k + k + k) by abel, hk3all k, add_zero]
  have hx3mem : x ^ 3 ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} :=
    Subgroup.pow_mem _ hx 3
  have hx3TN : x ^ 3 ∈ T ⊔ N := by
    apply hL.shift_zero (x ^ 3) hx3mem
    simpa [hN] using hx3norm
  have hrprime : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hcop3 : Nat.Coprime 3 (ringChar K ^ m) := by
    have h3r : Nat.Coprime 3 (ringChar K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hdvd =>
        hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hrprime).1 hdvd).symm
    exact h3r.pow_right m
  have hxTN : x ∈ T ⊔ N := by
    have hgcd := Nat.gcd_eq_gcd_ab 3 (ringChar K ^ m)
    rw [hcop3.gcd_eq_one, Nat.cast_one] at hgcd
    have e : x = (x ^ 3) ^ (Nat.gcdA 3 (ringChar K ^ m)) *
        (x ^ (ringChar K ^ m)) ^ (Nat.gcdB 3 (ringChar K ^ m)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hgcd,
        zpow_one]
    rw [e, hxpow, one_zpow, mul_one]
    exact (T ⊔ N).zpow_mem hx3TN _
  have hTN : T ≤ Subgroup.normalizer (N : Set (ModGL TwistTag.E6.tag K)) := by
    intro t ht
    apply hL.le_normalizer
    refine Subgroup.mem_inf.2 ⟨hL.T_le ht, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hL.T_comm t ht h₀ hL.h₀_mem_T
  obtain ⟨t, htT, l, hlN, rfl⟩ : ∃ t ∈ T, ∃ l ∈ N, t * l = x := by
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right T N hTN
    have hx' : x ∈ (↑T : Set (ModGL TwistTag.E6.tag K)) * (↑N : Set (ModGL TwistTag.E6.tag K)) := by
      rw [← hset]
      exact hxTN
    exact Set.mem_mul.1 hx'
  have hmove : ∀ (y : ModGL TwistTag.E6.tag K) (hy : y ∈ N) (R : ℕ),
      ∃ y' ∈ N, (t * y) ^ R = t ^ R * y' := by
    intro y hy R
    induction R with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ R ih =>
      obtain ⟨y', hy', h⟩ := ih
      refine ⟨(t⁻¹ * y' * t) * y, N.mul_mem ?_ hy, ?_⟩
      · have hmem := Subgroup.mem_normalizer_iff.1
          (inv_mem (hTN htT)) y'
        rw [inv_inv] at hmem
        exact hmem.mp hy'
      · rw [pow_succ, h]
        group
  obtain ⟨y, hy, hmove⟩ := hmove l hlN (ringChar K ^ m)
  have htR : t ^ (ringChar K ^ m) ∈ N := by
    have hR : t ^ (ringChar K ^ m) = y⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hmove]
      exact hxpow
    exact hR ▸ N.inv_mem hy
  have hTcard : Nat.Coprime (Nat.card T) (ringChar K) := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hrprime]
    intro hdvd
    haveI : Fact (ringChar K).Prime := ⟨hrprime⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (ringChar K) hdvd
    have hu1 : (u : ModGL TwistTag.E6.tag K) = 1 := by
      apply hL.torus_pow_eq_one u.2
      rw [← hu, pow_one]
      exact congrArg Subtype.val (pow_orderOf_eq_one u)
    have hu1' : u = 1 := Subtype.ext hu1
    have h1 : orderOf u = 1 := by rw [hu1', orderOf_one]
    rw [hu] at h1
    exact hrprime.ne_one h1
  have hcopT : Nat.Coprime (orderOf t) (ringChar K ^ m) :=
    (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard T htT) hTcard).pow_right m
  have htN : t ∈ N := by
    have hgcd := Nat.gcd_eq_gcd_ab (orderOf t) (ringChar K ^ m)
    rw [hcopT.gcd_eq_one, Nat.cast_one] at hgcd
    have e : t = (t ^ orderOf t) ^ (Nat.gcdA (orderOf t) (ringChar K ^ m)) *
        (t ^ (ringChar K ^ m)) ^ (Nat.gcdB (orderOf t) (ringChar K ^ m)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hgcd,
        zpow_one]
    rw [e, pow_orderOf_eq_one, one_zpow, one_mul]
    simpa using N.zpow_mem htR (Nat.gcdB (orderOf t) (ringChar K ^ m))
  exact N.mul_mem htN hlN

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three


namespace CFSG.LieType.SeitzGeneration.CubeCoverTwE6

section Frames


theorem exists_twLine_frames_h0 {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hs : MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) ∈ E) :
    ∃ (ℓ f : ℕ) (h : UnitaryFieldData ℓ f K)
      (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ),
      ℓ ^ f = q ∧ CFSG.IsQuasisimple (unitarySU ℓ f K 3) ∧
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ a b, ρ i a * ρ j b = ρ j b * ρ i a) ∧
      (∀ i a, MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) (ρ i a) = ρ i a) ∧
      (∀ ε ∈ E, ∃ m : Fin 3,
        (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + m)).range) ∧
          (m = 0 → ∀ i, ∃ a ∈ (suConj h).range, ∀ x, ε (ρ i x) = ρ i (a x))) ∧
      (∀ c : twistedE6RootGroup K σ,
        Commute c (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) →
        (∃ m : ℕ, c ^ (ringChar K ^ m) = 1) → c ∈ ⨆ i, (ρ i).range) := by
  classical
  let s : twistedE6RootGroup K σ := ⟨h₀, hL.h₀_mem⟩
  have hsh : (s : ModGL TwistTag.E6.tag K) = h₀ := rfl
  obtain ⟨ℓ, f, h, ρ, hℓf, hinj, hrange, hact⟩ :=
    (twLayerModel_of_torusModel twTorusModel_holds) K σ q hK3 hσ hKq h3 hq2 h₀ L T n hL
  have hYq : CFSG.IsQuasisimple (unitarySU ℓ f K 3) := by
    have e1 : unitarySU ℓ f K 3 ≃* (ρ 0).range := MonoidHom.ofInjective (hinj 0)
    have e2 : (ρ 0).range ≃* ((ρ 0).range.map (twistedE6RootGroup K σ).subtype) :=
      Subgroup.equivMapOfInjective _ _ (twistedE6RootGroup K σ).subtype_injective
    have e3 : ((ρ 0).range.map (twistedE6RootGroup K σ).subtype) ≃* L 0 :=
      MulEquiv.subgroupCongr (hrange 0)
    exact CFSG.IsQuasisimple.of_mulEquiv (e1.trans (e2.trans e3)) (hL.L_quasisimple 0)
  have hmem : ∀ i x, ((ρ i x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈ L i := by
    intro i x
    rw [← hrange i]
    exact ⟨ρ i x, ⟨x, rfl⟩, rfl⟩
  have hcomm : ∀ i j, i ≠ j → ∀ a b, ρ i a * ρ j b = ρ j b * ρ i a := fun i j hij a b =>
    Subtype.ext (hL.L_commute i j hij _ (hmem i a) _ (hmem j b))
  have hcen : ∀ i, ∀ y ∈ L i, y * h₀ = h₀ * y := by
    intro i y hy
    have hc : (⟨h₀, hL.h₀_mem_L i⟩ : ↥(L i)) ∈ Subgroup.center ↥(L i) := by
      rw [hL.L_center_eq i]
      exact Subgroup.mem_zpowers h₀
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
  have hσρ : ∀ i a, MulAut.conj s (ρ i a) = ρ i a := by
    intro i a
    apply Subtype.ext
    show (s : ModGL TwistTag.E6.tag K) * (ρ i a : ModGL TwistTag.E6.tag K) *
      (s : ModGL TwistTag.E6.tag K)⁻¹ = ρ i a
    rw [hsh, mul_inv_eq_iff_eq_mul]
    exact (hcen i _ (hmem i a)).symm
  have hdec : ∀ ε ∈ E, ∃ m : Fin 3,
      (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ a ∈ (suConj h).range, ∀ x, ε (ρ i x) = ρ i (a x)) := by
    intro ε hε
    have hε3 : ε ^ 3 = 1 := hE.2 ε hε
    have hεc : ε * MulAut.conj s = MulAut.conj s * ε :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨ε, hε⟩ : E) ⟨MulAut.conj s, hs⟩)
    obtain ⟨m, hm⟩ := twLayer_exists_shift_frames hL hsh hε3 hεc ρ hrange
    refine ⟨m, hm, fun hm0 i => ?_⟩
    subst hm0
    have hfix : ∀ i, (ρ i).range.map ε.toMonoidHom = (ρ i).range := fun i => by
      rw [hm i, add_zero]
    obtain ⟨γ, hγ⟩ := hact s hsh ε (hED hε) hεc hfix i
    obtain ⟨γ', hγ'⟩ := exists_suConj_eq_conjSU h γ
    exact ⟨suConj h γ', ⟨γ', rfl⟩, fun x => by rw [hγ x, hγ']⟩
  have hlast : ∀ c : twistedE6RootGroup K σ, Commute c s →
      (∃ m : ℕ, c ^ (ringChar K ^ m) = 1) → c ∈ ⨆ i, (ρ i).range := by
    intro c hc hcr
    have hcC : (c : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ ⊓
        Subgroup.centralizer ({h₀} : Set (ModGL TwistTag.E6.tag K)) := by
      refine Subgroup.mem_inf.2 ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg Subtype.val hc
      simpa [hsh] using h
    obtain ⟨m, hm⟩ := hcr
    have hm' : (c : ModGL TwistTag.E6.tag K) ^ (ringChar K ^ m) = 1 := by
      simpa using congrArg (fun x : twistedE6RootGroup K σ =>
        (x : ModGL TwistTag.E6.tag K)) hm
    have hcN := hL.mem_iSup_of_charPow hK3 hcC hm'
    have hmap : ((⨆ i, (ρ i).range).map (twistedE6RootGroup K σ).subtype) = ⨆ i, L i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hrange
    have hmemN : (c : ModGL TwistTag.E6.tag K) ∈
        ((⨆ i, (ρ i).range).map (twistedE6RootGroup K σ).subtype) := by
      rw [hmap]
      exact hcN
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hmemN
    have hyc' : y = c := Subtype.ext hyc
    rwa [← hyc']
  exact ⟨ℓ, f, h, ρ, hℓf, hYq, hinj, hcomm, hσρ, hdec, hlast⟩

theorem exists_twThreeA2_frames {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    {s : twistedE6RootGroup K σ} (hs : MulAut.conj s ∈ E)
    (h24 : twE6FixDim K σ s = 24) :
    ∃ (ℓ f : ℕ) (h : UnitaryFieldData ℓ f K)
      (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ),
      ℓ ^ f = q ∧ CFSG.IsQuasisimple (unitarySU ℓ f K 3) ∧
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ a b, ρ i a * ρ j b = ρ j b * ρ i a) ∧
      (∀ i a, MulAut.conj s (ρ i a) = ρ i a) ∧
      (∀ ε ∈ E, ∃ m : Fin 3,
        (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + m)).range) ∧
          (m = 0 → ∀ i, ∃ a ∈ (suConj h).range, ∀ x, ε (ρ i x) = ρ i (a x))) ∧
      (∀ c : twistedE6RootGroup K σ, Commute c s →
        (∃ m : ℕ, c ^ (ringChar K ^ m) = 1) → c ∈ ⨆ i, (ρ i).range) := by
  classical
  have hs3 : s ^ 3 = 1 := by
    have hc : s ^ 3 ∈ Subgroup.center (twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) => φ y)
        (show MulAut.conj (s ^ 3) = 1 by rw [map_pow]; exact hE.2 _ hs)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * s ^ 3 = (s ^ 3 * y * (s ^ 3)⁻¹) * s ^ 3 := by rw [h]
        _ = s ^ 3 * y := by group
    rw [exceptional_fixed_center_trivial TwistTag.E6 K σ] at hc
    exact Subgroup.mem_bot.1 hc
  obtain ⟨h₀, L, T, n, hL⟩ := twE6ThreeA2LineStmt_holds K σ q hK3 hσ hKq h3 hq2
  have hs3' : (s : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg (fun x : twistedE6RootGroup K σ =>
      (x : ModGL TwistTag.E6.tag K)) hs3
  have hs24 : Module.finrank K (LinearMap.ker
      (((s : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 :=
    h24
  obtain ⟨g, hgC, hgs⟩ := twE6ThreeA2Conj_holds K σ q hK3 hσ hKq h3 hq2
    (s : ModGL TwistTag.E6.tag K) s.2 h₀ hL.h₀_mem hs3' hL.h₀_pow hs24 hL.finrank_fixed
  let g' : twistedE6RootGroup K σ := ⟨g, hgC⟩
  have hgs' : g' * s * g'⁻¹ = ⟨h₀, hL.h₀_mem⟩ := by
    apply Subtype.ext
    simpa [g'] using hgs
  let τ : MulAut (twistedE6RootGroup K σ) := MulAut.conj g'
  let τi : MulAut (twistedE6RootGroup K σ) := MulAut.conj g'⁻¹
  have hτi : τi = τ⁻¹ := by simp only [τi, τ, map_inv]
  have hτs : τ s = ⟨h₀, hL.h₀_mem⟩ := by
    show g' * s * g'⁻¹ = _
    exact hgs'
  let E' : Subgroup (MulAut (twistedE6RootGroup K σ)) :=
    E.map (MulAut.conj τ).toMonoidHom
  have hE' : IsElemAbelian 3 E' := hE.map (MulAut.conj τ).toMonoidHom
  have hE'card : Nat.card E' = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective, hcard]
  have hE'D : E' ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rintro _ ⟨ε, hε, rfl⟩
    have hcD : τ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := Subgroup.mem_sup_left ⟨g', rfl⟩
    show τ * ε * τ⁻¹ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ
    exact mul_mem (mul_mem hcD (hED hε)) (inv_mem hcD)
  have hsig' : MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) ∈ E' := by
    refine Subgroup.mem_map.2 ⟨MulAut.conj s, hs, ?_⟩
    show (MulAut.conj τ) (MulAut.conj s) =
      MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ)
    apply MulEquiv.ext
    intro y
    change τ (s * τ⁻¹ y * s⁻¹) =
      (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) * y *
        (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ)⁻¹
    simp only [map_mul, map_inv, hτs]
    simp
  obtain ⟨ℓ, f, h, ρ₀, hℓf, hYq, hinj₀, hcomm₀, hcent₀, hdec₀, hlast₀⟩ :=
    exists_twLine_frames_h0 hK3 hσ hKq h3 hq2 hL hE' hE'card hE'D hsig'
  let ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ :=
    fun i => τi.toMonoidHom.comp (ρ₀ i)
  have hρrange : ∀ i, (ρ i).range = ((ρ₀ i).range).map τi.toMonoidHom :=
    fun i => MonoidHom.range_comp τi.toMonoidHom (ρ₀ i)
  refine ⟨ℓ, f, h, ρ, hℓf, hYq, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => τi.injective.comp (hinj₀ i)
  · intro i j hij a b
    have h := congrArg (⇑τi) (hcomm₀ i j hij a b)
    simpa [ρ, map_mul] using h
  · intro i a
    have hττi : τ (ρ i a) = ρ₀ i a := by
      change g' * (g'⁻¹ * ρ₀ i a * g') * g'⁻¹ = ρ₀ i a
      group
    have hconj : MulAut.conj s =
        τi * MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) * τ := by
      have hsEq : s = g'⁻¹ * ⟨h₀, hL.h₀_mem⟩ * g' := by
        rw [← hgs']
        group
      rw [hsEq, map_mul, map_mul]
    calc MulAut.conj s (ρ i a)
        = (τi * MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) * τ)
            (ρ i a) := by rw [hconj]
      _ = τi (MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) (τ (ρ i a))) := by
            rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = τi (MulAut.conj (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) (ρ₀ i a)) := by
            rw [hττi]
      _ = τi (ρ₀ i a) := by rw [hcent₀ i a]
      _ = ρ i a := rfl
  · intro ε hε
    let ε' : MulAut (twistedE6RootGroup K σ) := (MulAut.conj τ) ε
    have hε'E : ε' ∈ E' := Subgroup.mem_map.2 ⟨ε, hε, rfl⟩
    have hkey : ∀ x : twistedE6RootGroup K σ, ε (τi x) = τi (ε' x) := by
      intro x
      have hεeq : ε * τ⁻¹ = τ⁻¹ * ε' := by
        show ε * τ⁻¹ = τ⁻¹ * (τ * ε * τ⁻¹)
        group
      have h := congrArg (fun f : MulAut (twistedE6RootGroup K σ) => f x) hεeq
      simpa [hτi, ε', MulAut.mul_apply] using h
    obtain ⟨m, hm1, hm2⟩ := hdec₀ ε' hε'E
    refine ⟨m, ?_, ?_⟩
    · intro i
      calc (ρ i).range.map ε.toMonoidHom
          = (((ρ₀ i).range).map τi.toMonoidHom).map ε.toMonoidHom := by rw [hρrange i]
        _ = ((ρ₀ i).range).map (ε.toMonoidHom.comp τi.toMonoidHom) := by rw [Subgroup.map_map]
        _ = ((ρ₀ i).range).map (τi.toMonoidHom.comp ε'.toMonoidHom) := by
              rw [show ε.toMonoidHom.comp τi.toMonoidHom =
                τi.toMonoidHom.comp ε'.toMonoidHom from by
                  apply MonoidHom.ext
                  exact hkey]
        _ = (((ρ₀ i).range).map ε'.toMonoidHom).map τi.toMonoidHom := by rw [Subgroup.map_map]
        _ = ((ρ₀ (i + m)).range).map τi.toMonoidHom := by rw [hm1 i]
        _ = (ρ (i + m)).range := (hρrange (i + m)).symm
    · intro hm0 i
      obtain ⟨a, ha, haction⟩ := hm2 hm0 i
      exact ⟨a, ha, fun x => by
        show ε (τi (ρ₀ i x)) = τi (ρ₀ i (a x))
        rw [hkey, haction x]⟩
  · intro c hc hcr
    have hcomm : Commute (τ c) (⟨h₀, hL.h₀_mem⟩ : twistedE6RootGroup K σ) := by
      have h := hc.map τ.toMonoidHom
      have h2 : Commute (τ c) (τ s) := h
      rwa [hτs] at h2
    obtain ⟨m, hm⟩ := hcr
    have hpow : ∃ m : ℕ, (τ c) ^ (ringChar K ^ m) = 1 := by
      refine ⟨m, ?_⟩
      rw [← map_pow, hm, map_one]
    have hlast := hlast₀ (τ c) hcomm hpow
    have hmem : c ∈ ((⨆ i, (ρ₀ i).range).map τi.toMonoidHom) := by
      refine Subgroup.mem_map.2 ⟨τ c, hlast, ?_⟩
      show τi (τ c) = c
      rw [hτi, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hmap : ((⨆ i, (ρ₀ i).range).map τi.toMonoidHom) = ⨆ i, (ρ i).range := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => (hρrange i).symm
    rwa [hmap] at hmem

end Frames

end CFSG.LieType.SeitzGeneration.CubeCoverTwE6


namespace CFSG.LieType.SeitzGeneration.CubeCoverTwE6

section Lift


theorem exists_lift_twLayer_le_seitzHyperGamma {G C : Type} [Group G] [Group C] [Finite G]
    {π : G →* C} {ℓ f : ℕ} {k : Type} [Field k] (h : UnitaryFieldData ℓ f k)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (ind : MulAut G →* MulAut C)
    (hind : ∀ (f : MulAut G) (g : G), π (f g) = ind f (π g))
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    {ρ₀ : Fin 3 → unitarySU ℓ f k 3 →* C}
    (hYq : CFSG.IsQuasisimple (unitarySU ℓ f k 3))
    (hρ₀ : ∀ i, Function.Injective (ρ₀ i))
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ₀ i s * ρ₀ j t = ρ₀ j t * ρ₀ i s)
    {σ : MulAut G} (hσ : σ ∈ E) (hσ1 : σ ≠ 1)
    (hσρ : ∀ i s, ind σ (ρ₀ i s) = ρ₀ i s)
    (hdec : ∀ ε ∈ E, ∃ m : Fin 3,
      (∀ i, (ρ₀ i).range.map (ind ε).toMonoidHom = (ρ₀ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ a ∈ (suConj h).range, ∀ s, ind ε (ρ₀ i s) = ρ₀ i (a s))) :
    ∃ ρ : Fin 3 → unitarySU ℓ f k 3 →* G,
      (∀ i, π.comp (ρ i) = ρ₀ i) ∧ ∀ i, (ρ i).range ≤ seitzHyperGamma 3 E := by
  have hM : TwLayerFacts (unitarySU ℓ f k 3) (suConj h).range :=
    twLayerFacts_of_stmts twFixedNonCentral_holds twToralPlane_holds twInnerHeisPlane_holds
      twOuterHeisPlane_holds h hq3 hq (shiftQs_exists_noncomm hYq)
      (fun N _ => shiftQs_normal_dichotomy hYq N)
  haveI : Group.IsPerfect (unitarySU ℓ f k 3) := hYq.1
  obtain ⟨ρ, hρ, hρinj, hρcomm, hfix, hdecρ⟩ :=
    exists_lift_frames (Y := unitarySU ℓ f k 3) (C := C) (π := π)
      (Group.IsPerfect.commutator_eq_top)
      (shiftQs_exists_noncomm hYq)
      (fun β => exists_lift_SU3 h hq hπ hker β) hker ind hind hρ₀ hcomm hdec
  refine ⟨ρ, hρ, fun i => ?_⟩
  exact layerStep_abs hM hE hcard hρinj hρcomm hσ hσ1 (hfix σ hσρ) hdecρ i

end Lift

section All24


theorem seitzHyperGamma_eq_top_of_twAll24Plane {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ} (hk3 : ringChar k ≠ 3)
    (hσ : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2) (h3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEd : coverImage θ E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ)
    {P : Subgroup (MulAut (twistedE6RootGroup k σ))} (hPE : P ≤ coverImage θ E)
    (hPI : P ≤ twistedE6Inn k σ)
    (hP24 : ∀ s : twistedE6RootGroup k σ, MulAut.conj s ∈ P → s ≠ 1 →
      twE6FixDim k σ s = 24)
    (hgen : Inputs2311c.UniPlaneGen (ringChar k) P) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  let π : K →* twistedE6RootGroup k σ :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let ind : MulAut K →* MulAut (twistedE6RootGroup k σ) :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)
  have hind : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g) := by
    intro f g
    simp [π, ind, MulAut.congr, quotientCenterAut']
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
      apply θ.injective
      simpa [π] using hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hPE' : P ≤ E.map ind := by
    dsimp only [ind]
    exact hPE
  let Q : Subgroup (MulAut K) := E ⊓ P.comap ind
  have hQmap : Q.map ind = P := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hPE' hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have key : ∀ (φ : MulAut K) (hφ : φ ∈ Q) (hφ1 : ind φ ≠ 1),
      ∃ L : Subgroup K, L ≤ seitzHyperGamma 3 E ∧
        ∀ c : twistedE6RootGroup k σ, ind φ c = c →
          (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) → c ∈ L.map π := by
    intro φ hφQ hφ1
    obtain ⟨hφE, hφP⟩ := Subgroup.mem_inf.1 hφQ
    have hφI : ind φ ∈ twistedE6Inn k σ := hPI hφP
    obtain ⟨s, hs⟩ := hφI
    have hs1 : s ≠ 1 := by
      intro h1
      exact hφ1 (by rw [← hs, h1, map_one])
    have hs24 : twE6FixDim k σ s = 24 :=
      hP24 s (by rw [hs]; exact hφP) hs1
    have hsE : MulAut.conj s ∈ coverImage θ E := by
      rw [hs]
      exact hPE' hφP
    obtain ⟨ℓ, f, h, ρ₀, hℓf, hYq, hinj, hcomm, hcent, hdec, hlast⟩ :=
      exists_twThreeA2_frames hk3 hσ hkq h3 hq2 (isElemAbelian_coverImage θ hE)
        (by rw [card_coverImage hperf θ E, hcard]) hEd hsE hs24
    have hφne : φ ≠ 1 := fun h1 => hφ1 (by rw [h1, map_one])
    have hcard27 : Nat.card E = 27 := by
      simpa using hcard
    have h3' : 3 ∣ ℓ ^ f + 1 := by rw [hℓf]; exact h3
    have hq2' : ℓ ^ f ≠ 2 := by rw [hℓf]; exact hq2
    obtain ⟨ρ, hρcomp, hρle⟩ :=
      exists_lift_twLayer_le_seitzHyperGamma (π := π) (E := E) (ρ₀ := ρ₀) (σ := φ)
        h h3' hq2' hπ hker ind hind hE hcard27 hYq hinj hcomm hφE hφne
        (fun i a => by rw [← hs]; exact hcent i a)
        (fun ε hεE => hdec (ind ε) ⟨ε, hεE, rfl⟩)
    refine ⟨⨆ i, (ρ i).range, ?_, ?_⟩
    · exact iSup_le hρle
    · intro c hfix hpow
      have hcs : Commute c s := by
        rw [commute_iff_eq]
        have h := hfix
        rw [show ind φ = MulAut.conj s from hs.symm, MulAut.conj_apply] at h
        calc c * s = (s * c * s⁻¹) * s := by rw [h]
          _ = s * c := by group
      have hmem : c ∈ ⨆ i, (ρ₀ i).range := hlast c hcs hpow
      have hmaple : (⨆ i, (ρ i).range).map π = ⨆ i, (ρ₀ i).range := by
        rw [Subgroup.map_iSup]
        exact iSup_congr fun i => by
          rw [← MonoidHom.range_comp π (ρ i), hρcomp i]
      rw [hmaple]
      exact hmem
  let Lfun : MulAut K → Subgroup K := fun φ =>
    if h : φ ∈ Q ∧ ind φ ≠ 1 then Classical.choose (key φ h.1 h.2) else ⊥
  have hL : ∀ φ ∈ Q, ind φ ≠ 1 → Lfun φ ≤ seitzHyperGamma 3 E := by
    intro φ hφ hφ1
    dsimp only [Lfun]
    rw [dif_pos ⟨hφ, hφ1⟩]
    exact (Classical.choose_spec (key φ hφ hφ1)).1
  have hr : ∀ φ ∈ Q, ind φ ≠ 1 → ∀ c : twistedE6RootGroup k σ, ind φ c = c →
      (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) → c ∈ (Lfun φ).map π := by
    intro φ hφ hφ1 c hfix hpow
    dsimp only [Lfun]
    rw [dif_pos ⟨hφ, hφ1⟩]
    exact (Classical.choose_spec (key φ hφ hφ1)).2 c hfix hpow
  refine seitzHyperGamma_eq_top_of_uniPlaneGen_layers (π := π)
    hperf hπ hker ind (p := 3) (r := ringChar k) (E := E) (P := Q) ?_ Lfun hL hr
  rw [hQmap]
  exact hgen

end All24

end CFSG.LieType.SeitzGeneration.CubeCoverTwE6


namespace CFSG.LieType.SeitzGeneration.CubeCoverTwE6

section Planes


theorem uniPlaneGen_twE6 {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hk3 : ringChar k ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2)
    (hqmod : q % 3 = 2) (hq2 : q ≠ 2)
    (P : Subgroup (MulAut (twistedE6RootGroup k σ))) (hP : IsElemAbelian 3 P)
    (hcard : Nat.card P = 3 ^ 2) (h8 : q = 8 → P ≤ twistedE6Inn k σ) :
    Inputs2311c.UniPlaneGen (ringChar k) P := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  rw [hkq] at h1
  have hq0 : q ≠ 0 := by rintro rfl; simpa using h1
  have hq1 : q ≠ 1 := by rintro rfl; norm_num at h1
  have hq2le : 2 ≤ q := by omega
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq k q hkq hq2le
  let qp : TauCeti.PrimePower := ⟨ringChar k, f, hp, hf⟩
  have hqp : qp.card = q := by
    rw [TauCeti.PrimePower.card_def]
    exact hqf.symm
  have hv : (TauCeti.LieTypeIndex.twistedE6 qp).Valid := TauCeti.LieTypeIndex.valid_twistedE6 qp
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedE6 qp, hv⟩
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_twistedE6_of_field
    qp hv k (hqp ▸ hkq) σ (hqp ▸ hσ)
  let P₀ : Subgroup (MulAut (Cat d)) := P.map (MulAut.congr e.symm).toMonoidHom
  have hP₀ : IsElemAbelian 3 P₀ := hP.map _
  have hcard₀ : Nat.card P₀ = 3 ^ 2 := by
    have h1 : Nat.card P₀ = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.congr e.symm).injective
    rw [h1, hcard]
  have hpd : 3 ≠ d.1.characteristic := by
    dsimp [d]
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
    exact fun h => hk3 h.symm
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
    dsimp [d]
    exact not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 qp)
  have hopen : QuasiHigh5E6Cover.TwE6ThreeOpenPlanes :=
    QuasiHigh5E6Cover.twE6ThreeOpenPlanes_of QuasiHigh5E6Cover.twE6ThreeOpenInner_holds
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5.twE6ThreeOpenDiag_holds
  have hqmod' : qp.card % 3 = 2 := by rw [hqp]; exact hqmod
  have hqne' : qp.card ≠ 2 := by rw [hqp]; exact hq2
  have h8' : qp.card = 8 → InnerPlane d 3 P₀ := by
    intro h8c
    have hq8 : q = 8 := by rw [← hqp]; exact h8c
    have hPin : P ≤ twistedE6Inn k σ := h8 hq8
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨s, rfl⟩ := hPin hp
    exact ⟨e.symm s, (mulAut_congr_conj e.symm s).symm⟩
  have hgen₀ : Inputs2311c.UniPlaneGen d.1.characteristic P₀ :=
    QuasiHigh5E6Cover.uniSeitzPlanes_twE6_three_two_of_open hopen d 3 Nat.prime_three
      (by norm_num) hpd hex P₀ hP₀ hcard₀ ⟨rfl, qp, rfl, hqmod', hqne', h8'⟩
  have hchar : d.1.characteristic = ringChar k := by
    dsimp [d]
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
  have hgen₁ : Inputs2311c.UniPlaneGen (ringChar k) P₀ := hchar ▸ hgen₀
  have hmapP : P₀.map (MulAut.congr e).toMonoidHom = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hy
      have h1 : (MulAut.congr e).toMonoidHom
          ((MulAut.congr e.symm).toMonoidHom p) = p := by
        ext z
        simp [MulAut.congr_apply]
      rw [h1]
      exact hp
    · intro hx
      refine ⟨MulAut.congr e.symm x, Subgroup.mem_map_of_mem _ hx, ?_⟩
      ext z
      simp [MulAut.congr_apply]
  rw [← hmapP]
  exact (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.uniPlaneGen_map_congr
    e (ringChar k) P₀).2 hgen₁


theorem seitzHyperGamma_eq_top_twE6_diag_all24 {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hk3 : ringChar k ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2)
    (hqmod : q % 3 = 2) (hq2 : q ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEd : coverImage θ E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ)
    (hEi : ¬ coverImage θ E ≤ twistedE6Inn k σ)
    (hA : TwE6InnerAll24 k σ (coverImage θ E)) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  have h3 : 3 ∣ q + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  let P : Subgroup (MulAut (twistedE6RootGroup k σ)) :=
    coverImage θ E ⊓ twistedE6Inn k σ
  have hPE : P ≤ coverImage θ E := inf_le_left
  have hPI : P ≤ twistedE6Inn k σ := inf_le_right
  have hcardE : Nat.card (coverImage θ E) = 3 ^ 3 := by
    rw [card_coverImage hperf θ E, hcard]
  have hPcard : Nat.card P = 3 ^ 2 := by
    dsimp only [P]
    exact card_inf_twistedE6Inn hkq σ hσ hcardE hEd hEi
  have hPab : IsElemAbelian 3 P := (isElemAbelian_coverImage θ hE).mono hPE
  have hP24 : ∀ s : twistedE6RootGroup k σ, MulAut.conj s ∈ P → s ≠ 1 →
      twE6FixDim k σ s = 24 := fun s hs hs1 => hA s (hPE hs) hs1
  have hgen : Inputs2311c.UniPlaneGen (ringChar k) P :=
    uniPlaneGen_twE6 hk3 hσ hkq hqmod hq2 P hPab hPcard (fun _ => hPI)
  exact seitzHyperGamma_eq_top_of_twAll24Plane hperf hk3 hσ hkq h3 hq2 θ hE hcard hEd hPE hPI
    hP24 hgen

theorem seitzHyperGamma_eq_top_twE6_inner_of_plane {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hk3 : ringChar k ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2)
    (hqmod : q % 3 = 2) (hq2 : q ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEi : E ≤ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (MulAut (twistedE6RootGroup k σ))} (hPcard : Nat.card P = 3 ^ 2)
    (hPE : P ≤ coverImage θ E)
    (hP24 : ∀ s : twistedE6RootGroup k σ, MulAut.conj s ∈ P → s ≠ 1 →
      twE6FixDim k σ s = 24) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  have h3 : 3 ∣ q + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hInn : coverImage θ E ≤ twistedE6Inn k σ := by
    have h := coverImage_le_range_conj θ hEi
    simpa [twistedE6Inn, CFSG.ComponentClassification.OuterAutomorphisms.inner] using h
  have hEd : coverImage θ E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ :=
    hInn.trans le_sup_left
  have hPI : P ≤ twistedE6Inn k σ := hPE.trans hInn
  have hPab : IsElemAbelian 3 P := (isElemAbelian_coverImage θ hE).mono hPE
  have hgen : Inputs2311c.UniPlaneGen (ringChar k) P :=
    uniPlaneGen_twE6 hk3 hσ hkq hqmod hq2 P hPab hPcard (fun _ => hPI)
  exact seitzHyperGamma_eq_top_of_twAll24Plane hperf hk3 hσ hkq h3 hq2 θ hE hcard hEd hPE hPI
    hP24 hgen

theorem seitzHyperGamma_eq_top_twE6_inner_of_all24 {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hk3 : ringChar k ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2)
    (hqmod : q % 3 = 2) (hq2 : q ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEi : E ≤ (MulAut.conj : K →* MulAut K).range)
    {E₀ : Subgroup (twistedE6RootGroup k σ)}
    (hE₀ : E₀ = (coverImage θ E).comap
      (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)))
    (hAll : TwE6All24PlaneIn k σ E₀) :
    seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨P₀, hP₀le, hP₀card, hP₀24⟩ := hAll
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)) :=
    mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 k σ)
  let P : Subgroup (MulAut (twistedE6RootGroup k σ)) :=
    P₀.map (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ))
  have hPcard : Nat.card P = 3 ^ 2 := by
    dsimp only [P]
    rw [Subgroup.card_map_of_injective hinj, hP₀card]
  have hPE : P ≤ coverImage θ E := by
    rintro _ ⟨s, hs, rfl⟩
    have hsE : s ∈ E₀ := hP₀le hs
    rw [hE₀] at hsE
    exact Subgroup.mem_comap.1 hsE
  have hP24 : ∀ s : twistedE6RootGroup k σ, MulAut.conj s ∈ P → s ≠ 1 →
      twE6FixDim k σ s = 24 := by
    rintro s ⟨s₀, hs₀, hconj⟩ hs1
    have hs_eq : s₀ = s := hinj hconj
    have hs0 : s₀ ≠ 1 := by rwa [← hs_eq] at hs1
    rw [← hs_eq]
    exact hP₀24 s₀ hs₀ hs0
  exact seitzHyperGamma_eq_top_twE6_inner_of_plane hperf hk3 hσ hkq hqmod hq2 θ hE hcard
    hEi hPcard hPE hP24

end Planes

end CFSG.LieType.SeitzGeneration.CubeCoverTwE6

end
