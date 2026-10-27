module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiCover
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSSimple
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Facts
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiPGroup
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmL2p2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.KFacts.KS10L27
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

namespace L6LeavesKF64ii

theorem normalizer_le_of_rank_two {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {H Q M₀ : Subgroup A} {x z : A} (hBc : Nat.card ↥(zpowers x ⊔ zpowers z) = p ^ 2)
    (hΩ : ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z)
    (hwc : ∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z)
    (hNz : normalizer (zpowers z : Set A) ⊓ H ≤ M₀) {T : Subgroup A} (hTQ : T ≤ Q)
    (hT : 2 ≤ Open.pRank p T) : normalizer (T : Set A) ⊓ H ≤ M₀ := by
  obtain ⟨E, hET, hE, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp hT
  have hEB : E ≤ zpowers x ⊔ zpowers z := fun e he =>
    hΩ e (hTQ (hET he)) ((SU1.isElemAbelian_iff.mp hE).2 e he)
  have hEeq : E = zpowers x ⊔ zpowers z :=
    Subgroup.eq_of_le_of_card_ge hEB (by rw [hEc, hBc])
  have hBT : zpowers x ⊔ zpowers z ≤ T := hEeq ▸ hET
  intro g hg
  have hzB : z ∈ zpowers x ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hgz : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z := by
    refine hΩ _ (hTQ ((mem_normalizer_iff.mp hg.1 z).mp (hBT hzB))) ?_
    rw [conj_pow]
    have : z ^ p = 1 := (SU1.isElemAbelian_iff.mp (hEeq ▸ hE)).2 z hzB
    rw [this]
    simp
  have hgN : g ∈ normalizer ((zpowers z : Subgroup A) : Set A) := by
    refine L6LeavesNS.mem_normalizer_of_map_conj_le ?_
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr (hwc g hg.2 hgz)
  exact hNz ⟨hgN, hg.2⟩

theorem not_hasNormalPComplement_of_simple {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsSimpleGroup K) (hna : ∃ a b : K, a * b ≠ b * a)
    (hdvd : p ∣ Nat.card K) : ¬ CFSG.HasNormalPComplement p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨N, hN, hcop, hQ⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hinj : Function.Injective (QuotientGroup.mk' N) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have := (QuotientGroup.eq_one_iff a).mp ha
      rw [hbot] at this
      simpa using this
    have hKp : IsPGroup p K := hQ.of_injective (QuotientGroup.mk' N) hinj
    haveI : Nontrivial K := IsSimpleGroup.toNontrivial
    haveI := hKp.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hc | hc
    · obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center K))
      apply hc1
      apply Subtype.ext
      have : (c : K) ∈ (⊥ : Subgroup K) := hc ▸ c.2
      simpa using this
    · obtain ⟨a, b, hab⟩ := hna
      apply hab
      have : a ∈ Subgroup.center K := hc ▸ mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  · rw [htop, Subgroup.card_top] at hcop
    exact hp.one_lt.ne (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hdvd).symm

theorem centralizer_singleton_eq_zpowers {G : Type*} [Group G] (w : G) :
    centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

end L6LeavesKF64ii

theorem kFact64ii_coreNorm (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121) :
    ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (H Q M₀ : Subgroup A) (x z : A),
      p.Prime → 3 ≤ p → CFSG.Open.IsKGroup ↥H → orderOf x = p → orderOf z = p →
      x * z = z * x → x ∉ zpowers z → CFSG.ABGLocalTools.IsSylowOf p Q H →
      zpowers x ⊔ zpowers z ≤ Q →
      (∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) → x ∉ (frattini ↥Q).map Q.subtype →
      (∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z) →
      Q ≤ M₀ → M₀ ≤ H → normalizer (zpowers z : Set A) ⊓ H ≤ M₀ →
      ¬ H ≤ M₀ ⊔ rankThreePrimeCore p H →
      (∃ L : Subgroup A, S622IsSimpleSection L (rankThreePrimeCore p H) ∧ L ≤ H ∧ z ∈ L ∧
        CFSG.Open.pRank p L ≤ 1 ∧ ¬ L ≤ (M₀ ⊓ L) ⊔ rankThreePrimeCore p H ∧
        M₀ ≤ normalizer (L : Set A) ∧ H ≤ normalizer (L : Set A)) ∧
      (KFact64iiOuterNPC → ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
        ¬ CFSG.HasNormalPComplement p ↥(H ⊓ centralizer ({b} : Set A))) := by
  intro A _ _ p H Q M₀ x z hp hp3 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQH : Q ≤ H := hQsyl.le
  have hQp : IsPGroup p Q := hQsyl.isPGroup
  have hxp : x ^ p = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one x
  have hzp : z ^ p = 1 := by
    rw [← hzo]
    exact pow_orderOf_eq_one z
  have hx1 : x ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  have hznx : z ∉ zpowers x := by
    intro hz
    apply hxnz
    have heq : zpowers z = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hzo])
    rw [heq]
    exact mem_zpowers x
  set B : Subgroup A := zpowers x ⊔ zpowers z with hB
  have hcommxz : ∀ a ∈ zpowers x, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute x z from hxz) i j).eq
  have hBc : Nat.card B = p ^ 2 := by
    rw [hB, CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers x) hzp hznx
      (fun e he => hcommxz e he z (mem_zpowers z)), Nat.card_zpowers, hxo, pow_two]
  have hxB : x ∈ B := mem_sup_left (mem_zpowers x)
  have hzB : z ∈ B := mem_sup_right (mem_zpowers z)
  have hxQ : x ∈ Q := hBQ hxB
  have hzQ : z ∈ Q := hBQ hzB
  have hxH : x ∈ H := hQH hxQ
  have hzH : z ∈ H := hQH hzQ
  set O : Subgroup ↥H := primeComplementCore (G := ↥H) p with hO
  have hOc : Nat.Coprime p (Nat.card O) := XBar.coprime p H
  set π : ↥H →* XBar p H := XBar.mk p H with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set x' : ↥H := ⟨x, hxH⟩ with hx'
  set z' : ↥H := ⟨z, hzH⟩ with hz'
  have hQ'p : IsPGroup p (Q.subgroupOf H) := hQp.comap_subtype
  have hQs : ¬ p ∣ (Q.subgroupOf H).index := ((CFSG.ABGLocalTools.isSylowOf_iff).1 hQsyl).2.2
  obtain ⟨Qb, hQb⟩ := XBar.exists_sylow hQ'p hQs
  have hinj : Set.InjOn π (Q.subgroupOf H) := injOn_mk_of_isPGroup hp O hOc hQ'p
  have hxQ' : x' ∈ Q.subgroupOf H := hxQ
  have hzQ' : z' ∈ Q.subgroupOf H := hzQ
  have hx'o : orderOf x' = p := by rw [Subgroup.orderOf_mk, hxo]
  have hz'o : orderOf z' = p := by rw [Subgroup.orderOf_mk, hzo]
  have hπx1 : π x' ≠ 1 := (XBar.element hp hQp hQH hBQ hxB hx1).2
  have hπz1 : π z' ≠ 1 := (XBar.element hp hQp hQH hBQ hzB hz1).2
  have hx'p : x' ^ p = 1 := by
    have := pow_orderOf_eq_one x'
    rwa [hx'o] at this
  have hz'p : z' ^ p = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'o] at this
  have hπxp : (π x') ^ p = 1 := by rw [← map_pow, hx'p, map_one]
  have hπzp : (π z') ^ p = 1 := by rw [← map_pow, hz'p, map_one]
  have hB'map : (zpowers x' ⊔ zpowers z').map H.subtype = B := by
    rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hmap : (zpowers x' ⊔ zpowers z').map π = zpowers (π x') ⊔ zpowers (π z') := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  set Y : Subgroup A := M₀ ⊔ rankThreePrimeCore p H with hY
  have hMY : M₀ ≤ Y := le_sup_left
  have hDY : rankThreePrimeCore p H ≤ Y := le_sup_right
  set Mb : Subgroup (XBar p H) := (Y.subgroupOf H).map π with hMb
  have hSM : (Qb : Subgroup (XBar p H)) ≤ Mb := by
    rw [hQb]
    exact Subgroup.map_mono fun q hq => hMY (hQM hq)
  have hΓ2' : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ H ≤ Y :=
    fun S hS hk => (L6LeavesKF64ii.normalizer_le_of_rank_two hp hBc hΩ hwc hNz hS hk).trans hMY
  have hΓ2Z : ∀ T : Subgroup (XBar p H), T ≤ (Qb : Subgroup (XBar p H)) → 2 ≤ Open.pRank p T →
      normalizer (T : Set (XBar p H)) ≤ Mb := by
    intro T hT hk
    exact XBar.gamma2 hp hQ'p hΓ2' (by rw [← hQb]; exact hT) hk
  have hπzpow : (zpowers z').map π = zpowers (π z') := MonoidHom.map_zpowers π z'
  have hNzZ : normalizer ((zpowers (π z') : Subgroup (XBar p H)) : Set (XBar p H)) ≤ Mb := by
    have hRp : IsPGroup p (zpowers z') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'o, pow_one])
    have hmapz : (zpowers z').map H.subtype = zpowers z := by
      rw [MonoidHom.map_zpowers]
      rfl
    refine normalizer_le_map_of_gamma hp O hOc hRp (Y' := Y.subgroupOf H) (k := 1) ?_
      (le_of_eq hπzpow.symm) (P64Free.one_le_pRank_zpowers hp hπzp hπz1)
    intro S hSR hk
    obtain ⟨E, hES, hEl, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp hk
    have hEeq : E = zpowers z' := Subgroup.eq_of_le_of_card_ge (hES.trans hSR)
      (by rw [hEc, Nat.card_zpowers, hz'o, pow_one])
    have hSeq : S = zpowers z' := le_antisymm hSR (hEeq ▸ hES)
    rw [hSeq]
    refine normalizer_subgroupOf_le (zpowers z') ?_
    rw [hmapz]
    exact fun g hg => hMY (hNz hg)
  have hB'p : IsPGroup p ↥(zpowers x' ⊔ zpowers z') :=
    hQ'p.to_le (sup_le (zpowers_le.mpr hxQ') (zpowers_le.mpr hzQ'))
  have hB'c : Nat.card ↥(zpowers x' ⊔ zpowers z') = p ^ 2 := by
    rw [← hBc, ← hB'map]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hBel : IsElemAbelian p B :=
    SU1.IsElemAbelian.sup (SU1.isElemAbelian_zpowers hxp) (SU1.isElemAbelian_zpowers hzp)
      hcommxz
  have hπxz : π x' * π z' = π z' * π x' := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hxz)
  have hbarcomm : ∀ a ∈ zpowers (π x'), ∀ b ∈ zpowers (π z'), a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute (π x') (π z') from hπxz) i j).eq
  have hbarel : IsElemAbelian p (zpowers (π x') ⊔ zpowers (π z')) :=
    SU1.IsElemAbelian.sup (SU1.isElemAbelian_zpowers hπxp) (SU1.isElemAbelian_zpowers hπzp)
      hbarcomm
  have hbarcard : Nat.card ↥(zpowers (π x') ⊔ zpowers (π z')) = p ^ 2 := by
    rw [← hmap, CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp _ hOc hB'p, hB'c]
  have hNBZ : normalizer ((zpowers (π x') ⊔ zpowers (π z') : Subgroup (XBar p H)) :
      Set (XBar p H)) ≤
      normalizer ((zpowers (π z') : Subgroup (XBar p H)) : Set (XBar p H)) := by
    have hk2 : 2 ≤ Open.pRank p (zpowers (π x') ⊔ zpowers (π z')) :=
      SU1.le_pRank hp.one_lt le_rfl hbarel hbarcard
    have h1 := normalizer_le_map_of_gamma hp O hOc hB'p
      (Y' := normalizer ((zpowers z' : Subgroup ↥H) : Set ↥H)) (k := 2) ?_
      (le_of_eq hmap.symm) hk2
    · intro g hg
      obtain ⟨n, hn, rfl⟩ := h1 hg
      have h2 : π n ∈ normalizer (((zpowers z').map π : Subgroup (XBar p H)) :
          Set (XBar p H)) := Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hn)
      rwa [hπzpow] at h2
    · intro S hSR hk
      obtain ⟨E, hES, hEl, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp hk
      have hEeq : E = zpowers x' ⊔ zpowers z' :=
        Subgroup.eq_of_le_of_card_ge (hES.trans hSR) (by rw [hEc, hB'c])
      have hSeq : S = zpowers x' ⊔ zpowers z' := le_antisymm hSR (hEeq ▸ hES)
      rw [hSeq]
      intro g hg
      refine L6LeavesNS.mem_normalizer_of_map_conj_le ?_
      rw [MonoidHom.map_zpowers]
      refine zpowers_le.mpr ?_
      have hgz : g * z' * g⁻¹ ∈ zpowers x' ⊔ zpowers z' :=
        (mem_normalizer_iff.mp hg z').mp (mem_sup_right (mem_zpowers z'))
      have hA : (g : A) * z * (g : A)⁻¹ ∈ B := by
        rw [← hB'map]
        exact ⟨_, hgz, rfl⟩
      obtain ⟨k, hk'⟩ := mem_zpowers_iff.mp (hwc (g : A) g.2 hA)
      exact mem_zpowers_iff.mpr ⟨k, Subtype.ext hk'⟩
  have hMtop : ¬ ⊤ ≤ Mb := XBar.not_top_le hDY hnc
  have hmetaQ : CFSG.IsMetacyclic ↥Q :=
    L6LeavesKF64ii.isMetacyclic_of_omega_not_mem_frattini hp hp2 hQp hBQ hBc hΩ hxB hxfr
  have hmetaQb : CFSG.IsMetacyclic ↥(Qb : Subgroup (XBar p H)) := by
    rw [hQb]
    have e1 : ↥Q ≃* ↥(Q.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hQH).symm
    have e2 : ↥(Q.subgroupOf H) ≃* ↥((Q.subgroupOf H).map π) :=
      MulEquiv.ofBijective (π.subgroupMap (Q.subgroupOf H))
        ⟨fun a b hab => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab)),
          π.subgroupMap_surjective _⟩
    exact CFSG.Walter.Huppert.isMetacyclic_of_mulEquiv (e1.trans e2) hmetaQ
  have hCtx : L6LeavesKF64ii.Ctx p Qb (π x') (π z') Mb :=
    { prime := hp
      three_le := hp3
      catalog := (CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mpr hKH).quotient _
      core := primeComplementCore_quotient_eq_bot p
      x_order := orderOf_eq_prime hπxp hπx1
      z_order := orderOf_eq_prime hπzp hπz1
      commute := hπxz
      x_not_mem := by
        intro hmem
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
        rw [← map_zpow] at hk
        have hz'k : z' ^ k ∈ Q.subgroupOf H := Subgroup.zpow_mem _ hzQ' k
        have := hinj hz'k hxQ' hk
        apply hxnz
        exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val this⟩
      x_mem := by
        rw [hQb]
        exact ⟨x', hxQ', rfl⟩
      z_mem := by
        rw [hQb]
        exact ⟨z', hzQ', rfl⟩
      omega := by
        intro q hq hqp
        rw [hQb] at hq
        obtain ⟨q₀, hq₀, rfl⟩ := hq
        have hq₀p : q₀ ^ p = 1 :=
          hinj (Subgroup.pow_mem _ hq₀ p) (one_mem _) (by rw [map_pow, hqp, map_one])
        have hq₀A : (q₀ : A) ^ p = 1 := by simpa using congrArg Subtype.val hq₀p
        have hq₀B : (q₀ : A) ∈ B := hΩ _ hq₀ hq₀A
        have hq₀' : q₀ ∈ zpowers x' ⊔ zpowers z' := by
          rw [← hB'map] at hq₀B
          obtain ⟨w, hw, hwq⟩ := hq₀B
          exact (Subtype.ext hwq : w = q₀) ▸ hw
        have := Subgroup.mem_map_of_mem π hq₀'
        rwa [hmap] at this
      metacyclic := hmetaQb
      S_le := hSM
      gamma := hΓ2Z
      Nz := hNzZ
      NB := hNBZ
      not_top := hMtop }
  obtain ⟨K, hKc, hKs, hKn, hzK, hKr, hKM, hMK, b, hbB, hbz, hbcases⟩ :=
    hCtx.exists_component hOuter hI121
  have hKtop : ⊤ ≤ normalizer (K : Set (XBar p H)) := hCtx.top_le_normalizer_component hKc hMK
  refine ⟨?_, fun hNPC => ?_⟩
  ·
    set K' : Subgroup ↥H := K.comap π with hK'
    have hz'K' : z' ∈ K' := hzK
    have hL : (K'.map H.subtype).subgroupOf H = K' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K'
    refine ⟨K'.map H.subtype, ?_, Subgroup.map_subtype_le K', ⟨z', hz'K', rfl⟩, ?_, ?_, ?_, ?_⟩
    · have hsec : S622IsSimpleSection K' π.ker :=
        L6LeavesNS.s622IsSimpleSection_comap π hπsurj hKs hKn
      have hsec' := L6LeavesNS.s622IsSimpleSection_map H.subtype H.subtype_injective hsec
      have hker : π.ker = O := QuotientGroup.ker_mk' O
      rw [hker] at hsec'
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore]
      exact hsec'
    · rw [pRank_map_subtype hp.one_lt]
      exact L6LeavesNS.pRank_comap_le_one hp O hOc hKr
    · intro hle
      apply hKM
      intro k hk
      obtain ⟨l, rfl⟩ := hπsurj k
      have hlK' : l ∈ K' := hk
      have hlL : (l : A) ∈ K'.map H.subtype := ⟨l, hlK', rfl⟩
      have hle2 : (M₀ ⊓ K'.map H.subtype) ⊔ rankThreePrimeCore p H ≤ Y :=
        sup_le_sup_right inf_le_left _
      have hlY : (l : A) ∈ Y := hle2 (hle hlL)
      exact ⟨l, hlY, rfl⟩
    · intro m hm
      have hm' : (⟨m, hM₀H hm⟩ : ↥H) ∈ Y.subgroupOf H := hMY hm
      have h1 : π ⟨m, hM₀H hm⟩ ∈ Mb := ⟨_, hm', rfl⟩
      have h2 := L6LeavesNS.mem_normalizer_comap π (hMK h1)
      have h3 : (⟨m, hM₀H hm⟩ : ↥H) ∈
          normalizer (((K'.map H.subtype).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
        rw [hL]
        exact h2
      exact P64Free.mem_normalizer_of_mem_normalizer_subgroupOf (Subgroup.map_subtype_le K') h3
    ·
      intro m hm
      have h2 := L6LeavesNS.mem_normalizer_comap π (hKtop (mem_top (π ⟨m, hm⟩)))
      have h3 : (⟨m, hm⟩ : ↥H) ∈
          normalizer (((K'.map H.subtype).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
        rw [hL]
        exact h2
      exact P64Free.mem_normalizer_of_mem_normalizer_subgroupOf (Subgroup.map_subtype_le K') h3
  ·
    have hb' : b ∈ (zpowers x' ⊔ zpowers z').map π := by
      rw [hmap]
      exact hbB
    obtain ⟨b', hb'B, rfl⟩ := hb'
    have hb'1 : b' ≠ 1 := by
      intro h1
      apply hbz
      rw [h1, map_one]
      exact one_mem _
    have hb'p : b' ^ p = 1 := by
      have hbBA : (b' : A) ∈ B := by
        rw [← hB'map]
        exact ⟨b', hb'B, rfl⟩
      exact Subtype.ext (by simpa using hBel.2 _ hbBA)
    have hb'o : orderOf b' = p := orderOf_eq_prime hb'p hb'1
    refine ⟨(b' : A), ?_, ?_, ?_⟩
    · rw [← hB'map]
      exact ⟨b', hb'B, rfl⟩
    · intro hmem
      apply hbz
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      have : b' = z' ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [this, map_zpow]
      exact zpow_mem (mem_zpowers _) k
    · intro hhas
      set C' : Subgroup ↥H := centralizer ({b'} : Set ↥H) with hC'
      have hCmap : C'.map H.subtype = H ⊓ centralizer ({(b' : A)} : Set A) := by
        ext g
        constructor
        · rintro ⟨c, hc, rfl⟩
          refine ⟨c.2, ?_⟩
          have hc' : c * b' = b' * c :=
            Subgroup.mem_centralizer_singleton_iff.mp (show c ∈ centralizer ({b'} : Set ↥H) from hc)
          exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc')
        · rintro ⟨hgH, hgc⟩
          have hgc' : g * (b' : A) = (b' : A) * g := Subgroup.mem_centralizer_singleton_iff.mp
            (show g ∈ centralizer ({(b' : A)} : Set A) from hgc)
          refine ⟨⟨g, hgH⟩, ?_, rfl⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hgc')
      rw [← hCmap] at hhas
      have hC'npc : CFSG.HasNormalPComplement p ↥C' :=
        CFSG.hasNormalPComplement_of_map_subtype p H C' hhas
      have hCπ : CFSG.HasNormalPComplement p ↥(C'.map π) :=
        CFSG.RankThree.Coprime.hasNormalPComplement_map π hC'npc
      haveI hTp : Fact (IsPGroup p ↥(zpowers b')) :=
        ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb'o, pow_one])⟩
      have hcent : centralizer (((zpowers b').map π : Subgroup (XBar p H)) : Set (XBar p H)) =
          (centralizer ((zpowers b' : Subgroup ↥H) : Set ↥H)).map π :=
        CFSG.centralizer_map_quotient_eq_map_centralizer p (zpowers b') O inferInstance hOc
      have hcz : centralizer ({π b'} : Set (XBar p H)) = C'.map π := by
        rw [L6LeavesKF64ii.centralizer_singleton_eq_zpowers, ← MonoidHom.map_zpowers π b',
          hcent, hC', L6LeavesKF64ii.centralizer_singleton_eq_zpowers]
      have hKC : K ⊓ centralizer ({π b'} : Set (XBar p H)) ≤ C'.map π :=
        inf_le_right.trans hcz.le
      have hKnpc : CFSG.HasNormalPComplement p ↥(K ⊓ centralizer ({π b'} : Set (XBar p H))) :=
        CFSG.hasNormalPComplement_of_le p hKC hCπ
      have hdvd : p ∣ Nat.card K := P64Asm.dvd_card_of_isComponentOf hp hCtx.core hKc
      rcases hbcases with hbc | ⟨hy, hord, hout⟩
      · have hKle : K ≤ centralizer ({π b'} : Set (XBar p H)) := fun g hg =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hbc g hg).symm
        rw [inf_eq_left.mpr hKle] at hKnpc
        exact L6LeavesKF64ii.not_hasNormalPComplement_of_simple hp hKs hKn hdvd hKnpc
      · have hcatK := hCtx.isCatalog_component hKc
        have hrank := hCtx.pRank_top_component hI121 hKc
        have hnpc := hNPC p hp hp3 ↥K hKs hKn hcatK hrank _ hord hout
        apply hnpc
        have hF : Subgroup.closure {g : ↥K | (L6LeavesKF64ii.conjAut K (π b') hy) g = g} =
            (K ⊓ centralizer ({π b'} : Set (XBar p H))).subgroupOf K := by
          refine le_antisymm ((Subgroup.closure_le _).mpr fun g hg => ?_) (fun g hg => ?_)
          · have hg' : (L6LeavesKF64ii.conjAut K (π b') hy) g = g := hg
            have h1 := congrArg Subtype.val hg'
            rw [L6LeavesKF64ii.conjAut_apply] at h1
            show (g : XBar p H) ∈ K ⊓ centralizer ({π b'} : Set (XBar p H))
            refine ⟨g.2, ?_⟩
            exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1).symm
          · apply Subgroup.subset_closure
            show (L6LeavesKF64ii.conjAut K (π b') hy) g = g
            refine Subtype.ext ?_
            rw [L6LeavesKF64ii.conjAut_apply]
            have hg' : (g : XBar p H) ∈ K ⊓ centralizer ({π b'} : Set (XBar p H)) :=
              Subgroup.mem_subgroupOf.mp hg
            have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg'.2
            exact mul_inv_eq_iff_eq_mul.mpr h1.symm
        rw [hF]
        refine CFSG.hasNormalPComplement_of_map_subtype p K _ ?_
        rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        exact hKnpc

theorem kFact64ii_core (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121) :
    ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (H Q M₀ : Subgroup A) (x z : A),
      p.Prime → 3 ≤ p → CFSG.Open.IsKGroup ↥H → orderOf x = p → orderOf z = p →
      x * z = z * x → x ∉ zpowers z → CFSG.ABGLocalTools.IsSylowOf p Q H →
      zpowers x ⊔ zpowers z ≤ Q →
      (∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) → x ∉ (frattini ↥Q).map Q.subtype →
      (∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z) →
      Q ≤ M₀ → M₀ ≤ H → normalizer (zpowers z : Set A) ⊓ H ≤ M₀ →
      ¬ H ≤ M₀ ⊔ rankThreePrimeCore p H →
      (∃ L : Subgroup A, S622IsSimpleSection L (rankThreePrimeCore p H) ∧ L ≤ H ∧ z ∈ L ∧
        CFSG.Open.pRank p L ≤ 1 ∧ ¬ L ≤ (M₀ ⊓ L) ⊔ rankThreePrimeCore p H ∧
        M₀ ≤ normalizer (L : Set A)) ∧
      (KFact64iiOuterNPC → ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
        ¬ CFSG.HasNormalPComplement p ↥(H ⊓ centralizer ({b} : Set A))) := by
  intro A _ _ p H Q M₀ x z hp hp3 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  obtain ⟨⟨L, hL, hLH, hzL, hrk, hnc', hM₀L, -⟩, hb⟩ := kFact64ii_coreNorm hOuter hI121 A p H Q
    M₀ x z hp hp3 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  exact ⟨⟨L, hL, hLH, hzL, hrk, hnc', hM₀L⟩, hb⟩

theorem kFact64iiLNorm_of_inputs (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121) :
    ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (H Q M₀ : Subgroup A) (x z : A),
      p.Prime → 3 ≤ p → CFSG.Open.IsKGroup ↥H → orderOf x = p → orderOf z = p →
      x * z = z * x → x ∉ zpowers z → CFSG.ABGLocalTools.IsSylowOf p Q H →
      zpowers x ⊔ zpowers z ≤ Q →
      (∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) → x ∉ (frattini ↥Q).map Q.subtype →
      (∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z) →
      Q ≤ M₀ → M₀ ≤ H → normalizer (zpowers z : Set A) ⊓ H ≤ M₀ →
      ¬ H ≤ M₀ ⊔ rankThreePrimeCore p H →
      ∃ L : Subgroup A, S622IsSimpleSection L (rankThreePrimeCore p H) ∧ L ≤ H ∧ z ∈ L ∧
        CFSG.Open.pRank p L ≤ 1 ∧ ¬ L ≤ (M₀ ⊓ L) ⊔ rankThreePrimeCore p H ∧
        M₀ ≤ normalizer (L : Set A) ∧ H ≤ normalizer (L : Set A) := by
  intro A _ _ p H Q M₀ x z hp hp3 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  exact (kFact64ii_coreNorm hOuter hI121 A p H Q M₀ x z hp hp3 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ
    hxfr hwc hQM hM₀H hNz hnc).1

theorem kFact64iiL_of_inputs (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121) :
    KFact64iiL := by
  intro A _ _ p H Q M₀ x z hp hp5 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  exact (kFact64ii_core hOuter hI121 A p H Q M₀ x z hp (by omega) hKH hxo hzo hxz hxnz hQsyl hBQ
    hΩ hxfr hwc hQM hM₀H hNz hnc).1

theorem kFact64iiNPC_of_inputs (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121)
    (hNPC : KFact64iiOuterNPC) : KFact64iiNPC := by
  intro A _ _ p H Q M₀ x z hp hp5 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  exact (kFact64ii_core hOuter hI121 A p H Q M₀ x z hp (by omega) hKH hxo hzo hxz hxnz hQsyl hBQ
    hΩ hxfr hwc hQM hM₀H hNz hnc).2 hNPC

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
