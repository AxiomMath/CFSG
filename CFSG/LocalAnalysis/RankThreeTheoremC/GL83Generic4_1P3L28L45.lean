module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Basics
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28L45b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28L45c
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L45d
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def L28OuterOn (J : Subgroup G) (w : G) : Prop :=
  ¬ ∃ j ∈ J, ∀ j' ∈ J, (w * j' * w⁻¹)⁻¹ * (j * j' * j⁻¹) ∈ rankThreePrimeCore 3 J

theorem l28l45_exists_within_not_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK2 : KFactL28FieldSignalizer) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL28Normal M x J) (hxJ : x ∉ J) {U : Subgroup G} (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) {w : G}
    (hwU : w ∈ U) (hwx : w ∉ zpowers x) (hout : L28OuterOn J w) :
    ∃ A : Subgroup G, invariantTwoMaximalWithin U J A ∧ ¬ A ≤ M := by
  by_contra hno
  push Not at hno
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, hsyl, hrk⟩ := hgen
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hall : ∀ S : Subgroup G, S ≤ J → IsPGroup 2 S → U ≤ normalizer (S : Set G) → S ≤ M := by
    intro S hSJ hS2 hUS
    obtain ⟨S₁, hSS₁, hS₁⟩ := exists_invariantTwoMaximalWithin_containing U J S hSJ hS2 hUS
    exact hSS₁.trans (hno S₁ hS₁)
  have hJC : J ≤ centralizer ({x} : Set G) := hJ.le_centralizer
  have hxJc : ∀ j ∈ J, x * j = j * x := fun j hj =>
    (mem_centralizer_singleton_iff.mp (hJC hj)).symm
  have hUN : U ≤ normalizer (J : Set G) := fun g hg =>
    hJ.centralizer_le (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hU.1.is_comm.comm ⟨g, hg⟩ ⟨x, hxU⟩)))
  have hwN : w ∈ normalizer (J : Set G) := hUN hwU
  have hwNO : w ∈ normalizer (rankThreePrimeCore 3 J : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.primeCore_normalizer_normalizes 3 hprime J hwN
  have hwP : w ∈ (P : Subgroup G) := hUP hwU
  have hw3 : w ^ 3 = 1 := hU.2 w hwU
  have hUxw : U = zpowers x ⊔ zpowers w := by
    have hxw : x * w = w * x := congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hxU⟩ ⟨w, hwU⟩)
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime (zpowers x) hw3 hwx
      (fun e he => by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp he
        exact (Commute.zpow_left (hxw : Commute x w) m).eq)
    rw [Nat.card_zpowers, hxo] at hcard
    exact (Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hxU) (zpowers_le.mpr hwU))
      (by rw [hUc, hcard]; norm_num)).symm
  obtain ⟨Qt, instQ, ψ, hψ, hker, hQt⟩ := hJ.iso
  set O : Subgroup ↥J := ψ.ker
  have hOJ : rankThreePrimeCore 3 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 3 J
  have hOcop0 : Nat.Coprime 3 (Nat.card (rankThreePrimeCore 3 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 3 J
  have hOcop : Nat.Coprime 3 (Nat.card O) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv]
    exact hOcop0
  have hOn : O.Normal := MonoidHom.normal_ker ψ
  have hmemO : ∀ j : ↥J, j ∈ O ↔ (j : G) ∈ rankThreePrimeCore 3 J := fun j => by
    rw [hker, Subgroup.mem_subgroupOf]
  have hKt : IsRankThreeL28 (↥J ⧸ O) :=
    isL28_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψ) hQt
  have hSylJ : IsSylowOf 3 ((P : Subgroup G) ⊓ J) J := by
    have h := hsyl.inf_of_le_normalizer hJC hJ.centralizer_le
    rwa [inf_assoc, inf_eq_right.mpr hJC] at h
  obtain ⟨T, hT⟩ := hSylJ.exists_sylow_eq_subgroupOf
  have hTP : ∀ R : Subgroup ↥J, R ≤ (T : Subgroup ↥J) → R.map J.subtype ≤ (P : Subgroup G) := by
    intro R hR
    refine (Subgroup.map_mono (hR.trans hT.le)).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact inf_le_left
  have hOM : rankThreePrimeCore 3 J ≤ M := by
    have h1 : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M :=
      (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hrk.ge)
    refine le_trans ?_ h1
    exact CFSG.AGLEmbedding.le_glbPrimeCore (hOJ.trans hJC)
      (hJ.centralizer_le.trans
        (CFSG.PreuniquenessRankFour.Helpers.primeCore_normalizer_normalizes 3 hprime J))
      hOcop0
  set A : Subgroup ↥J := M.subgroupOf J
  have hOA : O ≤ A := by
    intro g hg
    rw [hker] at hg
    exact hOM hg
  have hN : ∀ R : Subgroup ↥J, R ≤ (T : Subgroup ↥J) → R ≠ ⊥ → normalizer (R : Set ↥J) ≤ A :=
    fun R hR hR1 n hn =>
      m11l45_normalizer_le hS hU0 hp hM hxP hxo hxJc hxJ (hTP R hR) hR1 hn
  obtain ⟨φ, hφapp⟩ : ∃ φ : ↥J ≃* ↥J, ∀ j : ↥J, (φ j : G) = w * j * w⁻¹ :=
    ⟨J.normalizerMonoidHom ⟨w, hwN⟩, fun j => Subgroup.normalizerMonoidHom_apply_apply_coe J _ j⟩
  have hφO : O.map (φ : ↥J →* ↥J) = O := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective φ.injective).ge
    rintro _ ⟨o, ho, rfl⟩
    have h : ((φ o : ↥J) : G) ∈ rankThreePrimeCore 3 J := by
      rw [hφapp]
      exact (mem_normalizer_iff.mp hwNO o).mp ((hmemO o).mp ho)
    exact (hmemO (φ o)).mpr h
  have hφT : ∀ t : ↥J, t ∈ (T : Subgroup ↥J) → φ t ∈ (T : Subgroup ↥J) := by
    intro t ht
    rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
    rw [hφapp]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hwP (Subgroup.mem_inf.mp ht).1) (inv_mem hwP),
      (mem_normalizer_iff.mp hwN t).mp t.2⟩
  have hφ3 : ∀ j : ↥J, φ (φ (φ j)) = j := fun j => by
    have hw3' : w * (w * w) = 1 := by rw [← pow_three]; exact hw3
    apply Subtype.ext
    rw [hφapp, hφapp, hφapp]
    calc w * (w * (w * (j : G) * w⁻¹) * w⁻¹) * w⁻¹
        = w * (w * w) * j * (w * (w * w))⁻¹ := by group
      _ = j := by rw [hw3', one_mul, inv_one, mul_one]
  obtain ⟨α, hαmk⟩ : ∃ α : MulAut (↥J ⧸ O),
      ∀ j : ↥J, α (QuotientGroup.mk' O j) = QuotientGroup.mk' O (φ j) :=
    ⟨QuotientGroup.congr O O φ hφO, fun j => QuotientGroup.congr_mk' O O φ hφO j⟩
  have hαout : ∀ k : ↥J ⧸ O, α ≠ MulAut.conj k := by
    intro k hk
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective O k
    refine hout ⟨j, j.2, fun j' hj' => ?_⟩
    have h2 : QuotientGroup.mk' O (φ ⟨j', hj'⟩) = QuotientGroup.mk' O (j * ⟨j', hj'⟩ * j⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← hαmk, hk, MulAut.conj_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h2
    have h3 := (hmemO _).mp (QuotientGroup.eq.mp h2)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hφapp] using h3
  have hα3' : α ^ 3 = 1 := by
    ext q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective O q
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hαmk, hαmk, hαmk, hφ3, MulAut.one_apply]
  have hα1 : α ≠ 1 := by
    have h := hαout 1
    rwa [map_one] at h
  have hα3 : orderOf α = 3 := orderOf_eq_prime hα3' hα1
  have hαT : ((T : Subgroup ↥J).map (QuotientGroup.mk' O)).map α.toMonoidHom =
      (T : Subgroup ↥J).map (QuotientGroup.mk' O) := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨φ t, hφT t ht, (hαmk t).symm⟩
  have hV : ∀ V : Subgroup (↥J ⧸ O), IsPGroup 2 V → V.map α.toMonoidHom = V →
      V ≤ A.map (QuotientGroup.mk' O) := by
    intro V hV2 hVα v hv
    have hxĈ : x ∈ normalizer
        (((V.comap (QuotientGroup.mk' O)).map J.subtype : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun h hh => (hxJc h (Subgroup.map_subtype_le _ hh)).symm)
    have hwĈ : w ∈ normalizer
        (((V.comap (QuotientGroup.mk' O)).map J.subtype : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨c, hc, rfl⟩
        refine ⟨φ c, ?_, hφapp c⟩
        show QuotientGroup.mk' O (φ c) ∈ V
        rw [← hαmk, ← hVα]
        exact Subgroup.mem_map_of_mem α.toMonoidHom (x := QuotientGroup.mk' O c) hc
      · rintro ⟨c, hc, hcg⟩
        have hgJ : g ∈ J := (mem_normalizer_iff.mp hwN g).mpr (by rw [← hcg]; exact c.2)
        have hφg : φ ⟨g, hgJ⟩ = c := Subtype.ext ((hφapp _).trans hcg.symm)
        refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
        have hc' : α (QuotientGroup.mk' O ⟨g, hgJ⟩) ∈ V.map α.toMonoidHom := by
          rw [hαmk, hφg, hVα]
          exact hc
        obtain ⟨v', hv', hv'eq⟩ := hc'
        have hv'eq' : α v' = α (QuotientGroup.mk' O ⟨g, hgJ⟩) := hv'eq
        show QuotientGroup.mk' O ⟨g, hgJ⟩ ∈ V
        rwa [← α.injective hv'eq']
    have hUĈ : U ≤ normalizer
        (((V.comap (QuotientGroup.mk' O)).map J.subtype : Subgroup G) : Set G) :=
      hUxw.le.trans (sup_le (zpowers_le.mpr hxĈ) (zpowers_le.mpr hwĈ))
    obtain ⟨W, hW2, hUW, hWV⟩ :=
      l28l45_exists_invariant_two_lift (P.isPGroup'.to_le hUP) O hOcop V hV2 hUĈ
    obtain ⟨s, hs, hsW, hsv⟩ := hWV v hv
    have hWM : W ⊓ J ≤ M := hall (W ⊓ J) inf_le_right (hW2.to_le inf_le_left)
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hUW hg, hUN hg⟩)
    exact ⟨⟨s, hs⟩, Subgroup.mem_subgroupOf.mpr (hWM ⟨hsW, hs⟩), hsv⟩
  have htop : A = ⊤ := l28l45_eq_top hK2 O hOcop hKt T hOA α hα3 hαout hαT hN hV
  refine hJ.not_le fun g hg => ?_
  have : (⟨g, hg⟩ : ↥J) ∈ A := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem l28_exists_maximal_not_le_of_plane (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK2 : KFactL28FieldSignalizer) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL28Normal M x J) (hxJ : x ∉ J) {U : Subgroup G} (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) {w : G}
    (hwU : w ∈ U) (hwx : w ∉ zpowers x) (hout : L28OuterOn J w) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  obtain ⟨A, hA, hAM⟩ := l28l45_exists_within_not_le hS hU0 hK2 hp hM hgen hJ hxJ hU hUc hUP hxU
    hwU hwx hout
  obtain ⟨S₁, hAS₁, hS₁⟩ := exists_maximal_invariant_two_subgroup_containing U A hA.2.1 hA.2.2.1
  exact ⟨S₁, hS₁, fun h => hAM (hAS₁.trans h)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
