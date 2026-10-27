module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTheoremE
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

omit [Finite G] in
private theorem wreathR_card_eq_eighty_one {P : Subgroup G} (e : P ≃* W₃) : Nat.card P = 81 := by
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, wreath_card_zmod_three]
  norm_num

omit [Finite G] in
private theorem wreathR_exists_isElemAbelian_card_twentySeven {P : Subgroup G} (e : P ≃* W₃) :
    ∃ V : Subgroup G, V ≤ P ∧ IsElemAbelian 3 V ∧ Nat.card V = 27 := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιP : ∀ w, ι w ∈ P := fun w => (e.symm w).2
  let A₀ : Subgroup W₃ := (RegularWreathProduct.rightHom :
    Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker
  have hA₀c : IsMulCommutative A₀ := wreath_ker_isElemAbelian.1
  refine ⟨A₀.map ι, ?_, ⟨Subgroup.map_isMulCommutative A₀ ι, ?_⟩, ?_⟩
  · rintro _ ⟨a, _, rfl⟩
    exact hιP a
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, wreath_ker_isElemAbelian.2 a ha, map_one]
  · exact (Subgroup.card_map_of_injective hιinj).trans wreath_card_ker

private theorem wreathR_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {Q P : Subgroup G}
    (hP : IsPGroup p P) (hQP : Q < P) : ∃ y ∈ P, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQP.ne ?_
    exact le_antisymm hQP.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQP.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem wreathR_centralizer_le (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {V : Subgroup G} (hVP : V ≤ (P : Subgroup G))
    (hV : IsElemAbelian 3 V) (hVc : Nat.card V = 27) {y : G} (hyV : y ∈ V) (hy1 : y ≠ 1) :
    centralizer ({y} : Set G) ≤ M := by
  have hPM := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  by_contra hCM
  have hVcomm : IsMulCommutative V := hV.1
  have hVC : V ≤ centralizer ({y} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm ha hyV)
  refine hsit.largeObstruction_empty y ⟨hPM (hVP hyV), hy1, hV.2 y hyV, ?_, hCM⟩
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_set_bddAbove 3 (by norm_num) _) ⟨V, hVC, hV, by rw [hVc]; norm_num⟩

theorem exists_noncyclic_le_normalizer_gamma_one_le (hS : Setting G) (hU0 : FullCoreLocal G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) :
    ∃ R : Subgroup G, R ≤ (P : Subgroup G) ∧
      R ≤ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ∧ IsPGroup 3 R ∧
      ¬ IsCyclic R ∧ rankThreeGamma 1 3 R ≤ M := by
  obtain ⟨V, hVP, hV, hVc⟩ := wreathR_exists_isElemAbelian_card_twentySeven e
  have hPc : Nat.card (P : Subgroup G) = 81 := wreathR_card_eq_eighty_one e
  have hplane := SmallRankPlane.of_situation hS hsit hx hz
  set B : Subgroup G := zpowers x ⊔ zpowers z
  have hBP : B ≤ P := sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)
  have hBc : Nat.card B = 9 := hplane.card_eq.trans (by norm_num)
  have hBlt : B < (P : Subgroup G) := lt_of_le_of_ne hBP fun h => by rw [h, hPc] at hBc; omega
  obtain ⟨g, hgP, hgN, hgB⟩ := wreathR_exists_mem_normalizer_not_mem P.isPGroup' hBlt
  set N : Subgroup G := normalizer (B : Set G)
  have hBNP : B < N ⊓ P := lt_of_le_of_ne (le_inf Subgroup.le_normalizer hBP) fun h =>
    hgB (by rw [h]; exact mem_inf.mpr ⟨hgN, hgP⟩)
  have hNP := Subgroup.relIndex_mul_card (H := N) (K := (P : Subgroup G))
  rw [hPc] at hNP
  have hNc : 27 ≤ Nat.card (N ⊓ P : Subgroup G) := by
    have h1 := Subgroup.card_lt_of_lt hBNP
    rw [hBc] at h1
    generalize Nat.card (N ⊓ P : Subgroup G) = n at *
    have h2 : n ∣ 81 := Dvd.intro_left _ hNP
    have h3 := Nat.le_of_dvd (by norm_num) h2
    interval_cases n <;> omega
  have hNr : N.relIndex P ≤ 3 := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hVP' := Subgroup.relIndex_mul_card (H := V) (K := (P : Subgroup G))
  rw [inf_eq_left.mpr hVP, hVc, hPc] at hVP'
  have hVr : V.relIndex P = 3 := by omega
  have hRP : V ⊓ N ≤ P := inf_le_left.trans hVP
  have hRc := Subgroup.relIndex_mul_card (H := V ⊓ N) (K := (P : Subgroup G))
  rw [inf_eq_left.mpr hRP, hPc] at hRc
  have hRr : (V ⊓ N).relIndex P ≤ 9 :=
    (Subgroup.relIndex_inf_le (H := V) (K := N) (L := (P : Subgroup G))).trans
      (by rw [hVr]; omega)
  have hR9 : 9 ≤ Nat.card (V ⊓ N : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    nlinarith
  refine ⟨V ⊓ N, hRP, inf_le_right, (P.isPGroup').to_le hRP, ?_, ?_⟩
  ·
    intro hcyclic
    obtain ⟨c, hc⟩ := hcyclic.exists_generator
    have hdvd : Nat.card (V ⊓ N : Subgroup G) ∣ 3 := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hc]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hV.2 c (mem_inf.mp c.2).1))
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · exact gamma_one_le_of_forall_centralizer_le hS hU0 hsit.mem_sigmaA hsit.isCoreMaxLocal hRP
      fun y hy hy1 _ => wreathR_centralizer_le hS hsit hVP hV hVc (mem_inf.mp hy).1 hy1

end CFSG.LocalAnalysis.RankThreeTheoremC
