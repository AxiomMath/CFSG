module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeNormalRank
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineCompetitorSplit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem pRank_le_pRank_inf_centralizer_of_normal (hp : p.Prime) {R A : Subgroup X}
    (hR : IsPGroup p R) (hAR : A ≤ R) (hRA : R ≤ Subgroup.normalizer (A : Set X))
    (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    CFSG.Open.pRank p R ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup R := A.subgroupOf R
  haveI : D.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAR).mpr hRA
  have hDel : IsElemAbelian p D := isElemAbelian_subgroupOf hA R
  have hDcard : Nat.card D = p ^ 2 := by
    rw [← hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv
  have hrank :=
    CFSG.PreuniquenessRankFour.Helpers.normal_elementary_rank_two_pGroup_centralizer_rank_eq
      p hR D hDel hDcard
  have hDA : D.map R.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAR
  have hle : (Subgroup.centralizer (D : Set R)).map R.subtype ≤
      R ⊓ Subgroup.centralizer (A : Set X) := by
    refine le_inf (Subgroup.map_subtype_le _) ?_
    have := map_subtype_centralizer_le D
    rwa [hDA] at this
  have e1 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp R.subtype
    R.subtype_injective (Subgroup.centralizer (D : Set R))
  have e2 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp R.subtype
    R.subtype_injective (⊤ : Subgroup R)
  have e3 : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [e3] at e2
  calc CFSG.Open.pRank p R
      = CFSG.Open.pRank p ((Subgroup.centralizer (D : Set R)).map R.subtype) := by
        rw [e1, hrank, e2]
    _ ≤ _ := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hle

theorem exists_plane_le_three_le_pRank_centralizer (hp : p.Prime) (hp2 : p ≠ 2)
    {R T : Subgroup X} (hR : IsPGroup p R) (hTR : T ≤ R)
    (hRT : R ≤ Subgroup.normalizer (T : Set X)) (hT : ¬ IsCyclic T)
    (h3 : 3 ≤ CFSG.Open.pRank p R) :
    ∃ A : Subgroup X, A ≤ T ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      3 ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup R := T.subgroupOf R
  haveI : C.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTR).mpr hRT
  have hCc : ¬ IsCyclic C := fun hc => hT (isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hTR).toMonoidHom (Subgroup.subgroupOfEquivOfLe hTR).surjective)
  obtain ⟨D, hDC, hDn, hDcard, hDexp, hDcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le hp2 hR C hCc
  have hDel : IsElemAbelian p D :=
    ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (hDcomm x x.2 y y.2), hDexp⟩
  set A : Subgroup X := D.map R.subtype with hAdef
  have hAR : A ≤ R := Subgroup.map_subtype_le D
  have hAel : IsElemAbelian p A :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hDel _
  have hAcard : Nat.card A = p ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective R.subtype_injective, hDcard]
  have hRA : R ≤ Subgroup.normalizer (A : Set X) := by
    intro r hr
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨⟨r, hr⟩ * d * ⟨r, hr⟩⁻¹, hDn.conj_mem d hd ⟨r, hr⟩, by simp⟩
  exact ⟨A, (Subgroup.map_mono hDC).trans (Subgroup.map_subgroupOf_eq_of_le hTR).le, hAel, hAcard,
    h3.trans (pRank_le_pRank_inf_centralizer_of_normal hp hR hAR hRA hAel hAcard)⟩

theorem centralizer_sup_components_le (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (Rb : Sylow p X) {X₀ : Subgroup X}
    (hNorm : ∀ A : Subgroup X, A ≤ Rb → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ CFSG.Open.pRank p ((Rb : Subgroup X) ⊓ Subgroup.centralizer (A : Set X)) →
      Subgroup.normalizer (A : Set X) ≤ X₀)
    (hTwo : CFSG.Open.pRank p (Rb : Subgroup X) ≤ 2 → ∃ E : Subgroup X, E ≤ Rb ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ w ∈ E, w ≠ 1 → Subgroup.centralizer (Subgroup.zpowers w : Set X) ≤ X₀)
    (hKn : (⨆ (L : Subgroup X) (_ : IsComponentOf L ⊤ ∧ ¬ L ≤ X₀), L).Normal)
    {L₀ : Subgroup X} (hL₀ : IsComponentOf L₀ ⊤) (hL₀X : ¬ L₀ ≤ X₀) :
    Subgroup.centralizer ((⨆ (L : Subgroup X) (_ : IsComponentOf L ⊤ ∧ ¬ L ≤ X₀), L :
      Subgroup X) : Set X) ≤ X₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup X := ⨆ (L : Subgroup X) (_ : IsComponentOf L ⊤ ∧ ¬ L ≤ X₀), L with hK
  have hleK : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ → L ≤ K := fun L hL hLX =>
    le_iSup₂_of_le L ⟨hL, hLX⟩ le_rfl
  have hC : ∀ A : Subgroup X, A ≤ Rb → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ CFSG.Open.pRank p ((Rb : Subgroup X) ⊓ Subgroup.centralizer (A : Set X)) →
      Subgroup.centralizer (A : Set X) ≤ X₀ := fun A h1 h2 h3 h4 =>
    (Subgroup.centralizer_le_normalizer _).trans (hNorm A h1 h2 h3 h4)
  have hu : ∀ L : Subgroup X, IsComponentOf L ⊤ → ∃ u ∈ (Rb : Subgroup X), u ∈ L ∧
      orderOf u = p ∧ ∃ c ∈ L, u * c ≠ c * u := by
    intro L hL
    obtain ⟨t, ⟨htR, htL⟩, htp, htc⟩ := exists_mem_sylow_inf_component hp hp2 hcore Rb hL
    refine ⟨t, htR, htL, htp, ?_⟩
    by_contra hall
    push Not at hall
    exact htc (Subgroup.mem_centralizer_iff.mpr fun c hc => (hall c hc).symm)
  obtain ⟨u, huR, huL, hup, c₀, hc₀, huc⟩ := hu L₀ hL₀
  have huK : u ∈ K := hleK L₀ hL₀ hL₀X huL
  have hS7 := pRank_inf_centralizer_component_le_one hp hC hL₀X huR huL hup ⟨c₀, hc₀, huc⟩
  set T : Subgroup X := (Rb : Subgroup X) ⊓ K with hT
  have hRbT : (Rb : Subgroup X) ≤ Subgroup.normalizer (T : Set X) := by
    intro r hr
    apply Subgroup.mem_normalizer_fintype
    intro t ht
    exact ⟨(Rb : Subgroup X).mul_mem ((Rb : Subgroup X).mul_mem hr ht.1)
      ((Rb : Subgroup X).inv_mem hr), hKn.conj_mem t ht.2 r⟩
  by_cases hrank : CFSG.Open.pRank p (Rb : Subgroup X) ≤ 2
  ·
    obtain ⟨E, hER, hE, hEcard, hEw⟩ := hTwo hrank
    obtain ⟨w, hwT, hwZ, hwp⟩ : ∃ w ∈ T, (∀ r ∈ (Rb : Subgroup X), r * w = w * r) ∧
        orderOf w = p := by
      haveI : Group.IsNilpotent (Rb : Subgroup X) := Rb.isPGroup'.isNilpotent
      haveI : (T.subgroupOf (Rb : Subgroup X)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hRbT
      have hT1 : T.subgroupOf (Rb : Subgroup X) ≠ ⊥ := by
        intro h
        have hmem : (⟨u, huR⟩ : (Rb : Subgroup X)) ∈ T.subgroupOf (Rb : Subgroup X) :=
          Subgroup.mem_subgroupOf.mpr ⟨huR, huK⟩
        rw [h, Subgroup.mem_bot] at hmem
        have hu1 : u = 1 := congrArg Subtype.val hmem
        rw [hu1, orderOf_one] at hup
        exact hp.one_lt.ne hup
      have hS := Group.IsNilpotent.inf_center_ne_bot_of_normal hT1
      set S := T.subgroupOf (Rb : Subgroup X) ⊓ Subgroup.center (Rb : Subgroup X) with hSdef
      have hSp : IsPGroup p S := Rb.isPGroup'.to_subgroup S
      haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS
      obtain ⟨n, hn, hcn⟩ := hSp.nontrivial_iff_card.mp inferInstance
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (G := S)
        (by rw [hcn]; exact dvd_pow_self p hn.ne')
      refine ⟨((x : (Rb : Subgroup X)) : X), Subgroup.mem_subgroupOf.mp x.2.1, fun r hr => ?_, ?_⟩
      · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2.2 ⟨r, hr⟩)
      · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hwp' : w ^ p = 1 := by rw [← hwp, pow_orderOf_eq_one]
    have hwE : w ∈ E := by
      by_contra hwE
      obtain ⟨hE3, hE3card⟩ := CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hE hEcard
        hwp' hwE fun e he => hwZ e (hER he)
      have h3 := (three_le_pRank_of_card hp hE3 hE3card).trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
          (sup_le hER (Subgroup.zpowers_le.mpr hwT.1)))
      omega
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hwp
      exact hp.one_lt.ne hwp
    exact (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hwT.2)).trans (hEw w hwE hw1)
  push Not at hrank
  by_cases hTc : IsCyclic T
  swap
  ·
    obtain ⟨A, hAT, hA, hAcard, hA3⟩ := exists_plane_le_three_le_pRank_centralizer hp hp2
      Rb.isPGroup' inf_le_left hRbT hTc (by omega)
    exact (Subgroup.centralizer_le (hAT.trans inf_le_right)).trans
      (hC A (hAT.trans inf_le_left) hA hAcard hA3)
  haveI := hTc
  have huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ → L = L₀ := by
    intro L hL hLX
    by_contra hne
    obtain ⟨u', hu'R, hu'L, hu'p, c', hc', hu'c⟩ := hu L hL
    have hu'u : u' ∈ Subgroup.zpowers u :=
      mem_zpowers_of_orderOf_eq_of_isCyclic (Z := T) ⟨hu'R, hleK L hL hLX hu'L⟩ ⟨huR, huK⟩
        (hu'p.trans hup.symm)
    have hu'L₀ : u' ∈ L₀ := (Subgroup.zpowers_le.mpr huL) hu'u
    exact hu'c (Subgroup.mem_centralizer_iff.mp
      (le_centralizer_of_component_ne hL₀ hL (Ne.symm hne) hu'L₀) c' hc').symm
  have hKL₀ : K = L₀ :=
    le_antisymm (iSup₂_le fun L hL => (huniq L hL.1 hL.2).le) (hleK L₀ hL₀ hL₀X)
  have hL₀n : L₀.Normal := hKL₀ ▸ hKn
  have hQcyc : IsCyclic ((Rb : Subgroup X) ⊓ Subgroup.centralizer (L₀ : Set X) : Subgroup X) := by
    by_contra hnc
    have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp hp2 (Rb.isPGroup'.to_le inf_le_left) hnc
    omega
  have huRb : ∀ r ∈ (Rb : Subgroup X), r * u * r⁻¹ ∈ Subgroup.zpowers u := fun r hr =>
    CFSG.AGLEmbedding.conj_mem_zpowers_of_isCyclic (T := T) rfl ⟨huR, huK⟩
      ((Subgroup.mem_normalizer_iff.mp (hRbT hr) u).mp ⟨huR, huK⟩)
  have hAz : ∀ z ∈ (Rb : Subgroup X), orderOf z = p → z ∈ Subgroup.centralizer (L₀ : Set X) →
      (∀ r ∈ (Rb : Subgroup X), r * z * r⁻¹ ∈ Subgroup.zpowers z) →
      Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) : Set X) ≤
        X₀ := by
    intro z hzR hzp hzC hzRb
    have hzu : z ∉ Subgroup.zpowers u := by
      intro hz
      have huz : u ∈ Subgroup.zpowers z :=
        mem_zpowers_of_orderOf_eq_of_isCyclic (Z := Subgroup.zpowers u) (Subgroup.mem_zpowers u)
          hz (hup.trans hzp.symm)
      exact huc (Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hzC) huz) c₀ hc₀).symm
    have hu' : u ^ p = 1 := by rw [← hup, pow_orderOf_eq_one]
    have hz' : z ^ p = 1 := by rw [← hzp, pow_orderOf_eq_one]
    have hE₁ : IsElemAbelian p (Subgroup.zpowers u) :=
      ⟨inferInstance, fun x hx => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu', one_zpow]⟩
    have hcard₁ : Nat.card (Subgroup.zpowers u) = p ^ 1 := by
      rw [Nat.card_zpowers, pow_one, hup]
    have hcomm : ∀ e ∈ Subgroup.zpowers u, e * z = z * e := fun e he =>
      (Subgroup.mem_centralizer_iff.mp hzC) e ((Subgroup.zpowers_le.mpr huL) he)
    obtain ⟨hA, hAcard⟩ :=
      CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hE₁ hcard₁ hz' hzu hcomm
    have hAR : Subgroup.zpowers u ⊔ Subgroup.zpowers z ≤ Rb :=
      sup_le (Subgroup.zpowers_le.mpr huR) (Subgroup.zpowers_le.mpr hzR)
    have hRA : (Rb : Subgroup X) ≤
        Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) : Set X) :=
      fun r hr => mem_normalizer_sup_zpowers (Subgroup.mem_sup_left (huRb r hr))
        (Subgroup.mem_sup_right (hzRb r hr))
    exact hNorm _ hAR hA hAcard
      ((by omega : 3 ≤ CFSG.Open.pRank p (Rb : Subgroup X)).trans
        (pRank_le_pRank_inf_centralizer_of_normal hp Rb.isPGroup' hAR hRA hA hAcard))
  have hmemN : ∀ z c : X, c ∈ Subgroup.centralizer (L₀ : Set X) →
      c * z * c⁻¹ ∈ Subgroup.zpowers z →
      c ∈ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) : Set X) := by
    intro z c hc hcz
    refine mem_normalizer_sup_zpowers (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hcz)
    have e : c * u * c⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hc u huL).symm
    rw [e]
    exact Subgroup.mem_zpowers u
  rw [hKL₀]
  have hcoreX : CFSG.fittingSubgroup X = CFSG.pCore p X := CFSG.Fitting_eq_pcore X p hcore
  by_cases hO : CFSG.pCore p X = ⊥
  swap
  ·
    haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal
    obtain ⟨z, hz, hzp⟩ : ∃ z ∈ CFSG.pCore p X, orderOf z = p := by
      obtain ⟨z, hz⟩ : ∃ x : CFSG.pCore p X, orderOf x = p := by
        rcases (CFSG.pCore_isPGroup (p := p) (G := X)).card_eq_or_dvd with h1 | hdvd
        · exact absurd (Subgroup.card_eq_one.mp h1) hO
        · exact exists_prime_orderOf_dvd_card' p hdvd
      exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩
    have hOR : CFSG.pCore p X ≤ Rb := CFSG.pCore_isPGroup.le_sylow_of_normal Rb
    have hOC : CFSG.pCore p X ≤ Subgroup.centralizer (L₀ : Set X) := by
      have hEC : CFSG.layer X ≤ Subgroup.centralizer (CFSG.pCore p X : Set X) := by
        rw [← hcoreX]
        exact Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute)
      exact Subgroup.le_centralizer_iff.mp
        ((CFSG.LocalCores.component_le_layer ((CFSG.isComponent_iff_open L₀).mpr hL₀)).trans hEC)
    haveI : IsCyclic (CFSG.pCore p X) := Subgroup.isCyclic_of_le (le_inf hOR hOC)
    have hzX : ∀ g : X, g * z * g⁻¹ ∈ Subgroup.zpowers z := fun g =>
      CFSG.AGLEmbedding.conj_mem_zpowers_of_isCyclic (T := CFSG.pCore p X) rfl hz
        ((inferInstance : (CFSG.pCore p X).Normal).conj_mem z hz g)
    intro c hc
    exact hAz z (hOR hz) hzp (hOC hz) (fun r _ => hzX r) (hmemN z c hc (hzX c))
  by_cases hJ : ∃ J : Subgroup X, IsComponentOf J ⊤ ∧ J ≠ L₀
  ·
    obtain ⟨J, hJc, hJne⟩ := hJ
    have hJX : J ≤ X₀ := by
      by_contra h
      exact hJne (huniq J hJc h)
    have hJC : J ≤ Subgroup.centralizer (L₀ : Set X) := le_centralizer_of_component_ne hJc hL₀ hJne
    obtain ⟨v, hvR, hvJ, hvp, d, hdJ, hvd⟩ := hu J hJc
    have hJn : J.Normal := by
      refine ⟨fun n hn g => ?_⟩
      set J' : Subgroup X := J.map (MulAut.conj g).toMonoidHom with hJ'
      have hJ'c : IsComponentOf J' ⊤ :=
        (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) J).mpr hJc
      have hJ'J : J' = J := by
        by_contra hne'
        have hJ'L₀ : J' ≠ L₀ := by
          intro h
          have hv : v ∈ L₀ := by
            have h1 : g * v * g⁻¹ ∈ L₀ := h ▸ ⟨v, hvJ, rfl⟩
            have := hL₀n.conj_mem _ h1 g⁻¹
            simpa [mul_assoc] using this
          have hd : d ∈ L₀ := by
            have h1 : g * d * g⁻¹ ∈ L₀ := h ▸ ⟨d, hdJ, rfl⟩
            have := hL₀n.conj_mem _ h1 g⁻¹
            simpa [mul_assoc] using this
          exact hvd (Subgroup.mem_centralizer_iff.mp (hJC hvJ) d hd).symm
        have hJ'C : J' ≤ Subgroup.centralizer (L₀ : Set X) :=
          le_centralizer_of_component_ne hJ'c hL₀ hJ'L₀
        obtain ⟨v', hv'R, hv'J, hv'p, d', hd', hv'd⟩ := hu J' hJ'c
        have hv'v : v' ∈ Subgroup.zpowers v :=
          mem_zpowers_of_orderOf_eq_of_isCyclic
            (Z := (Rb : Subgroup X) ⊓ Subgroup.centralizer (L₀ : Set X))
            ⟨hv'R, hJ'C hv'J⟩ ⟨hvR, hJC hvJ⟩ (hv'p.trans hvp.symm)
        have hv'J₁ : v' ∈ J := (Subgroup.zpowers_le.mpr hvJ) hv'v
        exact hv'd (Subgroup.mem_centralizer_iff.mp
          (le_centralizer_of_component_ne hJc hJ'c (Ne.symm hne') hv'J₁) d' hd').symm
      rw [← hJ'J]
      exact ⟨n, hn, rfl⟩
    haveI := hJn
    haveI : IsCyclic ((Rb : Subgroup X) ⊓ J : Subgroup X) :=
      Subgroup.isCyclic_of_le (inf_le_inf_left _ hJC)
    have hvN : ∀ g ∈ Subgroup.normalizer (((Rb : Subgroup X) ⊓ J : Subgroup X) : Set X),
        g * v * g⁻¹ ∈ Subgroup.zpowers v := fun g hg =>
      CFSG.AGLEmbedding.conj_mem_zpowers_of_isCyclic (T := (Rb : Subgroup X) ⊓ J) rfl ⟨hvR, hvJ⟩
        ((Subgroup.mem_normalizer_iff.mp hg v).mp ⟨hvR, hvJ⟩)
    have hRbN : (Rb : Subgroup X) ≤
        Subgroup.normalizer (((Rb : Subgroup X) ⊓ J : Subgroup X) : Set X) := by
      intro r hr
      apply Subgroup.mem_normalizer_fintype
      intro t ht
      exact ⟨(Rb : Subgroup X).mul_mem ((Rb : Subgroup X).mul_mem hr ht.1)
        ((Rb : Subgroup X).inv_mem hr), hJn.conj_mem t ht.2 r⟩
    have hN := hAz v hvR hvp (hJC hvJ) fun r hr => hvN r (hRbN hr)
    obtain ⟨S, hS⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
      (Subgroup.Normal.isSubnormal hJn)
    have htop := Sylow.normalizer_sup_eq_top S
    rw [hS] at htop
    intro c hc
    have hcm : c ∈ Subgroup.normalizer (((Rb : Subgroup X) ⊓ J : Subgroup X) : Set X) ⊔ J := by
      rw [htop]
      exact Subgroup.mem_top c
    obtain ⟨n, hn, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hcm
    have hnC : n ∈ Subgroup.centralizer (L₀ : Set X) := by
      have e : n = n * j * j⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ (hJC hj))
    exact X₀.mul_mem (hN (hmemN v n hnC (hvN n hn))) (hJX hj)
  push Not at hJ
  have hF : CFSG.generalizedFitting X ≤ L₀ := by
    refine sup_le ?_ (sSup_le fun J hJc => ?_)
    · rw [hcoreX, hO]
      exact bot_le
    · exact (hJ J ((CFSG.isComponent_iff_open J).mp hJc)).le
  calc Subgroup.centralizer (L₀ : Set X)
      ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := Subgroup.centralizer_le hF
    _ ≤ CFSG.fittingSubgroup X := CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup X
    _ = ⊥ := by rw [hcoreX, hO]
    _ ≤ X₀ := bot_le

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem centralizer_d1KBar_le_d1X0_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hK : d1KBar p M N ≠ ⊥) :
    Subgroup.centralizer ((d1KBar p M N : Subgroup (N ⧸ primeComplementCore (G := N) p)) :
      Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  obtain ⟨R, hBR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hB hBN
  have hRp : IsPGroup p (R.subgroupOf N) :=
    hR.isPGroup.comap_of_injective N.subtype N.subtype_injective
  set Rb : Sylow p (N ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (R.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  obtain ⟨L₀, hL₀, hL₀X⟩ := exists_component_of_d1KBar_ne_bot hK
  refine centralizer_sup_components_le hp he.ne_two (primeComplementCore_quotient_eq_bot p) Rb
    (fun A hA hAe hAc h3 => ?_) (fun h2 => ?_) (d1KBar_normal_of_escape he hB hBN hK) hL₀ hL₀X
  · rw [hRbeq] at hA h3
    exact normalizer_le_d1X0_of_escape he hR.le hRM hR.isPGroup A hA hAe hAc h3
  ·
    have hRrank : CFSG.Open.pRank p R ≤ 2 := by
      rw [hRbeq, pRank_map_mk_eq_pRank_map_subtype hp O hO,
        Subgroup.map_subgroupOf_eq_of_le hR.le] at h2
      exact h2
    obtain ⟨-, -, h3 | ⟨E, hEB, hE, hEc, hΓ⟩⟩ := hB
    · exfalso
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
      have := h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hBR)
      omega
    have hEN : E ≤ N := (hEB.trans hBR).trans hR.le
    have hEp : IsPGroup p (E.subgroupOf N) :=
      (hR.isPGroup.to_le (hEB.trans hBR)).comap_of_injective N.subtype N.subtype_injective
    refine ⟨(E.subgroupOf N).map π, ?_, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
      (isElemAbelian_subgroupOf hE N) π, ?_, fun w hw hw1 => ?_⟩
    · rw [hRbeq]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (hBR (hEB (Subgroup.mem_subgroupOf.mp hx)))
    · rw [card_map_mk_of_isPGroup hp O hO hEp, ← hEc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
    · obtain ⟨e, he', rfl⟩ := hw
      have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he'
      have hep : IsPGroup p (Subgroup.zpowers e) := hEp.to_le (Subgroup.zpowers_le.mpr he')
      have he1 : (e : G) ≠ 1 := by
        intro h
        apply hw1
        rw [show e = 1 from Subtype.ext h, map_one]
      have hNe : Subgroup.normalizer (Subgroup.zpowers (e : G) : Set G) ≤ M := by
        have hep' : (e : G) ^ p = 1 := hE.2 _ heE
        have hF1 : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers (e : G)) := by
          refine le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp _)
            ⟨Subgroup.zpowers (e : G), le_rfl, ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
          · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep', one_zpow]
          · rw [Nat.card_zpowers, orderOf_eq_prime hep' he1, pow_one]
        exact (le_sSup ⟨Subgroup.zpowers (e : G), Subgroup.zpowers_le.mpr heE, hF1, rfl⟩ :
          Subgroup.normalizer (Subgroup.zpowers (e : G) : Set G) ≤ GLBCore p 1 E).trans hΓ
      have hCN : Subgroup.centralizer (Subgroup.zpowers e : Set N) ≤ (N ⊓ M).subgroupOf N :=
        fun c hc => Subgroup.mem_subgroupOf.mpr ⟨c.property, hNe
          (Subgroup.centralizer_le_normalizer _ (by
            have := map_subtype_centralizer_le (Subgroup.zpowers e) ⟨c, hc, rfl⟩
            rwa [MonoidHom.map_zpowers] at this))⟩
      have hlift := Subgroup.map_mono (f := π) (comap_centralizer_map_le_sup hp O hO hep)
      rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
        Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]
        at hlift
      exact hlift.trans (Subgroup.map_mono hCN)
theorem d1PlusCore_le_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hK : d1KBar p M N ≠ ⊥) : d1PlusCore p N (d1KBar p M N) ≤ M := by
  set π := QuotientGroup.mk' (primeComplementCore (G := N) p) with hπ
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨m, hm, hmh⟩ := centralizer_d1KBar_le_d1X0_of_escape he hB hBN hK hh
  have h1 : π (m⁻¹ * h) = 1 := by rw [map_mul, map_inv, hmh, inv_mul_cancel]
  have hoM : ((m⁻¹ * h : N) : G) ∈ M :=
    core_le_of_base (muAt_of_escape he) hB hBN ⟨m⁻¹ * h, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have e : (h : G) = (m : G) * ((m⁻¹ * h : N) : G) := by simp
  rw [Subgroup.coe_subtype, e]
  exact M.mul_mem hmM hoM

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
