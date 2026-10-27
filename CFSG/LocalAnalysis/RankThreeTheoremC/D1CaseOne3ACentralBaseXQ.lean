module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockDatum
public import CFSG.Goldschmidt.Steps.G63Basic
public import CFSG.Goldschmidt.Steps.Sec82e
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenCaseTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ParabolicBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseX
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AKappaClass
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111 CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81TenFourteenThree : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)),
    D1ComponentConfig3 p P M H R Rbar →
    ∀ a : G, a ∈ M → orderOf a = p → ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → p ∣ Nat.card L →
    ¬ ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 M

theorem normalizer_zpowers_le_of_norm {p : ℕ} (hp : p.Prime) {M D : Subgroup G}
    (hD : IsElemAbelian p D) {x : G} (hx : x ∈ D)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNorm : ∀ B : Subgroup G, D ≤ B → B ≤ M → IsPGroup p B →
      Subgroup.normalizer (B : Set G) ≤ M) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  set Nx := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)
  set C := Subgroup.centralizer ({x} : Set G)
  have hCN : C ≤ Nx := fun c hc => by
    have hxc : x * c = c * x := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (show Commute x c from hxc) k).eq
  set C₁ := C.subgroupOf Nx
  have hC₁ : C₁.Normal := by
    refine ⟨fun c hc n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    have hn' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) x).mp
      (Subgroup.mem_zpowers x)
    obtain ⟨k, hk⟩ := hn'
    have hcx : (c : G) * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul]
    have hk' : (n : G)⁻¹ * x * (n : G)⁻¹⁻¹ = x ^ k := hk.symm
    rw [inv_inv] at hk'
    have e : x = (n : G) * x ^ k * (n : G)⁻¹ := by rw [← hk']; group
    rw [e]
    have hck : (c : G) * x ^ k = x ^ k * c :=
      (Commute.zpow_right (show Commute (c : G) x from hcx) k).eq
    calc (n : G) * c * (n : G)⁻¹ * ((n : G) * x ^ k * (n : G)⁻¹)
        = (n : G) * (c * x ^ k) * (n : G)⁻¹ := by group
      _ = (n : G) * (x ^ k * c) * (n : G)⁻¹ := by rw [hck]
      _ = (n : G) * x ^ k * (n : G)⁻¹ * ((n : G) * c * (n : G)⁻¹) := by group
  have hDC : D ≤ C := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((isMulCommutative_iff.mp hD.1) ⟨e, he⟩ ⟨x, hx⟩))
  have hDpG : IsPGroup p D := fun e => ⟨1, Subtype.ext (by simpa using hD.2 e e.2)⟩
  set D₁ : Subgroup C₁ := (D.subgroupOf Nx).subgroupOf C₁
  have hD₁ : IsPGroup p D₁ := hDpG.comap_subtype.comap_subtype
  obtain ⟨S, hS⟩ := hD₁.exists_le_sylow
  set B : Subgroup G := ((S : Subgroup C₁).map C₁.subtype).map Nx.subtype
  have hBC : B ≤ C := by
    rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp c.2
  have hDB : D ≤ B := by
    intro e he
    have heN : e ∈ Nx := hCN (hDC he)
    have heC : (⟨e, heN⟩ : Nx) ∈ C₁ := Subgroup.mem_subgroupOf.mpr (hDC he)
    have heD₁ : (⟨⟨e, heN⟩, heC⟩ : C₁) ∈ D₁ :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr he)
    exact ⟨_, ⟨_, hS heD₁, rfl⟩, rfl⟩
  have hBp : IsPGroup p B := (S.isPGroup'.map _).map _
  have hNB : Subgroup.normalizer (B : Set G) ≤ M := hNorm B hDB (hBC.trans hC) hBp
  have htop := Sylow.normalizer_sup_eq_top (p := p) (N := C₁) S
  intro n hn
  have hn' : (⟨n, hn⟩ : Nx) ∈
      Subgroup.normalizer (((S : Subgroup C₁).map C₁.subtype : Subgroup Nx) : Set Nx) ⊔ C₁ :=
    htop ▸ Subgroup.mem_top _
  have hle : Subgroup.normalizer
      (((S : Subgroup C₁).map C₁.subtype : Subgroup Nx) : Set Nx) ⊔ C₁ ≤
      M.comap Nx.subtype := by
    refine sup_le ?_ ?_
    · intro y hy
      have hy' : (y : G) ∈ Subgroup.normalizer (B : Set G) :=
        Subgroup.le_normalizer_map Nx.subtype ⟨y, hy, rfl⟩
      exact hNB hy'
    · intro c hc
      exact hC (Subgroup.mem_subgroupOf.mp hc)
  exact hle hn'

theorem gamma_one_le_of_norm {p : ℕ} (hp : p.Prime) {M E D : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) (hD : IsElemAbelian p D) (hED : E ≤ D)
    (hNE : Subgroup.normalizer (E : Set G) ≤ M)
    (hC : ∀ x ∈ E, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNorm : ∀ B : Subgroup G, D ≤ B → B ≤ M → IsPGroup p B →
      Subgroup.normalizer (B : Set G) ≤ M) :
    rankThreeGamma 1 p E ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  refine sSup_le ?_
  rintro _ ⟨Q, hQE, hQr, rfl⟩
  by_cases hQc : IsCyclic Q
  · obtain ⟨g, hg⟩ := hQc.exists_generator
    have hQ : Q = Subgroup.zpowers (g : G) := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact Q.zpow_mem g.2 k
    have hg1 : (g : G) ≠ 1 := by
      intro h1
      have hbot : Q = ⊥ := by rw [hQ, h1, Subgroup.zpowers_one_eq_bot]
      obtain ⟨A, hAQ, -, hAcard⟩ := pRank_attained p hp Q
      have hA : A = ⊥ := le_bot_iff.mp (hbot ▸ hAQ)
      rw [hA, Subgroup.card_bot] at hAcard
      have : p ^ 1 ≤ p ^ Open.pRank p Q := Nat.pow_le_pow_right hp.pos hQr
      rw [← hAcard, pow_one] at this
      exact absurd this (by linarith [hp.two_le])
    rw [hQ]
    exact normalizer_zpowers_le_of_norm hp hD (hED (hQE g.2)) (hC _ (hQE g.2) hg1) hNorm
  · have hdvd : Nat.card Q ∣ p ^ 2 := hEcard ▸ Subgroup.card_dvd_of_le hQE
    obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hk2 : k = 2 := by
      rcases k with _ | _ | k
      · haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by simpa using hkc)).1
        exact absurd isCyclic_of_subsingleton hQc
      · exact absurd (isCyclic_of_prime_card (p := p) (by simpa using hkc)) hQc
      · omega
    have hQeq : Q = E := Subgroup.eq_of_le_of_card_ge hQE (by rw [hEcard, hkc, hk2])
    rw [hQeq]
    exact hNE

theorem not_two_dvd_index_inf_of_coprime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B R L : Subgroup G}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo B R) (hBp : IsPGroup p B)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hpL : ¬ p ∣ Nat.card L) : ¬ 2 ∣ ((L ⊓ R).subgroupOf L).index := by
  obtain ⟨hR2, hBR, hmax⟩ := hR
  set D := L ⊔ R with hD
  have hRD : R ≤ D := le_sup_right
  have hidx := index_sup_eq_index_inf hRL
  rw [← hidx]
  have hpD : ¬ p ∣ Nat.card D := by
    have hcm := Subgroup.card_mul_index (R.subgroupOf D)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card (R.subgroupOf D) = 2 ^ n :=
      (hR2.comap_subtype (K := D)).exists_card_eq
    rw [hidx, hn] at hcm
    rw [← hcm]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact hpL (h.trans (Subgroup.index_dvd_card _))
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBL hb),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBR hb)]
  obtain ⟨S, ⟨hSD, hS2, hSmax⟩, hRS, hBS⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp Nat.prime_two hBp hpD hBD hRD hR2 hBR
  have hSR : S = R := hmax S hS2 hBS hRS
  subst hSR
  obtain ⟨T₀, hT₀⟩ := (hR2.comap_subtype (K := D)).exists_le_sylow
  have hT₀D : (T₀ : Subgroup D).map D.subtype ≤ D := Subgroup.map_subtype_le _
  have hRT : S ≤ (T₀ : Subgroup D).map D.subtype := fun x hx =>
    ⟨⟨x, hRD hx⟩, hT₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have heq := hSmax _ hT₀D (T₀.isPGroup'.map D.subtype) hRT
  have e : S.subgroupOf D = (T₀ : Subgroup D) := by
    rw [← heq]
    exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
  rw [e]
  exact T₀.not_dvd_index

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.commute_of_czElt (hd : D1OneSmall3Data p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) {x : G} (hx : x ∈ d1LiftX p H R K) : x * z = z * x := by
  have hp := hd.cfg.red.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hzR, -, hzH, hzc⟩ := hz
  obtain ⟨x', ⟨hxR, hxK⟩, rfl⟩ := hx
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hSp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp
    (primeComplementCore (G := H) p)
    (hp.coprime_iff_not_dvd.mp (primeComplementCore_coprime p)) _ hSp
  set zH : H := ⟨z, hzH⟩
  have hzR' : zH ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hzR
  have hcomm : π (x' * zH) = π (zH * x') := by
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hzc _ hxK)
  have h := hinj (a₁ := ⟨x' * zH, (R.subgroupOf H).mul_mem hxR hzR'⟩)
    (a₂ := ⟨zH * x', (R.subgroupOf H).mul_mem hzR' hxR⟩) (Subtype.ext (by exact hcomm))
  have h' := congrArg (fun y : R.subgroupOf H => ((y : H) : G)) h
  simpa using h'

theorem D1OneSmall3Data.not_isCyclic_X (hd : D1OneSmall3Data p P M H R Rbar K) :
    ¬ IsCyclic (d1LiftX p H R K) := by
  intro hc
  apply hd.noncyclic
  rw [← map_d1LiftX_eq_inf hd]
  haveI : IsCyclic ((d1LiftX p H R K).subgroupOf H) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (d1LiftX_le_H p H R K)).symm.toMonoidHom
      (MulEquiv.surjective _)
  exact isCyclic_of_surjective _
    ((QuotientGroup.mk' (primeComplementCore (G := H) p)).subgroupMap_surjective _)

theorem D1OneSmall3Data.isAGLQ_X_of_centralizer (hd : D1OneSmall3Data p P M H R Rbar K)
    (hCX : ∀ a ∈ d1LiftX p H R K, orderOf a = p →
      (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
      Subgroup.centralizer ({a} : Set G) ≤ M) :
    IsAGLQ p M (d1LiftX p H R K) := by
  have hp := hd.cfg.red.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hd.cfg.red.ne_two
  have he := hd.cfg.ext.toD1Escape
  have hRM : R ≤ M := he.le_M
  have hRP : R ≤ (P : Subgroup G) := he.le_P
  set X := d1LiftX p H R K with hXdef
  have hXR : X ≤ R := d1LiftX_le p H R K
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le hXR
  obtain ⟨E, hEX, hE, hEcard⟩ :=
    CFSG.Goldschmidt.G63.exists_isElemAbelian_card_sq hp hp2 hXp hd.not_isCyclic_X
  obtain ⟨z, hz, hzX⟩ := hd.exists_czElt
  have hzp : z ^ p = 1 := hz.2.1 ▸ pow_orderOf_eq_one z
  have hzc : ∀ e ∈ E, e * z = z * e := fun e he => hd.commute_of_czElt hz (hEX he)
  set D := E ⊔ Subgroup.zpowers z with hDdef
  obtain ⟨hD, hDcard⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hEcard hE.2 hzp
    (fun h => hzX (hEX h)) hzc
  have hDR : D ≤ R := sup_le (hEX.trans hXR) (Subgroup.zpowers_le.mpr hz.1)
  have hD3 : 3 ≤ Open.pRank p D := CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_rfl hD hDcard
  have hDQ : IsAGLQ p M D := ⟨hDR.trans hRM, hd.cfg.ext.isPGroup.to_le hDR,
    Or.inl (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact hD3)⟩
  have hNorm : ∀ B : Subgroup G, D ≤ B → B ≤ M → IsPGroup p B →
      Subgroup.normalizer (B : Set G) ≤ M := fun B hDB hBM hBp =>
    normalizer_le_of_isAGLQ hd.cfg.ext
      ⟨hBM, hBp, Or.inl (by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact hD3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hDB))⟩
  have hNE : Subgroup.normalizer (E : Set G) ≤ M := by
    refine (weakCore_le_iff p (P : Subgroup G) M).mp hd.cfg.ext.weakCore_le E
      ((hEX.trans hXR).trans hRP)
      (CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_rfl hE hEcard) ?_
    refine hD3.trans (CFSG.SectionRank.pRank_mono hp.one_lt (sup_le le_sup_left ?_))
    refine le_sup_of_le_right (Subgroup.zpowers_le.mpr ⟨hRP hz.1, ?_⟩)
    exact Subgroup.mem_centralizer_iff.mpr fun e he => hzc e he
  have hC : ∀ a ∈ E, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ M := by
    intro a ha ha1
    have haD : a ∈ D := le_sup_left (a := E) ha
    have hDC : D ≤ Subgroup.centralizer ({a} : Set G) := fun d hdD =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val ((isMulCommutative_iff.mp hD.1) ⟨d, hdD⟩ ⟨a, haD⟩))
    exact hCX a (hEX ha) (orderOf_eq_prime (hE.2 a ha) ha1) ⟨D, hDC, hDQ⟩
  exact ⟨hXR.trans hRM, hXp, Or.inr ⟨E, hEX, hE, hEcard,
    gamma_one_le_of_norm hp hE hEcard hD le_sup_left hNE hC hNorm⟩⟩

theorem D1OneSmall3Data.isAGLQ_X_of_tenFourteen (h1014 : AGL81TenFourteenThree G)
    (hd : D1OneSmall3Data p P M H R Rbar K) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hpL : p ∣ Nat.card L)
    (hXL : ∀ b ∈ d1LiftX p H R K, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) :
    IsAGLQ p M (d1LiftX p H R K) := by
  refine hd.isAGLQ_X_of_centralizer fun a ha hao hU => ?_
  by_contra hCa
  have hXM : d1LiftX p H R K ≤ M := (d1LiftX_le p H R K).trans hd.cfg.ext.toD1Escape.le_M
  exact h1014 p P M H R Rbar hd.cfg a (hXM ha) hao hCa hU L hL hpL (fun l hl => hXL a ha l hl)

theorem D1OneSmall3Data.prime_dvd_card_of_block (hUP : KFactUPrimeSmall)
    (hsec : SporSectionFacts3) (hNo2 : KFactSmallNoTwo) (hCent : KFactSmallCentNoTwo)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal) (hmod : StmtKlingenModel)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hd : D1OneSmall3Data p P M H R Rbar K)
    (hL34 : ¬ (p = 3 ∧ IsLinThreeFour K)) (hih : D1KappaIH p M H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal) :
    p ∣ Nat.card L := by
  by_contra hpL
  have hp := hd.cfg.red.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hF : ¬ (p = 5 ∧ IsFi22 K) := fun h => hd.false_of_isFi22 hsec h.2
  have hph := hd.toPhaseThree hUP hL34 hF
  have h93 := nineThree_of_oneSmall3 hd
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  have hKX : ¬ K ≤ d1X0 p M H :=
    (hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc).2
  have hext := hd.cfg.ext
  have hfac : AGLCompetitorFactorAt p M H K R :=
    factorAt_of_kMax (d1KMaxR_of_ih hext (fun N R' hN hlt => hih P M N R' hN hlt) le_rfl)
      (hyp917R_of_ext_self hext
        (hd.hyp917Ext_native h3 hother hSch hk hmod (d1LiftX_le p H R K)))
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  exact false_of_sylow_base_of_factorAtB hph hCGT
    (fun M' Y hM' hY hYs hX => hD2 G hph.glob M' Y hM' hY hYs hX) hKX
    (D1Escape.core_map_le hext.toD1Escape) h93.factor hfac h93.plusCore_le hL hLn
    hext.isPGroup hext.toD1Escape.le_H hext.toD1Escape.le_M
    (b3_of_oneSmall3 hNo2 hCent hd hL34 hF)
    fun RB hRB _ _ hRBM => not_two_dvd_index_inf_of_coprime hp hd.cfg.red.ne_two hRB
      hext.isPGroup (hRBM.trans hMn) (hext.toD1Escape.le_M.trans hMn) hpL

section Residues

variable (G) in
@[expose] def D1SmallRankTwoFactorX : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M →
    AGLRankTwoFactorAt p M H (d1LiftX p H R K) K

variable (G) in
@[expose] def D1SmallBlockX : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M →
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ (L.subgroupOf M).Normal ∧
      ∀ b ∈ d1LiftX p H R K, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M

theorem d1SmallCentralBaseX_of_parts (hUP : KFactUPrimeSmall) (hsec : SporSectionFacts3)
    (hNo2 : KFactSmallNoTwo) (hCent : KFactSmallCentNoTwo) (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (h1014 : AGL81TenFourteenThree G)
    (h2 : D1SmallRankTwoFactorX G) (hB : D1SmallBlockX G) : D1SmallCentralBaseX G := by
  intro p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz
  obtain ⟨L, hL, hLn, hXL⟩ := hB p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz
  have hL34 : ¬ (p = 3 ∧ IsLinThreeFour K) := fun h => hexc ⟨h.1, Or.inl h.2⟩
  have hpL := hd.prime_dvd_card_of_block hUP hsec hNo2 hCent h3 hother hSch hk hmod hCGT hD2 hL34
    hih hL hLn
  exact ⟨hd.isAGLQ_X_of_tenFourteen h1014 hL hpL hXL,
    h2 p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz, L, hL, hLn, hXL⟩

theorem D1OneSmall3Data.noPPrime (hd : D1OneSmall3Data p P M H R Rbar K) :
    ∀ V : Subgroup K, V.Normal → p.Coprime (Nat.card V) → V = ⊥ := by
  intro V hV hcop
  obtain ⟨hKs, -⟩ := hd.toCore.isSimpleGroup
  haveI := hKs
  have hp := hd.cfg.red.prime
  haveI : Fact p.Prime := ⟨hp⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h | h
  · exact h
  · exfalso
    set Q := ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p))
    have hQp : IsPGroup p Q := Rbar.isPGroup'.to_le inf_le_left
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card Q = p ^ n := hQp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hn).1
      exact hd.noncyclic isCyclic_of_subsingleton
    have hdvd : Nat.card Q ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
    have hpV : p ∣ Nat.card V := by
      rw [h, Subgroup.card_top]
      exact (dvd_pow_self p hn0).trans (hn ▸ hdvd)
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpV)

variable (G) in
@[expose] def D1SmallRankTwoAtX : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M → IsAGLQ p M (d1LiftX p H R K) →
    ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → d1LiftX p H R K ≤ N →
      AGLCovers p H N K → d1LiftX p H R K ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) →
      (T = d1LiftX p H R K ∨ Open.pRank p T ≤ 2) → Hyp93At p M N ∧ Hyp917At p M H N K

variable (G) in
@[expose] def D1SmallRankTwoKappaX : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M → IsAGLQ p M (d1LiftX p H R K) →
    ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → d1LiftX p H R K ≤ N →
      AGLCovers p H N K → d1LiftX p H R K ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) →
      (T = d1LiftX p H R K ∨ Open.pRank p T ≤ 2) → d1Kappa p M N ≤ d1Kappa p M H

@[expose] def KappaMaxAt (p : ℕ) (M H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (B : Subgroup G) : Prop :=
  ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N → AGLCovers p H N K →
    d1Kappa p M N ≤ d1Kappa p M H

theorem factorAt_of_kappaMaxAt {M H B : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hat : ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N → AGLCovers p H N K →
      Hyp93At p M N ∧ Hyp917At p M H N K)
    (hKp : ∀ V : Subgroup K, V.Normal → p.Coprime (Nat.card V) → V = ⊥)
    (hκ : d1Kappa p M H ≤ Nat.card K) (hmax : KappaMaxAt p M H K B) :
    AGLCompetitorFactorAt p M H K B := by
  intro N hN hNM hBN hcov
  obtain ⟨h93, h917⟩ := hat N hN hNM hBN hcov
  obtain ⟨W, hW, -, heq | hfac⟩ := h917.toEq hKp hκ (hmax N hN hNM hBN hcov)
  · exact factor_of_map_eq h93 hW heq.ge
  · exact hfac

theorem D1OneSmall3Data.rankTwoFactorX_of_at (hd : D1OneSmall3Data p P M H R Rbar K)
    (hat : ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → d1LiftX p H R K ≤ N →
      AGLCovers p H N K → d1LiftX p H R K ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) →
      (T = d1LiftX p H R K ∨ Open.pRank p T ≤ 2) → Hyp93At p M N ∧ Hyp917At p M H N K)
    (hκ : ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → d1LiftX p H R K ≤ N →
      AGLCovers p H N K → d1LiftX p H R K ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) →
      (T = d1LiftX p H R K ∨ Open.pRank p T ≤ 2) → d1Kappa p M N ≤ d1Kappa p M H) :
    AGLRankTwoFactorAt p M H (d1LiftX p H R K) K := by
  refine aglRankTwoFactorAt_of_at fun N T hN hNM hXN hcov hXT hTN hTM hT hmax hor => ?_
  obtain ⟨h93, h917⟩ := hat N T hN hNM hXN hcov hXT hTN hTM hT hmax hor
  exact ⟨h93, h917.toEq hd.noPPrime hd.d1Kappa_le_card
    (hκ N T hN hNM hXN hcov hXT hTN hTM hT hmax hor)⟩

variable (G) in
@[expose] def D1SmallBlockX3 : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M →
    p = 3 → ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ (L.subgroupOf M).Normal ∧
      ∀ b ∈ d1LiftX p H R K, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M

variable (G) in
@[expose] def D1SmallCentralizerXOdd : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M →
    p ≠ 3 → ∀ a ∈ d1LiftX p H R K, orderOf a = p →
      (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
      Subgroup.centralizer ({a} : Set G) ≤ M

variable (G) in
@[expose] def D1SmallBlockXDatum : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M →
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ (L.subgroupOf M).Normal ∧
      IsAGLBlockDatum M H (d1LiftX p H R K) L

theorem d1SmallCentralBaseXJ_of_parts (hUP : KFactUPrimeSmall) (hsec : SporSectionFacts3)
    (hNo2 : KFactSmallNoTwo) (hCent : KFactSmallCentNoTwo) (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (h1014 : AGL81TenFourteenThree G) (hat : D1SmallRankTwoAtX G)
    (hκ : D1SmallRankTwoKappaX G) (hB3 : D1SmallBlockX3 G)
    (hOdd : D1SmallCentralizerXOdd G) (hdat : D1SmallBlockXDatum G) :
    D1SmallCentralBaseXJ G := by
  intro p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz
  have hfac : IsAGLQ p M (d1LiftX p H R K) → AGLRankTwoFactorAt p M H (d1LiftX p H R K) K :=
    fun hXQ => hd.rankTwoFactorX_of_at
      (hat p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz hXQ)
      (hκ p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz hXQ)
  by_cases hp3 : p = 3
  · obtain ⟨L, hL, hLn, hXL⟩ := hB3 p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz hp3
    have hL34 : ¬ (p = 3 ∧ IsLinThreeFour K) := fun h => hexc ⟨h.1, Or.inl h.2⟩
    have hpL := hd.prime_dvd_card_of_block hUP hsec hNo2 hCent h3 hother hSch hk hmod hCGT hD2
      hL34 hih hL hLn
    have hXQ := hd.isAGLQ_X_of_tenFourteen h1014 hL hpL hXL
    exact ⟨hXQ, hfac hXQ, L, hL, hLn, Or.inl hXL⟩
  · have hXQ := hd.isAGLQ_X_of_centralizer
      (hOdd p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz hp3)
    exact ⟨hXQ, hfac hXQ, hdat p P M H R Rbar K hd hexc hC hih huniq z hz hPz hCz⟩

end Residues

end CFSG.LocalAnalysis.RankThreeTheoremC
