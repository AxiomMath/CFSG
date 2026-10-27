module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Data
import CFSG.LocalAnalysis.AGLEmbeddingD2.U3MSide
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisTools

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
  CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

structure D2HeisBorel (p : ℕ) {X : Type*} [Group X] (R : Sylow p X) (X₀ K : Subgroup X) :
    Prop where
  le_K : (R : Subgroup X) ≤ K
  card : Nat.card (R : Subgroup X) = p ^ 3
  normalizer_eq : Subgroup.normalizer ((R : Subgroup X) : Set X) = X₀
  centralizer_le : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R
  card_center : Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
    Subgroup X) = p
  commutator_eq : ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
    (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X)
  pow_eq_one : ∀ r ∈ (R : Subgroup X), r ^ p = 1
  dichotomy : ∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) →
    W = ⊥ ∨ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ W
  le_of_isPGroup : ∀ W : Subgroup X, X₀ ≤ Subgroup.normalizer (W : Set X) → IsPGroup p W → W ≤ R
  isSolvable : Group.IsSolvable X₀
  primeCore : primeComplementCore (G := X₀) p = ⊥
  lines : ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
    ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
    (∀ x ∈ (R : Subgroup X),
      ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
        t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
    (∀ x ∈ (R : Subgroup X),
      ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
        t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
    ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup X,
      (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
        F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
          t ^ j ∉ Subgroup.normalizer (F : Set X)

@[expose] def D2HeisBorelAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → D2HeisBorel p R X₀ K

structure D2HeisOver (p : ℕ) {X : Type*} [Group X] (R : Sylow p X) (X₀ : Subgroup X) : Prop where
  card : Nat.card (R : Subgroup X) = p ^ 3
  normalizer_le : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀
  centralizer_le : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R
  card_center : Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
    Subgroup X) = p
  commutator_eq : ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
    (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X)
  pow_eq_one : ∀ r ∈ (R : Subgroup X), r ^ p = 1
  dichotomy : ∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) →
    W = ⊥ ∨ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ W
  primeCore : primeComplementCore (G := X₀) p = ⊥
  lines : ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
    ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
    (∀ x ∈ (R : Subgroup X),
      ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
        t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
    (∀ x ∈ (R : Subgroup X),
      ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
        t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
    ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup X,
      (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
        F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
          t ^ j ∉ Subgroup.normalizer (F : Set X)

theorem D2HeisBorel.toOver {p : ℕ} {X : Type*} [Group X] {R : Sylow p X} {X₀ K : Subgroup X}
    (hB : D2HeisBorel p R X₀ K) : D2HeisOver p R X₀ :=
  ⟨hB.card, hB.normalizer_eq.le, hB.centralizer_le, hB.card_center, hB.commutator_eq,
    hB.pow_eq_one, hB.dichotomy, hB.primeCore, hB.lines⟩

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.exists_conj_eq_mul_of_map [Fact p.Prime] (h : D2Escape p P M A H R) {t x w : H}
    (htN : (t : G) ∈ Subgroup.normalizer (R : Set G)) (hx : (x : G) ∈ R) (hw : (w : G) ∈ R)
    (n : ℕ) {zb : H ⧸ primeComplementCore (G := H) p}
    (hzb : zb ∈ ((R ⊓ Subgroup.centralizer (R : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (heq : QuotientGroup.mk' (primeComplementCore (G := H) p) (t ^ n * x * (t ^ n)⁻¹) =
      QuotientGroup.mk' (primeComplementCore (G := H) p) w * zb) :
    ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
      (t : G) ^ n * x * ((t : G) ^ n)⁻¹ = w * z := by
  obtain ⟨z, hz, hzc⟩ := hzb
  refine ⟨(z : G), Subgroup.mem_subgroupOf.mp hz, ?_⟩
  have hmem1 : (((t ^ n * x * (t ^ n)⁻¹ : H)) : G) ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htN _) x).mp hx
  have hmem2 : (((w * z : H)) : G) ∈ R := R.mul_mem hw (Subgroup.mem_subgroupOf.mp hz).1
  exact congrArg Subtype.val (eq_of_mk_eq_of_mem h.isPGroup hmem1 hmem2 (by rw [heq, map_mul, hzc]))

theorem D2Escape.toPair_of_over [Fact p.Prime] (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hB : D2HeisOver p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))) :
    AGLPair p M H R :=
  h.toPair hglob (h.twoCore_inf_eq_of_primeCore_inf_eq (h.primeCore_inf_eq_iff.mpr hB.primeCore))

theorem D2Escape.toPair_of_borel [Fact p.Prime] (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hB : D2HeisBorel p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K) :
    AGLPair p M H R :=
  h.toPair_of_over hglob hB.toOver

theorem D2Escape.heisDataCore_of_over [Fact p.Prime] (h : D2Escape p P M A H R)
    (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hB : D2HeisOver p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))) :
    D2HeisDataCore p M H R (R ⊓ Subgroup.centralizer (R : Set G)) := by
  have hp : p.Prime := h.prime
  have hRH : R ≤ H := h.le_H
  have hRp : IsPGroup p R := h.isPGroup
  have hRN : R ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hRp (glbPrimeCore_coprime p H)
  have hcardR : Nat.card R = p ^ 3 := by
    rw [← h.card_map_eq le_rfl, ← hRbar]
    exact hB.card
  have hZb : ((R ⊓ Subgroup.centralizer (R : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [map_inf_centralizer_eq hRH hRp, hRbar]
  have hcardZ : Nat.card (R ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p := by
    rw [← h.card_map_eq inf_le_left, hZb]
    exact hB.card_center
  have hcommR : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set G) := by
    have hmap : ((⁅R, R⁆ : Subgroup G).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
        ((R ⊓ Subgroup.centralizer (R : Set G)).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
      rw [hZb, ← hB.commutator_eq, hRbar, ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRH,
        Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self R).trans hRH)]
    exact le_antisymm (le_of_map_mk_le hRH hRp (Subgroup.commutator_le_self R) inf_le_left hmap.le)
      (le_of_map_mk_le hRH hRp inf_le_left (Subgroup.commutator_le_self R) hmap.ge)
  have hπ : ∀ (x : G) (hx : x ∈ R),
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hRH hx⟩ ∈ (Rbar : Subgroup _) :=
    fun x hx => hRbar ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hpowR : ∀ r ∈ R, r ^ p = 1 := by
    intro u hu
    have h1 := hB.pow_eq_one _ (hπ u hu)
    have h2 : ((⟨u, hRH hu⟩ ^ p : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_pow, h1]
    have h3 : ((⟨u, hRH hu⟩ ^ p : H) : G) ∈ R ⊓ GLBPrimeCore p H :=
      ⟨by simpa using R.pow_mem hu p, h2⟩
    rw [hRN, Subgroup.mem_bot] at h3
    simpa using h3
  have hlines : ∃ t ∈ H ⊓ M, t ∈ Subgroup.normalizer (R : Set G) ∧
      ∃ m lam n : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ n ∧
      (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
        t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
      (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
        t ^ n * x * (t ^ n)⁻¹ = x⁻¹ * z) ∧
      ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup G,
        R ⊓ Subgroup.centralizer (R : Set G) ≤ F → F ≤ R → F.relIndex R = p →
          t ^ j ∉ Subgroup.normalizer (F : Set G) := by
    obtain ⟨c, hcN, m, lam, n, hm2, hlam, hn6, hscal, hinv, hline⟩ := hB.lines
    have hcX₀ : c ∈ ((H ⊓ M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := hB.normalizer_le hcN
    obtain ⟨t, htM, htN, htc⟩ := h.exists_lift_normalizer hcX₀ (hRbar ▸ hcN)
    refine ⟨(t : G), ⟨t.2, htM⟩, htN, m, lam, n, hm2, hlam, hn6, fun x hx => ?_, fun x hx => ?_,
      fun j hj0 hjm F hZF hFR hidx => ?_⟩
    · obtain ⟨zb, hzb, hzeq⟩ := hscal _ (hπ x hx)
      rw [← hZb] at hzb
      exact h.exists_conj_eq_mul_of_map (x := ⟨x, hRH hx⟩) (w := ⟨x, hRH hx⟩ ^ lam) htN hx
        (R.pow_mem hx lam) m hzb (by simpa only [map_mul, map_inv, map_pow, htc] using hzeq)
    · obtain ⟨zb, hzb, hzeq⟩ := hinv _ (hπ x hx)
      rw [← hZb] at hzb
      exact h.exists_conj_eq_mul_of_map (x := ⟨x, hRH hx⟩) (w := ⟨x, hRH hx⟩⁻¹) htN hx
        (R.inv_mem hx) n hzb (by simpa only [map_mul, map_inv, map_pow, htc] using hzeq)
    · intro hFn
      refine hline j hj0 hjm
        ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) ?_ ?_ ?_ ?_
      · rw [← hZb]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hZF)
      · rw [hRbar]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hFR)
      · rw [hRbar, h.relIndex_map_eq hFR]
        exact hidx
      · rw [← htc, ← map_pow]
        exact map_mk_le_normalizer_map_mk (Subgroup.zpowers_le.mpr hFn)
          ⟨t ^ j, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _), rfl⟩
  have hCR' : Subgroup.centralizer (((R.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [← hRbar]
    exact hB.centralizer_le
  refine ⟨h.toPair_of_over hglob hB, hcardR, ⟨hcardZ, hcommR, hpowR⟩, hlines, ?_, ?_,
    centralizer_le_of_map (X := R) fun y hy => hCR' hy.2,
    pRank_inf_le_of_pRank_top_le hp hK.pRank_top_eq.le⟩
  · obtain ⟨t, htK, htN, m, -, -, hm, -, -, -, -, hline⟩ := hlines
    exact fun V hZV hVR hV => eq_or_eq_of_lines hp hm hcardR hcardZ hline hZV hVR
      (hV ⟨htK, htN⟩)
  · exact fun Y hY hYN => le_glbPrimeCore_or_le_of_forall h.primeCore_le (inf_le_left.trans hRH)
      (hRp.to_le inf_le_left) (fun W hW hWn => by rw [hZb]; exact hB.dichotomy W hW hWn) hY hYN

theorem D2Escape.heisData_of_borel [Fact p.Prime] (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hB : D2HeisBorel p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K) :
    D2HeisData p M H R (R ⊓ Subgroup.centralizer (R : Set G)) :=
  ⟨h.heisDataCore_of_over hglob hRbar hK hB.toOver,
    fun _ hL hLL => le_glbPrimeCore_of_perfect hB.isSolvable hL hLL⟩

theorem inf_centralizer_le_of_borel
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hB : D2HeisBorel p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K) :
    (H ⊓ M) ⊓ Subgroup.centralizer (R : Set G) ≤ R ⊔ GLBPrimeCore p H := by
  have hCX : Subgroup.centralizer (((R.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [← hRbar]
    exact hB.centralizer_le
  rintro y ⟨hyHM, hyC⟩
  refine centralizer_le_of_map (inf_le_right.trans hCX) y hyHM fun x hx => ?_
  have hc := Subgroup.mem_centralizer_iff.mp hyC x hx
  rw [← hc, show x * y * y⁻¹ * x⁻¹ = 1 by group]
  exact one_mem _

theorem D2Escape.aglJConfig_of_borel [Fact p.Prime] (h : D2Escape p P M A H R)
    (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hB : D2HeisBorel p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) : AGLJConfig p M H R R :=
  AGLJConfig.of_pair (h.toPair_of_borel hglob hB) hRQ (inf_centralizer_le_of_borel hRbar hB)

theorem D2Escape.normal_sup_of_heisBorel [Fact p.Prime] (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h : D2Escape p P M A H R) (hglob : AGLGlobal G) (hD1 : D1For G) (hX : NoXBlockFor G)
    (hp5 : 5 ≤ p)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hB : D2HeisBorel p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K) :
    ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
  have hdata := h.heisData_of_borel hglob hRbar hK hB
  have hRK : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ≤ K := by
    rw [← hRbar]
    exact hB.le_K
  refine hdata.normal_sup_of_components hD1 hp5 h84 hX fun Lbar hLbar => ?_
  obtain ⟨L, hL2, hbar, hL⟩ := hdata.pair.exists_weakSBlock_or_le_inf hLbar
  rw [← hbar]
  rcases hL with hblock | hle
  · exact hdata.barM_le_centralizer_of_weakSBlock hD1 h84 h85 h86 h93 hX hK2 hC3 hK5 hKin hKP
      hC3p hK5p hp5 hblock
  · exact h.barM_le_centralizer_of_le_inf_of_simple hdata.pair hdata.perfect_le hK le_rfl hRK
      hD1 hp5 hα hSch hL2 hle

end Escape

@[expose] def D2HeisMSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Sylow p G) (M A H R : Subgroup G),
      D2Escape p P M A H R → D2EscapeMax p P M R → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      D2HeisBorel p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal

theorem d2HeisMSide_of (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2HeisMSide := by
  intro G _ _ hglob hD1 p _ hp5 P M A H R hesc _ _ Rbar K hRbar hK hB
  exact hesc.normal_sup_of_heisBorel hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    hglob.toAGLGlobal hD1 (hD2.noXBlockFor hglob.toD1Global) hp5 hRbar hK hB

end CFSG.AGLEmbeddingD2
