module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisCase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Case
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TorusData
import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsLeaves
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

structure D2TorusBorel (p : ℕ) {X : Type*} [Group X] (R : Sylow p X) (A X₀ K : Subgroup X) :
    Prop where
  eq_A : (R : Subgroup X) = A
  le_K : A ≤ K
  dichotomy : ∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) →
    W = ⊥ ∨ A ≤ W
  centralizer_le : X₀ ⊓ Subgroup.centralizer (A : Set X) ≤ R
  le_of_isPGroup : ∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) →
    IsPGroup p W → W ≤ A
  isSolvable : Group.IsSolvable X₀
  torus : ∃ t, t ∈ Subgroup.normalizer (A : Set X) ∧
    ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
    (∀ x ∈ A, t ^ m * x * (t ^ m)⁻¹ = x ^ lam) ∧ (∀ x ∈ A, t ^ e * x * (t ^ e)⁻¹ = x⁻¹) ∧
    ∀ k : ℕ, 0 < k → k < m → ∀ Y₀ : Subgroup X, Y₀ ≤ A → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set X)

@[expose] def D2TorusBorelAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → D2TorusBorel p R A X₀ K

theorem D2TorusBorel.xSurvivor {p : ℕ} {X : Type} [Group X] {R : Sylow p X}
    {A X₀ K : Subgroup X} (h : D2TorusBorel p R A X₀ K) : D2XSurvivor (R : Subgroup X) A X₀ :=
  ⟨h.dichotomy, h.centralizer_le⟩

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.torusData_of_borel [Fact p.Prime] (h : D2Escape p P M A H A)
    (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hB : D2TorusBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K) :
    D2TorusData p M H A A := by
  have hp : p.Prime := h.prime
  have hAH : A ≤ H := h.A_le_H
  have hAp : IsPGroup p A := h.isPGroup
  have hsurv : AGLSurvivorData p M H A A :=
    h.survivorData_of_reduced hglob hB.dichotomy (hB.centralizer_le.trans hRbar.le)
  have hπ : ∀ (x : G) (hx : x ∈ A), QuotientGroup.mk' (primeComplementCore (G := H) p)
      ⟨x, hAH hx⟩ ∈ (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    fun x hx => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have htorus : ∃ t ∈ H ⊓ M, t ∈ Subgroup.normalizer (A : Set G) ∧
      ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
      (∀ x ∈ A, t ^ m * x * (t ^ m)⁻¹ = x ^ lam) ∧ (∀ x ∈ A, t ^ e * x * (t ^ e)⁻¹ = x⁻¹) ∧
      ∀ k, 0 < k → k < m → ∀ Y₀ : Subgroup G, Y₀ ≤ A → Nat.card Y₀ = p →
        t ^ k ∉ Subgroup.normalizer (Y₀ : Set G) := by
    obtain ⟨c, hcN, m, lam, n, hm2, hlam, hn6, hscal, hinv, hline⟩ := hB.torus
    obtain ⟨t, htM, htN, htc⟩ := h.exists_lift_normalizer
      (hK.normalizer_le_of_le_A _ le_rfl hK.A_ne_bot hcN) hcN
    have key : ∀ (n : ℕ) (x w : H), (x : G) ∈ A → (w : G) ∈ A →
        c ^ n * QuotientGroup.mk' (primeComplementCore (G := H) p) x * (c ^ n)⁻¹ =
          QuotientGroup.mk' (primeComplementCore (G := H) p) w →
        (t : G) ^ n * x * ((t : G) ^ n)⁻¹ = w := by
      intro n x w hx hw hxw
      have hmem : (((t ^ n * x * (t ^ n)⁻¹ : H)) : G) ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htN n) x).mp hx
      exact congrArg Subtype.val (eq_of_mk_eq_of_mem hAp hmem hw
        (by simpa only [map_mul, map_inv, map_pow, htc] using hxw))
    refine ⟨(t : G), ⟨t.2, htM⟩, htN, m, lam, n, hm2, hlam, hn6, fun x hx => ?_, fun x hx => ?_,
      fun k hk0 hkm Y hYA hYp hYn => ?_⟩
    · exact key m ⟨x, hAH hx⟩ (⟨x, hAH hx⟩ ^ lam) hx (A.pow_mem hx lam)
        (by rw [map_pow]; exact hscal _ (hπ x hx))
    · exact key n ⟨x, hAH hx⟩ ⟨x, hAH hx⟩⁻¹ hx (A.inv_mem hx)
        (by rw [map_inv]; exact hinv _ (hπ x hx))
    · refine hline k hk0 hkm
        ((Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H hYA))
        (by rw [h.card_map_eq hYA]; exact hYp) ?_
      rw [← htc, ← map_pow]
      exact map_mk_le_normalizer_map_mk (Subgroup.zpowers_le.mpr hYn)
        ⟨t ^ k, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _), rfl⟩
  exact ⟨hsurv.pair, rfl, h.elem, h.card_A, htorus, hsurv.normal_dichotomy,
    fun Y hY hYN hYp => le_sup_glbPrimeCore_of_forall (fun W hW hWn hWp =>
      hB.le_of_isPGroup W hW hWn hWp) hY hYN hYp,
    hsurv.centralizer_le, pRank_inf_le_of_pRank_top_le hp hK.pRank_top_eq.le,
    fun L hL hLL => le_glbPrimeCore_of_perfect hB.isSolvable hL hLL⟩

theorem D2Escape.pCore_ne_bot_of_torusBorel [Fact p.Prime] (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h : D2Escape p P M A H A) (hglob : AGLGlobal G) (hD1 : D1For G) (hX : NoXBlockFor G)
    (hp5 : 5 ≤ p)
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hB : D2TorusBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥ := by
  have hdata := h.torusData_of_borel hglob hRbar hK hB
  exact hdata.pCore_ne_bot_of_components hD1 hp5 h84 hX
    (fun L hL hLK => h.barM_le_centralizer_of_le_inf_of_simple hdata.pair
      hdata.perfect_le hK le_rfl hB.le_K hD1 hp5 hα hSch hL hLK)
    (fun L hL => hdata.barM_le_centralizer_of_weakSBlock hD1 h84 h85 h86 h93 hX hK2 hC3 hK5 hKin
      hKP hC3p hK5p hp5 hL)

end Escape

@[expose] def D2TorusMSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Sylow p G) (M A H : Subgroup G),
      D2Escape p P M A H A → D2EscapeMax p P M A → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      D2TorusBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

theorem d2TorusMSide_of (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2TorusMSide := by
  intro G _ _ hglob hD1 p _ hp5 P M A H hesc _ _ Rbar K hRbar hK hB
  exact hesc.pCore_ne_bot_of_torusBorel hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    hglob.toAGLGlobal hD1 (hD2.noXBlockFor hglob.toD1Global) hp5 hRbar hK hB

theorem D2Escape.survivorData_of_heisTorusLeavesFor {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M A H : Subgroup G} (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (HB TB : TauCeti.CFSGIndex → ℕ → Prop)
    (hHB : ∀ i, D2HeisBorelAt i (HB i)) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex, IsD2SeitzException p d.1 → ¬ HB (.lie d) p →
      ¬ TB (.lie d) p → D2IndexCaseFor p P M A A (.lie d))
    (hSpor : ∀ s : TauCeti.SporadicName, ¬ HB (.sporadic s) p → ¬ TB (.sporadic s) p →
      D2IndexCaseFor p P M A A (.sporadic s))
    (hglob : AGLGlobal G) (hesc : D2Escape p P M A H A) : AGLSurvivorData p M H A A := by
  have : Fact p.Prime := ⟨hesc.prime⟩
  obtain ⟨Rbar, K, hRbar, hK⟩ := hesc.almostSimple hglob
  have hnHB : ∀ i, HB i p → Nonempty (K ≃* i.Group) → False := fun i hiB he => by
    have hc := (hHB i _ p hiB Rbar _ _ K hK he).card
    rw [hRbar, hK.card_A] at hc
    have := Nat.pow_right_injective hK.prime.two_le hc
    omega
  have hX := hK.xSurvivor_of_cases hRbar hrank hL3
    (fun q hq hi => d2IndexCaseFor_cyclic q hq H hesc Rbar K hRbar hK hi)
    (fun s hi => by
      by_cases hB : HB (.sporadic s) p
      · exact (hnHB _ hB hi).elim
      by_cases hT : TB (.sporadic s) p
      · exact (hTB _ _ p hT Rbar _ _ K hK hi).xSurvivor
      · exact (hSpor s hB hT H hesc Rbar K hRbar hK hi).elim)
    fun d hchar ⟨e⟩ => by
      by_cases hexcp : IsD2SeitzException p d.1
      · by_cases hB : HB (.lie d) p
        · exact (hnHB _ hB ⟨e⟩).elim
        by_cases hT : TB (.lie d) p
        · exact (hTB _ _ p hT Rbar _ _ K hK ⟨e⟩).xSurvivor
        · exact (hexc d hexcp hB hT H hesc Rbar K hRbar hK ⟨e⟩).elim
      · exact (hK.false_of_seitzCross hS d e hchar hexcp).elim
  obtain ⟨hD, hC⟩ := hX
  exact hesc.survivorData_of_reduced hglob hD (hRbar ▸ hC)

theorem d2SurvivorsAll_of_heisTorusLeaves (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (HB TB : TauCeti.CFSGIndex → ℕ → Prop)
    (hHB : ∀ i, D2HeisBorelAt i (HB i)) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p => ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p) :
    D2SurvivorsAll := by
  intro G _ _ hglob hD1 p P M A H hesc hmax hβ
  exact hesc.survivorData_of_heisTorusLeavesFor hrank hL3 hS HB TB hHB hTB
    (fun d hd hB hT => (hexc d).for hglob hD1 ⟨hd, hB, hT⟩ hmax hβ)
    (fun s hB hT => (hSpor s).for hglob hD1 ⟨hB, hT⟩ hmax hβ) hglob.toAGLGlobal

theorem D2Escape.false_of_torusBorelFor {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M A H R : Subgroup G} (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hglob : AGLGlobal G) (hD1p : D1At G p)
    (hX : NoXBlockFor G) (h : D2Escape p P M A H R) (hmax : D2EscapeMax p P M R)
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hB : D2TorusBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hsurv : ∀ H' : Subgroup G, D2Escape p P M A H' A → AGLSurvivorData p M H' A A)
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) : False := by
  have hAR : A = R := h.A_eq_of_map_eq (hRbar.symm.trans hB.eq_A)
  subst hAR
  exact false_of_survivorsAt hglob hD1p h84 hCGT hX h hmax hsurv hO

theorem d2IndexCaseAt_of_torusBorel {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (hiB : D2TorusBorelAt i Pp) (hp5 : ∀ p, Pp p → 5 ≤ p) (hMS : D2TorusMSide)
    (hsurv : D2SurvivorsAll) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) : D2IndexCaseAt i Pp := by
  intro G _ _ hglob hD1 p hpc P M A H R hesc hmax hβ Rbar K hRbar hK he
  have : Fact p.Prime := ⟨hesc.prime⟩
  have hB := hiB _ p hpc Rbar _ _ K hK he
  have hAR : A = R := hesc.A_eq_of_map_eq (hRbar.symm.trans hB.eq_A)
  subst hAR
  exact hesc.false_of_torusBorelFor h84 hCGT hglob.toAGLGlobal (hD1.at hβ)
    (hD2.noXBlockFor hglob.toD1Global) hmax hRbar hB
    (fun H' h' => hsurv G hglob hD1 p P M A H' h' hmax hβ)
    (hMS G hglob hD1 p (hp5 p hpc) P M A H hesc hmax hβ Rbar K hRbar hK hB)

theorem d2ComponentCase_of_families' (hrank : KFactLieCharRank) (hS : D2SeitzCross)
    (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hAlt5 : D2AltFive) (hA6 : D2AltSixCase) (hThree : D2U3Three)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (TB : TauCeti.CFSGIndex → ℕ → Prop) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hTB5 : ∀ i p, TB i p → 5 ≤ p)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p => ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p) :
    D2ComponentCase := by
  have hsurv : D2SurvivorsAll :=
    d2SurvivorsAll_of_heisTorusLeaves hrank kFactLinThreeCore hS HB TB hHB hTB hexc hSpor
  have hMS : D2TorusMSide :=
    d2TorusMSide_of hα hSch h84 h85 h86 h93 hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p
  have hTBcase : ∀ i, D2IndexCaseAt i (TB i) := fun i =>
    d2IndexCaseAt_of_torusBorel (hTB i) (hTB5 i) hMS hsurv h84 hCGT hD2
  refine d2ComponentCase_of_heis hrank hS hSch hα h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP
    hC3p hK5p hAlt5 hA6 hThree HB hHB hHB5 (fun d => ?_) fun s => ?_
  · intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
    by_cases hT : TB (.lie d) p
    · exact hTBcase (.lie d) G hglob hD1 p hT P M A H R hesc hmax hβ Rbar K hRbar hK he
    · exact hexc d G hglob hD1 p ⟨hp.1, hp.2, hT⟩ P M A H R hesc hmax hβ Rbar K hRbar hK he
  · intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
    by_cases hT : TB (.sporadic s) p
    · exact hTBcase (.sporadic s) G hglob hD1 p hT P M A H R hesc hmax hβ Rbar K hRbar hK he
    · exact hSpor s G hglob hD1 p ⟨hp, hT⟩ P M A H R hesc hmax hβ Rbar K hRbar hK he

end CFSG.AGLEmbeddingD2
