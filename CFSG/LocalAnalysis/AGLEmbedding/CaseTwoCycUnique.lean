module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
import CFSG.GH74.Uniqueness.Section15HeringCyclic
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFPerfect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbUnique
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

theorem not_dvd_card_of_perfect_of_normalizer_le {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    (hnc : normalizer ((P : Subgroup K) : Set K) ≤ centralizer ((P : Subgroup K) : Set K)) :
    ¬ p ∣ Nat.card K := by
  have hker : (MonoidHom.transferSylow P hnc).ker = ⊤ := by
    refine top_unique ?_
    rw [← (Group.IsPerfect.commutator_eq_top : commutator K = ⊤)]
    refine commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have ha := (MonoidHom.transferSylow P hnc a).2
    have hb := (MonoidHom.transferSylow P hnc b).2
    exact Subtype.ext (mem_centralizer_iff.mp (hnc (le_normalizer ha)) _ hb).symm
  have h := MonoidHom.not_dvd_card_ker_transferSylow P hnc
  rwa [hker, card_top] at h

theorem mem_zpowers_of_commute_of_cyclic {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {W : Subgroup X}
    (hcyc : ∀ Q : Subgroup X, Q ≤ W → IsPGroup p Q → IsCyclic Q) {a b : X} (haW : a ∈ W)
    (hbW : b ∈ W) (hab : Commute a b) (hap : orderOf a = p) (hbp : orderOf b = p) :
    a ∈ zpowers b := by
  set Q := zpowers a ⊔ zpowers b with hQ
  have hAp : IsPGroup p (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hap, pow_one])
  have hBp : IsPGroup p (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbp, pow_one])
  have hAB : zpowers a ≤ normalizer (zpowers b : Set X) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    refine zpowers_le.mpr ?_
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact ((hab.zpow_right k).eq).symm
  have hQp : IsPGroup p Q := hAp.to_sup_of_normal_right' hBp hAB
  have hQle : Q ≤ W := sup_le (zpowers_le.mpr haW) (zpowers_le.mpr hbW)
  have hQc : IsCyclic Q := hcyc Q hQle hQp
  have hAQ : zpowers a ≤ Q := le_sup_left
  have hBQ : zpowers b ≤ Q := le_sup_right
  have h1 : (zpowers a).subgroupOf Q = (zpowers b).subgroupOf Q := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (subgroupOfEquivOfLe hAQ).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBQ).toEquiv, Nat.card_zpowers, Nat.card_zpowers,
      hap, hbp]
  have h2 : (⟨a, hAQ (mem_zpowers a)⟩ : Q) ∈ (zpowers b).subgroupOf Q := by
    rw [← h1]
    exact mem_subgroupOf.mpr (mem_zpowers a)
  exact mem_subgroupOf.mp h2

theorem false_of_commute_of_cyclic {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] {V₁ V₂ : Subgroup X} (h₁ : ⁅V₁, V₁⁆ = V₁)
    (hc : V₁ ≤ centralizer (V₂ : Set X)) (hd₁ : p ∣ Nat.card V₁) (hd₂ : p ∣ Nat.card V₂)
    (hcyc : ∀ Q : Subgroup X, Q ≤ V₁ ⊔ V₂ → IsPGroup p Q → IsCyclic Q) : False := by
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' (G := V₂) p hd₂
  have hb₀p : orderOf (b₀ : X) = p := by rw [Subgroup.orderOf_coe]; exact hb₀
  have hkey : ∀ a ∈ V₁, orderOf a = p → a ∈ zpowers (b₀ : X) := fun a ha hap =>
    mem_zpowers_of_commute_of_cyclic hcyc (le_sup_left (a := V₁) ha)
      (le_sup_right (b := V₂) b₀.2) (mem_centralizer_iff.mp (hc ha) _ b₀.2).symm hap hb₀p
  have hV₁ : Group.IsPerfect V₁ := Subgroup.isPerfect_iff.mpr h₁
  obtain ⟨Q₁⟩ : Nonempty (Sylow p V₁) := inferInstance
  have hQ₁c : IsCyclic (Q₁ : Subgroup V₁) := by
    have h := hcyc ((Q₁ : Subgroup V₁).map V₁.subtype)
      ((map_subtype_le _).trans le_sup_left) (Q₁.isPGroup'.map _)
    exact isCyclic_of_injective
      ((Q₁ : Subgroup V₁).equivMapOfInjective V₁.subtype V₁.subtype_injective).toMonoidHom
      (MulEquiv.injective _)
  obtain ⟨⟨r, hrQ⟩, hr⟩ := hQ₁c.exists_generator
  have hQr : (Q₁ : Subgroup V₁) = zpowers r := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr hrQ)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hr ⟨x, hx⟩)
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hne := Q₁.ne_bot_of_dvd_card hd₁
  obtain ⟨n, hn⟩ := Q₁.isPGroup'.exists_card_eq
  have hor : orderOf r = p ^ n := by
    rw [← Nat.card_zpowers, ← hQr, hn]
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    exact Subgroup.card_eq_one.mp (by rw [hn, pow_zero])
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have hr0 : orderOf r ≠ 0 := by rw [hor]; exact pow_ne_zero _ hp.out.ne_zero
  have hpd : p ∣ orderOf r := by
    rw [hor]
    exact dvd_pow_self p (Nat.succ_ne_zero b)
  have hpb : orderOf (r ^ p ^ b) = p := by
    have h := orderOf_pow_orderOf_div hr0 hpd
    rwa [hor, pow_succ, Nat.mul_div_cancel _ hp.out.pos] at h
  have hcen : ((r ^ p ^ b : V₁) : X) ∈ zpowers (b₀ : X) :=
    hkey _ (r ^ p ^ b).2 (by rw [Subgroup.orderOf_coe]; exact hpb)
  have hcen' : ∀ y : V₁, y * r ^ p ^ b = r ^ p ^ b * y := by
    intro y
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hcen
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (mem_centralizer_iff.mp (hc y.2) _ (V₂.zpow_mem b₀.2 k)).symm
  have hNC : normalizer ((zpowers (r ^ p ^ b) : Subgroup V₁) : Set V₁) ≤
      centralizer ((zpowers (r ^ p ^ b) : Subgroup V₁) : Set V₁) := by
    intro y _
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (hcen' y).symm k).eq)
  have hNR := CFSG.GH74.Uniqueness.Hering.normalizer_le_centralizer_of_cyclic Q₁ hQr hor hNC
  exact not_dvd_card_of_perfect_of_normalizer_le Q₁ hNR hd₁

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.isCyclic_of_le_component (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    {X : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hXp : IsPGroup p X) (hXL : X ≤ L) :
    IsCyclic X := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  have hTc : IsCyclic (T : Subgroup L) := by
    have h := hd.cyclic L hL
    rw [← hT] at h
    exact isCyclic_of_injective
      ((T : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom
      (MulEquiv.injective _)
  obtain ⟨T', hT'⟩ := (hXp.comap_subtype (K := L)).exists_le_sylow
  have hT'c : IsCyclic (T' : Subgroup L) :=
    isCyclic_of_injective (Sylow.equiv T' T).toMonoidHom (MulEquiv.injective _)
  have hXc : IsCyclic (X.subgroupOf L) := Subgroup.isCyclic_of_le hT'
  exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hXL).symm.toMonoidHom
    (MulEquiv.injective _)

theorem D1CaseTwoDataAt.perf_barM_twoA_cyc (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (hph : D1PhaseThree p P M H R)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 p M H) :
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup p Q → IsCyclic Q := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  intro V hVB hVp Q hQV hQp
  set B := barM M (H ⊓ M)
  obtain ⟨θ, hθk, hθ⟩ := exists_barM_hom_of hph
  set V' := V.subgroupOf B
  set U := V'.map θ
  have hV'p : ⁅V', V'⁆ = V' := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVB, hVp]
  have hUp : ⁅U, U⁆ = U := by rw [← Subgroup.map_commutator, hV'p]
  have hUX : U ≤ d1X0 p M H := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨m, hm, hmx⟩ := x.2
    have hmA := Subgroup.mem_subgroupOf.mp hm
    have hx : x = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmx ▸ x.2⟩ := Subtype.ext hmx.symm
    rw [hx, hθ m hmA.1]
    exact ⟨⟨m, hmA.1⟩, Subgroup.mem_subgroupOf.mpr hmA, rfl⟩
  have hUL : U ≤ L₂ := D1CaseTwoDataAt.perfect_le_component hAut hS hKL hSch hd hL₂ hL₂X hUX hUp
  have hθk' : ∀ y, θ y = 1 → p.Coprime (orderOf y) := fun y hy =>
    hθk.coprime_dvd_right (Subgroup.orderOf_dvd_natCard θ.ker (x := y) hy)
  set Q' := Q.subgroupOf B
  have hQ'p : IsPGroup p Q' := hQp.comap_subtype
  have hinj := injective_comp_subtype_of_coprime θ hθk' hQ'p
  have hQ'U : Q'.map θ ≤ L₂ := (Subgroup.map_mono fun q hq =>
    Subgroup.mem_subgroupOf.mpr (hQV (Subgroup.mem_subgroupOf.mp hq))).trans hUL
  have hc : IsCyclic (Q'.map θ) :=
    D1CaseTwoDataAt.isCyclic_of_le_component hd hL₂ (hQ'p.map θ) hQ'U
  have hQ'c : IsCyclic Q' := by
    have e : Q' ≃* Q'.map θ := by
      have h1 : (θ.comp Q'.subtype).range = Q'.map θ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr h1)
    exact isCyclic_of_injective e.toMonoidHom (MulEquiv.injective _)
  exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe (hQV.trans hVB)).symm.toMonoidHom
    (MulEquiv.injective _)

theorem D1PhaseThree.barM_eq_of_perf_cyc_of_pRank (h : D1PhaseThree p P M H R)
    (hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hp5 : 5 ≤ p) {z : G} (hzK : z ∈ H ⊓ M)
    (hzp : orderOf z = p) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup p Q → IsCyclic Q) :
    ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ →
      IsWeakSBlock M (pCoreOf 2 H) L₂ → barM M L₁ = barM M L₂ := by
  intro L₁ L₂ hL₁ hL₂
  by_contra hne
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨V₁, hV₁P, hV₁p, hV₁d⟩ := D1PhaseThree.exists_perfect_dvd_of_pRank h hrk3 h84 h85 h86 h93
      hD2
    hInn hKP hC3 hK5 hK2 hC3' hK5' hp5 hzK hzp hCz hL₁
  obtain ⟨V₂, hV₂P, hV₂p, hV₂d⟩ := D1PhaseThree.exists_perfect_dvd_of_pRank h hrk3 h84 h85 h86 h93
      hD2
    hInn hKP hC3 hK5 hK2 hC3' hK5' hp5 hzK hzp hCz hL₂
  have hPHM : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≤ barM M (H ⊓ M) := by
    intro L hL
    refine barM_mono ?_
    rw [h.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  have hcomm : V₁ ≤ Subgroup.centralizer (V₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have h1 := le_centralizer_of_component_ne hL₁.component hL₂.component hne
    exact (hV₁P.trans (barM_mono inf_le_right)).trans
      (Subgroup.centralizer_le (hV₂P.trans (barM_mono inf_le_right)) |>.trans' h1)
  have hVp : ⁅V₁ ⊔ V₂, V₁ ⊔ V₂⁆ = V₁ ⊔ V₂ := by
    refine le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_)
    · calc V₁ = ⁅V₁, V₁⁆ := hV₁p.symm
        _ ≤ ⁅V₁ ⊔ V₂, V₁ ⊔ V₂⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc V₂ = ⁅V₂, V₂⁆ := hV₂p.symm
        _ ≤ ⁅V₁ ⊔ V₂, V₁ ⊔ V₂⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  exact false_of_commute_of_cyclic hV₁p hcomm hV₁d hV₂d fun Q hQ hQp =>
    hcyc _ (sup_le (hV₁P.trans (hPHM L₁ hL₁)) (hV₂P.trans (hPHM L₂ hL₂))) hVp Q hQ hQp

end CFSG.AGLEmbedding
