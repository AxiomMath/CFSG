module

public import CFSG.ClassicalInvolution.Asc77.AscS24Main
public import CFSG.ClassicalInvolution.Asc77.AscS24G2A
public import CFSG.ClassicalInvolution.AschTight.S19GC3
public import CFSG.ClassicalInvolution.AschTight.S19QFund
public import CFSG.ClassicalInvolution.AschTight.S19QF2b
public import CFSG.ClassicalInvolution.AschTight.S1911P3e
public import CFSG.ClassicalInvolution.AschTight.S1911P3h
public import CFSG.ClassicalInvolution.Asc77.AscT7XFin

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore IsElemAbelian)
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

namespace Ctx


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem not_layer_g2d4 [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} (ht : t = .G2 ∨ t = .trialityD4)
    (hLt : LayerLieType p f Ω C.e0 t 0) : False := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hc2 := C.e0_isPGroup hZ
  have hKt := C.K_mem_tq_e0 hZ
  have hne : (tqMembers Ω C.e0).Nonempty := ⟨K, hKt⟩
  have hs : SecData p f C.e0 (exactFamily Ω C.e0) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 hne
  obtain ⟨D, hD1, i, hDt, hDr⟩ := exists_local_of_layerLieType hLt
  set Y := centralizingLayer (exactFamily Ω C.e0) {C.e0} with hY
  set O := classicalInvolutionOddCore ↥Y with hO
  set mk := QuotientGroup.mk' O with hmk
  have hconj : ConjInvariant (oddQuotientFamily
      (restrictFamily (centralizingMembers (exactFamily Ω C.e0) {C.e0}) Y)) :=
    conjInvariant_oddQuotientFamily hs.inClass.conjInvariant
  set M := Disconnected.AschTight.S1911.ih8Model_of_lieSystemData D hD1 i hconj with hM
  have ht' : D.tag i = .G2 ∨ D.tag i = .trialityD4 := by rw [hDt]; exact ht
  have ht'' : (D.tag i = .G2 ∧ D.rank i = 0) ∨ (D.tag i = .trialityD4 ∧ D.rank i = 0) := by
    rcases ht' with h | h
    · exact Or.inl ⟨h, hDr⟩
    · exact Or.inr ⟨h, hDr⟩
  have hsimple : IsSimpleGroup (↥Y ⧸ O) := M.isSimpleGroup_of_g2d4 hp ht'
  set K₀ := exactCore C.e0 K with hK₀
  have hK₀mem : K₀ ∈ centralizingMembers (exactFamily Ω C.e0) {C.e0} :=
    ⟨exactCore_mem_exactFamily hKt, exactCore_le_centralizer _ _⟩
  have hK₀Y : K₀ ≤ Y := le_centralizingLayer hK₀mem
  set Kb := (K₀.subgroupOf Y).map mk with hKb
  have hKbΦ : Kb ∈ oddQuotientFamily
      (restrictFamily (centralizingMembers (exactFamily Ω C.e0) {C.e0}) Y) :=
    ⟨K₀.subgroupOf Y, ⟨K₀, hK₀mem, hK₀Y, rfl⟩, rfl⟩
  have hzK₀ : z ∈ K₀ := mem_exactCore C.K_classical hc2 hKt.2
  set zY : ↥Y := ⟨z, hK₀Y hzK₀⟩ with hzY
  have hK₀uniq : IsUniqueInvolution K₀ z :=
    ⟨hzK₀, C.hs.hz.ne_one, C.hs.hz.sq, fun y hy hy2 =>
      eq_one_or_eq_of_mem_exactCore C.K_classical hp hq hy hy2⟩
  have hKbuniq : IsUniqueInvolution Kb (mk zY) :=
    Disconnected.AschTight.S1911.isUniqueInvolution_map_mk
      (CFSG.ComponentClassification.OddCore.odd_card _)
      (Disconnected.AschTight.S1911.isUniqueInvolution_subgroupOf hK₀uniq hK₀Y)
  obtain ⟨F₁, hF₁, hF₁fin, hF₁odd, ⟨e₁⟩⟩ :=
    Disconnected.AschTight.S19Q.exists_equiv_sl2_of_mem_g2d4 M hp ht' hKbΦ
  obtain ⟨w₀, hw₀⟩ : ∃ w, IsClassicalMember p f Kb w := by
    obtain ⟨w, hw⟩ := hs.inClass.classical (K₀.subgroupOf Y) ⟨K₀, hK₀mem, hK₀Y, rfl⟩
    exact ⟨_, hw.map_oddQuotient⟩
  have h4₁ : 4 ≤ Nat.card F₁ := by
    by_contra h4
    obtain ⟨e'⟩ := hw₀.nonempty_equiv
    have hF2 : 2 ≤ Nat.card F₁ := by
      have := Fintype.ofFinite F₁
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hF3 : Nat.card F₁ ≤ 3 := by omega
    have hKb24 : Nat.card Kb ≤ 24 := by
      rw [Nat.card_congr e₁.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
      have : Nat.card F₁ ^ 2 ≤ 9 := by nlinarith
      have h1 : Nat.card F₁ ^ 2 - 1 ≤ 8 := by omega
      calc Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) ≤ 3 * 8 := Nat.mul_le_mul hF3 h1
        _ = 24 := by norm_num
    have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (classicalInvolutionOddCore ↥Kb)
    have hpos : 0 < Nat.card (classicalInvolutionOddCore ↥Kb) := Nat.card_pos
    have hqcard : Nat.card (↥Kb ⧸ classicalInvolutionOddCore ↥Kb) =
        p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e'.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        GaloisField.card p f (by rintro rfl; simp at hq)]
    have hbig : 120 ≤ p ^ f * ((p ^ f) ^ 2 - 1) := by
      have h25 : 25 ≤ (p ^ f) ^ 2 := by nlinarith
      have : 24 ≤ (p ^ f) ^ 2 - 1 := by omega
      calc 120 = 5 * 24 := by norm_num
        _ ≤ p ^ f * ((p ^ f) ^ 2 - 1) := Nat.mul_le_mul hq this
    have : p ^ f * ((p ^ f) ^ 2 - 1) ≤ Nat.card Kb := by
      rw [← hqcard, hquot]
      exact Nat.le_mul_of_pos_right _ hpos
    omega
  have hzb2 : orderOf (⟨mk zY, hKbuniq.mem⟩ : ↥Kb) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hKbuniq.sq) hKbuniq.ne_one
  have hKbO : oddCoreOf Kb = ⊥ := by
    have h := eq_bot_of_odd_normal_sl2 h4₁ e₁ (classicalInvolutionOddCore ↥Kb) inferInstance
      (CFSG.ComponentClassification.OddCore.odd_card _) hzb2
    show (classicalInvolutionOddCore ↥Kb).map Kb.subtype = ⊥
    rw [h, Subgroup.map_bot]
  have hnab : ∃ a b : ↥Y ⧸ O, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    apply hs.not_le_center hK₀mem.1
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hall y x
  have hconjinj := Disconnected.AschTight.S19Q.conj_injective_of_simple hnab
  obtain ⟨-, -, hFGiii⟩ := Disconnected.AschTight.S19G.factFG0 p f hp hq (↥Y ⧸ O) _ (D.tag i)
    (D.rank i) (D.exp i) ht'' ⟨M⟩ Kb hKbΦ (mk zY) hKbuniq
  obtain ⟨F, hF, hFt, ⟨eC⟩⟩ := Disconnected.AschTight.S19G.factFG0C p f hp hq (↥Y ⧸ O) _
    (D.tag i) (D.rank i) (D.exp i) ht'' ⟨M⟩ Kb hKbΦ
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'
  have hx₂W := C.D.x₂_mem
  have hx₂C : C.D.x₂ ∈ Subgroup.centralizer ({C.e0} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact C.comm_W hx₂W C.e0_mem
  have hx₂N : C.D.x₂ ∈ Subgroup.normalizer (Y : Set G) := hs.normalizes _ hx₂C
  set φ := quotAct Y ⟨C.D.x₂, hx₂N⟩ with hφ
  have hx₂R : C.D.x₂ ∈ C.D.F.ρ'.R :=
    (C.D.h₂ ▸ Subgroup.mem_zpowers C.D.x₂ : C.D.x₂ ∈ C.D.F.ρ'.R ⊓ W).1
  have hx₂K : C.D.x₂ ∈ K' := by
    have := C.D.F.ρ'.hRK.1 hx₂R
    rwa [C.hK'] at this
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℕ, C.D.x₂ ^ 2 ^ n = 1 := by
    obtain ⟨k, hk⟩ := C.D.F.ρ'.hRK.2.1 ⟨C.D.x₂, hx₂R⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hφ2 : IsPGroup 2 (Subgroup.zpowers φ) := by
    rw [Disconnected.AschTight.S19Q.isPGroup_zpowers_iff_exists_pow]
    refine ⟨n₂, ?_⟩
    have h1 : (⟨C.D.x₂, hx₂N⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ 2 ^ n₂ = 1 :=
      Subtype.ext (by simpa using hn₂)
    rw [hφ, ← map_pow, h1, map_one]
  have hx₂NK : C.D.x₂ ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin C.hs.hK'.1 hst.mem C.hs.hne hzK' C.hs.hz hx₂K
  have hx₂K₀ : conjSub C.D.x₂ K₀ = K₀ := by
    have h := exactCore_conjSub C.D.x₂ C.e0 K
    have hce : C.D.x₂ * C.e0 * C.D.x₂⁻¹ = C.e0 := by
      rw [C.comm_W hx₂W C.e0_mem]
      group
    rw [hce, conjSub_eq_of_mem_normalizer hx₂NK] at h
    exact h.symm
  have hOK₀ : ((oddCoreIn K₀).subgroupOf Y).map mk ≤ oddCoreOf Kb := by
    refine Disconnected.AschTight.S1916.le_oddCoreOf_of_odd ?_ ?_ ?_
    · exact Subgroup.map_mono (fun k hk => Subgroup.mem_subgroupOf.mpr
        (CFSG.ClassicalInvolution.Balance.oddCoreIn_le K₀ (Subgroup.mem_subgroupOf.mp hk)))
    · have hnormC : K₀.subgroupOf Y ≤ Subgroup.normalizer
          ((((oddCoreIn K₀).subgroupOf Y) : Subgroup _) : Set _) := by
        intro k hk
        rw [Subgroup.mem_subgroupOf] at hk
        have hkN := CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn K₀ hk
        rw [Subgroup.mem_normalizer_iff] at hkN ⊢
        intro n
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
          Subgroup.coe_mul, Subgroup.coe_inv]
        exact hkN n
      exact (Subgroup.map_mono hnormC).trans (Subgroup.le_normalizer_map _)
    · refine Odd.of_dvd_nat (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn K₀) ?_
      have h1 := Subgroup.card_map_dvd ((oddCoreIn K₀).subgroupOf Y) mk
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((CFSG.ClassicalInvolution.Balance.oddCoreIn_le K₀).trans hK₀Y)).toEquiv] at h1
  rw [hKbO] at hOK₀
  have hφfix : ∀ x ∈ Kb, φ x = x := by
    rintro _ ⟨k, hk, rfl⟩
    have hkK₀ : (k : G) ∈ K₀ := Subgroup.mem_subgroupOf.mp hk
    have hkK : (k : G) ∈ K := exactCore_le_left _ _ hkK₀
    rw [hφ, hmk, QuotientGroup.mk'_apply, quotAct_mk, QuotientGroup.eq]
    have hconjK₀ : C.D.x₂ * (k : G) * C.D.x₂⁻¹ ∈ K₀ := by
      rw [← hx₂K₀]
      exact conj_mem_conjSub hkK₀
    have hoK₀ : (C.D.x₂ * (k : G) * C.D.x₂⁻¹)⁻¹ * k ∈ K₀ :=
      K₀.mul_mem (K₀.inv_mem hconjK₀) hkK₀
    have hoOK : (C.D.x₂ * (k : G) * C.D.x₂⁻¹)⁻¹ * k ∈ oddCoreOf K := by
      have h1 := (hΩ.comm_le_oddCore_of_twin hst.mem C.hs.hK'.1 C.hs.hne.symm C.hs.hz hzK'
        (Subgroup.commutator_mem_commutator (K.inv_mem hkK) hx₂K)).1
      have e1 : (C.D.x₂ * (k : G) * C.D.x₂⁻¹)⁻¹ * k = ⁅(k : G)⁻¹, C.D.x₂⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e1]
      exact (oddCoreOf K).inv_mem h1
    have hoO₀ : (C.D.x₂ * (k : G) * C.D.x₂⁻¹)⁻¹ * k ∈ oddCoreIn K₀ := by
      rw [oddCoreIn_exactCore C.K_classical hc2 hKt.2]
      exact ⟨hoK₀, hoOK⟩
    have hmem : mk ⟨_, Y.mul_mem (Y.inv_mem (hK₀Y hconjK₀)) k.2⟩ ∈
        (⊥ : Subgroup (↥Y ⧸ O)) :=
      hOK₀ ⟨⟨_, Y.mul_mem (Y.inv_mem (hK₀Y hconjK₀)) k.2⟩, Subgroup.mem_subgroupOf.mpr hoO₀, rfl⟩
    have h2 := (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hmem)
    convert h2 using 1
    apply Subtype.ext
    rfl
  obtain ⟨yb, hybC, hφyb⟩ := hFGiii φ hφ2 hφfix
  have hzN : z ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer (hK₀Y hzK₀)
  have hφz : φ ^ (2 * C.D.m) = MulAut.conj (mk zY) := by
    have h1 : (⟨C.D.x₂, hx₂N⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ (2 * C.D.m) = ⟨z, hzN⟩ :=
      Subtype.ext (by
        rw [Subgroup.coe_pow]
        show C.D.x₂ ^ (2 * C.D.m) = z
        rw [C.D.z₂, C.hz])
    rw [hφ, ← map_pow, h1, quotAct_of_mem Y ⟨z, hzN⟩ (hK₀Y hzK₀)]
    rfl
  have hφ1 : φ ^ (4 * C.D.m) = 1 := by
    have h1 : (⟨C.D.x₂, hx₂N⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ (4 * C.D.m) = 1 :=
      Subtype.ext (by
        rw [Subgroup.coe_pow]
        show C.D.x₂ ^ (4 * C.D.m) = 1
        rw [← C.D.o₂]
        exact pow_orderOf_eq_one _)
    rw [hφ, ← map_pow, h1, map_one]
  have hyz : yb ^ (2 * C.D.m) = mk zY := hconjinj (by rw [map_pow, ← hφyb, hφz])
  have hy1 : yb ^ (4 * C.D.m) = 1 := hconjinj (by rw [map_pow, ← hφyb, hφ1, map_one])
  set Cb := Subgroup.centralizer (Kb : Set (↥Y ⧸ O)) with hCb
  have hzC : mk zY ∈ Cb := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hkK₀ : (k : G) ∈ K₀ := Subgroup.mem_subgroupOf.mp hk
    have hzk : z * (k : G) = k * z := C.hs.hz.commute_of_mem (exactCore_le_left _ _ hkK₀)
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext hzk.symm)
  have hF4 : 4 ≤ Nat.card F := by
    by_contra h4
    have hF3 : Fintype.card F ≤ 3 := by rw [← Nat.card_eq_fintype_card]; omega
    set w : ↥Cb := (⟨yb, hybC⟩ : ↥Cb) ^ C.c with hw
    have hc4 : C.c * 4 = 2 * C.D.m := by have := C.hc; omega
    have hc8 : C.c * 8 = 4 * C.D.m := by have := C.hc; omega
    have hw4 : w ^ 4 = ⟨mk zY, hzC⟩ := Subtype.ext (by
      rw [hw, ← pow_mul, Subgroup.coe_pow, hc4]
      exact hyz)
    have hw8 : w ^ 8 = 1 := Subtype.ext (by
      rw [hw, ← pow_mul, Subgroup.coe_pow, hc8]
      exact hy1)
    have h12 : eC w ^ 12 = 1 := sl2_pow_twelve hF3 _
    have hw12 : w ^ 12 = 1 := eC.injective (by rw [map_pow, h12, map_one])
    have h4' : w ^ 4 = 1 := by
      calc w ^ 4 = w ^ 12 * (w ^ 8)⁻¹ := by
            rw [show (12 : ℕ) = 4 + 8 from rfl, pow_add, mul_inv_cancel_right]
        _ = 1 := by rw [hw12, hw8, inv_one, one_mul]
    rw [hw4] at h4'
    exact hKbuniq.ne_one (congrArg Subtype.val h4')
  have hCperf : ⁅Cb, Cb⁆ = Cb := Subgroup.isPerfect_iff.mp (isPerfect_of_equiv_sl2 hF4 eC)
  have hYC : Y ≤ Subgroup.centralizer ({C.e0} : Set G) :=
    centralizingLayer_le_centralizer _ _
  set P₀ : Subgroup ↥Y := Cb.comap mk ⊓ (Subgroup.centralizer ({z} : Set G)).subgroupOf Y
    with hP₀
  have hzNO : z ∈ Subgroup.normalizer ((oddCoreOf Y : Subgroup G) : Set G) :=
    Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer hzN
  have hP₀map : P₀.map mk = Cb := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · intro c hc
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O c
      have hcz : mk zY * mk y = mk y * mk zY :=
        (Subgroup.mem_centralizer_iff.mp hc _ hKbuniq.mem)
      have hk : (y : G)⁻¹ * (z * y * z⁻¹) ∈ oddCoreOf Y := by
        have h1 : mk (y⁻¹ * (zY * y * zY⁻¹)) = 1 := by
          rw [map_mul, map_inv, map_mul, map_mul, map_inv, hcz]
          group
        have h2 := (QuotientGroup.eq_one_iff _).mp h1
        exact ⟨_, h2, rfl⟩
      obtain ⟨o, ho, hzo⟩ := Disconnected.AschTight.S1911.exists_mul_mem_centralizer_of_odd
        (oddCoreOf_odd_natCard Y) C.z_sq hzNO hk
      obtain ⟨hoY, hoO⟩ := mem_oddCoreOf_iff.mp ho
      refine ⟨y * ⟨o, hoY⟩, ⟨?_, ?_⟩, ?_⟩
      · show mk (y * ⟨o, hoY⟩) ∈ Cb
        have h0 : mk ⟨o, hoY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hoO
        rw [map_mul, h0, mul_one]
        exact hc
      · show y * ⟨o, hoY⟩ ∈ (Subgroup.centralizer ({z} : Set G)).subgroupOf Y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
        show (y : G) * o * z = z * ((y : G) * o)
        calc (y : G) * o * z = z * ((y : G) * o) * z⁻¹ * z := by rw [hzo]
          _ = z * ((y : G) * o) := by group
      · have h0 : mk ⟨o, hoY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hoO
        rw [map_mul, h0, mul_one]
  set P₁ := ⁅P₀, P₀⁆ with hP₁
  set P₂ := ⁅P₁, P₁⁆ with hP₂
  set P₃ := ⁅P₂, P₂⁆ with hP₃
  have hP₁map : P₁.map mk = Cb := by rw [hP₁, Subgroup.map_commutator, hP₀map, hCperf]
  have hP₂map : P₂.map mk = Cb := by rw [hP₂, Subgroup.map_commutator, hP₁map, hCperf]
  have hP₃map : P₃.map mk = Cb := by rw [hP₃, Subgroup.map_commutator, hP₂map, hCperf]
  have hcl' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ C.hs.hK'.1 hzK'
  obtain ⟨e'⟩ := hcl'.nonempty_equiv
  have hW : W ∈ WSet Ω := C.hd.hW
  have hρK := C.D.F.ρ.hRK
  have hρ'K := C.D.F.ρ'.hRK
  have hρ₃K := C.D.F.ρ₃.hRK
  rw [C.hK] at hρK
  rw [C.hK'] at hρ'K
  rw [C.hJ] at hρ₃K
  have hKK' : K ≠ K' := C.hs.hne.symm
  have hJK' : conjSub g⁻¹ K ≠ K' := by
    have h := C.D.F.hne₂
    rw [C.hK', C.hJ] at h
    exact fun e => h e.symm
  have hx₁K : C.D.x₁ ∈ K :=
    hρK.1 (C.D.h₁ ▸ Subgroup.mem_zpowers C.D.x₁ : C.D.x₁ ∈ C.D.F.ρ.R ⊓ W).1
  have hx₃J : C.D.x₃ ∈ conjSub g⁻¹ K :=
    hρ₃K.1 (C.D.h₃ ▸ Subgroup.mem_zpowers C.D.x₃ : C.D.x₃ ∈ C.D.F.ρ₃.R ⊓ W).1
  have hx₁NK' : C.D.x₁ ∈ Subgroup.normalizer (K' : Set G) :=
    (Thompson.inf_W_le_normalizer_of_ne hp hq hΩ hW hst.mem C.hs.hK'.1 hKK' C.D.F.ρ.hR
      C.D.F.ρ'.hR hρK hρ'K).1 ⟨hx₁K, C.D.x₁_mem⟩
  have hx₃NK' : C.D.x₃ ∈ Subgroup.normalizer (K' : Set G) :=
    (Thompson.inf_W_le_normalizer_of_ne hp hq hΩ hW C.J_mem C.hs.hK'.1 hJK' C.D.F.ρ₃.hR
      C.D.F.ρ'.hR hρ₃K hρ'K).1 ⟨hx₃J, C.D.x₃_mem⟩
  have hWN : W ≤ Subgroup.normalizer (K' : Set G) := by
    refine C.D.hgen.trans ?_
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact hx₁NK'
    · exact Subgroup.le_normalizer hx₂K
    · exact hx₃NK'
  set dd := dEl C.D C.c with hdd
  have hdW : dd ∈ W := dEl_mem C.D C.c
  have hd2 : IsPGroup 2 (Subgroup.zpowers dd) := by
    rw [Disconnected.AschTight.S19Q.isPGroup_zpowers_iff_exists_pow]
    refine ⟨2, ?_⟩
    have h1 := dEl_sq C.D C.hc hZ
    rw [C.hz] at h1
    calc dd ^ 2 ^ 2 = dd ^ 4 := by norm_num
      _ = (dd * dd) * (dd * dd) := by
          rw [pow_succ, pow_succ, pow_succ, pow_one, mul_assoc (dd * dd)]
      _ = z * z := by rw [h1]
      _ = 1 := C.z_sq
  have hdtq : dd ∈ trivialOnQuot K' :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hd2 C.hs.hK'.1).mpr
      ⟨C.D.F.ρ'.R, hρ'K, dEl_cent_R' C.D C.hc⟩
  have hdact : quotAct K' ⟨dd, hWN hdW⟩ = 1 := by
    refine quotAct_eq_one K' _ fun y hy => ?_
    have := hdtq.2 y hy
    rw [commutatorElement_def] at this
    exact this
  have hxK' : C.D.x₂ ^ C.D.m ∈ K' := K'.pow_mem hx₂K _
  set xb : ↥K' ⧸ classicalInvolutionOddCore ↥K' := QuotientGroup.mk ⟨C.D.x₂ ^ C.D.m, hxK'⟩
    with hxb
  have he0N : C.e0 ∈ Subgroup.normalizer (K' : Set G) := hWN C.e0_mem
  have he0act : quotAct K' ⟨C.e0, he0N⟩ = MulAut.conj xb := by
    have h1 : (⟨C.e0, he0N⟩ : ↥(Subgroup.normalizer (K' : Set G))) =
        ⟨dd, hWN hdW⟩ * ⟨C.D.x₂ ^ C.D.m, Subgroup.le_normalizer hxK'⟩ :=
      Subtype.ext (eEl_eq_dEl_mul C.D C.c)
    rw [h1, map_mul, hdact, one_mul, quotAct_of_mem K' _ hxK']
  have hpowK' : ∀ k : ℕ, xb ^ k =
      QuotientGroup.mk ⟨C.D.x₂ ^ (C.D.m * k), K'.pow_mem hx₂K _⟩ := by
    intro k
    rw [hxb, ← QuotientGroup.mk_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show (C.D.x₂ ^ C.D.m) ^ k = C.D.x₂ ^ (C.D.m * k)
    rw [← pow_mul]
  have hxb4 : orderOf xb = 4 := by
    have hz' : (⟨z, hcl'.mem⟩ : ↥K') ∉ classicalInvolutionOddCore ↥K' := by
      intro hmem
      have h1 : orderOf (⟨z, hcl'.mem⟩ : ↥K') ∣ Nat.card (classicalInvolutionOddCore ↥K') :=
        Subgroup.orderOf_dvd_natCard _ hmem
      rw [Subgroup.orderOf_mk, hcl'.orderOf_eq_two] at h1
      exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
        (even_iff_two_dvd.mpr h1)
    have h2 : ¬ xb ^ 2 ^ 1 = 1 := by
      intro h
      rw [pow_one, hpowK'] at h
      apply hz'
      have h3 := (QuotientGroup.eq_one_iff _).mp h
      have e1 : (⟨C.D.x₂ ^ (C.D.m * 2), K'.pow_mem hx₂K _⟩ : ↥K') = ⟨z, hcl'.mem⟩ := by
        apply Subtype.ext
        show C.D.x₂ ^ (C.D.m * 2) = z
        rw [mul_comm, C.D.z₂, C.hz]
      rwa [e1] at h3
    have h4 : xb ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 4 from rfl, hpowK', (QuotientGroup.eq_one_iff _).mpr]
      have e1 : (⟨C.D.x₂ ^ (C.D.m * 4), K'.pow_mem hx₂K _⟩ : ↥K') = 1 := by
        apply Subtype.ext
        show C.D.x₂ ^ (C.D.m * 4) = 1
        rw [mul_comm, ← C.D.o₂]
        exact pow_orderOf_eq_one _
      rw [e1]
      exact Subgroup.one_mem _
    exact orderOf_eq_prime_pow h2 h4
  have hswap : ∀ a ∈ Subgroup.centralizer ({z} : Set G),
      (conjSub a K = K ∧ conjSub a K' = K') ∨ (conjSub a K = K' ∧ conjSub a K' = K) := by
    intro a ha
    have haz : a * z * a⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp ha]
      group
    have h1 : conjSub a K ∈ twinSet Ω K := by
      refine ⟨hΩ.conjInvariant a K hst.mem, z, C.hs.hz, ?_⟩
      have := C.hs.hz.conj a
      rwa [haz] at this
    have h2 : conjSub a K' ∈ twinSet Ω K := by
      refine ⟨hΩ.conjInvariant a K' C.hs.hK'.1, z, C.hs.hz, ?_⟩
      have := hzK'.conj a
      rwa [haz] at this
    rw [C.hs.twinSet_eq] at h1 h2
    have hne' : conjSub a K ≠ conjSub a K' := fun h => hKK' (conjSub_injective a h)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne'
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne'
  have hcomN : ∀ a ∈ Subgroup.centralizer ({z} : Set G),
      ∀ b ∈ Subgroup.centralizer ({z} : Set G), ⁅a, b⁆ ∈ Subgroup.normalizer (K' : Set G) := by
    intro a ha b hb
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    show conjSub ⁅a, b⁆ K' = K'
    have hinvfix : ∀ c : G, conjSub c K = K ∧ conjSub c K' = K' →
        conjSub c⁻¹ K = K ∧ conjSub c⁻¹ K' = K' := by
      rintro c ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := conjSub_inv_conjSub c K
        rwa [h1] at this
      · have := conjSub_inv_conjSub c K'
        rwa [h2] at this
    have hinvswap : ∀ c : G, conjSub c K = K' ∧ conjSub c K' = K →
        conjSub c⁻¹ K = K' ∧ conjSub c⁻¹ K' = K := by
      rintro c ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := conjSub_inv_conjSub c K'
        rwa [h2] at this
      · have := conjSub_inv_conjSub c K
        rwa [h1] at this
    rw [commutatorElement_def, conjSub_mul, conjSub_mul, conjSub_mul]
    rcases hswap a ha with ha' | ha' <;> rcases hswap b hb with hb' | hb'
    · rw [(hinvfix b hb').2, (hinvfix a ha').2, hb'.2, ha'.2]
    · rw [(hinvswap b hb').2, (hinvfix a ha').1, hb'.1, ha'.2]
    · rw [(hinvfix b hb').2, (hinvswap a ha').2, hb'.1, ha'.1]
    · rw [(hinvswap b hb').2, (hinvswap a ha').1, hb'.2, ha'.1]
  have hP₀z : ∀ y ∈ P₀, ((y : ↥Y) : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    fun y hy => Subgroup.mem_subgroupOf.mp hy.2
  have hP₁N : P₁.map Y.subtype ≤ Subgroup.normalizer (K' : Set G) := by
    rw [hP₁, Subgroup.map_commutator, Subgroup.commutator_le]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hcomN _ (hP₀z a ha) _ (hP₀z b hb)
  set S := (P₁.map Y.subtype).subgroupOf (Subgroup.normalizer (K' : Set G)) with hS
  have hcommS : ∀ h ∈ S, quotAct K' h * MulAut.conj xb = MulAut.conj xb * quotAct K' h := by
    intro h hh
    have hhY : (h : G) ∈ Y := by
      obtain ⟨y, -, hy⟩ := Subgroup.mem_subgroupOf.mp hh
      rw [← hy]
      exact y.2
    have he0h : h * ⟨C.e0, he0N⟩ = ⟨C.e0, he0N⟩ * h :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hYC hhY))
    rw [← he0act, ← map_mul, ← map_mul, he0h]
  have hoddF : Odd (Nat.card (GaloisField p f)) :=
    (ModelFacts.odd_and_five_le_card_galoisField (p := p) hp hq).1
  have hwx : (QuotientGroup.mk ⟨C.D.x₂, hx₂K⟩ : ↥K' ⧸ classicalInvolutionOddCore ↥K') * xb =
      xb * QuotientGroup.mk ⟨C.D.x₂, hx₂K⟩ := by
    rw [hxb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show C.D.x₂ * C.D.x₂ ^ C.D.m = C.D.x₂ ^ C.D.m * C.D.x₂
    rw [← pow_succ', ← pow_succ]
  have hw2 : ∃ n : ℕ,
      (QuotientGroup.mk ⟨C.D.x₂, hx₂K⟩ : ↥K' ⧸ classicalInvolutionOddCore ↥K') ^ 2 ^ n = 1 := by
    refine ⟨n₂, ?_⟩
    rw [← QuotientGroup.mk_pow]
    have e1 : (⟨C.D.x₂, hx₂K⟩ : ↥K') ^ 2 ^ n₂ = 1 := Subtype.ext (by simpa using hn₂)
    rw [e1, QuotientGroup.mk_one]
  have hfixK' := fix_of_second_derived hoddF e' (quotAct K') S hxb4 hcommS hw2 hwx
  have hSmap : S.map (Subgroup.normalizer (K' : Set G)).subtype = P₁.map Y.subtype := by
    rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₁N]
  have hS3map : (⁅⁅S, S⁆, ⁅S, S⁆⁆).map (Subgroup.normalizer (K' : Set G)).subtype =
      P₃.map Y.subtype := by
    simp only [Subgroup.map_commutator, hSmap, hP₃, hP₂]
  have hP₃fix : ∀ y ∈ P₃, ((y : ↥Y) : G)⁻¹ * C.D.x₂ * ((y : ↥Y) : G) * C.D.x₂⁻¹ ∈
      oddCoreOf K' := by
    intro y hy
    have hyG : ((y⁻¹ : ↥Y) : G) ∈ P₃.map Y.subtype := ⟨y⁻¹, P₃.inv_mem hy, rfl⟩
    rw [← hS3map] at hyG
    obtain ⟨s, hs3, hsy⟩ := hyG
    have h1 := hfixK' s hs3
    rw [quotAct_mk, QuotientGroup.eq_iff_div_mem] at h1
    have hsy' : (s : G) = ((y : ↥Y) : G)⁻¹ := hsy
    refine ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_subtype, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      normAut_apply, hsy', inv_inv]
  set Qb := ((oddCoreOf K' ⊓ Y).subgroupOf Y).map mk with hQb
  have hQbodd : Odd (Nat.card Qb) := by
    refine Odd.of_dvd_nat (oddCoreOf_odd_natCard K') ?_
    have h1 := Subgroup.card_map_dvd ((oddCoreOf K' ⊓ Y).subgroupOf Y) mk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      oddCoreOf K' ⊓ Y ≤ Y)).toEquiv] at h1
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hQbN : ∀ c ∈ Cb, ∀ q ∈ Qb, c * q * c⁻¹ ∈ Qb := by
    intro c hc q hq
    rw [← hP₁map] at hc
    obtain ⟨p₁, hp₁, rfl⟩ := hc
    obtain ⟨o, ho, rfl⟩ := hq
    have hp₁N : ((p₁ : ↥Y) : G) ∈ Subgroup.normalizer (K' : Set G) := hP₁N ⟨p₁, hp₁, rfl⟩
    have hoK' : (o : G) ∈ oddCoreOf K' := (Subgroup.mem_subgroupOf.mp ho).1
    refine ⟨p₁ * o * p₁⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, (p₁ * o * p₁⁻¹).2⟩, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp
        (Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer hp₁N) _).mp hoK'
      simpa using h1
    · rw [map_mul, map_mul, map_inv]
  set N := Qb.subgroupOf Cb with hN
  have hNnormal : N.Normal := by
    constructor
    intro n hn c
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hQbN c c.2 n hn
  have hNodd : Odd (Nat.card N) := by
    refine Odd.of_dvd_nat hQbodd ?_
    have h1 : Nat.card N = Nat.card (N.map Cb.subtype) :=
      (Nat.card_congr (N.equivMapOfInjective _ Cb.subtype_injective).toEquiv)
    rw [h1, hN, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hzC2 : orderOf (⟨mk zY, hzC⟩ : ↥Cb) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hKbuniq.sq) hKbuniq.ne_one
  have hNbot : N = ⊥ := eq_bot_of_odd_normal_sl2 hF4 eC N hNnormal hNodd hzC2
  have hφC : ∀ c ∈ Cb, φ c = c := by
    intro c hc
    have hc' := hc
    rw [← hP₃map] at hc'
    obtain ⟨y, hy, rfl⟩ := hc'
    have hoK' := hP₃fix y hy
    set o : ↥Y := y⁻¹ * normAut Y ⟨C.D.x₂, hx₂N⟩ y with ho
    have hoG : (o : G) = ((y : ↥Y) : G)⁻¹ * C.D.x₂ * ((y : ↥Y) : G) * C.D.x₂⁻¹ := by
      rw [ho, Subgroup.coe_mul, Subgroup.coe_inv, normAut_apply]
      group
    have hoQ : mk o ∈ Qb := ⟨o, Subgroup.mem_subgroupOf.mpr ⟨by rw [hoG]; exact hoK', o.2⟩, rfl⟩
    have hφy : φ (mk y) = yb * mk y * yb⁻¹ := by rw [hφyb, MulAut.conj_apply]
    have hφy' : φ (mk y) = mk y * mk o := by
      rw [hφ, hmk]
      simp only [QuotientGroup.mk'_apply]
      rw [quotAct_mk, ← QuotientGroup.mk_mul, ho, mul_inv_cancel_left]
    have hoC : mk o ∈ Cb := by
      have e1 : mk o = (mk y)⁻¹ * (yb * mk y * yb⁻¹) := by
        rw [← hφy, hφy', inv_mul_cancel_left]
      rw [e1]
      exact Cb.mul_mem (Cb.inv_mem hc) (Cb.mul_mem (Cb.mul_mem hybC hc) (Cb.inv_mem hybC))
    have hoN : (⟨mk o, hoC⟩ : ↥Cb) ∈ N := Subgroup.mem_subgroupOf.mpr hoQ
    rw [hNbot] at hoN
    have hmo : mk o = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hoN)
    rw [hφy', hmo, mul_one]
  have hycen : ∀ q : ↥Cb, (⟨yb, hybC⟩ : ↥Cb) * q = q * ⟨yb, hybC⟩ := by
    intro q
    apply Subtype.ext
    have h1 := hφC q q.2
    rw [hφyb, MulAut.conj_apply] at h1
    show yb * (q : ↥Y ⧸ O) = q * yb
    calc yb * (q : ↥Y ⧸ O) = yb * q * yb⁻¹ * yb := by group
      _ = q * yb := by rw [h1]
  have hy2 : yb * yb = 1 := congrArg Subtype.val (sq_eq_one_of_central_sl2 eC hycen)
  have hfin : yb ^ (2 * C.D.m) = 1 := by rw [pow_mul, pow_two, hy2, one_pow]
  rw [hyz] at hfin
  exact hKbuniq.ne_one hfin

end Ctx


variable (p f : ℕ) [Fact p.Prime]

theorem layerE0_proved : LayerE0 p f := by
  intro G _ _ _ Ω K K' W S R R' z u g C
  have hZ := C.hd.hZ
  rcases C.D.layer_shape C.hs C.hK C.hK' C.hc hZ with h | h | h
  · exact h
  · exact (C.not_layer_g2d4 hZ (Or.inl rfl) h).elim
  · exact (C.not_layer_g2d4 hZ (Or.inr rfl) h).elim

theorem c24_pair_proved : C24_pair p f := c24_pair_of_layer (layerE0_proved p f)

theorem c24_8_big_proved : C24_8_big p f := c24_8_big_of_layer (layerE0_proved p f)

end CFSG.ClassicalInvolution.Asc77.S24
