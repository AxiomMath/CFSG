module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Rel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Center

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam fuel comm_famL₂ rel_C2 rel_C3 rel_C5
  centerEqs centerEqs_vanish tWord traceZeros traceZeros_sound centerChecks_V0 centerChecks_V1
  coordsOf)
open scoped commutatorElement

@[expose] def testsS4 : List ℕ := [2, 4, 5, 10]

@[expose] def traceS4 : List (ℕ × ℕ) := [(17, 4), (19, 10), (41, 2), (44, 9), (65, 7), (92, 5)]

theorem traceS4_ok :
    traceZeros (centerEqs testsS4) [0, 1, 3, 12, 13, 15] traceS4 [2, 4, 5, 7, 9, 10] = true := by
  decide +kernel

theorem centerChecks_S4 : ∀ n ∈ testsS4,
    collectCheck fuel (sylowWord ++ tWord n) (coordsOf fuel (sylowWord ++ tWord n)) = true ∧
      collectCheck fuel (tWord n ++ sylowWord) (coordsOf fuel (tWord n ++ sylowWord)) = true := by
  intro n hn
  simp only [testsS4, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact centerChecks_V0 2 (by decide)
  · exact centerChecks_V0 4 (by decide)
  · exact centerChecks_V1 5 (by decide)
  · exact centerChecks_V0 10 (by decide)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem comm_famAF (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅fam a K 0 s, fam a K 6 t⁆ = fam a K 8 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide) (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simpa [polyEval, monoEval, coordVal] using this

omit [Finite K] in
theorem forced_S4 (c e f g h i j k l : K)
    (hcomm : ∀ n ∈ testsS4, sylowV a K 0 0 c 0 e f g h i j k l * fam a K n 1 =
      fam a K n 1 * sylowV a K 0 0 c 0 e f g h i j k l) :
    c = 0 ∧ e = 0 ∧ f = 0 ∧ h = 0 ∧ j = 0 ∧ k = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hz := traceZeros_sound (m := a) (coordVal a 0 0 c 0 e f g h i j k l)
    (coordVal_add_twelve (m := a) 0 0 c 0 e f g h i j k l) (centerEqs testsS4)
    (centerEqs_vanish (by decide) centerChecks_S4 0 0 c 0 e f g h i j k l hcomm)
    (zs₀ := [0, 1, 3, 12, 13, 15]) (by
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · rfl
      · exact largeReeSigma_zero
      · exact largeReeSigma_zero
      · exact largeReeSigma_zero) traceS4_ok
  exact ⟨hz 2 (by decide), hz 4 (by decide), hz 5 (by decide), hz 7 (by decide),
    hz 9 (by decide), hz 10 (by decide)⟩

theorem sylowVec_eq_of_mem_S2 (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Fin 12 → K}
    (hx : ∀ n ∈ ({0, 1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 12)), x n = 0) :
    sylowVec a K x = rootElt K a .i11 (x 6) * rootElt K a .i12 (x 8) * rootElt K a .i10 (x 11) := by
  rw [sylowVec_eq_prod_rootElt hK, hx 0 (by decide), hx 1 (by decide), hx 2 (by decide),
    hx 3 (by decide), hx 4 (by decide), hx 5 (by decide), hx 7 (by decide), hx 9 (by decide),
    hx 10 (by decide)]
  simp only [rootElt_zero, one_mul, mul_one]


theorem S2_le_centralizer_S4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S2 K a ≤ centralizer (S4 K a : Set (ModGL F4.tag K)) := by
  have hS4P : S4 K a ≤ F4.reeFixedPosUnipotent K a := rootJoin_le_sylowP hK _
  refine iSup₂_le fun i hi => ?_
  rw [rootV, closure_le]
  rintro _ ⟨u, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · rw [S4_eq_tKernel hK] at hw
    exact mem_centralizer_singleton_iff.1 (tKernel_le_centralizer hK u hw)
  · have hs : weylOne K ∈ normalizer (tKernel K a : Set (ModGL F4.tag K)) :=
      rankOneGroupOne_le_normalizer_tKernel hK weylS_mem_leviN
    rw [S4_eq_tKernel hK] at hw hS4P
    have hw' : (weylOne K)⁻¹ * w * weylOne K ∈ tKernel K a := by
      have := (mem_normalizer_iff.1 (inv_mem hs) w).1 hw
      rwa [inv_inv] at this
    have hc := commute_centralZ ha hK (hS4P hw') u
    rw [← sylowH_zero_eq_centralZ] at hc
    show w * sylowF a K 0 u = sylowF a K 0 u * w
    rw [← weylOne_conj_sylowH]
    calc w * (weylOne K * sylowH a K 0 u * (weylOne K)⁻¹)
        = weylOne K * (((weylOne K)⁻¹ * w * weylOne K) * sylowH a K 0 u) * (weylOne K)⁻¹ := by
          group
      _ = weylOne K * (sylowH a K 0 u * ((weylOne K)⁻¹ * w * weylOne K)) * (weylOne K)⁻¹ := by
          rw [hc]
      _ = weylOne K * sylowH a K 0 u * (weylOne K)⁻¹ * w := by group
  · have hc := commute_centralZ ha hK (hS4P hw) u
    rwa [← sylowH_zero_eq_centralZ] at hc

theorem mem_S2_of_commute_S4 (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ S4 K a) (hc : ∀ w ∈ S4 K a, w * u = u * w) : u ∈ S2 K a := by
  have hu' : u ∈ (S4 K a : Set (ModGL F4.tag K)) := hu
  rw [(S4_spec hK).2.1] at hu'
  obtain ⟨x, hx, rfl⟩ := hu'
  have h0 : x 0 = 0 := hx 0 (by decide)
  have h1 : x 1 = 0 := hx 1 (by decide)
  have h3 : x 3 = 0 := hx 3 (by decide)
  have hmem : ∀ n ∈ testsS4, fam a K n 1 ∈ S4 K a := by
    intro n hn
    simp only [testsS4, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact rootV_le_rootJoin (i := .i2) (by decide) (rootElt_mem_rootV .i2 1)
    · exact rootV_le_rootJoin (i := .i8) (by decide) (rootElt_mem_rootV .i8 1)
    · exact rootV_le_rootJoin (i := .i6) (by decide) (rootElt_mem_rootV .i6 1)
    · exact rootV_le_rootJoin (i := .i9) (by decide) (rootElt_mem_rootV .i9 1)
  obtain ⟨h2, h4, h5, h7, h9, h10⟩ := forced_S4 (a := a) (x 2) (x 4) (x 5) (x 6) (x 7) (x 8)
    (x 9) (x 10) (x 11) fun n hn => by
      have := hc _ (hmem n hn)
      rw [sylowVec, h0, h1, h3] at this
      exact this.symm
  have hS2 : sylowVec a K x ∈ (S2 K a : Set (ModGL F4.tag K)) := by
    rw [(S2_spec hK).2.1]
    refine ⟨x, fun n hn => ?_, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  exact hS2

theorem mul_self_of_mem_S2 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ S2 K a) : u * u = 1 := by
  have hu' : u ∈ (S2 K a : Set (ModGL F4.tag K)) := hu
  rw [(S2_spec hK).2.1] at hu'
  obtain ⟨x, hx, rfl⟩ := hu'
  rw [sylowVec_eq_of_mem_S2 hK hx]
  have hS24 : S2 K a ≤ S4 K a :=
    (S1_le_S2_le_S3_le_S4_le_radS hK).2.1.trans (S1_le_S2_le_S3_le_S4_le_radS hK).2.2.1
  have hcomm : ∀ {y z : ModGL F4.tag K}, y ∈ S2 K a → z ∈ S2 K a → y * z = z * y :=
    fun hy hz => (mem_centralizer_iff.1 (S2_le_centralizer_S4 ha hK hy) _ (hS24 hz)).symm
  have hp : rootElt K a .i11 (x 6) ∈ S2 K a :=
    rootV_le_rootJoin (i := .i11) (by decide) (rootElt_mem_rootV _ _)
  have hq : rootElt K a .i12 (x 8) ∈ S2 K a :=
    rootV_le_rootJoin (i := .i12) (by decide) (rootElt_mem_rootV _ _)
  have hr : rootElt K a .i10 (x 11) ∈ S2 K a :=
    rootV_le_rootJoin (i := .i10) (by decide) (rootElt_mem_rootV _ _)
  set p := rootElt K a .i11 (x 6)
  set q := rootElt K a .i12 (x 8)
  set r := rootElt K a .i10 (x 11)
  have hpp : p * p = 1 := rootElt_mul_self hK rfl _
  have hqq : q * q = 1 := rootElt_mul_self hK rfl _
  have hrr : r * r = 1 := rootElt_mul_self hK rfl _
  have e1 : r * p = p * r := hcomm hr hp
  have e2 : q * p = p * q := hcomm hq hp
  have e3 : r * q = q * r := hcomm hr hq
  calc p * q * r * (p * q * r) = p * q * (r * p) * q * r := by group
    _ = p * q * (p * r) * q * r := by rw [e1]
    _ = p * (q * p) * (r * q) * r := by group
    _ = p * (p * q) * (q * r) * r := by rw [e2, e3]
    _ = (p * p) * (q * q) * (r * r) := by group
    _ = 1 := by rw [hpp, hqq, hrr, one_mul, one_mul]

theorem reeFixedTorus_le_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedTorus K a ≤ F4.reeGamma K a :=
  torusH_eq_reeFixedTorus hK ▸ torusH_le_reeGamma hK

theorem exists_conj_invE_of_mem_S1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {u : ModGL F4.tag K} (hu : u ∈ S1 K a) (hu1 : u ≠ 1) :
    ∃ x ∈ F4.reeGamma K a, x * u * x⁻¹ = invE K a := by
  obtain ⟨-, -, -, hH, -, -, -⟩ := large_Ree_every_involution_fuses a ha K hK
  have hu' : u ∈ (S1 K a : Set (ModGL F4.tag K)) := hu
  rw [(S1_spec hK).2.1] at hu'
  obtain ⟨x, hx, rfl⟩ := hu'
  have hform : sylowVec a K x = sylowF a K 0 (x 6) * sylowH a K 0 (x 8) := by
    rw [sylowVec_eq_prod_rootElt hK, hx 0 (by decide), hx 1 (by decide), hx 2 (by decide),
      hx 3 (by decide), hx 4 (by decide), hx 5 (by decide), hx 7 (by decide), hx 9 (by decide),
      hx 10 (by decide), hx 11 (by decide)]
    simp only [rootElt_zero, one_mul, mul_one]
    rfl
  rw [hform] at hu1 ⊢
  by_cases hg : x 6 = 0
  · rw [hg, wordF_zero, one_mul] at hu1 ⊢
    have hi : x 8 ≠ 0 := fun h0 => hu1 (by rw [h0, wordH_zero])
    obtain ⟨y, hy, hyH⟩ := hH (x 8) 1 hi one_ne_zero
    exact ⟨y, reeFixedTorus_le_reeGamma hK hy, hyH⟩
  · set c := x 8 * (x 6)⁻¹ with hcdef
    have hcg : c * x 6 = x 8 := by rw [hcdef, mul_assoc, inv_mul_cancel₀ hg, mul_one]
    have hAΓ : sylowA a K c ∈ F4.reeGamma K a := rootV_le_reeGamma hK .i3 (rootElt_mem_rootV _ _)
    have hFP : sylowF a K 0 (x 6) ∈ F4.reeFixedPosUnipotent K a :=
      rootV_le_sylowP hK .i11 (rootElt_mem_rootV _ _)
    have hAF : ⁅sylowA a K c, sylowF a K 0 (x 6)⁆ = sylowH a K 0 (c * x 6) := comm_famAF hK _ _
    have hHF := commute_centralZ ha hK hFP (x 8)
    rw [← sylowH_zero_eq_centralZ] at hHF
    have hAF' : sylowA a K c * sylowF a K 0 (x 6) * (sylowA a K c)⁻¹ =
        sylowF a K 0 (x 6) * sylowH a K 0 (x 8) := by
      have e1 : sylowA a K c * sylowF a K 0 (x 6) * (sylowA a K c)⁻¹ =
          ⁅sylowA a K c, sylowF a K 0 (x 6)⁆ * sylowF a K 0 (x 6) := by
        rw [commutatorElement_def]
        group
      rw [e1, hAF, hcg]
      exact hHF.symm
    obtain ⟨y, hy, hyH⟩ := hH (x 6) 1 hg one_ne_zero
    refine ⟨y * weylOne K * (sylowA a K c)⁻¹, mul_mem (mul_mem (reeFixedTorus_le_reeGamma hK hy)
      weylS_mem_reeGamma) (inv_mem hAΓ), ?_⟩
    have hF : (sylowA a K c)⁻¹ * (sylowF a K 0 (x 6) * sylowH a K 0 (x 8)) * sylowA a K c =
        sylowF a K 0 (x 6) := by
      rw [← hAF']
      group
    calc y * weylOne K * (sylowA a K c)⁻¹ * (sylowF a K 0 (x 6) * sylowH a K 0 (x 8)) *
          (y * weylOne K * (sylowA a K c)⁻¹)⁻¹
        = y * (weylOne K * ((sylowA a K c)⁻¹ * (sylowF a K 0 (x 6) * sylowH a K 0 (x 8)) *
            sylowA a K c) * (weylOne K)⁻¹) * y⁻¹ := by group
      _ = y * (weylOne K * sylowF a K 0 (x 6) * (weylOne K)⁻¹) * y⁻¹ := by rw [hF]
      _ = y * sylowH a K 0 (x 6) * y⁻¹ := by rw [weylOne_conj_sylowF]
      _ = invE K a := hyH

theorem exists_conj_invF_of_mem_S2 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {u : ModGL F4.tag K} (hu : u ∈ S2 K a) (hu1 : u ∉ S1 K a) :
    ∃ x ∈ F4.reeGamma K a, x * u * x⁻¹ = invF K a := by
  obtain ⟨-, -, -, -, hL, -, -⟩ := large_Ree_every_involution_fuses a ha K hK
  have hu' : u ∈ (S2 K a : Set (ModGL F4.tag K)) := hu
  rw [(S2_spec hK).2.1] at hu'
  obtain ⟨x, hx, rfl⟩ := hu'
  have hl : x 11 ≠ 0 := by
    intro h0
    apply hu1
    have hS1 : sylowVec a K x ∈ (S1 K a : Set (ModGL F4.tag K)) := by
      rw [(S1_spec hK).2.1]
      refine ⟨x, fun n hn => ?_, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx 0 (by decide)
      · exact hx 1 (by decide)
      · exact hx 2 (by decide)
      · exact hx 3 (by decide)
      · exact hx 4 (by decide)
      · exact hx 5 (by decide)
      · exact hx 7 (by decide)
      · exact hx 9 (by decide)
      · exact hx 10 (by decide)
      · exact h0
    exact hS1
  rw [sylowVec_eq_of_mem_S2 hK hx]
  show ∃ y ∈ F4.reeGamma K a,
    y * (sylowF a K 0 (x 6) * sylowH a K 0 (x 8) * sylowL a K (x 11)) * y⁻¹ = sylowL a K 1
  set g := x 6
  set i := x 8
  set l := x 11
  set B := sylowB a K (g * l⁻¹) 0
  set D := sylowD a K (i * l⁻¹) 0
  have hBΓ : B ∈ F4.reeGamma K a := rootV_le_reeGamma hK .i1 (rootElt_mem_rootV _ _)
  have hDΓ : D ∈ F4.reeGamma K a := rootV_le_reeGamma hK .i4 (rootElt_mem_rootV _ _)
  have hBP : B ∈ F4.reeFixedPosUnipotent K a := rootV_le_sylowP hK .i1 (rootElt_mem_rootV _ _)
  have hFP : sylowF a K 0 g ∈ F4.reeFixedPosUnipotent K a :=
    rootV_le_sylowP hK .i11 (rootElt_mem_rootV _ _)
  have hli : l⁻¹ * l = 1 := inv_mul_cancel₀ hl
  have hC3 : ⁅D, sylowL a K l⁆ = sylowH a K 0 i := by
    have := rel_C3 hK (i * l⁻¹) l
    rwa [mul_assoc, hli, mul_one] at this
  have hC2 : ⁅B, sylowL a K l⁆ = sylowF a K 0 g := by
    have := rel_C2 hK (g * l⁻¹) l
    rwa [mul_assoc, hli, mul_one] at this
  have hBH := commute_centralZ ha hK hBP i
  have hFH := commute_centralZ ha hK hFP i
  rw [← sylowH_zero_eq_centralZ] at hBH hFH
  have hD : D * sylowL a K l * D⁻¹ = sylowH a K 0 i * sylowL a K l := by
    rw [← hC3, commutatorElement_def]
    group
  have hB : B * sylowL a K l * B⁻¹ = sylowF a K 0 g * sylowL a K l := by
    rw [← hC2, commutatorElement_def]
    group
  have hy : (B * D) * sylowL a K l * (B * D)⁻¹ =
      sylowF a K 0 g * sylowH a K 0 i * sylowL a K l := by
    calc (B * D) * sylowL a K l * (B * D)⁻¹ = B * (D * sylowL a K l * D⁻¹) * B⁻¹ := by group
      _ = B * sylowH a K 0 i * B⁻¹ * (B * sylowL a K l * B⁻¹) := by rw [hD]; group
      _ = sylowH a K 0 i * (sylowF a K 0 g * sylowL a K l) := by
          rw [hB, hBH, mul_inv_cancel_right]
      _ = sylowF a K 0 g * sylowH a K 0 i * sylowL a K l := by rw [← mul_assoc, ← hFH]
  obtain ⟨z, hz, hzL⟩ := hL l 1 hl one_ne_zero
  refine ⟨z * (B * D)⁻¹, mul_mem (reeFixedTorus_le_reeGamma hK hz) (inv_mem (mul_mem hBΓ hDΓ)),
    ?_⟩
  rw [← hy]
  calc z * (B * D)⁻¹ * ((B * D) * sylowL a K l * (B * D)⁻¹) * (z * (B * D)⁻¹)⁻¹ =
      z * sylowL a K l * z⁻¹ := by group
    _ = sylowL a K 1 := hzL

theorem comm_sylowD_invF (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ⁅sylowD a K 1 0, invF K a⁆ = invE K a := by
  have := rel_C3 hK (m := a) 1 1
  rwa [one_mul] at this

theorem conj_invF_sylowD (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sylowD a K 1 0 * invF K a * (sylowD a K 1 0)⁻¹ = invE K a * invF K a := by
  rw [← comm_sylowD_invF hK, commutatorElement_def]
  group

theorem invF_eq_comm (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    invF K a = ⁅sylowB a K 0 1, sylowD a K 0 1⁆ * ⁅weylOne K, invE K a⁆⁻¹ := by
  have h5 : ⁅sylowB a K 0 1, sylowD a K 0 1⁆ = sylowL a K 1 * sylowF a K 0 1 * sylowH a K 0 1 := by
    have := rel_C5 hK (m := a) 1 1
    simp only [largeReeSigma_one, one_mul] at this
    exact this
  have hse : ⁅weylOne K, invE K a⁆ = sylowF a K 0 1 * sylowH a K 0 1 := by
    have hee : (sylowH a K 0 1)⁻¹ = sylowH a K 0 1 :=
      inv_eq_of_mul_eq_one_right (rootElt_mul_self hK (i := .i12) rfl 1)
    show ⁅weylOne K, sylowH a K 0 1⁆ = _
    rw [commutatorElement_def, weylOne_conj_sylowH, hee]
  rw [h5, hse]
  show sylowL a K 1 = _
  group

theorem mem_rootV12_of_commute (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {u : ModGL F4.tag K} (hu : u ∈ F4.reeFixedPosUnipotent K a)
    (hc : ∀ w ∈ F4.reeFixedPosUnipotent K a, w * u = u * w) : u ∈ rootV K a .i12 := by
  have hmem : u ∈ ((center (F4.reeFixedPosUnipotent K a)).map
      (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) :=
    ⟨⟨u, hu⟩, mem_center_iff.2 fun w => Subtype.ext (hc w w.2), rfl⟩
  rw [coe_center_eq_range_centralZ ha hK] at hmem
  obtain ⟨c, rfl⟩ := hmem
  rw [← sylowH_zero_eq_centralZ]
  exact rootElt_mem_rootV .i12 c

theorem exists_torusH_conj_invE (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {u : ModGL F4.tag K} (hu : u ∈ rootV K a .i12) (hu1 : u ≠ 1) :
    ∃ x ∈ torusH K a, x * invE K a * x⁻¹ = u := by
  obtain ⟨-, -, -, hH, -⟩ := large_Ree_every_involution_fuses a ha K hK
  have hu' : u ∈ (rootV K a .i12 : Set (ModGL F4.tag K)) := hu
  rw [coe_rootV hK] at hu'
  obtain ⟨x, hx, rfl⟩ := hu'
  rw [(sylowVec_eq_of_supp .i12 hx).2 rfl] at hu1 ⊢
  have hc : x Idx.i12.coord ≠ 0 := fun h0 => hu1 (by rw [h0, rootElt_zero])
  obtain ⟨y, hy, hyH⟩ := hH 1 (x Idx.i12.coord) one_ne_zero hc
  exact ⟨y, (torusH_eq_reeFixedTorus hK).symm ▸ hy, hyH⟩

theorem invF_mem_S2_not_mem_S1 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    invF K a ∈ S2 K a ∧ invF K a ∉ S1 K a ∧ invE K a ∈ S1 K a ∧ rootElt K a .i11 1 ∈ S1 K a ∧
      rootElt K a .i11 1 ≠ 1 ∧ rootElt K a .i11 1 ≠ invE K a := by
  have hinj := (bijOn_sylowVec (m := a) (K := K) hK).injOn
  refine ⟨rootV_le_rootJoin (i := .i10) (by decide) (rootElt_mem_rootV _ _), fun hf => ?_,
    rootV_le_rootJoin (i := .i12) (by decide) (rootElt_mem_rootV _ _),
    rootV_le_rootJoin (i := .i11) (by decide) (rootElt_mem_rootV _ _),
    fun h1 => ?_, fun h1 => ?_⟩
  · have hf' : invF K a ∈ (S1 K a : Set (ModGL F4.tag K)) := hf
    rw [(S1_spec hK).2.1] at hf'
    obtain ⟨x, hx, hxe⟩ := hf'
    have hx' : x = Pi.single Idx.i10.coord 1 :=
      hinj (Set.mem_univ _) (Set.mem_univ _) (hxe.trans (rootElt_eq_sylowVec .i10 1))
    have h11 := hx 11 (by decide)
    rw [hx'] at h11
    simp [Idx.coord] at h11
  · have := rootElt_injective hK .i11 (h1.trans (rootElt_zero .i11).symm)
    exact one_ne_zero this
  · have h2 := (rootElt_eq_sylowVec (a := a) (K := K) .i11 1).symm.trans
      (h1.trans (rootElt_eq_sylowVec .i12 1))
    have hx' := congrFun (hinj (Set.mem_univ _) (Set.mem_univ _) h2) 6
    simp [Idx.coord] at hx'

end Model

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem elt_mul' {x y : ModGL F4.tag h.K} (hx : x ∈ F4.reeGamma h.K h.a)
    (hy : y ∈ F4.reeGamma h.K h.a) : h.elt (x * y) = h.elt x * h.elt y := by
  rw [h.elt_of_mem hx, h.elt_of_mem hy, h.elt_of_mem (mul_mem hx hy), ← map_mul]
  rfl

theorem elt_inv' {x : ModGL F4.tag h.K} (hx : x ∈ F4.reeGamma h.K h.a) :
    h.elt x⁻¹ = (h.elt x)⁻¹ := by
  rw [h.elt_of_mem hx, h.elt_of_mem (inv_mem hx), ← map_inv]
  rfl

theorem elt_one' : h.elt 1 = 1 := by
  rw [h.elt_of_mem (one_mem _)]
  exact map_one h.emb

theorem elt_conj' {x y : ModGL F4.tag h.K} (hx : x ∈ F4.reeGamma h.K h.a)
    (hy : y ∈ F4.reeGamma h.K h.a) : h.elt (x * y * x⁻¹) = h.elt x * h.elt y * (h.elt x)⁻¹ := by
  rw [h.elt_mul' (mul_mem hx hy) (inv_mem hx), h.elt_mul' hx hy, h.elt_inv' hx]

theorem elt_commutator {x y : ModGL F4.tag h.K} (hx : x ∈ F4.reeGamma h.K h.a)
    (hy : y ∈ F4.reeGamma h.K h.a) : h.elt ⁅x, y⁆ = ⁅h.elt x, h.elt y⁆ := by
  rw [commutatorElement_def, commutatorElement_def,
    h.elt_mul' (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy), h.elt_conj' hx hy,
    h.elt_inv' hy]

theorem elt_injOn {x y : ModGL F4.tag h.K} (hx : x ∈ F4.reeGamma h.K h.a)
    (hy : y ∈ F4.reeGamma h.K h.a) (e : h.elt x = h.elt y) : x = y := by
  rw [h.elt_of_mem hx, h.elt_of_mem hy] at e
  exact congrArg Subtype.val (h.emb_injective e)

theorem exists_elt_eq {l : G} (hl : l ∈ h.L) : ∃ g ∈ F4.reeGamma h.K h.a, h.elt g = l := by
  rw [← h.range_emb] at hl
  obtain ⟨g, rfl⟩ := hl
  exact ⟨g, g.2, h.elt_of_mem g.2⟩

theorem mem_pull_iff_elt {M : Subgroup (ModGL F4.tag h.K)} {u : G} :
    u ∈ h.pull M ↔ ∃ g ∈ M, g ∈ F4.reeGamma h.K h.a ∧ h.elt g = u := by
  rw [mem_pull]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, g.2, h.elt_of_mem g.2⟩
  · rintro ⟨g, hg, hgΓ, rfl⟩
    exact ⟨⟨g, hgΓ⟩, hg, (h.elt_of_mem hgΓ).symm⟩

theorem commute_elt_iff {x y : ModGL F4.tag h.K} (hx : x ∈ F4.reeGamma h.K h.a)
    (hy : y ∈ F4.reeGamma h.K h.a) : h.elt x * h.elt y = h.elt y * h.elt x ↔ x * y = y * x := by
  rw [← h.elt_mul' hx hy, ← h.elt_mul' hy hx]
  exact ⟨h.elt_injOn (mul_mem hx hy) (mul_mem hy hx), fun e => by rw [e]⟩

theorem exists_conj_e_or_f {l : G}
    (hl : l ∈ h.L) (hl2 : l * l = 1) (hl1 : l ≠ 1) :
    ∃ x ∈ h.L, x * l * x⁻¹ = h.e ∨ x * l * x⁻¹ = h.f := by
  obtain ⟨g, hgΓ, rfl⟩ := h.exists_elt_eq hl
  obtain ⟨hinv, -⟩ := large_Ree_every_involution_fuses h.a h.one_le_a h.K h.card_K
  have hg2 : g ^ 2 = 1 := by
    rw [sq]
    refine h.elt_injOn (mul_mem hgΓ hgΓ) (one_mem _) ?_
    rw [h.elt_mul' hgΓ hgΓ, hl2, h.elt_one']
  have hg1 : g ≠ 1 := fun e => hl1 (by rw [e, h.elt_one'])
  rcases hinv g hgΓ hg2 hg1 with ⟨x, hx, hxg⟩ | ⟨x, hx, hxg⟩
  · refine ⟨h.elt x, h.elt_mem hx, Or.inl ?_⟩
    rw [← h.elt_conj' hx hgΓ, hxg]
    rfl
  · refine ⟨h.elt x, h.elt_mem hx, Or.inr ?_⟩
    rw [← h.elt_conj' hx hgΓ, hxg]
    rfl

theorem elt_sylowD_mem_P :
    h.elt (sylowD h.a h.K 1 0) ∈ h.P :=
  (h.elt_mem_pull (rootV_le_reeGamma h.card_K .i4 (rootElt_mem_rootV _ _))).2
    (rootV_le_sylowP h.card_K .i4 (rootElt_mem_rootV _ _))

theorem e_eq_commutator :
    h.e = ⁅h.elt (sylowD h.a h.K 1 0), h.f⁆ := by
  have hD : sylowD h.a h.K 1 0 ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i4 (rootElt_mem_rootV _ _)
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i10 (rootElt_mem_rootV _ _)
  rw [Setup.f, ← h.elt_commutator hD hF, comm_sylowD_invF h.card_K]
  rfl

theorem conj_f_eq :
    h.elt (sylowD h.a h.K 1 0) * h.f * (h.elt (sylowD h.a h.K 1 0))⁻¹ = h.e * h.f := by
  have hD : sylowD h.a h.K 1 0 ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i4 (rootElt_mem_rootV _ _)
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i10 (rootElt_mem_rootV _ _)
  have hE : invE h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)
  rw [Setup.f, Setup.e, ← h.elt_conj' hD hF, ← h.elt_mul' hE hF, conj_invF_sylowD h.card_K]

theorem f_eq_commutator :
    ∃ x y z w : G, x * h.f = h.f * x ∧ y * h.f = h.f * y ∧ z * h.f = h.f * z ∧
      w * h.f = h.f * w ∧ h.f = ⁅x, y⁆ * ⁅z, w⁆⁻¹ := by
  have hK := h.card_K
  have hB : sylowB h.a h.K 0 1 ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma hK .i2 (rootElt_mem_rootV _ _)
  have hD : sylowD h.a h.K 0 1 ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma hK .i8 (rootElt_mem_rootV _ _)
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a := rootV_le_reeGamma hK .i10 (rootElt_mem_rootV _ _)
  have hE : invE h.K h.a ∈ F4.reeGamma h.K h.a := rootV_le_reeGamma hK .i12 (rootElt_mem_rootV _ _)
  have hS : weylOne h.K ∈ F4.reeGamma h.K h.a := weylS_mem_reeGamma
  have hcm : ∀ {x y : ModGL F4.tag h.K}, x ∈ F4.reeGamma h.K h.a → y ∈ F4.reeGamma h.K h.a →
      ⁅x, y⁆ ∈ F4.reeGamma h.K h.a := fun hx hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hS4 : ∀ {i : Idx}, i ∈ ({.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12} : Finset Idx) →
      ∀ u, rootElt h.K h.a i u * invF h.K h.a = invF h.K h.a * rootElt h.K h.a i u := by
    intro i hi u
    have hmem : rootElt h.K h.a i u ∈ tKernel h.K h.a := by
      rw [← S4_eq_tKernel hK]
      exact rootV_le_rootJoin hi (rootElt_mem_rootV _ _)
    exact mem_centralizer_singleton_iff.1 (tKernel_le_centralizer hK 1 hmem)
  have hsf : weylOne h.K * invF h.K h.a = invF h.K h.a * weylOne h.K :=
    mem_centralizer_singleton_iff.1 (rankOneGroupOne_le_centralizer_sylowL 1 weylS_mem_leviN)
  refine ⟨h.elt (sylowB h.a h.K 0 1), h.elt (sylowD h.a h.K 0 1), h.elt (weylOne h.K), h.e,
    (h.commute_elt_iff hB hF).2 (hS4 (i := .i2) (by decide) 1),
    (h.commute_elt_iff hD hF).2 (hS4 (i := .i8) (by decide) 1),
    (h.commute_elt_iff hS hF).2 hsf,
    (h.commute_elt_iff hE hF).2 (hS4 (i := .i12) (by decide) 1), ?_⟩
  rw [Setup.f, Setup.e, ← h.elt_commutator hB hD, ← h.elt_commutator hS hE,
    ← h.elt_inv' (hcm hS hE), ← h.elt_mul' (hcm hB hD) (inv_mem (hcm hS hE)),
    ← invF_eq_comm hK]

theorem mem_V12_of_commute_P
    {u : G} (hu : u ∈ h.P) (hc : ∀ w ∈ h.P, w * u = u * w) : u ∈ h.V .i12 := by
  obtain ⟨g, hgP, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  refine (h.mem_pull_iff_elt).2 ⟨g, mem_rootV12_of_commute h.one_le_a h.card_K hgP fun w hw => ?_,
    hgΓ, rfl⟩
  have hwΓ : w ∈ F4.reeGamma h.K h.a := (mem_inf.1 hw).2
  exact (h.commute_elt_iff hwΓ hgΓ).1 (hc _ ((h.elt_mem_pull hwΓ).2 hw))

theorem exists_conj_e_of_mem_V12
    {v : G} (hv : v ∈ h.V .i12) (hv1 : v ≠ 1) : ∃ x ∈ h.H, x * h.e * x⁻¹ = v := by
  obtain ⟨g, hgV, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hv
  have hg1 : g ≠ 1 := fun e => hv1 (by rw [e, h.elt_one'])
  obtain ⟨x, hx, hxg⟩ := exists_torusH_conj_invE h.one_le_a h.card_K hgV hg1
  have hxΓ : x ∈ F4.reeGamma h.K h.a := torusH_le_reeGamma h.card_K hx
  have hE : invE h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)
  refine ⟨h.elt x, (h.elt_mem_pull hxΓ).2 hx, ?_⟩
  rw [Setup.e, ← h.elt_conj' hxΓ hE, hxg]

theorem S₂_commute {u w : G}
    (hu : u ∈ h.S₂) (hw : w ∈ h.S₄) : u * w = w * u := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  obtain ⟨k, hk, hkΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hw
  exact (h.commute_elt_iff hgΓ hkΓ).2
    (mem_centralizer_iff.1 (S2_le_centralizer_S4 h.one_le_a h.card_K hg) k hk).symm

theorem mem_S₂_of_commute {u : G}
    (hu : u ∈ h.S₄) (hc : ∀ w ∈ h.S₄, w * u = u * w) : u ∈ h.S₂ := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  refine (h.mem_pull_iff_elt).2 ⟨g, mem_S2_of_commute_S4 h.card_K hg fun k hk => ?_, hgΓ, rfl⟩
  have hkΓ : k ∈ F4.reeGamma h.K h.a := rootJoin_le_sylowP h.card_K _ hk |>.2
  exact (h.commute_elt_iff hkΓ hgΓ).1 (hc _ ((h.elt_mem_pull hkΓ).2 hk))

theorem mul_self_of_mem_S₂ {u : G}
    (hu : u ∈ h.S₂) : u * u = 1 := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  rw [← h.elt_mul' hgΓ hgΓ, mul_self_of_mem_S2 h.one_le_a h.card_K hg, h.elt_one']

theorem exists_conj_e_of_mem_S₁
    {u : G} (hu : u ∈ h.S₁) (hu1 : u ≠ 1) : ∃ x ∈ h.L, x * u * x⁻¹ = h.e := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  have hg1 : g ≠ 1 := fun e => hu1 (by rw [e, h.elt_one'])
  obtain ⟨x, hx, hxg⟩ := exists_conj_invE_of_mem_S1 h.one_le_a h.card_K hg hg1
  exact ⟨h.elt x, h.elt_mem hx, by rw [← h.elt_conj' hx hgΓ, hxg]; rfl⟩

theorem exists_conj_f_of_mem_S₂
    {u : G} (hu : u ∈ h.S₂) (hu1 : u ∉ h.S₁) : ∃ x ∈ h.L, x * u * x⁻¹ = h.f := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  have hg1 : g ∉ S1 h.K h.a := fun e => hu1 ((h.elt_mem_pull hgΓ).2 e)
  obtain ⟨x, hx, hxg⟩ := exists_conj_invF_of_mem_S2 h.one_le_a h.card_K hg hg1
  exact ⟨h.elt x, h.elt_mem hx, by rw [← h.elt_conj' hx hgΓ, hxg]; rfl⟩

theorem f_mem_S₂_e_mem_S₁ :
    h.f ∈ h.S₂ ∧ h.f ∉ h.S₁ ∧ h.e ∈ h.S₁ ∧ ∃ x ∈ h.S₁, x ≠ 1 ∧ x ≠ h.e := by
  have hK := h.card_K
  obtain ⟨hf2, hf1, he1, hx1, hx1', hxe⟩ := invF_mem_S2_not_mem_S1 (a := h.a) hK
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a := rootV_le_reeGamma hK .i10 (rootElt_mem_rootV _ _)
  have hE : invE h.K h.a ∈ F4.reeGamma h.K h.a := rootV_le_reeGamma hK .i12 (rootElt_mem_rootV _ _)
  have hX : rootElt h.K h.a .i11 1 ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma hK .i11 (rootElt_mem_rootV _ _)
  refine ⟨(h.elt_mem_pull hF).2 hf2, fun e => hf1 ((h.elt_mem_pull hF).1 e),
    (h.elt_mem_pull hE).2 he1, h.elt (rootElt h.K h.a .i11 1), (h.elt_mem_pull hX).2 hx1,
    fun e => hx1' (h.elt_injOn hX (one_mem _) (by rw [e, h.elt_one'])),
    fun e => hxe (h.elt_injOn hX hE e)⟩

theorem S₄_le :
    h.S₄ ≤ h.L ⊓ centralizer ({h.f} : Set G) := by
  intro u hu
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i10 (rootElt_mem_rootV _ _)
  refine ⟨h.elt_mem hgΓ, mem_centralizer_singleton_iff.2 ((h.commute_elt_iff hgΓ hF).2 ?_)⟩
  rw [S4_eq_tKernel h.card_K] at hg
  exact mem_centralizer_singleton_iff.1 (tKernel_le_centralizer h.card_K 1 hg)

theorem pull_centralizer_f :
    h.pull (F4.reeGamma h.K h.a ⊓ centralizer {invF h.K h.a}) =
      h.L ⊓ centralizer ({h.f} : Set G) := by
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i10 (rootElt_mem_rootV _ _)
  rw [h.pull_inf, h.pull_reeGamma, h.pull_centralizer hF, ← inf_assoc, inf_idem]
  rfl

theorem conj_mem_S₄
    {y s : G} (hy : y ∈ h.L ⊓ centralizer ({h.f} : Set G))
    (hs : s ∈ h.S₄) : y * s * y⁻¹ ∈ h.S₄ := by
  obtain ⟨-, -, -, -, -, -, -, htN, -⟩ :=
    large_Ree_two_involution_centralizers h.a h.one_le_a h.K h.card_K
  rw [← h.pull_centralizer_f] at hy
  obtain ⟨d, hd, hdΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hy
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hs
  rw [← h.elt_conj' hdΓ hgΓ]
  refine (h.elt_mem_pull (mul_mem (mul_mem hdΓ hgΓ) (inv_mem hdΓ))).2 ?_
  rw [S4_eq_tKernel h.card_K] at hg ⊢
  have hgD : g ∈ F4.reeGamma h.K h.a ⊓ centralizer {invF h.K h.a} := by
    rw [(reeGamma_inf_centralizer_invE_invF h.one_le_a h.card_K).2.2.1, S4_eq_tKernel h.card_K]
    exact mem_sup_left hg
  have hn := htN.conj_mem ⟨g, hgD⟩ (by rwa [mem_subgroupOf]) ⟨d, hd⟩
  rwa [mem_subgroupOf] at hn

theorem le_S₄_of_normal
    {M : Subgroup G}
    (hM : M ≤ h.L ⊓ centralizer ({h.f} : Set G))
    (hMn : ∀ y ∈ h.L ⊓ centralizer ({h.f} : Set G), ∀ m ∈ M, y * m * y⁻¹ ∈ M)
    (hM2 : IsPGroup 2 M) : M ≤ h.S₄ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpc, -⟩ :=
    large_Ree_two_involution_centralizers h.a h.one_le_a h.K h.card_K
  set D := F4.reeGamma h.K h.a ⊓ centralizer {invF h.K h.a} with hDdef
  have hD : D = F4.reeGamma h.K h.a ⊓ centralizer {sylowL h.a h.K 1} := rfl
  have hDpull : ∀ {d : ModGL F4.tag h.K}, d ∈ D → h.elt d ∈ h.L ⊓ centralizer ({h.f} : Set G) :=
    fun hd => by
      rw [← h.pull_centralizer_f]
      exact (h.elt_mem_pull (mem_inf.1 hd).1).2 hd
  let N : Subgroup (ModGL F4.tag h.K) :=
    { carrier := {g | g ∈ F4.reeGamma h.K h.a ∧ h.elt g ∈ M}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [h.elt_mul' hx.1 hy.1]; exact mul_mem hx.2 hy.2⟩
      one_mem' := ⟨one_mem _, by rw [h.elt_one']; exact one_mem _⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [h.elt_inv' hx.1]; exact inv_mem hx.2⟩ }
  have hND : N ≤ D := by
    intro g hg
    have hgL := (hM hg.2).2
    refine mem_inf.2 ⟨hg.1, mem_centralizer_singleton_iff.2 ?_⟩
    have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a :=
      rootV_le_reeGamma h.card_K .i10 (rootElt_mem_rootV _ _)
    exact (h.commute_elt_iff hg.1 hF).1 (mem_centralizer_singleton_iff.1 hgL)
  have hNn : (N.subgroupOf D).Normal := by
    refine ⟨fun n hn d => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hdΓ := (mem_inf.1 d.2).1
    refine ⟨mul_mem (mul_mem hdΓ hn.1) (inv_mem hdΓ), ?_⟩
    simp only [coe_mul, coe_inv]
    rw [h.elt_conj' hdΓ hn.1]
    exact hMn _ (hDpull d.2) _ hn.2
  have hN2 : IsPGroup 2 (N.subgroupOf D) := by
    intro n
    obtain ⟨k, hk⟩ := hM2 ⟨h.elt n, n.2.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hnΓ : ((n : D) : ModGL F4.tag h.K) ∈ F4.reeGamma h.K h.a := n.2.1
    have hpow : ∀ j : ℕ, h.elt (((n : D) : ModGL F4.tag h.K) ^ j) =
        h.elt ((n : D) : ModGL F4.tag h.K) ^ j := by
      intro j
      induction j with
      | zero => rw [pow_zero, pow_zero, h.elt_one']
      | succ j ih => rw [pow_succ, pow_succ, h.elt_mul' (pow_mem hnΓ j) hnΓ, ih]
    have hk' : h.elt ((n : D) : ModGL F4.tag h.K) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    refine h.elt_injOn (pow_mem hnΓ _) (one_mem _) ?_
    rw [hpow, hk', h.elt_one']
  have hle : N.subgroupOf D ≤ CFSG.pCore 2 D := le_sSup ⟨hNn, hN2⟩
  rw [hD] at hle
  rw [hpc] at hle
  intro m hm
  obtain ⟨g, hgΓ, rfl⟩ := h.exists_elt_eq (hM hm).1
  have hgN : g ∈ N := ⟨hgΓ, hm⟩
  have hgD : g ∈ D := hND hgN
  have hgT : g ∈ tKernel h.K h.a := hle (show (⟨g, hgD⟩ : D) ∈ N.subgroupOf D from hgN)
  rw [Setup.S₄, h.elt_mem_pull hgΓ, S4_eq_tKernel h.card_K]
  exact hgT

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
