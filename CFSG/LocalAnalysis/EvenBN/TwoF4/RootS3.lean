module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootA1R

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair f4i)
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam fuel centerEqs centerEqs_vanish tWord
  traceZeros traceZeros_sound centerChecks_V0 coordsOf)
open scoped commutatorElement

@[expose] def testsS3 : List ℕ := [9, 10]

@[expose] def traceS3 : List (ℕ × ℕ) := [(19, 7), (20, 4), (43, 2), (44, 5)]

theorem traceS3_ok :
    traceZeros (centerEqs testsS3) [0, 1, 3, 12, 13, 15] traceS3 [2, 4, 5, 7] = true := by
  decide +kernel

theorem centerChecks_S3 : ∀ n ∈ testsS3,
    collectCheck fuel (sylowWord ++ tWord n) (coordsOf fuel (sylowWord ++ tWord n)) = true ∧
      collectCheck fuel (tWord n ++ sylowWord) (coordsOf fuel (tWord n ++ sylowWord)) = true := by
  intro n hn
  simp only [testsS3, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact centerChecks_V0 9 (by decide)
  · exact centerChecks_V0 10 (by decide)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] in
theorem forced_S3 (c e f g h i j k l : K)
    (hcomm : ∀ n ∈ testsS3, sylowV a K 0 0 c 0 e f g h i j k l * fam a K n 1 =
      fam a K n 1 * sylowV a K 0 0 c 0 e f g h i j k l) :
    c = 0 ∧ e = 0 ∧ f = 0 ∧ h = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hz := traceZeros_sound (m := a) (coordVal a 0 0 c 0 e f g h i j k l)
    (coordVal_add_twelve (m := a) 0 0 c 0 e f g h i j k l) (centerEqs testsS3)
    (centerEqs_vanish (by decide) centerChecks_S3 0 0 c 0 e f g h i j k l hcomm)
    (zs₀ := [0, 1, 3, 12, 13, 15]) (by
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · rfl
      · exact largeReeSigma_zero
      · exact largeReeSigma_zero
      · exact largeReeSigma_zero) traceS3_ok
  exact ⟨hz 2 (by decide), hz 4 (by decide), hz 5 (by decide), hz 7 (by decide)⟩

theorem mem_S3_of_mem_S4_of_commute (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ S4 K a) (h7 : u * rootElt K a .i7 1 = rootElt K a .i7 1 * u)
    (h9 : u * rootElt K a .i9 1 = rootElt K a .i9 1 * u) : u ∈ S3 K a := by
  have hu' : u ∈ (S4 K a : Set (ModGL F4.tag K)) := hu
  rw [(S4_spec hK).2.1] at hu'
  obtain ⟨x, hx, rfl⟩ := hu'
  have h0 : x 0 = 0 := hx 0 (by decide)
  have h1 : x 1 = 0 := hx 1 (by decide)
  have h3 : x 3 = 0 := hx 3 (by decide)
  obtain ⟨h2, h4, h5, h7'⟩ := forced_S3 (a := a) (x 2) (x 4) (x 5) (x 6) (x 7) (x 8)
    (x 9) (x 10) (x 11) fun n hn => by
      simp only [testsS3, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · have := h7
        rw [sylowVec, h0, h1, h3] at this
        exact this
      · have := h9
        rw [sylowVec, h0, h1, h3] at this
        exact this
  have hS3 : sylowVec a K x ∈ (S3 K a : Set (ModGL F4.tag K)) := by
    rw [(S3_spec hK).2.1]
    refine ⟨x, fun n hn => ?_, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  exact hS3

omit [Finite K] [CharP K F4.prime]
  in
theorem commutator_rootSpan_levelSet_le {ℓ : Fin F4.tag.rank → ℤ} (hℓ : ∀ k, 0 ≤ ℓ k)
    {t t' : ℤ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    ⁅rootSpan F4.tag K (levelSet ℓ t), rootSpan F4.tag K (levelSet ℓ t')⁆ ≤
      rootSpan F4.tag K (levelSet ℓ (t + t')) := by
  have hpos : ∀ s : ℤ, rootSpan F4.tag K (levelSet ℓ s) ≤ posUnipotent F4.tag K := fun s =>
    rootSpan_mono fun α hα => ⟨hα.1, hα.2.1⟩
  have h1 := hpos t
  have h2 := hpos t'
  rw [rootSpan_eq_closure K (levelSet ℓ t)] at h1 ⊢
  rw [rootSpan_eq_closure K (levelSet ℓ t')] at h2 ⊢
  refine commutator_closure_le_of_le_normalizer h1 h2
    (posUnipotent_le_normalizer_of_absorbs (fun α hα => ⟨hα.1, hα.2.1⟩)
      (levelSet_absorbs hℓ (t + t'))) ?_
  rintro _ ⟨α, hα, c, rfl⟩ _ ⟨β, hβ, d, rfl⟩
  by_cases hab : α = β
  · subst hab
    rw [commutatorElement_eq_one_iff_mul_comm.2 (rootSubgroup_mul_comm K
      (Subgroup.subset_closure ⟨c, rfl⟩) (Subgroup.subset_closure ⟨d, rfl⟩))]
    exact one_mem _
  · have hle := commutator_rootSubgroup_le K hα.1 hβ.1 hα.2.1 hβ.2.1 hab
    refine (hle.trans (iSup₂_le fun γ hγ => ?_)) (commutator_mem_commutator
      (Subgroup.subset_closure ⟨c, rfl⟩) (Subgroup.subset_closure ⟨d, rfl⟩))
    obtain ⟨hγr, m, n, hm, hn, rfl⟩ := hγ
    have hlev : ∀ {γ : Fin F4.tag.rank → ℤ}, IsRoot F4.tag γ → 0 < height γ →
        0 ≤ level ℓ γ := by
      intro γ hγ hγp
      have := nonneg_of_isRoot_of_height_pos hγ hγp
      unfold level
      have h0 := mul_nonneg (hℓ (f4i 0)) (this (f4i 0))
      have h1 := mul_nonneg (hℓ (f4i 1)) (this (f4i 1))
      have h2 := mul_nonneg (hℓ (f4i 2)) (this (f4i 2))
      have h3 := mul_nonneg (hℓ (f4i 3)) (this (f4i 3))
      linarith
    have e : level ℓ (m • α + n • β) = (m : ℤ) * level ℓ α + (n : ℤ) * level ℓ β := by
      simp only [level, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      ring
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have hαl := hα.2.2
    have hβl := hβ.2.2
    have hα0 := hlev hα.1 hα.2.1
    have hβ0 := hlev hβ.1 hβ.2.1
    have hαp := hα.2.1
    have hβp := hβ.2.1
    refine le_iSup₂_of_le (m • α + n • β) ⟨hγr, ?_, ?_⟩ le_rfl
    · rw [CFSG.LieType.Chevalley.height_nsmul_add_nsmul]
      nlinarith
    · rw [e]
      nlinarith

theorem commutator_reeGamma_le :
    ⁅F4.reeGamma K a, F4.reeGamma K a⁆ ≤ F4.reeGamma K a :=
  (commutator_le).2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem commutator_S4_S3_le (hK : Nat.card K = 2 ^ (2 * a + 1)) : ⁅S4 K a, S3 K a⁆ ≤ S1 K a := by
  have hlev := commutator_rootSpan_levelSet_le (K := K) (ℓ := ![0, 10, 7, 0])
    (fun k => by fin_cases k <;> decide) (t := 17) (t' := 24) (by norm_num) (by norm_num)
  rw [show (17 : ℤ) + 24 = 41 by norm_num] at hlev
  rw [(S4_spec hK).1, (S3_spec hK).1, (S1_spec hK).1]
  exact le_inf ((commutator_mono inf_le_left inf_le_left).trans hlev)
    ((commutator_mono inf_le_right inf_le_right).trans commutator_reeGamma_le)

omit [Finite K] [CharP K F4.prime]
  in
theorem rootJoin_le_centralizer_rootJoin {I J : Finset Idx}
    (hc : ∀ i ∈ I, ∀ j ∈ J, ∀ c d : K,
      rootElt K a i c * rootElt K a j d = rootElt K a j d * rootElt K a i c) :
    rootJoin K a I ≤ centralizer (rootJoin K a J : Set (ModGL F4.tag K)) := by
  refine iSup₂_le fun i hi => ?_
  rw [rootV, closure_le]
  rintro _ ⟨c, rfl⟩
  have hle : rootJoin K a J ≤ centralizer {rootElt K a i c} := iSup₂_le fun j hj => by
    rw [rootV, closure_le]
    rintro _ ⟨d, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hc i hi j hj c d).symm
  exact mem_centralizer_iff.2 fun g hg => mem_centralizer_singleton_iff.1 (hle hg)

omit [Finite K] [CharP K F4.prime]
  in
theorem rootV_le_centralizer_rootV {i j : Idx}
    (hc : ∀ c d : K, rootElt K a i c * rootElt K a j d = rootElt K a j d * rootElt K a i c) :
    rootV K a i ≤ centralizer (rootV K a j : Set (ModGL F4.tag K)) := by
  have e : ∀ k : Idx, rootJoin K a {k} = rootV K a k := fun k => by
    rw [rootJoin]
    simp
  rw [← e i, ← e j]
  exact rootJoin_le_centralizer_rootJoin fun i' hi' j' hj' c d => by
    rw [Finset.mem_singleton] at hi' hj'
    subst hi' hj'
    exact hc c d

theorem S3_le_centralizer_S3 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S3 K a ≤ centralizer (S3 K a : Set (ModGL F4.tag K)) := by
  have hS2 := S2_le_centralizer_S4 ha hK
  have hS34 : S3 K a ≤ S4 K a := (S1_le_S2_le_S3_le_S4_le_radS hK).2.2.1
  have h2 : ∀ {k : Idx}, k ∈ ({.i10, .i11, .i12} : Finset Idx) → ∀ (e : K)
      (g : ModGL F4.tag K), g ∈ S4 K a → rootElt K a k e * g = g * rootElt K a k e :=
    fun hk e g hg =>
      (mem_centralizer_iff.1 (hS2 (rootV_le_rootJoin hk (rootElt_mem_rootV _ _))) g hg).symm
  have hS3 : ∀ {k : Idx}, k ∈ ({.i7, .i9, .i10, .i11, .i12} : Finset Idx) → ∀ e : K,
      rootElt K a k e ∈ S4 K a := fun hk e => hS34 (rootV_le_rootJoin hk (rootElt_mem_rootV _ _))
  have h79 : ∀ {i : Idx}, i ∈ ({.i7, .i9, .i10, .i11, .i12} : Finset Idx) →
      i ∉ ({.i10, .i11, .i12} : Finset Idx) → i = .i7 ∨ i = .i9 := by decide
  refine rootJoin_le_centralizer_rootJoin fun i hi j hj c d => ?_
  by_cases hi' : i ∈ ({.i10, .i11, .i12} : Finset Idx)
  · exact h2 hi' c _ (hS3 hj d)
  by_cases hj' : j ∈ ({.i10, .i11, .i12} : Finset Idx)
  · exact (h2 hj' d _ (hS3 hi c)).symm
  rcases h79 hi hi' with rfl | rfl <;> rcases h79 hj hj' with rfl | rfl
  · rw [← rootElt_add hK rfl, ← rootElt_add hK rfl, add_comm]
  · exact commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_7_9 hK c d)
  · exact (commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_7_9 hK d c)).symm
  · rw [← rootElt_add hK rfl, ← rootElt_add hK rfl, add_comm]

omit [Finite K] [CharP K F4.prime]
  in
theorem mem_normalizer_rootJoin_of_forall {I : Finset Idx} {g : ModGL F4.tag K}
    (hg : ∀ i ∈ I, g ∈ normalizer (rootV K a i : Set (ModGL F4.tag K))) :
    g ∈ normalizer (rootJoin K a I : Set (ModGL F4.tag K)) := by
  have key : ∀ {g : ModGL F4.tag K},
      (∀ i ∈ I, g ∈ normalizer (rootV K a i : Set (ModGL F4.tag K))) →
      ∀ x ∈ rootJoin K a I, g * x * g⁻¹ ∈ rootJoin K a I := by
    intro g hg x hx
    have hle : rootJoin K a I ≤ (rootJoin K a I).comap (MulAut.conj g).toMonoidHom :=
      iSup₂_le fun i hi y hy => rootV_le_rootJoin hi ((mem_normalizer_iff.1 (hg i hi) y).1 hy)
    exact hle hx
  refine mem_normalizer_of_conj_mem (key hg) fun x hx => ?_
  have := key (g := g⁻¹) (fun i hi => inv_mem (hg i hi)) x hx
  rwa [inv_inv] at this

omit [Finite K] in
theorem weylS_mem_normalizer_rootJoin {I : Finset Idx} (h3 : Idx.i3 ∉ I)
    (hI : ∀ i ∈ I, i.sPerm ∈ I) :
    weylS K ∈ normalizer (rootJoin K a I : Set (ModGL F4.tag K)) := by
  have hle : ∀ x ∈ rootJoin K a I, weylS K * x * (weylS K)⁻¹ ∈ rootJoin K a I := by
    intro x hx
    have hle' : rootJoin K a I ≤ (rootJoin K a I).comap (MulAut.conj (weylS K)).toMonoidHom := by
      refine iSup₂_le fun i hi => ?_
      rw [rootV, closure_le]
      rintro _ ⟨u, rfl⟩
      show weylS K * rootElt K a i u * (weylS K)⁻¹ ∈ rootJoin K a I
      rw [weylS_conj_rootElt (fun e => h3 (e ▸ hi))]
      exact rootV_le_rootJoin (hI i hi) (rootElt_mem_rootV _ _)
    exact hle' hx
  have hinv : (weylS K)⁻¹ = weylS K := inv_eq_of_mul_eq_one_right weylS_mul_self
  refine mem_normalizer_of_conj_mem hle fun x hx => ?_
  have := hle x hx
  rw [hinv] at this ⊢
  exact this

theorem leviN_three_le_normalizer_rootJoin (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {I : Finset Idx} (h3 : Idx.i3 ∉ I) (hI : ∀ i ∈ I, i.sPerm ∈ I)
    (hP : F4.reeFixedPosUnipotent K a ≤ normalizer (rootJoin K a I : Set (ModGL F4.tag K))) :
    leviN K a .i3 ≤ normalizer (rootJoin K a I : Set (ModGL F4.tag K)) := by
  rw [leviN_three_eq_closure ha hK, closure_le]
  rintro x (hx | hx)
  · exact hP (rootV_le_sylowP hK .i3 hx)
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact weylS_mem_normalizer_rootJoin h3 hI

theorem reeGamma_inf_normalizer_radS_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {I : Finset Idx}
    (hP : F4.reeFixedPosUnipotent K a ≤ normalizer (rootJoin K a I : Set (ModGL F4.tag K)))
    (hN : leviN K a .i3 ≤ normalizer (rootJoin K a I : Set (ModGL F4.tag K))) :
    F4.reeGamma K a ⊓ normalizer (radS K a : Set (ModGL F4.tag K)) ≤
      normalizer (rootJoin K a I : Set (ModGL F4.tag K)) := by
  rw [(miyamoto_2_3 ha hK).2.1]
  refine sup_le (sup_le ((rootJoin_le_sylowP hK _).trans hP) hN) fun x hx => ?_
  exact mem_normalizer_rootJoin_of_forall fun i _ =>
    torusH_le_normalizer_rootV hK i (torusHi_le_torusH _ hx)

omit [Finite K] [CharP K F4.prime]
  in
theorem exactEntrywiseAut_mem_rootJoin (σ : K ≃+* K) {J : Finset Idx} {g : ModGL F4.tag K}
    (hg : g ∈ rootJoin K a J) : exactEntrywiseAut F4.tag σ g ∈ rootJoin K a J := by
  have hle : rootJoin K a J ≤
      (rootJoin K a J).comap (exactEntrywiseAut F4.tag σ).toMonoidHom := by
    refine iSup₂_le fun i hi => ?_
    rw [rootV, closure_le]
    rintro _ ⟨u, rfl⟩
    show exactEntrywiseAut F4.tag σ (rootElt K a i u) ∈ rootJoin K a J
    rw [exactEntrywiseAut_apply, entrywise_rootElt]
    exact rootV_le_rootJoin hi (rootElt_mem_rootV _ _)
  exact hle hg

theorem rootElt_not_mem_of_coe (hK : Nat.card K = 2 ^ (2 * a + 1))
    {H : Subgroup (ModGL F4.tag K)} {Z : Finset (Fin 12)}
    (hH : (H : Set (ModGL F4.tag K)) = sylowVec a K '' {x | ∀ n ∈ Z, x n = 0}) {i : Idx}
    (hi : i.coord ∈ Z) {u : K} (hu : u ≠ 0) : rootElt K a i u ∉ H := by
  intro hmem
  have h' : rootElt K a i u ∈ (H : Set (ModGL F4.tag K)) := hmem
  rw [hH, rootElt_eq_sylowVec] at h'
  obtain ⟨x, hx, hxe⟩ := h'
  have hx' := (bijOn_sylowVec (m := a) (K := K) hK).injOn (Set.mem_univ _) (Set.mem_univ _) hxe
  have h2 := congrFun hx' i.coord
  rw [Pi.single_eq_same, hx _ hi] at h2
  exact hu h2.symm

theorem reeGamma_inf_centralizer_S3_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ centralizer (S3 K a : Set (ModGL F4.tag K)) ≤ S3 K a := by
  rintro y ⟨hyΓ, hyc⟩
  obtain ⟨h12, -, -, -⟩ := S1_le_S2_le_S3_le_S4_le_radS (K := K) (a := a) hK
  have hfS3 : invF K a ∈ S3 K a := rootV_le_rootJoin (i := .i10) (by decide)
    (rootElt_mem_rootV _ _)
  have hyD : y ∈ F4.reeGamma K a ⊓ centralizer {invF K a} :=
    mem_inf.2 ⟨hyΓ, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hyc _ hfS3).symm⟩
  rw [(reeGamma_inf_centralizer_invE_invF ha hK).2.2.1, sup_comm] at hyD
  have hN4 : leviN K a .i3 ≤ normalizer (S4 K a : Set (ModGL F4.tag K)) := by
    rw [S4_eq_tKernel hK]
    exact rankOneGroupOne_le_normalizer_tKernel hK
  have hyD' : y ∈ ((leviN K a .i3 ⊔ S4 K a : Subgroup (ModGL F4.tag K)) :
      Set (ModGL F4.tag K)) := hyD
  rw [coe_mul_of_left_le_normalizer_right _ _ hN4, Set.mem_mul] at hyD'
  obtain ⟨n, hn, q, hq, rfl⟩ := hyD'
  have hN2 : leviN K a .i3 ≤ normalizer (S2 K a : Set (ModGL F4.tag K)) :=
    leviN_three_le_normalizer_rootJoin ha hK (by decide) (by decide) (S2_spec hK).2.2.2
  have hN3 : leviN K a .i3 ≤ normalizer (S3 K a : Set (ModGL F4.tag K)) :=
    leviN_three_le_normalizer_rootJoin ha hK (by decide) (by decide) (S3_spec hK).2.2.2
  let D : Subgroup (leviN K a .i3) :=
    { carrier := {m | ∀ v ∈ S3 K a, ⁅(m : ModGL F4.tag K), v⁆ ∈ S2 K a}
      mul_mem' := fun {m m'} hm hm' v hv => by
        have e : ⁅((m * m' : leviN K a .i3) : ModGL F4.tag K), v⁆ =
            (m : ModGL F4.tag K) * ⁅(m' : ModGL F4.tag K), v⁆ * (m : ModGL F4.tag K)⁻¹ *
              ⁅(m : ModGL F4.tag K), v⁆ := by
          rw [Subgroup.coe_mul]
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.1 (hN2 m.2) _).1 (hm' v hv)) (hm v hv)
      one_mem' := fun v _ => by
        rw [OneMemClass.coe_one, commutatorElement_one_left]
        exact one_mem _
      inv_mem' := fun {m} hm v hv => by
        have hw : (m : ModGL F4.tag K)⁻¹ * v * m ∈ S3 K a := by
          have := (mem_normalizer_iff.1 (hN3 (inv_mem m.2)) v).1 hv
          rwa [inv_inv] at this
        have e : ⁅((m⁻¹ : leviN K a .i3) : ModGL F4.tag K), v⁆ =
            ⁅(m : ModGL F4.tag K), (m : ModGL F4.tag K)⁻¹ * v * m⁆⁻¹ := by
          rw [InvMemClass.coe_inv]
          simp only [commutatorElement_def]
          group
        rw [e]
        exact inv_mem (hm _ hw) }
  have hDn : D.Normal := ⟨fun m hm k v hv => by
    have hw : (k : ModGL F4.tag K)⁻¹ * v * k ∈ S3 K a := by
      have := (mem_normalizer_iff.1 (hN3 (inv_mem k.2)) v).1 hv
      rwa [inv_inv] at this
    have e : ⁅((k * m * k⁻¹ : leviN K a .i3) : ModGL F4.tag K), v⁆ =
        (k : ModGL F4.tag K) * ⁅(m : ModGL F4.tag K), (k : ModGL F4.tag K)⁻¹ * v * k⁆ *
          (k : ModGL F4.tag K)⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (hN2 k.2) _).1 (hm _ hw)⟩
  obtain ⟨hs, -⟩ := isSimpleGroup_leviN ha hK .i3
  have h7 : rootElt K a .i7 1 ∈ S3 K a := rootV_le_rootJoin (i := .i7) (by decide)
    (rootElt_mem_rootV _ _)
  have h9 : rootElt K a .i9 1 ∈ S3 K a := rootV_le_rootJoin (i := .i9) (by decide)
    (rootElt_mem_rootV _ _)
  have h3 : (⟨rootElt K a .i3 1, rootV_le_leviN hK .i3 (rootElt_mem_rootV _ _)⟩ :
      leviN K a .i3) ∉ D := by
    intro hmem
    have hc := hmem _ h7
    simp only [rootElt_comm_3_7 hK, largeReeSigma_one, one_mul] at hc
    have h10 : rootElt K a .i10 1 ∈ S2 K a := rootV_le_rootJoin (i := .i10) (by decide)
      (rootElt_mem_rootV _ _)
    have h9' : rootElt K a .i9 1 ∈ S2 K a := by
      have := mul_mem hc (inv_mem h10)
      rwa [mul_inv_cancel_right] at this
    exact rootElt_not_mem_of_coe hK (S2_spec hK).2.1 (i := .i9) (by decide) one_ne_zero h9'
  have hnD : (⟨n, hn⟩ : leviN K a .i3) ∈ D := fun v hv => by
    have hc : ⁅q, v⁆ ∈ S2 K a := h12 (commutator_S4_S3_le hK (commutator_mem_commutator hq hv))
    have hcomm := mem_centralizer_iff.1 hyc v hv
    have h1 : n * q * v * (n * q)⁻¹ = v := by rw [← hcomm]; group
    have e : ⁅n, v⁆ = (n * ⁅q, v⁆ * n⁻¹)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc ⁅n, v⁆ * (n * ⁅q, v⁆ * n⁻¹) =
          n * v * n⁻¹ * v⁻¹ * (n * (q * v * q⁻¹ * v⁻¹) * n⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def]
        _ = n * v * n⁻¹ * v⁻¹ * (n * q * v * (n * q)⁻¹) * (n * v⁻¹ * n⁻¹) := by group
        _ = 1 := by rw [h1]; group
    show ⁅n, v⁆ ∈ S2 K a
    rw [e]
    exact inv_mem ((mem_normalizer_iff.1 (hN2 hn) _).1 hc)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs D hDn with hD | hD
  · have hn1 : n = 1 := by
      have hmem : (⟨n, hn⟩ : leviN K a .i3) ∈ (⊥ : Subgroup (leviN K a .i3)) := hD ▸ hnD
      exact congrArg Subtype.val ((mem_bot).1 hmem)
    subst hn1
    rw [one_mul] at hyc ⊢
    exact mem_S3_of_mem_S4_of_commute hK hq (mem_centralizer_iff.1 hyc _ h7).symm
      (mem_centralizer_iff.1 hyc _ h9).symm
  · exact (h3 (by rw [hD]; exact mem_top _)).elim

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem S3_le_reeGamma : S3 h.K h.a ≤ F4.reeGamma h.K h.a :=
  (rootJoin_le_sylowP h.card_K _).trans inf_le_right

theorem V_le_S₃ {k : Idx} (hk : k ∈ ({.i7, .i9, .i10, .i11, .i12} : Finset Idx)) :
    h.V k ≤ h.S₃ := h.pull_mono (rootV_le_rootJoin hk)

theorem L_inf_centralizer_S₃_le : h.L ⊓ centralizer (h.S₃ : Set G) ≤ h.S₃ := by
  rw [S₃, ← h.pull_centralizer_subgroup h.S3_le_reeGamma]
  intro x hx
  obtain ⟨g, hg, hgΓ, rfl⟩ := h.mem_pull_iff_elt.1 hx
  exact (h.elt_mem_pull hgΓ).2
    (reeGamma_inf_centralizer_S3_le h.one_le_a h.card_K (mem_inf.2 ⟨hgΓ, hg⟩))

theorem C_inf_centralizer_S₃_le : h.C ⊓ centralizer (h.S₃ : Set G) ≤ h.S₃ ⊔ zpowers h.t := by
  intro x hx
  obtain ⟨hxC, hxS⟩ := mem_inf.1 hx
  have hxV : x ∈ h.CE := mem_inf.2 ⟨hxC, centralizer_le (SetLike.coe_subset_coe.2
    (h.V_le_S₃ (k := .i12) (by decide))) hxS⟩
  obtain ⟨r, hr, m, hm, hxe | hxe⟩ := h.exists_of_mem_CE hxV
  all_goals
    have hlL : r * m ∈ h.L := mul_mem (h.R_le_L hr) (h.N_le_L _ hm)
    have htS : h.t ∈ centralizer (h.S₃ : Set G) :=
      centralizer_le (SetLike.coe_subset_coe.2 (h.pull_le_L _)) h.htL
    have hlS : r * m ∈ centralizer (h.S₃ : Set G) := by
      first
        | rw [← hxe]; exact hxS
        | (have := mul_mem hxS (inv_mem htS); rwa [hxe, mul_inv_cancel_right] at this)
    have hl : r * m ∈ h.S₃ := h.L_inf_centralizer_S₃_le (mem_inf.2 ⟨hlL, hlS⟩)
  · rw [hxe]
    exact mem_sup_left hl
  · rw [hxe]
    exact mul_mem (mem_sup_left hl) (mem_sup_right (mem_zpowers _))

theorem S₃_comm {u v : G} (hu : u ∈ h.S₃) (hv : v ∈ h.S₃) : u * v = v * u := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hu
  obtain ⟨k, hk, hkΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hv
  exact (h.commute_elt_iff hgΓ hkΓ).2
    (mem_centralizer_iff.1 (S3_le_centralizer_S3 h.one_le_a h.card_K hg) k hk).symm

theorem comm_S₄_S₃_mem {u v : G} (hu : u ∈ h.S₄) (hv : v ∈ h.S₃) : ⁅u, v⁆ ∈ h.S₁ := by
  have hS4Γ : S4 h.K h.a ≤ F4.reeGamma h.K h.a := (rootJoin_le_sylowP h.card_K _).trans inf_le_right
  have e := h.pull_mono (commutator_S4_S3_le h.card_K)
  rw [h.pull_commutator hS4Γ h.S3_le_reeGamma] at e
  exact e (commutator_mem_commutator hu hv)

theorem V_comm_of_rootElt_comm {i j : Idx}
    (hc : ∀ c d : h.K, rootElt h.K h.a i c * rootElt h.K h.a j d =
      rootElt h.K h.a j d * rootElt h.K h.a i c) {g v : G} (hg : g ∈ h.V i) (hv : v ∈ h.V j) :
    g * v = v * g :=
  (mem_centralizer_iff.1 (h.pull_le_centralizer (rootV_le_centralizer_rootV hc) hg) v hv).symm

theorem comm_V7_V9_V10 :
    (∀ g ∈ h.V .i7, ∀ v ∈ h.V .i9, g * v = v * g) ∧
      (∀ g ∈ h.V .i7, ∀ v ∈ h.V .i10, g * v = v * g) ∧
      (∀ g ∈ h.V .i6, ∀ v ∈ h.V .i10, g * v = v * g) :=
  ⟨fun _ hg _ hv => h.V_comm_of_rootElt_comm (fun c d =>
      commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_7_9 h.card_K c d)) hg hv,
    fun _ hg _ hv => h.V_comm_of_rootElt_comm (fun c d =>
      commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_7_10 h.card_K c d)) hg hv,
    fun _ hg _ hv => h.V_comm_of_rootElt_comm (fun c d =>
      commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_6_10 h.card_K c d)) hg hv⟩

theorem V_le_R {k : Idx} (hk : k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx)) :
    h.V k ≤ h.R := h.pull_mono (rootV_le_rootJoin hk)

theorem left_mem_normalizer (x : h.C) {M : Subgroup (ModGL F4.tag h.K)}
    (hMΓ : M ≤ F4.reeGamma h.K h.a)
    (hσ : ∀ (σ : h.K ≃+* h.K) {g : ModGL F4.tag h.K}, g ∈ M → exactEntrywiseAut F4.tag σ g ∈ M)
    (hx : ∀ v ∈ h.pull M, (x : G) * v * (x : G)⁻¹ ∈ h.pull M) :
    ((h.actSemi x).left : ModGL F4.tag h.K) ∈ normalizer (M : Set (ModGL F4.tag h.K)) := by
  have hyΓ := ((h.actSemi x).left).2
  have hfin : Finite M := by
    have := h.finite_reeGamma
    exact Finite.of_injective (fun z : M => (⟨z, hMΓ z.2⟩ : F4.reeGamma h.K h.a))
      fun z z' e => Subtype.ext (by simpa using congrArg Subtype.val e)
  have hle : M.map (MulAut.conj ((h.actSemi x).left : ModGL F4.tag h.K)).toMonoidHom ≤ M := by
    rintro _ ⟨g', hg', rfl⟩
    have hg : (exactEntrywiseAut F4.tag (h.fieldFactor x)).symm g' ∈ M :=
      hσ (h.fieldFactor x).symm hg'
    have hgg' : Units.map (entrywiseHom (h.fieldFactor x).toRingHom)
        ((exactEntrywiseAut F4.tag (h.fieldFactor x)).symm g') = g' :=
      (exactEntrywiseAut F4.tag (h.fieldFactor x)).apply_symm_apply g'
    have h1 := hx _ ((h.elt_mem_pull (hMΓ hg)).2 hg)
    rw [h.conj_elt_eq x (hMΓ hg), hgg'] at h1
    exact (h.elt_mem_pull (mul_mem (mul_mem hyΓ (hMΓ hg')) (inv_mem hyΓ))).1 h1
  exact mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj _).injective]))

theorem conj_mem_pull_of_left (x : h.C) {M : Subgroup (ModGL F4.tag h.K)}
    (hMΓ : M ≤ F4.reeGamma h.K h.a)
    (hσ : ∀ (σ : h.K ≃+* h.K) {g : ModGL F4.tag h.K}, g ∈ M → exactEntrywiseAut F4.tag σ g ∈ M)
    (hy : ((h.actSemi x).left : ModGL F4.tag h.K) ∈ normalizer (M : Set (ModGL F4.tag h.K)))
    {v : G} (hv : v ∈ h.pull M) : (x : G) * v * (x : G)⁻¹ ∈ h.pull M := by
  have hyΓ := ((h.actSemi x).left).2
  obtain ⟨g, hg, hgΓ, rfl⟩ := h.mem_pull_iff_elt.1 hv
  have hg' : Units.map (entrywiseHom (h.fieldFactor x).toRingHom) g ∈ M := hσ _ hg
  rw [h.conj_elt_eq x hgΓ]
  exact (h.elt_mem_pull (mul_mem (mul_mem hyΓ (hMΓ hg')) (inv_mem hyΓ))).2
    ((mem_normalizer_iff.1 hy _).1 hg')

theorem Kp_le_normalizer_pull {M : Subgroup (ModGL F4.tag h.K)} (hMΓ : M ≤ F4.reeGamma h.K h.a)
    (hσ : ∀ (σ : h.K ≃+* h.K) {g : ModGL F4.tag h.K}, g ∈ M → exactEntrywiseAut F4.tag σ g ∈ M)
    (hN : F4.reeGamma h.K h.a ⊓ normalizer (radS h.K h.a : Set (ModGL F4.tag h.K)) ≤
      normalizer (M : Set (ModGL F4.tag h.K))) :
    h.Kp ≤ normalizer (h.pull M : Set G) := by
  have hσS : ∀ (σ : h.K ≃+* h.K) {g : ModGL F4.tag h.K}, g ∈ radS h.K h.a →
      exactEntrywiseAut F4.tag σ g ∈ radS h.K h.a := fun σ _ hg =>
    exactEntrywiseAut_mem_rootJoin σ hg
  have key : ∀ k ∈ h.Kp, ∀ v ∈ h.pull M, k * v * k⁻¹ ∈ h.pull M := by
    intro k hk v hv
    obtain ⟨hkC, hkS⟩ := mem_inf.1 hk
    have hkS' : k ∈ normalizer (h.pull (radS h.K h.a) : Set G) := hkS
    have hyS := h.left_mem_normalizer ⟨k, hkC⟩ (radS_le_reeGamma h.card_K) hσS
      fun w hw => (mem_normalizer_iff.1 hkS' w).1 hw
    exact h.conj_mem_pull_of_left ⟨k, hkC⟩ hMΓ hσ
      (hN (mem_inf.2 ⟨((h.actSemi ⟨k, hkC⟩).left).2, hyS⟩)) hv
  intro k hk
  refine mem_normalizer_of_conj_mem (key k hk) fun v hv => ?_
  have := key k⁻¹ (inv_mem hk) v hv
  rwa [inv_inv] at this

theorem Kp_le_normalizer_S₂_S₃_S₄ :
    h.Kp ≤ normalizer (h.S₂ : Set G) ∧ h.Kp ≤ normalizer (h.S₃ : Set G) ∧
      h.Kp ≤ normalizer (h.S₄ : Set G) := by
  have hK := h.card_K
  have ha := h.one_le_a
  have hσ : ∀ (I : Finset Idx) (σ : h.K ≃+* h.K) {g : ModGL F4.tag h.K},
      g ∈ rootJoin h.K h.a I → exactEntrywiseAut F4.tag σ g ∈ rootJoin h.K h.a I :=
    fun I σ _ hg => exactEntrywiseAut_mem_rootJoin σ hg
  have hΓ : ∀ I : Finset Idx, rootJoin h.K h.a I ≤ F4.reeGamma h.K h.a := fun I =>
    (rootJoin_le_sylowP hK I).trans inf_le_right
  have h2 : h.Kp ≤ normalizer (h.pull (S2 h.K h.a) : Set G) :=
    h.Kp_le_normalizer_pull (hΓ _) (hσ _)
      (reeGamma_inf_normalizer_radS_le ha hK (S2_spec hK).2.2.2
        (leviN_three_le_normalizer_rootJoin ha hK (by decide) (by decide) (S2_spec hK).2.2.2))
  have h3 : h.Kp ≤ normalizer (h.pull (S3 h.K h.a) : Set G) :=
    h.Kp_le_normalizer_pull (hΓ _) (hσ _)
      (reeGamma_inf_normalizer_radS_le ha hK (S3_spec hK).2.2.2
        (leviN_three_le_normalizer_rootJoin ha hK (by decide) (by decide) (S3_spec hK).2.2.2))
  have hN4 : leviN h.K h.a .i3 ≤ normalizer (S4 h.K h.a : Set (ModGL F4.tag h.K)) := by
    rw [S4_eq_tKernel hK]
    exact rankOneGroupOne_le_normalizer_tKernel hK
  have h4 : h.Kp ≤ normalizer (h.pull (S4 h.K h.a) : Set G) :=
    h.Kp_le_normalizer_pull (hΓ _) (hσ _)
      (reeGamma_inf_normalizer_radS_le ha hK (S4_spec hK).2.2.2 hN4)
  exact ⟨h2, h3, h4⟩

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem comm_V_WA_eq_one {m j : Idx} (hm : m.isCenter = false) (hmR : h.V m ≤ h.R)
    (hjj : IsWPair j j) (hjS : j.isSz = false)
    (hmj : ∀ g ∈ h.V m, ∀ v ∈ h.V j, g * v = v * g)
    (hb : Idx.brace m j ≠ Idx.brace m .i12) {g x : G} (hg : g ∈ h.V m) (hx : x ∈ d.WA j) :
    ⁅g, x⁆ = 1 := by
  classical
  have hbr := hjj.brace
  have hex : ∀ c : h.K, ∃ z ∈ d.WA j, ⁅z, h.t⁆ = h.elt (rootElt h.K h.a j c) := fun c =>
    d.exists_WA_comm_t (h.V_le_R₁ hjj.mem) (h.V_le_CH hjj.isCenter (Or.inl rfl))
      (h.elt_rootElt_mem_V j c)
  choose lam hlam hlamt using hex
  have hR : ∀ {g z : G}, g ∈ h.V m → z ∈ d.WA j → ⁅g, z⁆ ∈ h.R₁ := fun {g z} hg hz => by
    obtain ⟨hA, ht⟩ := d.comm_J_A1 (h.R_le_J (hmR hg)) hz.1
    refine d.mem_R₁_of_mem_A1 hA ?_
    rw [ht, commutatorElement_eq_one_iff_mul_comm.2
      (hmj _ hg _ (d.comm_t_mem_V_of_mem_WA hjj.isCenter hbr hz))]
  have hV12 : ∀ {g z : G}, g ∈ h.V m → z ∈ d.WA j → ⁅g, z⁆ ∈ h.V .i12 := fun {g z} hg hz =>
    h.mem_V_of_mem_R₁_of_mem_CH (i := .i5) (k := .i12) rfl (by decide) (hR hg hz)
      (d.W12_le_CH (d.commutator_R_A1_le (commutator_mem_commutator (hmR hg) hz.1)))
  have hmod : ∀ {z : G}, z ∈ d.WA j → ∀ {c : h.K},
      ⁅z, h.t⁆ = h.elt (rootElt h.K h.a j c) → z * (lam c)⁻¹ ∈ h.V j := fun {z} hz {c} hzc =>
    d.mem_V_of_mem_WA hjj.isCenter hbr (mul_mem hz (inv_mem (hlam c))) (by
      rw [d.comm_t_mul_A1 hz.1 (inv_mem (hlam c)).1, d.comm_t_inv_A1 (hlam c).1, hzc, hlamt,
        mul_inv_cancel])
  have hred : ∀ {g v z : G}, g ∈ h.V m → v ∈ h.V j → z ∈ d.WA j →
      ⁅g, v * z⁆ = ⁅g, z⁆ := fun {g v z} hg hv hz => by
    rw [commutatorElement_mul_right_eq,
      commutatorElement_eq_one_iff_mul_comm.2 (hmj _ hg _ hv), one_mul,
      h.R₁_comm (h.V_le_R₁ hjj.mem hv) (hR hg hz), mul_inv_cancel_right]
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hmside : ∀ e c : h.K, h.r1c ⁅h.elt (rootElt h.K h.a m e), lam c⁆ .i12 = 0 := by
    intro e c
    have hg := h.elt_rootElt_mem_V m e
    refine h.r1c_eq_zero_of_brace_ne' (i := m) (j := j) hm
      (Ψ := fun c => ⁅h.elt (rootElt h.K h.a m e), lam c⁆) (fun c c' l hl => ?_)
      (fun t ht c l hl => ?_) (k := .i12) rfl hb c
    · show h.r1c ⁅h.elt (rootElt h.K h.a m e), lam (c + c')⁆ l =
        h.r1c ⁅h.elt (rootElt h.K h.a m e), lam c⁆ l +
          h.r1c ⁅h.elt (rootElt h.K h.a m e), lam c'⁆ l
      have hz : lam c * lam c' ∈ d.WA j := mul_mem (hlam c) (hlam c')
      have hzc : ⁅lam c * lam c', h.t⁆ = h.elt (rootElt h.K h.a j (c + c')) := by
        rw [d.comm_t_mul_A1 (hlam c).1 (hlam c').1, hlamt, hlamt, rootElt_add h.card_K hjS,
          h.elt_mul' (hΓ _ _) (hΓ _ _)]
      have hv : lam (c + c') * (lam c * lam c')⁻¹ ∈ h.V j := by
        have := inv_mem (hmod hz hzc)
        rwa [mul_inv_rev, inv_inv] at this
      have e1 : lam (c + c') = (lam (c + c') * (lam c * lam c')⁻¹) * (lam c * lam c') := by
        group
      rw [e1, hred hg hv hz, commutatorElement_mul_right_eq, ← mem_centralizer_iff.1
        (d.A1_le_centralizer_R₁ (hlam c).1) _ (hR hg (hlam c')), mul_inv_cancel_right,
        h.r1c_mul (hR hg (hlam c)) (hR hg (hlam c')) hl]
    · set b := h.elt (torusPair h.a t) with hbdef
      have hb : b ∈ h.Ht m := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hbH := h.Ht_le_H m hb
      have hgb : h.elt (rootElt h.K h.a m e) * b = b * h.elt (rootElt h.K h.a m e) :=
        (mem_centralizer_iff.1 (h.V_le_CH (i := m) hm (Or.inl rfl) hg) b hb).symm
      have hz : b * lam c * b⁻¹ ∈ d.WA j := d.conj_H_mem_WA hbH (hlam c)
      have hbt : b * h.t * b⁻¹ = h.t := by
        rw [h.mul_t_comm (h.H_le_L hbH), mul_inv_cancel_right]
      have hzc : ⁅b * lam c * b⁻¹, h.t⁆ =
          h.elt (rootElt h.K h.a j ((rootChar h.K h.a j t : h.K) * c)) := by
        rw [← h.elt_torusPair_conj_rootElt, ← hlamt c, ← hbdef]
        conv_lhs => rw [← hbt]
        simp only [commutatorElement_def]; group
      have hv : lam ((rootChar h.K h.a j t : h.K) * c) * (b * lam c * b⁻¹)⁻¹ ∈ h.V j := by
        have := inv_mem (hmod hz hzc)
        rwa [mul_inv_rev, inv_inv] at this
      have e1 : lam ((rootChar h.K h.a j t : h.K) * c) =
          (lam ((rootChar h.K h.a j t : h.K) * c) * (b * lam c * b⁻¹)⁻¹) *
            (b * lam c * b⁻¹) := by group
      show h.r1c ⁅h.elt (rootElt h.K h.a m e), lam ((rootChar h.K h.a j t : h.K) * c)⁆ l =
        (rootChar h.K h.a l t : h.K) * h.r1c ⁅h.elt (rootElt h.K h.a m e), lam c⁆ l
      rw [e1, hred hg hv hz, commutatorElement_conj_of_commute hgb, hbdef,
        h.r1c_torus (hR hg (hlam c)) t hl]
  have hkey : ∀ e, ⁅h.elt (rootElt h.K h.a m e), x⁆ = 1 := by
    intro e
    obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt hjS (d.comm_t_mem_V_of_mem_WA hjj.isCenter hbr hx)
    have e2 : ⁅h.elt (rootElt h.K h.a m e), x⁆ = ⁅h.elt (rootElt h.K h.a m e), lam c⁆ := by
      rw [show x = (x * (lam c)⁻¹) * lam c by group,
        hred (h.elt_rootElt_mem_V m e) (hmod hx hc) (hlam c)]
    rw [e2]
    have h12 := hV12 (h.elt_rootElt_mem_V m e) (hlam c)
    refine h.eq_of_r1c_eq (h.V12_le_R₁ h12) (one_mem _) fun l hl => ?_
    rw [h.r1c_one hl]
    by_cases hl12 : l = .i12
    · subst hl12
      exact hmside e c
    · exact h.r1c_eq_zero_of_mem_V12 h12 hl hl12
  have hle : h.V m ≤ centralizer ({x} : Set G) := h.V_le_of_forall_elt_mem fun e =>
    mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 (hkey e))
  exact commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 (hle hg))

theorem comm_V7_WA9_WA10 :
    (∀ g ∈ h.V .i7, ∀ x ∈ d.WA .i9, ⁅g, x⁆ = 1) ∧ (∀ g ∈ h.V .i7, ∀ x ∈ d.WA .i10, ⁅g, x⁆ = 1) ∧
      (∀ g ∈ h.V .i6, ∀ x ∈ d.WA .i10, ⁅g, x⁆ = 1) := by
  obtain ⟨h79, h710, h610⟩ := h.comm_V7_V9_V10
  refine ⟨fun g hg x hx => d.comm_V_WA_eq_one rfl (h.V_le_R (by decide))
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) rfl h79 (by decide) hg hx,
    fun g hg x hx => d.comm_V_WA_eq_one rfl (h.V_le_R (by decide))
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) rfl h710 (by decide) hg hx,
    fun g hg x hx => d.comm_V_WA_eq_one rfl (h.V_le_R (by decide))
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) rfl h610 (by decide) hg hx⟩

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
