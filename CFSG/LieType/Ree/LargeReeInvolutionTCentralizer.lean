module

public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizerBruhat
public import CFSG.LieType.Ree.LargeReeInvolutionCoordinateReduction
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolicOne

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open ReeTag
open scoped Pointwise
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair
  torusPair_apply torusPair_conj_pinnedX torusWeight torusWeight_apply torusExp0 torusExp1)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem orbitCertRoot_thirtyThree : orbitCertRoot F4.tag 33 = Pi.single largeReeI1 1 := by
  decide

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem orbitCertRoot_twentyFour : orbitCertRoot F4.tag 24 = Pi.single largeReeI4 1 := by
  decide

omit [Finite K] in
theorem commute_sylowL_of_E1
    (c d : K) :
    Commute (sylowX K 33 d) (sylowL a K c) ∧ Commute (sylowX K 24 d) (sylowL a K c) := by
  have H : ∀ {i j : ℕ}, 24 ≤ i ∧ i ≤ 47 → 24 ≤ j ∧ j ≤ 47 → i ≠ j → commFactors i j = [] →
      ∀ s t : K, Commute (sylowX K i s) (sylowX K j t) :=
    fun hi hj hij h s t => sylowX_commute_of_commFactors hi hj hij h s t
  exact ⟨(H (by norm_num) (by norm_num) (by norm_num) (by decide) _ _).mul_right
      (H (by norm_num) (by norm_num) (by norm_num) (by decide) _ _),
    (H (by norm_num) (by norm_num) (by norm_num) (by decide) _ _).mul_right
      (H (by norm_num) (by norm_num) (by norm_num) (by decide) _ _)⟩

omit [Finite K] in
theorem rootSpan_E1_le_centralizer
    (c : K) :
    rootSpan F4.tag K (F4.fixedOrbitRoots ⟨0, by decide⟩) ≤
      Subgroup.centralizer {sylowL a K c} := by
  rw [F4_fixedOrbitRoots_zero]
  refine iSup₂_le fun α hα => ?_
  intro x hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hα with rfl | rfl
  · rw [← orbitCertRoot_thirtyThree]
    exact (commute_sylowL_of_E1 c d).1.eq
  · rw [← orbitCertRoot_twentyFour]
    exact (commute_sylowL_of_E1 c d).2.eq

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedOrbitElement_zero_smul_41 :
    F4.fixedOrbitElement ⟨0, by decide⟩ • orbitCertRoot F4.tag 41 = orbitCertRoot F4.tag 41 := by
  rw [fixedOrbitElement_smul]
  decide +kernel

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedOrbitElement_zero_smul_45 :
    F4.fixedOrbitElement ⟨0, by decide⟩ • orbitCertRoot F4.tag 45 = orbitCertRoot F4.tag 45 := by
  rw [fixedOrbitElement_smul]
  decide +kernel

omit [Finite K] in
theorem canonicalRep_conj_sylowL
    (c : K) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
        sylowL a K c *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ =
      sylowL a K c := by
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := ‹CharP K F4.prime›
    exact CharTwo.two_eq_zero
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  simp only [sylowL, sylowX]
  rw [e, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _
      (sylowRoot_pos (r := 41) (by norm_num) (by norm_num)).1,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 _
      (sylowRoot_pos (r := 45) (by norm_num) (by norm_num)).1,
    fixedOrbitElement_zero_smul_41, fixedOrbitElement_zero_smul_45]

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem cartanPair_41 : F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 41) = 0 ∧
    F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 41) = 1 ∧
    F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 41) = -1 ∧
    F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 41) = 0 := by
  decide +kernel

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem cartanPair_45 : F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 45) = 0 ∧
    F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 45) = 0 := by
  decide +kernel

omit [Finite K] [CharP K F4.prime] in
theorem torusWeight_left_41_45 (u : Kˣ) :
    torusWeight a (orbitCertRoot F4.tag 41) (u, 1) = 1 ∧
      torusWeight a (orbitCertRoot F4.tag 45) (u, 1) = 1 := by
  obtain ⟨h0, -, -, h3⟩ := cartanPair_41
  obtain ⟨h0', h3'⟩ := cartanPair_45
  refine ⟨?_, ?_⟩ <;> rw [torusWeight_apply, one_zpow, mul_one] <;> simp only [torusExp0]
  · rw [h0, h3, zero_mul, add_zero, zpow_zero]
  · rw [h0', h3', zero_mul, add_zero, zpow_zero]

omit [Finite K] [CharP K F4.prime] in
theorem torusOne_conj_sylowL
    (u : Kˣ) (c : K) :
    pairedTorusHom a (f4i 0) (f4i 3) u * sylowL a K c *
        (pairedTorusHom a (f4i 0) (f4i 3) u)⁻¹ = sylowL a K c := by
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  obtain ⟨h41, h45⟩ := torusWeight_left_41_45 (a := a) u
  rw [← rankOneTorusPair_left]
  simp only [sylowL, sylowX]
  rw [e, torusPair_conj_pinnedX a (u, 1) (sylowRoot_pos (r := 41) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a (u, 1) (sylowRoot_pos (r := 45) (by norm_num) (by norm_num)).1,
    h41, h45, Units.val_one, one_mul, one_mul]

theorem rankOneGroupOne_le_centralizer_sylowL
    (c : K) :
    rankOneGroupOne K a ≤ Subgroup.centralizer {sylowL a K c} := by
  rw [rankOneGroupOne, Subgroup.closure_le]
  have hcomm : ∀ {g x : ModGL F4.tag K}, g * x * g⁻¹ = x → g * x = x * g := fun {g x} h => by
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  rintro g ((hg | ⟨u, rfl⟩) | rfl)
  · exact rootSpan_E1_le_centralizer c (Subgroup.mem_inf.1 hg).1
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm (torusOne_conj_sylowL u c)
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm (canonicalRep_conj_sylowL c)

variable (K a) in
abbrev tKernel
    : Subgroup (ModGL F4.tag K) :=
  F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊓ Subgroup.centralizer {sylowL a K 1}

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem complement_zero_check : ∀ r ∈ ([25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39,
    40, 41, 42, 43, 44, 45, 46, 47] : List ℕ), (24 ≤ r ∧ r ≤ 47) ∧
      ∃ i, F4.fixedOrbitIndex i ≠ ⟨0, by decide⟩ ∧ orbitCertRoot F4.tag r i ≠ 0 := by
  decide +kernel

omit [Finite K] [CharP K F4.prime] in
theorem sylowX_mem_complement
    {r : ℕ} (hr : r ∈ ([25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36,
    37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] : List ℕ)) (c : K) :
    sylowX K r c ∈ rootSpan F4.tag K (F4.fixedOrbitComplementRoots ⟨0, by decide⟩) := by
  obtain ⟨⟨h1, h2⟩, hex⟩ := complement_zero_check r hr
  exact pinnedX_mem_rootSpan (mem_fixedOrbitComplementRoots_iff.2
    ⟨(sylowRoot_pos h1 h2).1, (sylowRoot_pos h1 h2).2, hex⟩) c

omit [Finite K] [CharP K F4.prime] in
theorem sylowV_zero_mem_rootSpan
    (b c d e f g h i j k l : K) :
    sylowV a K 0 b c d e f g h i j k l ∈
      rootSpan F4.tag K (F4.fixedOrbitComplementRoots ⟨0, by decide⟩) := by
  have H : ∀ r ∈ ([25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
      45, 46, 47] : List ℕ), ∀ c : K, sylowX K r c ∈
        rootSpan F4.tag K (F4.fixedOrbitComplementRoots ⟨0, by decide⟩) :=
    fun r hr c => sylowX_mem_complement hr c
  have hA : sylowA a K (0 : K) = 1 := by
    rw [sylowA, largeReeSigma_zero, sylowX, sylowX, pinnedX_zero, pinnedX_zero, one_mul]
  rw [sylowV, hA, one_mul]
  simp only [sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact mul_mem (mul_mem (mul_mem (H 25 (by decide) _) (H 27 (by decide) _))
      (H 28 (by decide) _)) (H 30 (by decide) _)
  · exact mul_mem (mul_mem (mul_mem (H 26 (by decide) _) (H 34 (by decide) _))
      (H 36 (by decide) _)) (H 39 (by decide) _)
  · exact mul_mem (mul_mem (mul_mem (H 29 (by decide) _) (H 37 (by decide) _))
      (H 43 (by decide) _)) (H 46 (by decide) _)
  · exact mul_mem (mul_mem (mul_mem (H 35 (by decide) _) (H 32 (by decide) _))
      (H 44 (by decide) _)) (H 47 (by decide) _)
  · exact mul_mem (H 31 (by decide) _) (H 40 (by decide) _)
  · exact mul_mem (H 38 (by decide) _) (H 42 (by decide) _)
  · exact mul_mem (H 41 (by decide) _) (H 45 (by decide) _)

theorem sylowV_mem
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (a' b c d e f g h i j k l : K) :
    sylowV a K a' b c d e f g h i j k l ∈ F4.reeFixedPosUnipotent K a := by
  have hv := (bijOn_sylowVec hK).1 (Set.mem_univ ![a', b, c, d, e, f, g, h, i, j, k, l])
  simpa [sylowVec] using hv

theorem sylowV_zero_mem_complement
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (b c d e f g h i j k l : K) :
    sylowV a K 0 b c d e f g h i j k l ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
  Subgroup.mem_inf.2 ⟨sylowV_zero_mem_rootSpan b c d e f g h i j k l,
    (Subgroup.mem_inf.1 (sylowV_mem hK 0 b c d e f g h i j k l)).2⟩

omit [Finite K] [CharP K F4.prime] in
theorem sylowA_mem_rootSpan
    (c : K) :
    sylowA a K c ∈ rootSpan F4.tag K (F4.fixedOrbitRoots ⟨0, by decide⟩) := by
  rw [sylowA, F4_fixedOrbitRoots_zero]
  refine mul_mem ?_ ?_
  · rw [sylowX, orbitCertRoot_twentyFour]
    exact pinnedX_mem_rootSpan (by simp) _
  · rw [sylowX, orbitCertRoot_thirtyThree]
    exact pinnedX_mem_rootSpan (by simp) _

theorem eq_zero_of_sylowV_mem_complement
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {a' b c d e f g h i j k l : K}
    (hv : sylowV a K a' b c d e f g h i j k l ∈
      F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩) : a' = 0 := by
  have hw := sylowV_zero_mem_complement hK b c d e f g h i j k l
  have hA0 : sylowA a K (0 : K) = 1 := by
    rw [sylowA, largeReeSigma_zero, sylowX, sylowX, pinnedX_zero, pinnedX_zero, one_mul]
  have e : sylowV a K a' b c d e f g h i j k l =
      sylowA a K a' * sylowV a K 0 b c d e f g h i j k l := by
    simp only [sylowV, hA0, one_mul, mul_assoc]
  have hAV : sylowA a K a' ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
    have := mul_mem hv (inv_mem hw)
    rwa [e, mul_inv_cancel_right] at this
  have hAU : sylowA a K a' ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ :=
    Subgroup.mem_inf.2 ⟨sylowA_mem_rootSpan a', (Subgroup.mem_inf.1 hAV).2⟩
  have h1 : sylowA a K a' = 1 := by
    have := Subgroup.mem_inf.2 ⟨hAV, hAU⟩
    rwa [reeFixedOrbitComplementUnipotent_inf_reeFixedOrbitUnipotent, Subgroup.mem_bot] at this
  have h24 := sylowRoot_pos (r := 24) (by norm_num) (by norm_num)
  have h33 := sylowRoot_pos (r := 33) (by norm_num) (by norm_num)
  rw [sylowA, sylowX, sylowX] at h1
  have h1' : pinnedX F4.tag K (orbitCertRoot F4.tag 24) a' *
      pinnedX F4.tag K (orbitCertRoot F4.tag 33) (largeReeSigma a a') =
        pinnedX F4.tag K (orbitCertRoot F4.tag 24) 0 *
          pinnedX F4.tag K (orbitCertRoot F4.tag 33) 0 := by
    rw [pinnedX_zero, pinnedX_zero, mul_one]
    exact h1
  exact (pinnedX_mul_pinnedX_inj (Or.inl ⟨h24, h33⟩) (by decide) h1').1

omit [Finite K] [CharP K F4.prime] in
theorem tSix_inj
    {lam mu p p' r r' lam' mu' s s' z z' : K}
    (h : tSix K lam mu p p' r r' = tSix K lam' mu' s s' z z') :
    lam = lam' ∧ mu = mu' ∧ p = s ∧ p' = s' ∧ r = z ∧ r' = z' := by
  have hnd : ∀ lam mu p p' r r' : K, ((tSixList lam mu p p' r r').map Prod.fst).Nodup :=
    fun _ _ _ _ _ _ => by rw [map_fst_tSixList]; exact tSixRoots_nodup
  rw [tSix_eq_rootProd, tSix_eq_rootProd, rootProd_eq_map_rootParam (hnd _ _ _ _ _ _),
    rootProd_eq_map_rootParam (hnd _ _ _ _ _ _), map_fst_tSixList, map_fst_tSixList] at h
  have hinj := pinnedX_list_prod_injective (R := K) (tSixRoots.map (orbitCertRoot F4.tag))
    tSixRoots_nodup (fun α hα => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hα
      exact sylowRoot_pos (by simp at hr; omega) (by simp at hr; omega)) _ _ h
  have key : ∀ (q : ℕ) (hq : q ∈ tSixRoots) (x x' : K),
      (orbitCertRoot F4.tag q, x) ∈ tSixList lam mu p p' r r' →
        (orbitCertRoot F4.tag q, x') ∈ tSixList lam' mu' s s' z z' → x = x' := by
    intro q hq x x' hx hx'
    have e1 : rootParam (tSixList lam mu p p' r r') (orbitCertRoot F4.tag q) = x :=
      rootParam_of_mem (hnd _ _ _ _ _ _) hx
    have e2 : rootParam (tSixList lam' mu' s s' z z') (orbitCertRoot F4.tag q) = x' :=
      rootParam_of_mem (hnd _ _ _ _ _ _) hx'
    rw [← e1, ← e2]
    exact hinj _ (List.mem_map_of_mem hq)
  exact ⟨key 41 (by decide) _ _ (by simp) (by simp), key 45 (by decide) _ _ (by simp) (by simp),
    key 43 (by decide) _ _ (by simp) (by simp), key 46 (by decide) _ _ (by simp) (by simp),
    key 44 (by decide) _ _ (by simp) (by simp), key 47 (by decide) _ _ (by simp) (by simp)⟩

omit [Finite K] in
theorem sylowL_conj_eq
    (x : Fin 12 → K) :
    sylowVec a K x * sylowL a K 1 * (sylowVec a K x)⁻¹ =
      tSix K 1 1 (x 1 * 1) (largeReeSigma a (x 1) * 1) (x 3 * 1 + x 0 * x 1 * 1)
        (largeReeSigma a (x 3) * 1 + largeReeSigma a (x 0) * largeReeSigma a (x 1) * 1) := by
  rw [sylowL, largeReeSigma_one, sylowVec]
  exact sylowV_conj_tPair _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem coe_tKernel
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (tKernel K a : Set (ModGL F4.tag K)) =
      sylowVec a K '' {x | x 0 = 0 ∧ x 1 = 0 ∧ x 3 = 0} := by
  ext u
  rw [mem_image_sylowVec_iff hK]
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hV, hc⟩ => ⟨reeFixedOrbitComplementUnipotent_le _ hV, fun x hx => ?_⟩,
    fun ⟨hu, hS⟩ => ?_⟩
  · subst hx
    have ha := eq_zero_of_sylowV_mem_complement hK hV
    have hct : sylowVec a K x * sylowL a K 1 * (sylowVec a K x)⁻¹ = sylowL a K 1 := by
      rw [hc, mul_inv_cancel_right]
    rw [sylowL_conj_eq] at hct
    rw [sylowL_one_eq_tSix (a := a)] at hct
    obtain ⟨-, -, hb, -, hd, -⟩ := tSix_inj hct
    rw [mul_one] at hb
    rw [hb, ha, mul_one, zero_mul, zero_mul, add_zero] at hd
    exact ⟨ha, hb, hd⟩
  · obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
    obtain ⟨h0, h1, h3⟩ := hS x rfl
    refine ⟨?_, ?_⟩
    · have := sylowV_zero_mem_complement hK (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
        (x 9) (x 10) (x 11)
      rw [← h0] at this
      exact this
    · have hct : sylowVec a K x * sylowL a K 1 * (sylowVec a K x)⁻¹ = sylowL a K 1 := by
        rw [sylowL_conj_eq, h0, h1, h3, largeReeSigma_zero]
        simp only [zero_mul, mul_zero, add_zero]
        exact (sylowL_one_eq_tSix (a := a)).symm
      calc sylowVec a K x * sylowL a K 1 =
          sylowVec a K x * sylowL a K 1 * (sylowVec a K x)⁻¹ * sylowVec a K x := by group
        _ = sylowL a K 1 * sylowVec a K x := by rw [hct]

theorem card_tKernel
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (tKernel K a) = (2 ^ (2 * a + 1)) ^ 9 :=
  card_centralizer_of_eq hK (coe_tKernel hK) {0, 1, 3} (by ext x; simp)

theorem complement_zero_inf_rankOneGroupOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊓ rankOneGroupOne K a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxR⟩ := Subgroup.mem_inf.1 hx
  rw [rankOneGroupOne_eq_range hK] at hxR
  obtain ⟨g, rfl⟩ := hxR
  have hxU : largeReeA1Hom K a g ∈ posUnipotent F4.tag K :=
    (Subgroup.mem_inf.1 (reeFixedOrbitComplementUnipotent_le _ hxV)).1
  have hXU : ∀ c : K, xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) ∈
      posUnipotent F4.tag K := fun c =>
    mul_mem (xUnit_mem_posUnipotent _ _) (xUnit_mem_posUnipotent _ _)
  have hXB : ∀ c : K, xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) ∈
      borelGroup F4.tag K := fun c => Subgroup.mem_sup_right (hXU c)
  have hHT : ∀ u : Kˣ, torusElt F4.tag K largeReeI1 u *
      torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u) ∈
        torusGroup F4.tag K := fun u =>
    mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [eq_HSL_mul_uSL hc] at hxV hxU ⊢
    generalize Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc) = u at hxV hxU ⊢
    generalize (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0 = b
      at hxV hxU ⊢
    rw [map_mul, largeReeA1Hom_HSL, largeReeA1Hom_uSL] at hxV hxU ⊢
    have hTU : torusElt F4.tag K largeReeI1 u *
        torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u) ∈
          posUnipotent F4.tag K := by
      have := mul_mem hxU (inv_mem (hXU b))
      rwa [mul_inv_cancel_right] at this
    have hT1 : torusElt F4.tag K largeReeI1 u *
        torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u) = 1 := by
      have := Subgroup.mem_inf.2 ⟨hHT u, hTU⟩
      rwa [torusGroup_inf_posUnipotent, Subgroup.mem_bot] at this
    rw [hT1, one_mul] at hxV ⊢
    have hXU1 : xUnit F4.tag K largeReeI1 b * xUnit F4.tag K largeReeI4 (b ^ 2 ^ a) ∈
        F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
      rw [← SetLike.mem_coe, coe_reeFixedOrbitUnipotent_zero hK]
      exact ⟨b, rfl⟩
    have := Subgroup.mem_inf.2 ⟨hxV, hXU1⟩
    rwa [reeFixedOrbitComplementUnipotent_inf_reeFixedOrbitUnipotent] at this
  · exfalso
    rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc, map_mul, map_mul, map_mul, largeReeA1Hom_uSL,
      largeReeA1Hom_HSL, largeReeA1Hom_WSL, largeReeA1Hom_uSL] at hxU
    refine weylElt_mul_weylElt_not_mem_borelGroup (K := K) ?_
    generalize hx₁ : xUnit F4.tag K largeReeI1 ((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0) * xUnit F4.tag K largeReeI4
        (((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 ^ a) =
          x₁ at hxU
    generalize hx₂ : xUnit F4.tag K largeReeI1 ((g : Matrix (Fin 2) (Fin 2) K) 1 1 /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0) * xUnit F4.tag K largeReeI4
        (((g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 ^ a) =
          x₂ at hxU
    generalize hh : torusElt F4.tag K largeReeI1
        (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
          (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) *
        torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom
          (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
            (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc))) = h at hxU
    have hx₁B : x₁ ∈ borelGroup F4.tag K := hx₁ ▸ hXB _
    have hx₂B : x₂ ∈ borelGroup F4.tag K := hx₂ ▸ hXB _
    have hhB : h ∈ borelGroup F4.tag K := hh ▸ Subgroup.mem_sup_left (hHT _)
    have hB : x₁ * h * (weylElt F4.tag K largeReeI1 1 * weylElt F4.tag K largeReeI4 1) * x₂ ∈
        borelGroup F4.tag K := Subgroup.mem_sup_right hxU
    have e : weylElt F4.tag K largeReeI1 1 * weylElt F4.tag K largeReeI4 1 =
        h⁻¹ * x₁⁻¹ * (x₁ * h * (weylElt F4.tag K largeReeI1 1 *
          weylElt F4.tag K largeReeI4 1) * x₂) * x₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem hhB) (inv_mem hx₁B)) hB) (inv_mem hx₂B)

omit [Finite K] [CharP K F4.prime] in
theorem torusWeight_right_41 (v : Kˣ) :
    torusWeight a (orbitCertRoot F4.tag 41) (1, v) = v ^ ((1 : ℤ) - 2 ^ a) := by
  obtain ⟨-, h1, h2, -⟩ := cartanPair_41
  rw [torusWeight_apply, one_zpow, one_mul]
  congr 1
  simp only [torusExp1]
  rw [h1, h2]
  ring

omit [CharP K F4.prime] in
theorem eq_one_of_zpow_one_sub (hK : Nat.card K = 2 ^ (2 * a + 1)) {v : Kˣ}
    (hv : v ^ ((1 : ℤ) - 2 ^ a) = 1) : v = 1 := by
  classical
  have := Fintype.ofFinite K
  have hq : v ^ (Fintype.card Kˣ) = 1 := pow_card_eq_one
  rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK] at hq
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have e : v = (v ^ ((1 : ℤ) - 2 ^ a)) ^ ((2 : ℤ) * 2 ^ a + 2) * v ^ (2 ^ (2 * a + 1) - 1) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    conv_lhs => rw [← zpow_one v]
    congr 1
    rw [Nat.cast_sub h1]
    push_cast
    ring
  rw [e, hv, one_zpow, one_mul, hq]

theorem tKernel_le_reeGamma
    : tKernel K a ≤ F4.reeGamma K a :=
  fun _ hx => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2

variable (K a) in
abbrev centralizerT
    : Subgroup (ModGL F4.tag K) :=
  tKernel K a ⊔ rankOneGroupOne K a

theorem centralizerT_le_centralizer
    : centralizerT K a ≤ Subgroup.centralizer {sylowL a K 1} :=
  sup_le inf_le_right (rankOneGroupOne_le_centralizer_sylowL 1)

theorem reeGamma_inf_centralizer_tOne_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {sylowL a K 1} = centralizerT K a := by
  refine le_antisymm (fun g hg => ?_)
    (le_inf (sup_le tKernel_le_reeGamma (rankOneGroupOne_le_reeGamma hK))
      centralizerT_le_centralizer)
  obtain ⟨t, ht, s, hs, rfl⟩ :=
    exists_mul_of_mem_reeLocalParabolic_zero hK (reeGamma_inf_centralizer_tOne_le hK hg)
  obtain ⟨v, rfl⟩ := ht
  have hs' : s ∈ (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :
      Set (ModGL F4.tag K)) * (rankOneGroupOne K a : Set (ModGL F4.tag K)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (rankOneGroupOne_le_normalizer_complement hK)]
    exact hs
  obtain ⟨x, hx, r, hr, rfl⟩ := hs'
  have hgc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
  have hrc := Subgroup.mem_centralizer_singleton_iff.1 (rankOneGroupOne_le_centralizer_sylowL 1 hr)
  have hrt : r * sylowL a K 1 * r⁻¹ = sylowL a K 1 := by rw [hrc, mul_inv_cancel_right]
  have key : pairedTorusHom a (f4i 1) (f4i 2) v * (x * sylowL a K 1 * x⁻¹) *
      (pairedTorusHom a (f4i 1) (f4i 2) v)⁻¹ = sylowL a K 1 := by
    calc pairedTorusHom a (f4i 1) (f4i 2) v * (x * sylowL a K 1 * x⁻¹) *
          (pairedTorusHom a (f4i 1) (f4i 2) v)⁻¹ =
        pairedTorusHom a (f4i 1) (f4i 2) v * (x * (r * sylowL a K 1 * r⁻¹) * x⁻¹) *
          (pairedTorusHom a (f4i 1) (f4i 2) v)⁻¹ := by rw [hrt]
      _ = pairedTorusHom a (f4i 1) (f4i 2) v * (x * r) * sylowL a K 1 *
          (pairedTorusHom a (f4i 1) (f4i 2) v * (x * r))⁻¹ := by group
      _ = sylowL a K 1 := by rw [hgc, mul_inv_cancel_right]
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 (reeFixedOrbitComplementUnipotent_le _ hx)
  rw [sylowL_conj_eq, ← rankOneTorusPair_right, torusPair_conj_tSix] at key
  conv_rhs at key => rw [sylowL_one_eq_tSix (a := a)]
  obtain ⟨h41, -⟩ := tSix_inj key
  have hv : v = 1 := by
    refine eq_one_of_zpow_one_sub hK ?_
    rw [← torusWeight_right_41]
    exact Units.ext (by rw [mul_one] at h41; exact h41)
  subst hv
  rw [map_one, one_mul] at hgc ⊢
  have hxQ : sylowVec a K y ∈ tKernel K a := by
    refine Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc sylowVec a K y * sylowL a K 1 =
        sylowVec a K y * r * sylowL a K 1 * r⁻¹ := by rw [mul_assoc _ r, hrc]; group
      _ = sylowL a K 1 * sylowVec a K y := by rw [hgc]; group
  exact mul_mem (Subgroup.mem_sup_left hxQ) (Subgroup.mem_sup_right hr)

theorem tKernel_inf_rankOneGroupOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    tKernel K a ⊓ rankOneGroupOne K a = ⊥ :=
  eq_bot_iff.2 fun x hx => by
    rw [← complement_zero_inf_rankOneGroupOne hK]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1,
      (Subgroup.mem_inf.1 hx).2⟩

theorem rankOneGroupOne_le_normalizer_tKernel
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ Subgroup.normalizer (tKernel K a : Set (ModGL F4.tag K)) :=
  fun _ hr => Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨rankOneGroupOne_le_normalizer_complement hK hr,
      Subgroup.le_normalizer (rankOneGroupOne_le_centralizer_sylowL 1 hr)⟩)

theorem centralizerT_le_normalizer
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    centralizerT K a ≤ Subgroup.normalizer (tKernel K a : Set (ModGL F4.tag K)) :=
  sup_le Subgroup.le_normalizer (rankOneGroupOne_le_normalizer_tKernel hK)

@[expose] def afWord : Word :=
  [(33, [[]]), (24, [[]]), (43, [[]]), (46, [[]])]

@[expose] def faWord : Word :=
  [(43, [[]]), (46, [[]]), (33, [[]]), (24, [[]])]

@[expose] def afCoords : List Poly :=
  [[[]], [], [], [], [], [], [], [], [], [[]], [], [], [], [], [], [], [], [], [], [[]], [], [],
    [[]], []]

@[expose] def faCoords : List Poly :=
  [[[]], [], [], [], [], [], [], [], [], [[]], [], [], [], [], [], [], [], [], [], [[]], [[]], [],
    [[]], [[]]]

theorem afWord_check : collectCheck 100 afWord afCoords = true := by
  decide +kernel

theorem faWord_check : collectCheck 100 faWord faCoords = true := by
  decide +kernel

omit [Finite K] in
theorem centralAOne_mul_ne :
    (centralAOne : ModGL F4.tag K) * (sylowX K 43 1 * sylowX K 46 1) ≠
      sylowX K 43 1 * sylowX K 46 1 * centralAOne := by
  have : CharP K 2 := ‹CharP K F4.prime›
  intro h
  have hA : (centralAOne : ModGL F4.tag K) = sylowX K 33 1 * sylowX K 24 1 := by
    rw [centralAOne, sylowX, sylowX, orbitCertRoot_thirtyThree, orbitCertRoot_twentyFour,
      pinnedX_single, pinnedX_single]
  have h1 : (centralAOne : ModGL F4.tag K) * (sylowX K 43 1 * sylowX K 46 1) =
      wordEval K (fun _ => 0) afWord := by
    rw [hA]
    simp [wordEval, afWord, polyEval, monoEval, sylowX, mul_assoc]
  have h2 : sylowX K 43 1 * sylowX K 46 1 * centralAOne = wordEval K (fun _ => 0) faWord := by
    rw [hA]
    simp [wordEval, faWord, polyEval, monoEval, sylowX, mul_assoc]
  rw [h1, h2] at h
  have := (wordEval_eq_iff afWord_check faWord_check (fun _ => (0 : K))).1 h ⟨20, by omega⟩
  simp [afCoords, faCoords, polyEval, monoEval] at this

theorem sylowF_zero_one_mem_tKernel
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sylowX K 43 1 * sylowX K 46 1 ∈ tKernel K a := by
  have e : sylowX K 43 1 * sylowX K 46 1 = sylowVec a K ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
      largeReeSigma_zero, largeReeSigma_one, sylowX, pinnedX_zero]
  rw [e, ← SetLike.mem_coe, coe_tKernel hK]
  exact ⟨_, by simp, rfl⟩

theorem tKernel_isPGroup
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 (tKernel K a) :=
  (isPGroup_reeFixedPosUnipotent ha hK).to_le
    (fun _ hx => reeFixedOrbitComplementUnipotent_le _ (Subgroup.mem_inf.1 hx).1)

theorem centralizerT_kernel
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((tKernel K a).subgroupOf (centralizerT K a)).Normal ∧
      IsPGroup 2 ((tKernel K a).subgroupOf (centralizerT K a)) ∧
      Subgroup.centralizer (((tKernel K a).subgroupOf (centralizerT K a) :
        Subgroup (centralizerT K a)) : Set (centralizerT K a)) ≤
          (tKernel K a).subgroupOf (centralizerT K a) ∧
      (∀ M : Subgroup (centralizerT K a), M.Normal → IsPGroup 2 M →
        M ≤ (tKernel K a).subgroupOf (centralizerT K a)) ∧
      ∀ M : Subgroup (centralizerT K a), M.Normal → Odd (Nat.card M) → M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := F4.tag) (K := K)
  have hle : tKernel K a ≤ centralizerT K a := le_sup_left
  have hRle : rankOneGroupOne K a ≤ centralizerT K a := le_sup_right
  have hN : ((tKernel K a).subgroupOf (centralizerT K a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (centralizerT_le_normalizer hK)
  have hN2 : IsPGroup 2 ((tKernel K a).subgroupOf (centralizerT K a)) :=
    (tKernel_isPGroup ha hK).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hNR : (tKernel K a).subgroupOf (centralizerT K a) ⊔
      (rankOneGroupOne K a).subgroupOf (centralizerT K a) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hle hRle, Subgroup.subgroupOf_self]
  obtain ⟨hsimple, x, y, hxy⟩ := isSimpleGroup_rankOneGroupOne ha hK
  set e := Subgroup.subgroupOfEquivOfLe hRle
  have : IsSimpleGroup ((rankOneGroupOne K a).subgroupOf (centralizerT K a)) := e.isSimpleGroup
  have hRnab : ∃ x y : (rankOneGroupOne K a).subgroupOf (centralizerT K a), x * y ≠ y * x := by
    refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact e.symm.injective h
  have hA : (centralAOne : ModGL F4.tag K) ∈ rankOneGroupOne K a := by
    have h : (centralAOne : ModGL F4.tag K) ∈
        (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
      rw [coe_reeFixedOrbitUnipotent_zero hK]
      exact ⟨1, by simp [centralAOne]⟩
    exact Subgroup.subset_closure (.inl (.inl h))
  have hF := sylowF_zero_one_mem_tKernel (a := a) hK
  have hne : (⟨centralAOne, hRle hA⟩ : centralizerT K a) * ⟨_, hle hF⟩ ≠
      ⟨_, hle hF⟩ * ⟨centralAOne, hRle hA⟩ := by
    intro h
    apply centralAOne_mul_ne (K := K)
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h'
    exact h'
  have hact : ∃ r ∈ (rankOneGroupOne K a).subgroupOf (centralizerT K a),
      ∃ n ∈ (tKernel K a).subgroupOf (centralizerT K a), r * n ≠ n * r :=
    ⟨⟨_, hRle hA⟩, hA, ⟨_, hle hF⟩, hF, hne⟩
  obtain ⟨hC, hO, hOdd⟩ := kernel_selfCentralizing hN hN2 hNR hRnab hact
  exact ⟨hN, hN2, hC, hO, hOdd⟩

theorem card_centralizerT
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (centralizerT K a) = Nat.card (tKernel K a) * Nat.card (rankOneGroupOne K a) := by
  have hset : ((centralizerT K a : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      (tKernel K a : Set (ModGL F4.tag K)) * (rankOneGroupOne K a : Set (ModGL F4.tag K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rankOneGroupOne_le_normalizer_tKernel hK)
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective (fun p : tKernel K a × rankOneGroupOne K a =>
      (⟨(p.1 : ModGL F4.tag K) * p.2,
        mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
          centralizerT K a)) ⟨?_, ?_⟩)).symm
  · rintro ⟨v, r⟩ ⟨v', r'⟩ h
    have h' : (v : ModGL F4.tag K) * r = v' * r' := congrArg Subtype.val h
    have hm : (v' : ModGL F4.tag K)⁻¹ * v ∈ tKernel K a ⊓ rankOneGroupOne K a := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem v'.2) v.2, ?_⟩
      have e : (v' : ModGL F4.tag K)⁻¹ * v = r' * (r : ModGL F4.tag K)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      rw [e]
      exact mul_mem r'.2 (inv_mem r.2)
    rw [tKernel_inf_rankOneGroupOne hK, Subgroup.mem_bot, inv_mul_eq_one] at hm
    have hv : v = v' := Subtype.ext hm.symm
    subst hv
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  · rintro ⟨g, hg⟩
    have hg' : g ∈ ((centralizerT K a : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := hg
    rw [hset] at hg'
    obtain ⟨v, hv, r, hr, rfl⟩ := hg'
    exact ⟨(⟨v, hv⟩, ⟨r, hr⟩), rfl⟩

theorem sylowL_mem_tKernel
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    sylowL a K c ∈ tKernel K a := by
  have e : sylowL a K c = sylowVec a K ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK,
      largeReeSigma_zero, sylowX, pinnedX_zero]
  rw [e, ← SetLike.mem_coe, coe_tKernel hK]
  exact ⟨_, by simp, rfl⟩

theorem tKernel_le_centralizer
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    tKernel K a ≤ Subgroup.centralizer {sylowL a K c} := by
  intro u hu
  have hu' : u ∈ (tKernel K a : Set (ModGL F4.tag K)) := hu
  rw [coe_tKernel hK] at hu'
  obtain ⟨x, ⟨h0, h1, h3⟩, rfl⟩ := hu'
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hct : sylowVec a K x * sylowL a K c * (sylowVec a K x)⁻¹ = sylowL a K c := by
    rw [sylowL, sylowVec, sylowV_conj_tPair, h0, h1, h3, largeReeSigma_zero]
    simp only [zero_mul, mul_zero, add_zero, tSix, sylowX, pinnedX_zero, mul_one]
  calc sylowVec a K x * sylowL a K c =
      sylowVec a K x * sylowL a K c * (sylowVec a K x)⁻¹ * sylowVec a K x := by group
    _ = sylowL a K c * sylowVec a K x := by rw [hct]

theorem sylowL_mem_center
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    (⟨sylowL a K c, Subgroup.mem_sup_left (sylowL_mem_tKernel hK c)⟩ : centralizerT K a) ∈
      Subgroup.center (centralizerT K a) := by
  refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
  exact Subgroup.mem_centralizer_singleton_iff.1
    (sup_le (tKernel_le_centralizer hK c) (rankOneGroupOne_le_centralizer_sylowL c) g.2)

theorem card_reeFixedPosUnipotent
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeFixedPosUnipotent K a) = (2 ^ (2 * a + 1)) ^ 12 := by
  have h := card_image_sylowVec hK ∅
  have himg : sylowVec a K '' {x | ∀ i ∈ (∅ : Finset (Fin 12)), x i = 0} =
      (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
    rw [show {x : Fin 12 → K | ∀ i ∈ (∅ : Finset (Fin 12)), x i = 0} = Set.univ by ext; simp]
    exact (bijOn_sylowVec hK).image_eq
  rw [himg, Finset.card_empty, Nat.sub_zero] at h
  exact h

theorem card_centralizerT_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (centralizerT K a) = (2 ^ (2 * a + 1)) ^ 10 * ((2 ^ (2 * a + 1)) ^ 2 - 1) := by
  rw [card_centralizerT hK, card_tKernel hK, card_rankOneGroupOne hK]
  ring

theorem large_Ree_tOne_centralizer
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {sylowL a K 1} =
      tKernel K a ⊔ rankOneGroupOne K a ∧
    tKernel K a ⊓ rankOneGroupOne K a = ⊥ ∧
    (tKernel K a : Set (ModGL F4.tag K)) = sylowVec a K '' {x | x 0 = 0 ∧ x 1 = 0 ∧ x 3 = 0} ∧
    Nat.card (tKernel K a) = (2 ^ (2 * a + 1)) ^ 9 ∧
    Nonempty (SL2 K ≃* rankOneGroupOne K a) ∧
    ((tKernel K a).subgroupOf (centralizerT K a)).Normal ∧
    IsPGroup 2 ((tKernel K a).subgroupOf (centralizerT K a)) ∧
    Subgroup.centralizer (((tKernel K a).subgroupOf (centralizerT K a) :
      Subgroup (centralizerT K a)) : Set (centralizerT K a)) ≤
        (tKernel K a).subgroupOf (centralizerT K a) ∧
    (∀ M : Subgroup (centralizerT K a), M.Normal → IsPGroup 2 M →
      M ≤ (tKernel K a).subgroupOf (centralizerT K a)) ∧
    (∀ M : Subgroup (centralizerT K a), M.Normal → Odd (Nat.card M) → M = ⊥) ∧
    (∀ c : K, (⟨sylowL a K c, Subgroup.mem_sup_left (sylowL_mem_tKernel hK c)⟩ :
      centralizerT K a) ∈ Subgroup.center (centralizerT K a)) ∧
    Nat.card (centralizerT K a) = Nat.card (tKernel K a) * Nat.card (rankOneGroupOne K a) ∧
    Nat.card (rankOneGroupOne K a) = 2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1) ∧
    Nat.card (centralizerT K a) = (2 ^ (2 * a + 1)) ^ 10 * ((2 ^ (2 * a + 1)) ^ 2 - 1) ∧
    Nat.card (F4.reeFixedPosUnipotent K a) = (2 ^ (2 * a + 1)) ^ 12 := by
  obtain ⟨hN, hN2, hC, hO, hOdd⟩ := centralizerT_kernel ha hK
  exact ⟨reeGamma_inf_centralizer_tOne_eq hK, tKernel_inf_rankOneGroupOne hK, coe_tKernel hK,
    card_tKernel hK, ⟨rankOneEquivSL K a hK⟩, hN, hN2, hC, hO, hOdd, sylowL_mem_center hK,
    card_centralizerT hK, card_rankOneGroupOne hK, card_centralizerT_eq hK,
    card_reeFixedPosUnipotent hK⟩

end CFSG.LieType.Ree.LargeReeInvolution
