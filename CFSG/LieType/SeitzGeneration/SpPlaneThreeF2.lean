module

public import CFSG.LieType.SeitzGeneration.SpPlaneThree

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration.SpPlaneThree

variable {r : ℕ} {K : Type} [Field K]

namespace SpPlaneThreeF2

theorem eq_one_of_card_two (hK : Nat.card K = 2) {a : K} (ha : a ≠ 0) : a = 1 := by
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
  exact (hc a ha).trans (hc 1 one_ne_zero).symm

theorem one_add_one_of_card_two (hK : Nat.card K = 2) : (1 : K) + 1 = 0 := by
  by_contra h
  have h1 := eq_one_of_card_two hK h
  exact one_ne_zero (by linear_combination h1 : (1 : K) = 0)

abbrev LineIdx (E : Subgroup (StatedSp r K)) : Type :=
  Option {M : Subgroup ↥E // Nat.card M = 3}

@[expose] def PairCenters (E : Subgroup (StatedSp r K)) (i j : LineIdx E) : Prop :=
  ∀ y ∈ spInnerSummand 3 E i, ∀ y' ∈ spInnerSummand 3 E j, y ≠ 0 → y' ≠ 0 →
    TransCenter (centralizerSpan E) (y + y')

variable {E : Subgroup (StatedSp r K)}

theorem PairCenters.symm {i j : LineIdx E} (h : PairCenters E i j) : PairCenters E j i :=
  fun y hy y' hy' hy0 hy'0 => by
    rw [add_comm]
    exact h y' hy' y hy hy'0 hy0

theorem pairCenters_none (D : SpPlaneDecomp 3 E) {M : Subgroup ↥E} (hM : Nat.card M = 3) :
    PairCenters E none (some ⟨M, hM⟩) := fun y hy y' hy' _ _ =>
  transCenter_add_of_mem_summands_three D hM hy hy'

theorem PairCenters.of_one [Finite K] (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E)
    {i j : LineIdx E} (hij : i ≠ j) {y₀ y₀' : Fin r ⊕ Fin r → K}
    (hy₀ : y₀ ∈ spInnerSummand 3 E i) (hy₀' : y₀' ∈ spInnerSummand 3 E j) (h0 : y₀ ≠ 0)
    (h0' : y₀' ≠ 0) (hmix : TransCenter (centralizerSpan E) (y₀ + y₀')) : PairCenters E i j := by
  intro y hy y' hy' hy0 hy'0
  obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ := exists_mem_fixing_eq (U := spInnerSummand 3 E i)
    (D.nondeg i) (fun c hc => transCenter_of_mem_summand_three hcard i hc) hy₀ hy h0 hy0
  obtain ⟨g₂, hg₂, hg₂w, hg₂fix⟩ := exists_mem_fixing_eq (U := spInnerSummand 3 E j)
    (D.nondeg j) (fun c hc => transCenter_of_mem_summand_three hcard j hc) hy₀' hy' h0' hy'0
  have h2 : spEnd g₂ y₀ = y₀ := hg₂fix y₀ (fun c hc => D.orth i j hij y₀ hy₀ c hc)
  have h1 : spEnd g₁ y' = y' := hg₁fix y' (fun c hc => D.orth j i hij.symm y' hy' c hc)
  have := hmix.map ((centralizerSpan E).mul_mem hg₁ hg₂)
  rwa [spEnd_mul, Module.End.mul_apply, map_add, h2, hg₂w, map_add, hg₁u, h1] at this

theorem PairCenters.pivot [Finite K] (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E)
    {i j k : LineIdx E} (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j)
    (hk : spInnerSummand 3 E k ≠ ⊥) (h1 : PairCenters E i k) (h2 : PairCenters E k j) :
    PairCenters E i j := by
  intro y hy y' hy' hy0 hy'0
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hUnd : ((spForm r K).restrict
      (spInnerSummand 3 E k ⊔ spInnerSummand 3 E j)).Nondegenerate :=
    nondegenerate_sup_of_orthogonal (D.nondeg k) (D.nondeg j)
      (fun u hu v hv => D.orth k j hkj u hu v hv)
      (fun v hv u hu => D.orth j k hkj.symm v hv u hu)
  have hUc : ∀ c ∈ spInnerSummand 3 E k ⊔ spInnerSummand 3 E j,
      TransCenter (centralizerSpan E) c := by
    intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
    by_cases ha0 : a = 0
    · rw [ha0, zero_add]
      exact transCenter_of_mem_summand_three hcard j hb
    by_cases hb0 : b = 0
    · rw [hb0, add_zero]
      exact transCenter_of_mem_summand_three hcard k ha
    exact h2 a ha b hb ha0 hb0
  obtain ⟨g, hg, hgw, hgfix⟩ := exists_mem_fixing_eq hUnd hUc (Submodule.mem_sup_left hw)
    (Submodule.mem_sup_right hy') hw0 hy'0
  have hyfix : spEnd g y = y := by
    refine hgfix y fun c hc => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
    rw [map_add, D.orth i k hik y hy a ha, D.orth i j hij y hy b hb, add_zero]
  have := (h1 y hy w hw hy0 hw0).map hg
  rwa [map_add, hyfix, hgw] at this

theorem exists_big_or_fixed [Finite K] (hr : 5 ≤ r) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E) :
    spPlaneFix E ≠ ⊥ ∨
      ∃ (M : Subgroup ↥E) (_ : Nat.card M = 3), 3 ≤ Module.finrank K (spLineSpace M) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hfix, hle⟩ := hcon
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hP : CFSG.RankThree.PartOne.KCUnitaryPlane.IsPlane 3 ↥E :=
    ⟨Nat.prime_three, by rw [hcard]; norm_num, fun x => Subtype.ext (hexp x x.2)⟩
  haveI : Fintype {M : Subgroup ↥E // Nat.card M = 3} := Fintype.ofFinite _
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap (spInnerSummand 3 E))
    D.internal).finrank_eq
  rw [Module.finrank_directSum, Fintype.sum_option] at e
  have hV : Module.finrank K (Fin r ⊕ Fin r → K) = r + r := by simp
  have h0 : Module.finrank K (spInnerSummand 3 E none) = 0 := by
    change Module.finrank K (spPlaneFix E) = 0
    rw [hfix]
    exact finrank_bot K _
  have hsum : ∑ M : {M : Subgroup ↥E // Nat.card M = 3},
      Module.finrank K (spInnerSummand 3 E (some M)) ≤ 8 := by
    change ∑ M : {M : Subgroup ↥E // Nat.card M = 3}, Module.finrank K (spLineSpace M.1) ≤ 8
    rw [← Finset.sum_subtype (CFSG.RankThree.PartOne.KCUnitaryPlane.lines 3 ↥E)
      (fun L => CFSG.RankThree.PartOne.KCUnitaryPlane.mem_lines)
      (fun L => Module.finrank K (spLineSpace L))]
    calc _ ≤ (CFSG.RankThree.PartOne.KCUnitaryPlane.lines 3 ↥E).card • 2 :=
          Finset.sum_le_card_nsmul _ _ _ fun L hL => by
            have := hle L (CFSG.RankThree.PartOne.KCUnitaryPlane.mem_lines.mp hL)
            omega
      _ = 8 := by rw [hP.card_lines]; norm_num
  omega

theorem exists_pair_of_big {U : Submodule K (Fin r ⊕ Fin r → K)}
    (hnd : ((spForm r K).restrict U).Nondegenerate) (hbig : 3 ≤ Module.finrank K U)
    {g : StatedSp r K} (hg : g ^ 3 = 1) (hstab : ∀ v ∈ U, spEnd g v ∈ U)
    (hfix : ∀ v ∈ U, spEnd g v = v → v = 0) :
    ∃ y ∈ U, ∃ yb ∈ U, spForm r K y (spEnd g y) ≠ 0 ∧ yb ≠ 0 ∧ spForm r K yb y = 0 ∧
      spForm r K yb (spEnd g y) = 0 := by
  have hU : U ≠ ⊥ := by
    rintro rfl
    simp at hbig
  obtain ⟨y, hy, hyne⟩ := exists_spForm_ne_zero_of_no_fixed hnd hg hstab hfix hU
  have hPU : Submodule.span K {y, spEnd g y} ≤ U := Submodule.span_le.2 (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [hy, hstab y hy])
  have hPrank : Module.finrank K (Submodule.span K {y, spEnd g y}) = 2 :=
    finrank_span_pair_of_spForm hyne
  have hcompl := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (spForm_isAlt (r := r) (K := K)).isRefl (nondegenerate_span_pair hyne)
  have hnot : ¬ U ≤ Submodule.span K {y, spEnd g y} := fun h => by
    have := Submodule.finrank_mono h
    omega
  obtain ⟨w, hwU, hwP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hw : w ∈ Submodule.span K {y, spEnd g y} ⊔
      LinearMap.BilinForm.orthogonal (spForm r K) (Submodule.span K {y, spEnd g y}) := by
    rw [hcompl.sup_eq_top]
    trivial
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hw
  have hqU : q ∈ U := by
    have : q = w - p := by rw [← hpq]; abel
    rw [this]
    exact U.sub_mem hwU (hPU hp)
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hwP
    rw [add_zero] at hpq
    rw [← hpq]
    exact hp
  have hq1 : spForm r K y q = 0 :=
    hq y (Submodule.subset_span (Set.mem_insert _ _))
  have hq2 : spForm r K (spEnd g y) q = 0 :=
    hq _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  refine ⟨y, hy, q, hqU, hyne, hq0, ?_, ?_⟩
  · rw [← spForm_isAlt.neg_eq y q, hq1, neg_zero]
  · rw [← spForm_isAlt.neg_eq (spEnd g y) q, hq2, neg_zero]

theorem mix_core {z : StatedSp r K} (hz : z ^ 3 = 1) (h2 : (1 : K) + 1 = 0)
    {A B : Submodule K (Fin r ⊕ Fin r → K)} (horth : ∀ a ∈ A, ∀ b ∈ B, spForm r K a b = 0)
    (hstabA : ∀ v ∈ A, spEnd z v ∈ A) (hstabB : ∀ v ∈ B, spEnd z v ∈ B)
    (hnormA : ∀ v ∈ A, v + spEnd z v + spEnd z (spEnd z v) = 0)
    (hnormB : ∀ v ∈ B, v + spEnd z v + spEnd z (spEnd z v) = 0)
    {y yb yc : Fin r ⊕ Fin r → K} (hy : y ∈ A) (hyb : yb ∈ A) (hyc : yc ∈ B)
    (hy1 : spForm r K y (spEnd z y) = 1) (hyc1 : spForm r K yc (spEnd z yc) = 1)
    (hyby : spForm r K yb y = 0) (hybz : spForm r K yb (spEnd z y) = 0) :
    spForm r K (y + yc) (spEnd z (y + yc)) = 0 ∧
      spEnd (mixElt z (y + yc) 1) (y + yb) = yb + yc := by
  have h2v : ∀ w : Fin r ⊕ Fin r → K, w + w = 0 := fun w => by
    have h := congrArg (fun c : K => c • w) h2
    simpa [add_smul] using h
  have hsy : spEnd z y ∈ A := hstabA y hy
  have hssy : spEnd z (spEnd z y) ∈ A := hstabA _ hsy
  have hsyc : spEnd z yc ∈ B := hstabB yc hyc
  have hssyc : spEnd z (spEnd z yc) ∈ B := hstabB _ hsyc
  have hBA : ∀ b ∈ B, ∀ a ∈ A, spForm r K b a = 0 := fun b hb a ha => by
    rw [← spForm_isAlt.neg_eq a b, horth a ha b hb, neg_zero]
  have hny := hnormA y hy
  have hnc := hnormB yc hyc
  have hssy_eq : spEnd z (spEnd z y) = -y - spEnd z y := by
    linear_combination (norm := module) hny
  have f1 : spForm r K y yc = 0 := horth y hy yc hyc
  have f2 : spForm r K yb yc = 0 := horth yb hyb yc hyc
  have f3 : spForm r K y (spEnd z yc) = 0 := horth y hy _ hsyc
  have f4 : spForm r K yb (spEnd z yc) = 0 := horth yb hyb _ hsyc
  have f5 : spForm r K y (spEnd z (spEnd z yc)) = 0 := horth y hy _ hssyc
  have f6 : spForm r K yb (spEnd z (spEnd z yc)) = 0 := horth yb hyb _ hssyc
  have f7 : spForm r K yc (spEnd z y) = 0 := hBA yc hyc _ hsy
  have f8 : spForm r K y (spEnd z (spEnd z y)) = -1 := by
    rw [hssy_eq, map_sub, map_neg, spForm_isAlt.self_eq_zero y, hy1]
    ring
  have f9 : spForm r K yb (spEnd z (spEnd z y)) = 0 := by
    rw [hssy_eq, map_sub, map_neg, hyby, hybz]
    ring
  have hu : spForm r K (y + yc) (spEnd z (y + yc)) = 0 := by
    simp only [map_add, LinearMap.add_apply]
    rw [hy1, f7, f3, hyc1]
    linear_combination h2
  refine ⟨hu, ?_⟩
  have e1 : spForm r K (y + yb) (y + yc) = 0 := by
    simp only [map_add, LinearMap.add_apply]
    rw [spForm_isAlt.self_eq_zero y, hyby, f1, f2]
    ring
  have e2 : spForm r K (y + yb) (spEnd z (y + yc)) = 1 := by
    simp only [map_add, LinearMap.add_apply]
    rw [hy1, hybz, f3, f4]
    ring
  have e3 : spForm r K (y + yb) (spEnd z (spEnd z (y + yc))) = -1 := by
    simp only [map_add, LinearMap.add_apply]
    rw [f8, f9, f5, f6]
    ring
  rw [spEnd_mixElt hz hu 1, e1, e2, e3]
  simp only [map_add]
  linear_combination (norm := module) hny + hnc -
    h2v (spEnd z (spEnd z y) + yc + spEnd z (spEnd z yc))

theorem mixed_transCenter_F2 [Finite K] (hK : Nat.card K = 2) {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E) {L N : Subgroup ↥E} (hL : Nat.card L = 3)
    (hN : Nat.card N = 3) (hLN : L ≠ N) (hbig : 3 ≤ Module.finrank K (spLineSpace L))
    (hVN : spLineSpace N ≠ ⊥) :
    ∃ y ∈ spLineSpace L, ∃ y' ∈ spLineSpace N, y ≠ 0 ∧ y' ≠ 0 ∧
      TransCenter (centralizerSpan E) (y + y') := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h2 := one_add_one_of_card_two hK
  obtain ⟨a, haL, ha1⟩ := exists_ne_one_of_one_lt_card (M := L) (by rw [hL]; norm_num)
  obtain ⟨b, hbN, hb1⟩ := exists_ne_one_of_one_lt_card (M := N) (by rw [hN]; norm_num)
  have hbot : L ⊓ N = ⊥ := inf_eq_bot_of_card_prime Nat.prime_three hL hN hLN
  have hzL : a * b ∉ L := by
    intro hz
    have hb' : b ∈ L := by simpa using L.mul_mem (L.inv_mem haL) hz
    have : b ∈ L ⊓ N := ⟨hb', hbN⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hb1 this
  have hzN : a * b ∉ N := by
    intro hz
    have ha' : a ∈ N := by simpa using N.mul_mem hz (N.inv_mem hbN)
    have : a ∈ L ⊓ N := ⟨haL, ha'⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  obtain ⟨z, hzdef⟩ : ∃ z : ↥E, z = a * b := ⟨_, rfl⟩
  rw [← hzdef] at hzL hzN
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ L.one_mem)
  have hz3' : z ^ 3 = 1 := Subtype.ext (hexp z z.2)
  have hz3 : (z : StatedSp r K) ^ 3 = 1 := hexp z z.2
  have hz1' : (z : StatedSp r K) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hZcard : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz3' hz1
  have hLZ : L ≠ Subgroup.zpowers z := fun h => hzL (h ▸ Subgroup.mem_zpowers z)
  have hNZ : N ≠ Subgroup.zpowers z := fun h => hzN (h ▸ Subgroup.mem_zpowers z)
  have hstabL : ∀ v ∈ spLineSpace L, spEnd (z : StatedSp r K) v ∈ spLineSpace L :=
    fun v hv => spLineSpace_stable_of_comm hcomm z hv
  have hstabN : ∀ v ∈ spLineSpace N, spEnd (z : StatedSp r K) v ∈ spLineSpace N :=
    fun v hv => spLineSpace_stable_of_comm hcomm z hv
  have hfixL : ∀ v ∈ spLineSpace L, spEnd (z : StatedSp r K) v = v → v = 0 :=
    fun v hv h => D.eq_zero_of_fixed_spLineSpace hL hZcard hLZ z.2 (Subgroup.mem_zpowers z) hz1'
      hv h
  have hfixN : ∀ v ∈ spLineSpace N, spEnd (z : StatedSp r K) v = v → v = 0 :=
    fun v hv h => D.eq_zero_of_fixed_spLineSpace hN hZcard hNZ z.2 (Subgroup.mem_zpowers z) hz1'
      hv h
  obtain ⟨y, hy, yb, hyb, hyne, hyb0, hyby, hybz⟩ := exists_pair_of_big
    (U := spLineSpace L) (D.nondeg (some ⟨L, hL⟩)) hbig hz3 hstabL hfixL
  obtain ⟨yc, hyc, hycne⟩ := exists_spForm_ne_zero_of_no_fixed (U := spLineSpace N)
    (D.nondeg (some ⟨N, hN⟩)) hz3 hstabN hfixN hVN
  have hne : (some ⟨L, hL⟩ : LineIdx E) ≠ some ⟨N, hN⟩ :=
    fun h => hLN (congrArg Subtype.val (Option.some.inj h))
  have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
    fun a ha b hb => D.orth _ _ hne a ha b hb
  obtain ⟨hu, hmixv⟩ := mix_core hz3 h2 horth hstabL hstabN
    (fun v hv => norm_eq_zero_of_no_fixed hz3 hstabL hfixL hv)
    (fun v hv => norm_eq_zero_of_no_fixed hz3 hstabN hfixN hv) hy hyb hyc
    (eq_one_of_card_two hK hyne) (eq_one_of_card_two hK hycne) hyby hybz
  have hvc : TransCenter (centralizerSpan E) (y + yb) :=
    transCenter_of_mem_summand_three hcard (some ⟨L, hL⟩) ((spLineSpace L).add_mem hy hyb)
  have hmem : mixElt (z : StatedSp r K) (y + yc) 1 ∈ centralizerSpan E :=
    mem_centralizerSpan z.2 hz1' (mixElt_comm hz3 hu 1)
  have key := hvc.map hmem
  rw [hmixv] at key
  exact ⟨yb, hyb, yc, hyc, hyb0,
    fun h => hycne (by rw [h, map_zero, LinearMap.zero_apply]), key⟩

theorem pairCenters_all [Finite K] (hK : Nat.card K = 2) (hr : 5 ≤ r)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E)
    (i j : LineIdx E) (hij : i ≠ j) : PairCenters E i j := by
  classical
  have key : ∀ (L N : Subgroup ↥E) (hL : Nat.card L = 3) (hN : Nat.card N = 3), L ≠ N →
      3 ≤ Module.finrank K (spLineSpace L) →
      PairCenters E (some ⟨L, hL⟩) (some ⟨N, hN⟩) := by
    intro L N hL hN hLN hbig y hy y' hy' hy0 hy'0
    have hVN : spLineSpace N ≠ ⊥ := fun h' => hy'0 (by
      have : y' ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy'
      exact (Submodule.mem_bot K).mp this)
    obtain ⟨yb, hyb, yc, hyc, hyb0, hyc0, hmix⟩ :=
      mixed_transCenter_F2 hK hcomm hexp hcard D hL hN hLN hbig hVN
    have hne : (some ⟨L, hL⟩ : LineIdx E) ≠ some ⟨N, hN⟩ :=
      fun h => hLN (congrArg Subtype.val (Option.some.inj h))
    exact (PairCenters.of_one hcard D hne hyb hyc hyb0 hyc0 hmix) y hy y' hy' hy0 hy'0
  rcases i with _ | ⟨L, hL⟩ <;> rcases j with _ | ⟨N, hN⟩
  · exact absurd rfl hij
  · exact pairCenters_none D hN
  · exact (pairCenters_none D hL).symm
  · have hLN : L ≠ N := fun h => hij (by subst h; rfl)
    rcases exists_big_or_fixed hr hexp hcard D with hfix | ⟨M, hM, hbig⟩
    · exact PairCenters.pivot hcard D (k := none) (Option.some_ne_none _)
        (Option.some_ne_none _).symm hij hfix (pairCenters_none D hL).symm (pairCenters_none D hN)
    · by_cases hLM : L = M
      · subst hLM
        exact key L N hL hN hLN hbig
      by_cases hNM : N = M
      · subst hNM
        exact (key N L hN hL hLN.symm hbig).symm
      · have hVM : spLineSpace M ≠ ⊥ := fun h' => by
          rw [h'] at hbig
          simp at hbig
        exact PairCenters.pivot hcard D (k := some ⟨M, hM⟩)
          (fun h => hLM (congrArg Subtype.val (Option.some.inj h)))
          (fun h => hNM (congrArg Subtype.val (Option.some.inj h)).symm) hij hVM
          (key M L hM hL (Ne.symm hLM) hbig).symm (key M N hM hN (Ne.symm hNM) hbig)

end SpPlaneThreeF2

theorem closure_centralizers_spPlane_three_F2 [Finite K] (hK : Nat.card K = 2) {r : ℕ}
    (hr : 5 ≤ r) {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) :
    Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  have h3 : (3 : K) ≠ 0 := by
    have h2 := SpPlaneThreeF2.one_add_one_of_card_two hK
    have : (3 : K) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  have D := exists_spPlaneDecomp_three h3 hcomm hexp hcard
  exact eq_top_of_transCenter (transCenter_of_pairs (Vs := spInnerSummand 3 E)
    D.internal.submodule_iSup_eq_top D.orth D.nondeg
    (fun i c hc => SpPlaneThree.transCenter_of_mem_summand_three hcard i hc)
    (fun i j hij => SpPlaneThreeF2.pairCenters_all hK hr hcomm hexp hcard D i j hij))

end CFSG.LieType.SeitzGeneration
