module

public import CFSG.LieType.SeitzGeneration.SpPlaneBlocksThree
public import CFSG.LieType.SeitzGeneration.SpBlockPlanes
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerMixing

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration.SpPlaneThree

variable {r : ℕ} {K : Type} [Field K]

namespace SpPlaneThree

theorem exists_mixed_transCenter [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E) {L N : Subgroup ↥E} (hL : Nat.card L = 3)
    (hN : Nat.card N = 3) (hLN : L ≠ N) (hVL : spLineSpace L ≠ ⊥) (hVN : spLineSpace N ≠ ⊥) :
    ∃ u ∈ spLineSpace L, ∃ w ∈ spLineSpace N, u ≠ 0 ∧ w ≠ 0 ∧
      TransCenter (centralizerSpan E) (u + w) := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hNL : N ≠ L := fun h => hLN h.symm
  obtain ⟨a, haL, ha1⟩ := exists_ne_one_of_one_lt_card (M := L) (by rw [hL]; norm_num)
  obtain ⟨b, hbN, hb1⟩ := exists_ne_one_of_one_lt_card (M := N) (by rw [hN]; norm_num)
  have ha1' : (a : StatedSp r K) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : StatedSp r K) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have ha3 : (a : StatedSp r K) ^ 3 = 1 := hexp a a.2
  have hb3 : (b : StatedSp r K) ^ 3 = 1 := hexp b b.2
  have hstabL : ∀ v ∈ spLineSpace L, spEnd (b : StatedSp r K) v ∈ spLineSpace L :=
    fun v hv => spLineSpace_stable_of_comm hcomm b hv
  have hstabN : ∀ v ∈ spLineSpace N, spEnd (a : StatedSp r K) v ∈ spLineSpace N :=
    fun v hv => spLineSpace_stable_of_comm hcomm a hv
  have hfixL : ∀ v ∈ spLineSpace L, spEnd (b : StatedSp r K) v = v → v = 0 :=
    fun v hv h => D.eq_zero_of_fixed_spLineSpace hL hN hLN b.2 hbN hb1' hv h
  have hfixN : ∀ v ∈ spLineSpace N, spEnd (a : StatedSp r K) v = v → v = 0 :=
    fun v hv h => D.eq_zero_of_fixed_spLineSpace hN hL hNL a.2 haL ha1' hv h
  obtain ⟨u, huL, hu⟩ := exists_spForm_ne_zero_of_no_fixed (U := spLineSpace L)
    (D.nondeg (some ⟨L, hL⟩)) hb3 hstabL hfixL hVL
  obtain ⟨w, hwN, hw⟩ := exists_spForm_ne_zero_of_no_fixed (U := spLineSpace N)
    (D.nondeg (some ⟨N, hN⟩)) ha3 hstabN hfixN hVN
  have hnu := norm_eq_zero_of_no_fixed hb3 hstabL hfixL huL
  have hnw := norm_eq_zero_of_no_fixed ha3 hstabN hfixN hwN
  have hbuL := hstabL u huL
  have hawN := hstabN w hwN
  set P : Submodule K (Fin r ⊕ Fin r → K) := Submodule.span K {u, spEnd (b : StatedSp r K) u}
    with hP
  set Q : Submodule K (Fin r ⊕ Fin r → K) := Submodule.span K {w, spEnd (a : StatedSp r K) w}
    with hQ
  have hPL : P ≤ spLineSpace L := Submodule.span_le.2 (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [huL, hbuL])
  have hQN : Q ≤ spLineSpace N := Submodule.span_le.2 (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [hwN, hawN])
  have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥E // Nat.card M = 3}) ≠ some ⟨N, hN⟩ :=
    fun h => hLN (congrArg Subtype.val (Option.some.inj h))
  have horth : ∀ x ∈ P, ∀ y ∈ Q, spForm r K x y = 0 := fun x hx y hy =>
    D.orth _ _ hne x (hPL hx) y (hQN hy)
  have horth' : ∀ y ∈ Q, ∀ x ∈ P, spForm r K y x = 0 := fun y hy x hx => by
    rw [← spForm_isAlt.neg_eq x y, horth x hx y hy, neg_zero]
  have hWnd : ((spForm r K).restrict (P ⊔ Q)).Nondegenerate :=
    nondegenerate_sup_of_orthogonal (nondegenerate_span_pair hu) (nondegenerate_span_pair hw)
      horth horth'
  have hdisj : Disjoint P Q := (D.disjoint_lineSpace hL hN hLN).mono hPL hQN
  have hdim : Module.finrank K (P ⊔ Q : Submodule K _) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [disjoint_iff.mp hdisj, finrank_bot, hP, hQ, finrank_span_pair_of_spForm hu,
      finrank_span_pair_of_spForm hw] at h
    omega
  have haW : ∀ v ∈ P ⊔ Q, spEnd (a : StatedSp r K) v ∈ P ⊔ Q := by
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, spEnd_eq_of_mem_spLineSpace haL (hPL hx)]
    exact Submodule.add_mem_sup hx (span_pair_stable hnw y hy)
  have hbW : ∀ v ∈ P ⊔ Q, spEnd (b : StatedSp r K) v ∈ P ⊔ Q := by
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, spEnd_eq_of_mem_spLineSpace hbN (hQN hy)]
    exact Submodule.add_mem_sup (span_pair_stable hnu x hx) hy
  have hcommab : Commute (a : StatedSp r K) b := hcomm a a.2 b b.2
  have hind : (b : StatedSp r K) ∉ Subgroup.zpowers (a : StatedSp r K) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hbL : b ∈ L := by
      have : b = a ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [this]
      exact L.zpow_mem haL k
    have : b ∈ L ⊓ N := ⟨hbL, hbN⟩
    rw [inf_eq_bot_of_card_prime Nat.prime_three hL hN hLN, Subgroup.mem_bot] at this
    exact hb1 this
  have hao : orderOf (a : StatedSp r K) = 3 := orderOf_eq_prime ha3 ha1'
  have hbo : orderOf (b : StatedSp r K) = 3 := orderOf_eq_prime hb3 hb1'
  have hEeq : Subgroup.closure ({(a : StatedSp r K), (b : StatedSp r K)} : Set (StatedSp r K)) =
      E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      exacts [a.2, b.2]
    · rw [card_closure_pair' Nat.prime_three hcommab hao hbo hind, hcard]
      norm_num
  have hstabE : E ≤ spStab (P ⊔ Q) := by
    rw [← hEeq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact mem_spStab_of_stable ha3 haW
    · exact mem_spStab_of_stable hb3 hbW
  have huW : u ∈ P ⊔ Q := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert _ _))
  have hwW : w ∈ P ⊔ Q := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  have hfaith : ∀ x ∈ E, (∀ v ∈ P ⊔ Q, spEnd x v = v) → x = 1 := by
    intro x hxE hx
    by_contra hx1
    have hx1' : (⟨x, hxE⟩ : ↥E) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hx3 : (⟨x, hxE⟩ : ↥E) ^ 3 = 1 := Subtype.ext (hexp x hxE)
    have hXcard : Nat.card (Subgroup.zpowers (⟨x, hxE⟩ : ↥E)) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hx3 hx1'
    have hxX : (⟨x, hxE⟩ : ↥E) ∈ Subgroup.zpowers (⟨x, hxE⟩ : ↥E) := Subgroup.mem_zpowers _
    by_cases hXL : Subgroup.zpowers (⟨x, hxE⟩ : ↥E) = L
    · have hxL : (⟨x, hxE⟩ : ↥E) ∈ L := hXL ▸ hxX
      have hw0 : w = 0 := D.eq_zero_of_fixed_spLineSpace hN hL hNL hxE hxL hx1 hwN (hx w hwW)
      exact hw (by rw [hw0, map_zero, LinearMap.zero_apply])
    · have hu0 : u = 0 := D.eq_zero_of_fixed_spLineSpace hL hXcard (Ne.symm hXL) hxE hxX hx1 huL
        (hx u huW)
      exact hu (by rw [hu0, map_zero, LinearMap.zero_apply])
  refine ⟨u, huL, w, hwN, fun h => hu (by rw [h, map_zero, LinearMap.zero_apply]),
    fun h => hw (by rw [h, map_zero, LinearMap.zero_apply]), ?_⟩
  exact transCenter_of_four h3 hK hcomm hexp hcard hWnd hdim hstabE hfaith
    (Submodule.add_mem _ huW hwW)

theorem transCenter_of_mem_summand_three {E : Subgroup (StatedSp r K)} (hcard : Nat.card E = 9)
    (i : Option {M : Subgroup ↥E // Nat.card M = 3}) {c : Fin r ⊕ Fin r → K}
    (hc : c ∈ spInnerSummand 3 E i) : TransCenter (centralizerSpan E) c := by
  rcases i with _ | ⟨M, hM⟩
  · obtain ⟨t, htE, ht1⟩ := exists_ne_one_of_one_lt_card (M := E) (by rw [hcard]; norm_num)
    exact transCenter_of_fixed htE ht1
      (CFSG.RankThree.Classical.mem_fixSub.mp hc ⟨t, htE⟩ (Subgroup.mem_top _))
  · obtain ⟨t, htM, ht1⟩ := exists_ne_one_of_one_lt_card (M := M) (by rw [hM]; norm_num)
    exact transCenter_of_fixed t.2 (fun h => ht1 (Subtype.ext h))
      (spEnd_eq_of_mem_spLineSpace htM hc)

theorem transCenter_add_of_mem_summands_three {E : Subgroup (StatedSp r K)}
    (D : SpPlaneDecomp 3 E) {M : Subgroup ↥E} (hM : Nat.card M = 3) {y y' : Fin r ⊕ Fin r → K}
    (hy : y ∈ spPlaneFix E) (hy' : y' ∈ spLineSpace M) :
    TransCenter (centralizerSpan E) (y + y') := by
  obtain ⟨t, htM, ht1⟩ := exists_ne_one_of_one_lt_card (M := M) (by rw [hM]; norm_num)
  have hker := D.ker_eq M hM t htM ht1
  have hmem : y + y' ∈ spLineFix M := by
    rw [hker.2]
    exact Submodule.add_mem_sup hy hy'
  rw [← hker.1] at hmem
  exact transCenter_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hmem)

theorem transCenter_pair_three [Finite K] (h3 : (3 : K) ≠ 0) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E)
    (i j : Option {M : Subgroup ↥E // Nat.card M = 3}) (hij : i ≠ j) {y y' : Fin r ⊕ Fin r → K}
    (hy : y ∈ spInnerSummand 3 E i) (hy' : y' ∈ spInnerSummand 3 E j) (hy0 : y ≠ 0)
    (hy'0 : y' ≠ 0) : TransCenter (centralizerSpan E) (y + y') := by
  classical
  rcases i with _ | ⟨L, hL⟩ <;> rcases j with _ | ⟨N, hN⟩
  · exact absurd rfl hij
  · exact transCenter_add_of_mem_summands_three D hN hy hy'
  · rw [add_comm]
    exact transCenter_add_of_mem_summands_three D hL hy' hy
  · have hLN : L ≠ N := fun h' => hij (by subst h'; rfl)
    have hVL : spLineSpace L ≠ ⊥ := fun h' => hy0 (by
      have : y ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy
      exact (Submodule.mem_bot K).mp this)
    have hVN : spLineSpace N ≠ ⊥ := fun h' => hy'0 (by
      have : y' ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy'
      exact (Submodule.mem_bot K).mp this)
    obtain ⟨u₀, hu₀, w₀, hw₀, hu₀0, hw₀0, hmix⟩ :=
      exists_mixed_transCenter h3 hK hcomm hexp hcard D hL hN hLN hVL hVN
    have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥E // Nat.card M = 3}) ≠ some ⟨N, hN⟩ :=
      fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
    have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
      fun a ha b hb => D.orth _ _ hne a ha b hb
    have horth' : ∀ b ∈ spLineSpace N, ∀ a ∈ spLineSpace L, spForm r K b a = 0 :=
      fun b hb a ha => by rw [← spForm_isAlt.neg_eq, horth a ha b hb, neg_zero]
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ := exists_mem_fixing_eq (U := spLineSpace L)
      (D.nondeg (some ⟨L, hL⟩))
      (fun c hc => transCenter_of_mem_summand_three hcard (some ⟨L, hL⟩) hc) hu₀ hy hu₀0 hy0
    obtain ⟨g₂, hg₂, hg₂w, hg₂fix⟩ := exists_mem_fixing_eq (U := spLineSpace N)
      (D.nondeg (some ⟨N, hN⟩))
      (fun c hc => transCenter_of_mem_summand_three hcard (some ⟨N, hN⟩) hc) hw₀ hy' hw₀0 hy'0
    have h2 : spEnd g₂ u₀ = u₀ := hg₂fix u₀ (fun c hc => horth u₀ hu₀ c hc)
    have h1 : spEnd g₁ y' = y' := hg₁fix y' (fun c hc => horth' y' hy' c hc)
    have := hmix.map ((centralizerSpan E).mul_mem hg₁ hg₂)
    rwa [spEnd_mul, Module.End.mul_apply, map_add, h2, hg₂w, map_add, hg₁u, h1] at this

end SpPlaneThree

theorem closure_centralizers_spPlane_three [Finite K] (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {r : ℕ} (hr : 2 ≤ r) {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  have D := exists_spPlaneDecomp_three h3 hcomm hexp hcard
  exact eq_top_of_transCenter (transCenter_of_pairs (Vs := spInnerSummand 3 E)
    D.internal.submodule_iSup_eq_top D.orth D.nondeg
    (fun i c hc => SpPlaneThree.transCenter_of_mem_summand_three hcard i hc)
    (fun i j hij y hy y' hy' hy0 hy'0 =>
      SpPlaneThree.transCenter_pair_three h3 hK hcomm hexp hcard D i j hij hy hy' hy0 hy'0))

end CFSG.LieType.SeitzGeneration
