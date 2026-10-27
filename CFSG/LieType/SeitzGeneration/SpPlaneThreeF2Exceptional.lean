module

public import CFSG.LieType.SeitzGeneration.SpPlaneThreeF2

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration.SpPlaneThree

variable {r : ℕ} {K : Type} [Field K]

namespace SpPlaneThreeF2

theorem pairCenters_all_of_big_or_fixed [Finite K] (hK : Nat.card K = 2)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) (D : SpPlaneDecomp 3 E)
    (hbf : spPlaneFix E ≠ ⊥ ∨
      ∃ (M : Subgroup ↥E) (_ : Nat.card M = 3), 3 ≤ Module.finrank K (spLineSpace M))
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
    rcases hbf with hfix | ⟨M, hM, hbig⟩
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

theorem closure_centralizers_spPlane_three_F2_of_big_or_fixed [Finite K] (hK : Nat.card K = 2)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9)
    (hbf : spPlaneFix E ≠ ⊥ ∨
      ∃ (M : Subgroup ↥E) (_ : Nat.card M = 3), 3 ≤ Module.finrank K (spLineSpace M)) :
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
    (fun i j hij => SpPlaneThreeF2.pairCenters_all_of_big_or_fixed hK hcomm hexp hcard D hbf i j
      hij))

theorem pow_three_eq_one_of_commute_of_not_big_or_fixed [Finite K] (hK : Nat.card K = 2)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9)
    (hnot : ¬ (spPlaneFix E ≠ ⊥ ∨
      ∃ (M : Subgroup ↥E) (_ : Nat.card M = 3), 3 ≤ Module.finrank K (spLineSpace M)))
    (g : StatedSp r K) (hg : ∀ x ∈ E, g * x = x * g) : g ^ 3 = 1 := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h2 := SpPlaneThreeF2.one_add_one_of_card_two hK
  have h3 : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  have D := exists_spPlaneDecomp_three h3 hcomm hexp hcard
  push Not at hnot
  obtain ⟨hfix, hle⟩ := hnot
  have h2v : ∀ w : Fin r ⊕ Fin r → K, w + w = 0 := fun w => by
    have h := congrArg (fun c : K => c • w) h2
    simpa [add_smul] using h
  have hgcomm : ∀ x ∈ E, spEnd g * spEnd x = spEnd x * spEnd g := fun x hx => by
    rw [← spEnd_mul, ← spEnd_mul, hg x hx]
  have hstabg : ∀ (M : Subgroup ↥E) {s : Fin r ⊕ Fin r → K}, s ∈ spLineSpace M →
      spEnd g s ∈ spLineSpace M := by
    intro M s hs
    refine ⟨?_, ?_⟩
    · change spEnd g s ∈ CFSG.RankThree.Classical.fixSub (spRep E) M
      rw [CFSG.RankThree.Classical.mem_fixSub]
      intro d hd
      have h1 : spRep E d s = s := CFSG.RankThree.Classical.mem_fixSub.mp hs.1 d hd
      have h1' : spEnd (d : StatedSp r K) s = s := h1
      change spEnd (d : StatedSp r K) (spEnd g s) = spEnd g s
      rw [← Module.End.mul_apply, ← hgcomm d d.2, Module.End.mul_apply, h1']
    · rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have hu0 : u = 0 := by
        have : u ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := hfix ▸ hu
        exact (Submodule.mem_bot K).mp this
      rw [hu0]
      simp
  have hinj : Function.Injective (spEnd g) := by
    intro a b hab
    have := congrArg (spEnd g⁻¹) hab
    simpa [← Module.End.mul_apply, ← spEnd_mul, spEnd_one] using this
  have hall : ∀ v, spEnd (g ^ 3) v = v := by
    intro v
    have hv : v ∈ ⨆ i, spInnerSummand 3 E i := by
      rw [D.internal.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction (spInnerSummand 3 E) (motive := fun v => spEnd (g ^ 3) v = v)
      hv ?_ ?_ ?_
    · rintro (_ | ⟨M, hM⟩) x hx
      · have hx0 : x = 0 := by
          have : x ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := hfix ▸ hx
          exact (Submodule.mem_bot K).mp this
        rw [hx0, map_zero]
      · change x ∈ spLineSpace M at hx
        by_cases hVM : spLineSpace M = ⊥
        · have hx0 : x = 0 := by
            have : x ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := hVM ▸ hx
            exact (Submodule.mem_bot K).mp this
          rw [hx0, map_zero]
        · obtain ⟨z, hzM⟩ : ∃ z : ↥E, z ∉ M := by
            by_contra hcon
            push Not at hcon
            have : M = ⊤ := eq_top_iff.2 fun z _ => hcon z
            rw [this, Subgroup.card_top, hcard] at hM
            norm_num at hM
          have hz1 : z ≠ 1 := fun h => hzM (h ▸ M.one_mem)
          have hz3' : z ^ 3 = 1 := Subtype.ext (hexp z z.2)
          have hz3 : (z : StatedSp r K) ^ 3 = 1 := hexp z z.2
          have hz1' : (z : StatedSp r K) ≠ 1 := fun h => hz1 (Subtype.ext h)
          have hZcard : Nat.card (Subgroup.zpowers z) = 3 := by
            rw [Nat.card_zpowers]
            exact orderOf_eq_prime hz3' hz1
          have hMZ : M ≠ Subgroup.zpowers z := fun h => hzM (h ▸ Subgroup.mem_zpowers z)
          have hstab : ∀ v ∈ spLineSpace M, spEnd (z : StatedSp r K) v ∈ spLineSpace M :=
            fun v hv => spLineSpace_stable_of_comm hcomm z hv
          have hfixz : ∀ v ∈ spLineSpace M, spEnd (z : StatedSp r K) v = v → v = 0 :=
            fun v hv h => D.eq_zero_of_fixed_spLineSpace hM hZcard hMZ z.2
              (Subgroup.mem_zpowers z) hz1' hv h
          obtain ⟨u, huM, hu⟩ := exists_spForm_ne_zero_of_no_fixed (U := spLineSpace M)
            (D.nondeg (some ⟨M, hM⟩)) hz3 hstab hfixz hVM
          have hPU : Submodule.span K {u, spEnd (z : StatedSp r K) u} ≤ spLineSpace M :=
            Submodule.span_le.2 (by
              intro y hy
              rcases hy with rfl | rfl
              exacts [huM, hstab u huM])
          have hPrank : Module.finrank K (Submodule.span K {u, spEnd (z : StatedSp r K) u}) = 2 :=
            finrank_span_pair_of_spForm hu
          have hUle : Module.finrank K (spLineSpace M) ≤ 2 := by
            have := hle M hM
            omega
          have hPeq : Submodule.span K {u, spEnd (z : StatedSp r K) u} = spLineSpace M :=
            Submodule.eq_of_le_of_finrank_le hPU (by omega)
          have hn := norm_eq_zero_of_no_fixed hz3 hstab hfixz huM
          have hSS : spEnd (z : StatedSp r K) (spEnd (z : StatedSp r K) u) =
              u + spEnd (z : StatedSp r K) u := by
            have := h2v (u + spEnd (z : StatedSp r K) u)
            linear_combination (norm := module) hn - this
          have hzc : spEnd g * spEnd (z : StatedSp r K) = spEnd (z : StatedSp r K) * spEnd g :=
            hgcomm z z.2
          have hzc' : ∀ w, spEnd g (spEnd (z : StatedSp r K) w) =
              spEnd (z : StatedSp r K) (spEnd g w) := fun w => by
            have := congrArg (fun f : Module.End K (Fin r ⊕ Fin r → K) => f w) hzc
            simpa using this
          have hgu : spEnd g u ∈ Submodule.span K {u, spEnd (z : StatedSp r K) u} := by
            rw [hPeq]
            exact hstabg M huM
          obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.1 hgu
          have hu0 : u ≠ 0 := fun h => hu (by rw [h]; simp)
          have hT3 : ∀ w, spEnd (g ^ 3) w = spEnd g (spEnd g (spEnd g w)) := fun w => by
            rw [pow_three, spEnd_mul, spEnd_mul]
            rfl
          have hg3u : spEnd (g ^ 3) u = u ∧
              spEnd (g ^ 3) (spEnd (z : StatedSp r K) u) = spEnd (z : StatedSp r K) u := by
            have hTSu : spEnd g (spEnd (z : StatedSp r K) u) =
                spEnd (z : StatedSp r K) (spEnd g u) := hzc' u
            have hc01 : ∀ c : K, c = 0 ∨ c = 1 := fun c => by
              by_cases h : c = 0
              · exact Or.inl h
              · exact Or.inr (SpPlaneThreeF2.eq_one_of_card_two hK h)
            rcases hc01 c₁ with rfl | rfl <;> rcases hc01 c₂ with rfl | rfl
            · exfalso
              simp only [zero_smul, add_zero] at hc
              exact hu0 (hinj (by rw [← hc, map_zero]))
            · simp only [zero_smul, one_smul, zero_add] at hc
              have hTu : spEnd g u = spEnd (z : StatedSp r K) u := hc.symm
              have hTSu' : spEnd g (spEnd (z : StatedSp r K) u) =
                  u + spEnd (z : StatedSp r K) u := by rw [hTSu, hTu, hSS]
              have hTa : spEnd g (u + spEnd (z : StatedSp r K) u) = u := by
                rw [map_add, hTu, hTSu']
                linear_combination (norm := module) h2v (spEnd (z : StatedSp r K) u)
              exact ⟨by rw [hT3, hTu, hTSu', hTa], by rw [hT3, hTSu', hTa, hTu]⟩
            · simp only [one_smul, zero_smul, add_zero] at hc
              have hTu : spEnd g u = u := hc.symm
              have hTSu' : spEnd g (spEnd (z : StatedSp r K) u) = spEnd (z : StatedSp r K) u := by
                rw [hTSu, hTu]
              exact ⟨by rw [hT3, hTu, hTu, hTu], by rw [hT3, hTSu', hTSu', hTSu']⟩
            · simp only [one_smul] at hc
              have hTu : spEnd g u = u + spEnd (z : StatedSp r K) u := hc.symm
              have hTSu' : spEnd g (spEnd (z : StatedSp r K) u) = u := by
                rw [hTSu, hTu, map_add, hSS]
                linear_combination (norm := module) h2v (spEnd (z : StatedSp r K) u)
              have hTTu : spEnd g (u + spEnd (z : StatedSp r K) u) =
                  spEnd (z : StatedSp r K) u := by
                rw [map_add, hTu, hTSu']
                linear_combination (norm := module) h2v u
              exact ⟨by rw [hT3, hTu, hTTu, hTSu'], by rw [hT3, hTSu', hTu, hTTu]⟩
          have hx : x ∈ Submodule.span K {u, spEnd (z : StatedSp r K) u} := by
            rw [hPeq]
            exact hx
          obtain ⟨a₁, a₂, rfl⟩ := Submodule.mem_span_pair.1 hx
          rw [map_add, map_smul, map_smul, hg3u.1, hg3u.2]
    · rw [map_zero]
    · intro x y hx hy
      rw [map_add, hx, hy]
  have h1 : spEnd (g ^ 3) = spEnd (1 : StatedSp r K) := by
    rw [spEnd_one]
    exact LinearMap.ext hall
  exact spLin_injective (Units.ext h1)

theorem pow_three_eq_one_of_commute_of_closure_ne_top [Finite K] (hK : Nat.card K = 2)
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9)
    (hne : Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} ≠ ⊤)
    (g : StatedSp r K) (hg : ∀ x ∈ E, g * x = x * g) : g ^ 3 = 1 := by
  by_cases hbf : spPlaneFix E ≠ ⊥ ∨
      ∃ (M : Subgroup ↥E) (_ : Nat.card M = 3), 3 ≤ Module.finrank K (spLineSpace M)
  · exact absurd (closure_centralizers_spPlane_three_F2_of_big_or_fixed hK hcomm hexp hcard hbf) hne
  · exact pow_three_eq_one_of_commute_of_not_big_or_fixed hK hcomm hexp hcard hbf g hg

end CFSG.LieType.SeitzGeneration
