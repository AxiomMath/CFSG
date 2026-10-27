module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.PerfectGroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.MinimalNormal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.CentralOdd

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private theorem exists_minimal_normal_le {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} (hQn : Q.Normal) (hQ : Q ≠ ⊥) :
    ∃ P : Subgroup G, P.Normal ∧ P ≠ ⊥ ∧ P ≤ Q ∧ ∀ R ≤ P, R.Normal → R = ⊥ ∨ R = P := by
  classical
  have hex : ∃ n, ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧ R ≤ Q ∧ Nat.card R = n :=
    ⟨_, Q, hQn, hQ, le_rfl, rfl⟩
  obtain ⟨P, hPn, hP1, hPQ, hPc⟩ := Nat.find_spec hex
  refine ⟨P, hPn, hP1, hPQ, fun R hRP hRn => ?_⟩
  by_cases hR : R = ⊥
  · exact Or.inl hR
  · refine Or.inr (Subgroup.eq_of_le_of_card_ge hRP ?_)
    rw [hPc]
    exact Nat.find_min' hex ⟨R, hRn, hR, hRP.trans hPQ, rfl⟩

private theorem quotient_card_eq_four_mul_odd {X : Type*} [Group X] [Finite X] (V : Subgroup X)
    [V.Normal] (S : Sylow 2 X) (hS : Nat.card ↥(S : Subgroup X) = 64)
    (hV : Nat.card V = 16) :
    ∃ m, Odd m ∧ Nat.card (X ⧸ V) = 4 * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (S : Subgroup X).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Sylow.not_dvd_index S
  have hX1 : Nat.card X = 64 * (S : Subgroup X).index := by
    rw [← Subgroup.card_mul_index (S : Subgroup X), hS]
  have hX2 : Nat.card X = Nat.card (X ⧸ V) * 16 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, hV]
  refine ⟨(S : Subgroup X).index, hodd, ?_⟩
  have h : Nat.card (X ⧸ V) * 16 = (4 * (S : Subgroup X).index) * 16 := by
    rw [← hX2, hX1]
    ring
  exact Nat.mul_right_cancel (show 0 < 16 by norm_num) h

private theorem not_four_dvd_of_two_dvd {m q n : ℕ} (hm : Odd m) (hY : 4 * m = q * n)
    (hn : 2 ∣ n) : ¬ 4 ∣ q := by
  intro h4
  obtain ⟨a, ha⟩ := h4
  obtain ⟨b, hb⟩ := hn
  have h8 : 8 ∣ 4 * m := by
    refine ⟨a * b, ?_⟩
    rw [hY, ha, hb]
    ring
  obtain ⟨c, hc⟩ := h8
  have hm2 : m = 2 * c := by
    apply Nat.mul_left_cancel (show 0 < 4 by norm_num)
    rw [hc]
    ring
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr ⟨c, hm2⟩)

theorem isSimpleGroup_quotient_of_perfect {X : Type*} [Group X] [Finite X] (V : Subgroup X)
    [V.Normal] [Group.IsPerfect (X ⧸ V)] [Nontrivial (X ⧸ V)]
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hcent : ∀ x : X, (∀ v ∈ V, v * x = x * v) → x ∈ V)
    (S : Sylow 2 X) (hVS : V ≤ (S : Subgroup X))
    (hZ : Nat.card (Subgroup.center ↥(S : Subgroup X)) = 2)
    (hS : Nat.card ↥(S : Subgroup X) = 64) (hV : Nat.card V = 16)
    (hdvd : Nat.card (X ⧸ V) ∣ 20160) :
    IsSimpleGroup (X ⧸ V) := by
  classical
  obtain ⟨m, hm_odd, hmY⟩ := quotient_card_eq_four_mul_odd V S hS hV
  refine { eq_bot_or_eq_top_of_normal := ?_ }
  intro R hR
  by_cases hRb : R = ⊥
  · exact Or.inl hRb
  · right
    obtain ⟨N, hNn, hNne, hNR, hNmin⟩ := exists_minimal_normal_le hR hRb
    have hmin' : ∀ Rn : Subgroup (X ⧸ V), Rn.Normal → Rn ≤ N → Rn = ⊥ ∨ Rn = N :=
      fun Rn hRnn hRnle => hNmin Rn hRnle hRnn
    have hNtop : N = ⊤ := by
      have hnsolv : ¬ Group.IsSolvable ↥N := by
        intro hs
        haveI : Group.IsSolvable ↥N := hs
        obtain ⟨p, hp, hab, hpow⟩ :=
          minimal_normal_elementary_of_solvable N hNne hmin'
        by_cases hp2 : p = 2
        · rw [hp2] at hpow
          haveI : Nontrivial ↥N := N.nontrivial_iff_ne_bot.mpr hNne
          obtain ⟨g, hg⟩ := exists_ne (1 : ↥N)
          have hg2 : g ^ 2 = 1 :=
            Subtype.ext (by simpa using hpow (g : X ⧸ V) g.2)
          have h2N : 2 ∣ Nat.card ↥N := by
            rw [← orderOf_eq_prime hg2 hg]
            exact orderOf_dvd_natCard g
          have hcardY : 4 * m = Nat.card ((X ⧸ V) ⧸ N) * Nat.card ↥N := by
            rw [← hmY, Subgroup.card_eq_card_quotient_mul_card_subgroup N]
          have hq4 : ¬ 4 ∣ Nat.card ((X ⧸ V) ⧸ N) :=
            not_four_dvd_of_two_dvd hm_odd hcardY h2N
          by_cases hsub : Subsingleton ((X ⧸ V) ⧸ N)
          · have hNtop2 : N = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton N hsub
            haveI : IsMulCommutative (X ⧸ V) :=
              isMulCommutative_iff.mpr fun a b =>
                hab a (hNtop2.symm ▸ Subgroup.mem_top a)
                    b (hNtop2.symm ▸ Subgroup.mem_top b)
            haveI : Subsingleton (X ⧸ V) := inferInstance
            exact (not_subsingleton_iff_nontrivial.mpr
              (inferInstance : Nontrivial (X ⧸ V))) inferInstance
          · haveI : Nontrivial ((X ⧸ V) ⧸ N) :=
              not_subsingleton_iff_nontrivial.mp hsub
            exact hq4 (perfect_four_dvd_card (Y := (X ⧸ V) ⧸ N))
        · have hab' : ∀ a b : ↥N, a * b = b * a :=
            fun a b => Subtype.ext (hab a a.2 b b.2)
          have hpow' : ∀ a : ↥N, a ^ p = 1 :=
            fun a => Subtype.ext (by simpa using hpow (a : X ⧸ V) a.2)
          have hdvdN : Nat.card ↥N ∣ 20160 :=
            (Subgroup.card_subgroup_dvd_card N).trans hdvd
          haveI : Nontrivial ↥N := N.nontrivial_iff_ne_bot.mpr hNne
          have hcardN := card_mem_of_elementary_odd_dvd (N := ↥N) hp hp2 hpow' hdvdN
          have haut := card_mulAut_lt_sixty_of_elementary (N := ↥N) hp hab' hpow' hcardN
          have hcenterN : N ≤ Subgroup.center (X ⧸ V) :=
            le_center_of_perfect_of_card_mulAut_lt N haut
          let M : Subgroup X := N.comap (QuotientGroup.mk' V)
          haveI hMn : M.Normal := (inferInstance : N.Normal).comap (QuotientGroup.mk' V)
          have hVM : V ≤ M := by
            intro v hv
            show (QuotientGroup.mk' V) v ∈ N
            rw [show (QuotientGroup.mk' V) v = 1 from (QuotientGroup.eq_one_iff v).mpr hv]
            exact N.one_mem
          have hMX : ∀ mm ∈ M, ∀ x : X, mm * x * mm⁻¹ * x⁻¹ ∈ V := by
            intro mm hmm x
            have hmN : (QuotientGroup.mk' V) mm ∈ N := hmm
            have hc : (QuotientGroup.mk' V) mm * (QuotientGroup.mk' V) x =
                (QuotientGroup.mk' V) x * (QuotientGroup.mk' V) mm :=
              ((Subgroup.mem_center_iff.mp (hcenterN hmN)) ((QuotientGroup.mk' V) x)).symm
            have hπ : (QuotientGroup.mk' V) (mm * x * mm⁻¹ * x⁻¹) = 1 := by
              simp only [map_mul, map_inv]
              rw [hc]
              group
            exact (QuotientGroup.eq_one_iff (mm * x * mm⁻¹ * x⁻¹)).mp hπ
          have hrel : V.relIndex M = Nat.card ↥N := by
            calc V.relIndex M = (QuotientGroup.mk' V).ker.relIndex M :=
                  congrArg (fun H : Subgroup X => H.relIndex M)
                    (QuotientGroup.ker_mk' V).symm
              _ = Nat.card ((N.comap (QuotientGroup.mk' V)).map (QuotientGroup.mk' V)) :=
                  Subgroup.relIndex_ker (QuotientGroup.mk' V) (K := M)
              _ = Nat.card ↥N := by
                  rw [Subgroup.map_comap_eq_self_of_surjective
                    (QuotientGroup.mk'_surjective V) N]
          have hoddV : Odd (V.relIndex M) := by
            rw [hrel]
            rcases hcardN with h | h | h | h <;> rw [h] <;> decide
          have hMV : M = V :=
            eq_of_central_odd_section V M hVM hVab hcent hMX hoddV S hVS hZ
          have hNbot : N = ⊥ := by
            have hmap : N = M.map (QuotientGroup.mk' V) := by
              change N = (N.comap (QuotientGroup.mk' V)).map (QuotientGroup.mk' V)
              rw [Subgroup.map_comap_eq_self_of_surjective
                (QuotientGroup.mk'_surjective V) N]
            rw [hmap, hMV, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
          exact hNne hNbot
      haveI hcommNorm : (⁅N, N⁆ : Subgroup (X ⧸ V)).Normal :=
        Subgroup.commutator_normal N N
      have hcommN : ⁅N, N⁆ = N := by
        rcases hmin' ⁅N, N⁆ hcommNorm (Subgroup.commutator_le_self N) with h | h
        · exfalso
          haveI : IsMulCommutative ↥N := Subgroup.commutator_self_eq_bot_iff.mp h
          exact hnsolv (Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance))
        · exact h
      haveI : Group.IsPerfect ↥N := Subgroup.isPerfect_iff.mpr hcommN
      haveI : Nontrivial ↥N := N.nontrivial_iff_ne_bot.mpr hNne
      have h4N : 4 ∣ Nat.card ↥N := perfect_four_dvd_card
      have hcardY : Nat.card (X ⧸ V) =
          Nat.card ((X ⧸ V) ⧸ N) * Nat.card ↥N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have hqodd : Odd (Nat.card ((X ⧸ V) ⧸ N)) := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2q
        obtain ⟨a, ha⟩ := h4N
        obtain ⟨b, hb⟩ := h2q
        have h4m : 4 * m = Nat.card ((X ⧸ V) ⧸ N) * Nat.card ↥N := by
          rw [← hmY, hcardY]
        have hm2 : m = 2 * (a * b) := by
          apply Nat.mul_left_cancel (show 0 < 4 by norm_num)
          rw [h4m, hb, ha]
          ring
        exact (Nat.not_even_iff_odd.mpr hm_odd) (even_iff_two_dvd.mpr ⟨a * b, hm2⟩)
      have hsolv : Group.IsSolvable ((X ⧸ V) ⧸ N) :=
        CFSG.FeitThompson.isSolvable_of_odd_natCard _ hqodd
      have hsub : Subsingleton ((X ⧸ V) ⧸ N) := by
        by_contra h
        haveI : Nontrivial ((X ⧸ V) ⧸ N) := not_subsingleton_iff_nontrivial.mp h
        exact (Group.IsPerfect.not_isSolvable ((X ⧸ V) ⧸ N)) hsolv
      exact QuotientGroup.subgroup_eq_top_of_subsingleton N hsub
    exact top_le_iff.mp (hNtop ▸ hNR)

end CFSG.EvenSporadicStandard.HNRecog.GH73
