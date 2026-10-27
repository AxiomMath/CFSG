module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyTrans
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHCoset
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignD

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier

theorem fyRel_of_ctx
    (hΛ : HSCtx) :
    FyRel hΛ.sigma tL fyRe fyAe fyLe fyCe := by
  obtain ⟨r3, rne, hc, hbr, h02, h03, h13, hAs, hAr, c01, c20, c20z, hfus⟩ := hΛ.fy_facts
  exact
    { z_central := hΛ.tL_central
      z_sq := (tL_involution hΛ).1
      r3 := r3
      r_ne := rne
      c_sq := fun i hi => (hc i hi).1
      c_r := fun i hi => (hc i hi).2.1
      c_a := fun i hi => (hc i hi).2.2
      braid := hbr
      comm02 := h02
      comm03 := h03
      comm13 := h13
      a_sig := hAs
      a_r := hAr
      c01 := c01
      c20 := c20
      c20z := c20z
      fusion := hfus }

section Main


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y : G} {S₀ : Subgroup G} {n : G}

theorem Sect7Hyps.f_not_mem_L (hH : Sect7Hyps G L f s y S₀ n) : f ∉ L := by
  intro h
  have hf4 := hH.four.order
  rcases hH.four.eq_one_or_eq_sq_of_mem h hH.four.mem_cent with h1 | h1
  · rw [h1, orderOf_one] at hf4
    omega
  · have : f = 1 := by
      have h2 : f * f⁻¹ = f ^ 2 * f⁻¹ := by rw [← h1]
      calc f = f ^ 2 * f⁻¹ := by group
        _ = f * f⁻¹ := by rw [← h1]
        _ = 1 := by group
    rw [this, orderOf_one] at hf4
    omega

theorem Sect7Hyps.f_sq_ne_one (hH : Sect7Hyps G L f s y S₀ n) : f ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hH.four.order] at this
  omega

theorem fyModelFacts_of_model (hHN : HNCentralizerFacts) (h3 : HSThreeClass)
    (hI : HSInvolutionClasses) (hO : HSOuterThree) (hH : Sect7Hyps G L f s y S₀ n) :
    FyModelFacts L f y := by
  refine ⟨?_, fun w hww hw hwf => hH.exists_three_commuting hO hww hw hwf⟩
  obtain ⟨hΛ, ι, y₁, hy₁mem, hy₁L, hy₁sq, hy₁conj⟩ :=
    exists_model hHN hH.four hH.yy hH.y_not hH.cent_eq hH.quot
  have hrel := fyRel_of_ctx hΛ
  have hf2L : f ^ 2 ∈ L := hH.sq_mem_L
  have hy₁f : y₁ * f * y₁⁻¹ = f⁻¹ :=
    H1_conj_f_of_not_mem hH.four hH.yy hH.yf hH.cent_eq hy₁mem hy₁L
  have hz : ι ⟨f ^ 2, hf2L⟩ = tL := by
    obtain ⟨τ, hτZ, hτ⟩ := hH.four.exists_center_gen
    have hτe : (⟨f ^ 2, hf2L⟩ : L) = τ := Subtype.ext hτ.symm
    rw [hτe]
    have hmem : ι τ ∈ center HSCover := by
      have := map_center_eq_of_mulEquiv ι
      rw [← this]
      exact ⟨τ, hτZ, rfl⟩
    have hne : ι τ ≠ 1 := by
      intro h1
      have : τ = 1 := ι.injective (by rw [h1, map_one])
      exact hH.f_sq_ne_one (by rw [← hτ, this]; rfl)
    exact (hΛ.eq_one_or_tL hmem).resolve_left hne
  obtain ⟨r, yr, x, hTD, hrL, ⟨a, haL, hyr⟩, hx, ⟨n₀, hn₀L, hn₀⟩, ⟨hvL, hvv, hv1, hvt⟩⟩ :=
    thetaData_of_model ι hΛ.sigma hrel (fun u hu => hH.comm_f hu) hH.f_pow_four
      hH.f_sq_ne_one hf2L hy₁sq hy₁f hy₁conj hz
  obtain ⟨Θ, hinj, hΘr, hΘsr, hΘc, hΘx⟩ := hTD.exists_hom
  have hr3 : orderOf r = 3 := orderOf_eq_prime hTD.r3 hTD.r_ne
  have hΘt : Θ (DihedralGroup.r 2, 1, 1) = f ^ 2 := FyThetaData.theta_r_two Θ hΘr
  have hΘv : Θ (1, 1, v0) = x 0 * x 2 := FyThetaData.theta_v0 Θ hΘx
  have hΘr1 : Θ (1, Multiplicative.ofAdd 1, 1) = r := by
    have := hΘc (Multiplicative.ofAdd 1)
    have h1 : (1 : ZMod 3).val = 1 := rfl
    simpa [h1] using this
  have hcomm_t : ∀ m : HModel, Θ m * f ^ 2 = f ^ 2 * Θ m := by
    intro m
    rw [← hΘt, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (d8_mul_r2 m.1) (Prod.ext (by simp) (by simp))
  have hcomm_r : ∀ m : HModel, Θ m * r = r * Θ m := by
    intro m
    rw [← hΘr1, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (by simp) (Prod.ext (mul_comm _ _) (by simp))
  have hconf : FyConf (f ^ 2) r Θ := by
    refine ⟨hinj, ?_, hΘt, hΘr1, ?_, ?_, ?_⟩
    · intro g
      constructor
      · rintro ⟨hgt, hgr⟩
        have hHs : Θ.range ≤ centralizer ({f ^ 2, r} : Set G) := by
          rintro _ ⟨m, rfl⟩
          rw [mem_centralizer_iff]
          intro h hh
          rcases hh with rfl | hh
          · exact (hcomm_t m).symm
          · rw [Set.mem_singleton_iff] at hh
            rw [hh]; exact (hcomm_r m).symm
        have hcard : Nat.card (centralizer ({f ^ 2, r} : Set G)) ≤ Nat.card Θ.range := by
          rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_hmodel]
          exact hH.card_cent_le h3 hrL hr3
        have hrange := Subgroup.eq_of_le_of_card_ge hHs hcard
        rw [hrange, mem_centralizer_iff]
        intro h hh
        rcases hh with rfl | hh
        · exact hgt.symm
        · rw [Set.mem_singleton_iff] at hh
          rw [hh]; exact hgr.symm
      · rintro ⟨m, rfl⟩
        exact ⟨hcomm_t m, hcomm_r m⟩
    ·
      have hvt' : (DihedralGroup.r 2, (1 : Z3), v0) =
          ((DihedralGroup.r 2 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
            (1, 1, v0) := by
        ext <;> simp
      have hΘδ : Θ (DihedralGroup.r 2, 1, v0) = f ^ 2 * (x 0 * x 2) := by
        rw [hvt', map_mul, hΘt, hΘv]
      rcases hH.dichotomy hI hvL hvv hv1 hvt with ⟨⟨g, hg⟩, hng⟩ | ⟨⟨g, hg⟩, hng⟩
      · refine ⟨1, Or.inl rfl, ⟨g, ?_⟩, ?_⟩
        · rw [hΘv]; exact hg
        · rw [hΘv]
          exact hng
      · refine ⟨DihedralGroup.r 2, Or.inr rfl, ⟨g, ?_⟩, ?_⟩
        · rw [hΘδ]; exact hg
        · rw [hΘδ]
          rintro ⟨g', hg'⟩
          apply hng
          refine ⟨g', ?_⟩
          have : f ^ 2 * (f ^ 2 * (x 0 * x 2)) = x 0 * x 2 := by
            have hff : f ^ 2 * f ^ 2 = 1 := by rw [← pow_add]; exact hH.f_pow_four
            calc f ^ 2 * (f ^ 2 * (x 0 * x 2)) = (f ^ 2 * f ^ 2) * (x 0 * x 2) := by group
              _ = x 0 * x 2 := by rw [hff, one_mul]
          rw [← this]; exact hg'
    · intro a ha ha3
      obtain ⟨g, hgL, hg⟩ := hH.exists_conj_of_three h3 ha ha3 (hH.comm_t hrL) hr3
      exact ⟨g, hH.comm_t hgL, hg⟩
    · refine ⟨n₀, hH.comm_t hn₀L, ?_⟩
      have e1 : Θ (DihedralGroup.sr 0, 1, 1) = yr := by
        rw [hΘsr]; simp
      have e2 : Θ (DihedralGroup.sr 1, 1, Equiv.swap 0 1) = f⁻¹ * yr * x 0 := by
        have : ((DihedralGroup.sr 1 : DihedralGroup 4), (1 : Z3), Equiv.swap (0 : Fin 5) 1) =
            (DihedralGroup.sr 1, 1, 1) * (1, 1, CFSG.Permutation.SymmetricCoxeter.adjSwap 4 0) := by
          rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt (by omega : 0 < 4)]
          ext <;> simp
        have h1 : (1 : ZMod 4).val = 1 := rfl
        rw [this, map_mul, hΘsr, hΘx 0 (by omega), h1]
        simp
      rw [e1, e2]
      exact hn₀
  have hy₁H : ∃ a₁ ∈ L, y₁ = a₁ * y := by
    rcases H1_cases hH.four hH.yy hH.cent_eq hy₁mem with h | h
    · exact absurd h hy₁L
    · exact h
  have hyr' : ∃ a' ∈ L, yr = a' * y := by
    obtain ⟨a₁, ha₁, hy₁e⟩ := hy₁H
    exact ⟨a * a₁, L.mul_mem haL ha₁, by rw [hyr, hy₁e, mul_assoc]⟩
  have hcos : FyCoset L f y Θ :=
    fyCoset_of_theta L f y yr r x Θ hΘr hΘsr hΘc hΘx (fun u hu => hH.comm_f hu) hf2L
      hH.f_not_mem_L hrL hx hyr' hH.y_not
      (fun k hk => zpow_f_mem_H1 hH.four hH.yy hH.y_not hH.cent_eq hk)
  exact ⟨r, Θ, hconf, hcos⟩

end Main

end CFSG.EvenSporadicStandard.TwoHS
