module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTrans2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R16ExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank

section Certificate

private theorem not_dvd_gcd_three_sub_one_of_ne_three {p n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.gcd 3 (2 ^ n - 1) := by
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
    (h.trans (Nat.gcd_dvd_left 3 _)))

private theorem not_dvd_gcd_three_sub_one_of_three_dvd_add_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    ¬ 3 ∣ Nat.gcd 3 (2 ^ n - 1) := by
  intro hg
  have h' : 3 ∣ 2 ^ n - 1 := hg.trans (Nat.gcd_dvd_right 3 _)
  have h2 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h h'
  rw [show (2 ^ n + 1) - (2 ^ n - 1) = 2 by
    have := Nat.one_le_two_pow (n := n); omega] at h2
  norm_num at h2

private theorem not_dvd_gcd_three_add_one_of_ne_three {p n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.gcd 3 (2 ^ n + 1) := by
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
    (h.trans (Nat.gcd_dvd_left 3 _)))

private theorem not_dvd_gcd_three_add_one_of_three_dvd_sub_one {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    ¬ 3 ∣ Nat.gcd 3 (2 ^ n + 1) := by
  intro hg
  have h' : 3 ∣ 2 ^ n + 1 := hg.trans (Nat.gcd_dvd_right 3 _)
  have h2 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h' h
  rw [show (2 ^ n + 1) - (2 ^ n - 1) = 2 by
    have := Nat.one_le_two_pow (n := n); omega] at h2
  norm_num at h2

private theorem two_le_n_of_i165FamTwE6 {lab : GLALabel} {p : ℕ} (hn1 : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (h : i165FamTwE6 lab p) : 2 ≤ lab.n := by
  obtain ⟨-, hm1 | hm6⟩ := h
  · by_contra hlt
    have hn : lab.n = 1 := by omega
    rw [hn] at hm1
    have h1 : p ∣ 2 ^ 1 - 1 := rk2Ord_eq_one_iff.1 hm1
    exact hp.not_dvd_one (by simpa using h1)
  · by_contra hlt
    have hn : lab.n = 1 := by omega
    rw [hn] at hm6
    have hdvd : p ∣ 2 ^ 6 - 1 := by
      have := (rk2Ord_dvd_iff (p := p) (n := 1) 6).1 (by rw [hm6])
      simpa using this
    have hp37 : p = 3 ∨ p = 7 := by
      have h63 : p ∣ 3 ^ 2 * 7 := by
        simpa using hdvd
      rcases hp.dvd_mul.1 h63 with h3 | h7
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
          (hp.dvd_of_dvd_pow h3))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7)
    rcases hp37 with rfl | rfl
    · rw [rk2Ord_three_one_eq_two] at hm6
      omega
    · rw [rk2Ord_seven_one_eq_three] at hm6
      omega

theorem i165On_famE6_of_models (h2 : E6Model165At 2) (h3 : E6Model165At 3) :
    I165On i165FamE6 := by
  refine i165On_of_cover_sc ?_
  intro K _ _ lab p q hK hfam hp hp2 hq hq2 hqp hns he hm4
  obtain ⟨ht, hcase⟩ := hfam
  have hn2 : 2 ≤ lab.n := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h
  have hm : rk2Ord p lab.n = 2 ∨ rk2Ord p lab.n = 3 := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hqdiv : q ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 ∧ q = 3 := by
    have h3 : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3 he.symm
    exact dvd_two_pow_sub_one_or_eq_three_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (by rw [ht]; trivial)
  obtain ⟨F, hField, hFinite, π, hCard, hπ, hker⟩ := exists_cover_e6_of_isLabel hK ht hn2
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hCard
  have hZcard : Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) =
      Nat.gcd 3 (2 ^ lab.n - 1) := by
    rw [← hCard]
    exact (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F).1
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
    rw [hZcard]
    rcases eq_or_ne p 3 with hp3 | hp3
    · subst hp3
      have hm2 : rk2Ord 3 lab.n = 2 := by
        rcases hm with h | h
        · exact h
        · have := rk2Ord_three_le lab.n
          omega
      exact not_dvd_gcd_three_sub_one_of_three_dvd_add_one
        ((rk2Ord_eq_two_iff Nat.prime_three (by norm_num)).1 hm2)
    · exact not_dvd_gcd_three_sub_one_of_ne_three hp hp3
  have hpk : ¬ p ∣ Nat.card π.ker := fun h =>
    hpZ (h.trans (Subgroup.card_dvd_of_le hker))
  refine ⟨↥(e6Data_valid.minGroup F), inferInstance, inferInstance, π, hπ, hker, hpk, ?_⟩
  intro Ã hAe hASC hmax hA3
  have hmodel : Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
      (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
    rcases hm with hm2 | hm3
    · exact h2 F lab.n p q hCard hn2 hp hp2 hm2 hq hq2 hqp hqdiv Ã hAe hASC hmax hA3
    · exact h3 F lab.n p q hCard hn2 hp hp2 hm3 hq hq2 hqp hqdiv Ã hAe hASC hmax hA3
  obtain ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, hFZ⟩ := hmodel
  exact ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3,
    le_bot_iff.mp ((inf_le_inf_left F' hker).trans (le_of_eq hFZ))⟩

theorem i165On_famTwE6_of_models (h1 : TwE6Model165At 1) (h6 : TwE6Model165At 6) :
    I165On i165FamTwE6 := by
  refine i165On_of_cover_sc ?_
  intro K _ _ lab p q hK hfam hp hp2 hq hq2 hqp hns he hm4
  have hlam := (quasisimple_markedModel_of_isLabel hK).2.1
  have hn2 : 2 ≤ lab.n := two_le_n_of_i165FamTwE6 hlam.1 hp hp2 hfam
  obtain ⟨ht, hm⟩ := hfam
  have hqdiv : q ∣ 2 ^ lab.n + 1 := by
    have h3 : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3 he.symm
    exact dvd_two_pow_add_one_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (Or.inr ht)
  obtain ⟨k, hkfield, hkfin, θ, hkcard, hθ, π, hπ, hker⟩ :=
    exists_cover_twE6_of_isLabel hK ht hn2
  letI : Field k := hkfield
  letI : Finite k := hkfin
  letI : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  haveI : Finite ↥(fixedGroup k θ) := Subtype.finite
  have hk2 : Nat.card k = 2 ^ (2 * lab.n) := by
    rw [hkcard, ← pow_mul, mul_comm]
  haveI : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hk2
  have hZcard : Nat.card (Subgroup.center ↥(fixedGroup k θ)) =
      Nat.gcd 3 (2 ^ lab.n + 1) :=
    (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
      (q := 2 ^ lab.n) hkcard hθ).1
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥(fixedGroup k θ)) := by
    rw [hZcard]
    rcases eq_or_ne p 3 with hp3 | hp3
    · subst hp3
      have hm1 : rk2Ord 3 lab.n = 1 := by
        rcases hm with h | h
        · exact h
        · have := rk2Ord_three_le lab.n
          omega
      exact not_dvd_gcd_three_add_one_of_three_dvd_sub_one (rk2Ord_eq_one_iff.1 hm1)
    · exact not_dvd_gcd_three_add_one_of_ne_three hp hp3
  have hpk : ¬ p ∣ Nat.card π.ker := fun h =>
    hpZ (h.trans (Subgroup.card_dvd_of_le hker))
  refine ⟨↥(fixedGroup k θ), inferInstance, inferInstance, π, hπ, hker, hpk, ?_⟩
  intro Ã hAe hASC hmax hA3
  have hmodel : Concl165Avoid ↥(fixedGroup k θ) p q Ã
      (Subgroup.center ↥(fixedGroup k θ)) := by
    rcases hm with hm1 | hm6
    · exact h1 k lab.n p q θ hkcard hθ hn2 hp hp2 hm1 hq hq2 hqp hqdiv Ã hAe hASC hmax hA3
    · exact h6 k lab.n p q θ hkcard hθ hn2 hp hp2 hm6 hq hq2 hqp hqdiv Ã hAe hASC hmax hA3
  obtain ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, hFZ⟩ := hmodel
  exact ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3,
    le_bot_iff.mp ((inf_le_inf_left F' hker).trans (le_of_eq hFZ))⟩

theorem i165On_famE7_of_models (h3 : E7Model165At 3) (h6 : E7Model165At 6) :
    I165On i165FamE7 := by
  refine i165On_of_model_sc ?_
  intro K _ _ lab p q hK hfam hp hp2 hq hq2 hqp hns he hm4 A hAe hASC hmax hA3
  obtain ⟨ht, hm⟩ := hfam
  obtain ⟨hQo, hlam, hMo⟩ := CFSG.LocalAnalysis.GLTheoremA.rk2_model_of_isLabel hK
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.i61_center_eq_bot_of_model hQo
      (CFSG.LocalAnalysis.GLTheoremA.i61_model_E7 hMo ht)
      (CFSG.LocalAnalysis.GLTheoremA.i61_gen_E7 hlam.1)
      CFSG.LocalAnalysis.GLTheoremA.i61_exc_E7
  obtain ⟨F, hField, hFinite, hCard, ⟨e⟩⟩ :=
    exists_mulEquiv_adjointGroup_E7_of_hasLabel hK ht hZ
  letI : Field F := hField
  letI : Finite F := hFinite
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hlam.1 hCard
  have hqdiv : q ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 ∧ q = 3 := by
    have h3' : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3' he.symm
    exact dvd_two_pow_sub_one_or_eq_three_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (by rw [ht]; trivial)
  let Ã : Subgroup ↥(adjointGroup .E7 F) := A.map e.toMonoidHom
  have hÃe : IsElemAbelian p Ã := CFSG.SectionRank.isElemAbelian_map hAe e.toMonoidHom
  have hÃrank : CFSG.Open.pRank p Ã = CFSG.Open.pRank p A := by
    have htop : (⊤ : Subgroup A).map (e.toMonoidHom.comp A.subtype) = Ã := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← htop, pRank_eq_pRank_top_subgroup A]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (e.toMonoidHom.comp A.subtype) (fun x y h => Subtype.ext (e.injective h)) ⊤
  have hÃmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup .E7 F)) ≤
      CFSG.Open.pRank p Ã := by
    rw [← pRank_top_eq_of_mulEquiv hp.one_lt e, hÃrank]
    exact hmax
  have hÃ3 : 3 ≤ CFSG.Open.pRank p Ã := by
    rw [hÃrank]
    exact hA3
  have hÃSC : ∀ g ∈ Subgroup.centralizer (Ã : Set ↥(adjointGroup .E7 F)),
      orderOf g = p → g ∈ Ã := by
    intro g hg hgord
    obtain ⟨x, rfl⟩ := e.surjective g
    refine Subgroup.mem_map_of_mem e.toMonoidHom (hASC x ?_ ?_)
    · rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro a ha
      have h2 := hg (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha)
      exact e.injective (by simpa only [map_mul] using h2)
    · have hxp : x ^ p = 1 := by
        apply e.injective
        rw [map_pow, map_one, ← hgord]
        exact pow_orderOf_eq_one (e x)
      have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
      have hxne : x ≠ 1 := by
        intro hx1
        rw [hx1, map_one] at hgord
        simp at hgord
        exact hp.ne_one hgord.symm
      exact (Nat.dvd_prime hp).1 hdvd |>.resolve_left
        (fun h1 => hxne (orderOf_eq_one_iff.1 h1))
  have hmodel : Concl165 ↥(adjointGroup .E7 F) p q Ã := by
    rcases hm with hm3 | hm6
    · exact h3 F lab.n p q hCard hlam.1 hp hp2 hm3 hq hq2 hqp hqdiv Ã hÃe hÃSC hÃmax hÃ3
    · exact h6 F lab.n p q hCard hlam.1 hp hp2 hm6 hq hq2 hqp hqdiv Ã hÃe hÃSC hÃmax hÃ3
  exact concl165_of_mulEquiv hp hq e hmodel

theorem i165On_famE8_of_models (h3 : E8Model165At 3) (h4 : E8Model165At 4)
    (h6 : E8Model165At 6) : I165On i165FamE8 := by
  refine i165On_of_model_sc ?_
  intro K _ _ lab p q hK hfam hp hp2 hq hq2 hqp hns he hm4 A hAe hASC hmax hA3
  obtain ⟨ht, hm⟩ := hfam
  obtain ⟨hQo, hlam, hMo⟩ := CFSG.LocalAnalysis.GLTheoremA.rk2_model_of_isLabel hK
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.i61_center_eq_bot_of_model hQo
      (CFSG.LocalAnalysis.GLTheoremA.i61_model_E8 hMo ht)
      (CFSG.LocalAnalysis.GLTheoremA.i61_gen_E8)
      CFSG.LocalAnalysis.GLTheoremA.i61_exc_E8
  obtain ⟨e⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E8 hK ht hZ
  let F := GaloisField 2 lab.n
  have hn1 : 1 ≤ lab.n := hlam.1
  have hCard : Nat.card F = 2 ^ lab.n := GaloisField.card 2 lab.n (by omega)
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hlam.1 hCard
  have hqdiv : q ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 ∧ q = 3 := by
    have h3' : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3' he.symm
    exact dvd_two_pow_sub_one_or_eq_three_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (by rw [ht]; trivial)
  let Ã : Subgroup ↥(adjointGroup .E8 F) := A.map e.toMonoidHom
  have hÃe : IsElemAbelian p Ã := CFSG.SectionRank.isElemAbelian_map hAe e.toMonoidHom
  have hÃrank : CFSG.Open.pRank p Ã = CFSG.Open.pRank p A := by
    have htop : (⊤ : Subgroup A).map (e.toMonoidHom.comp A.subtype) = Ã := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← htop, pRank_eq_pRank_top_subgroup A]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (e.toMonoidHom.comp A.subtype) (fun x y h => Subtype.ext (e.injective h)) ⊤
  have hÃmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup .E8 F)) ≤
      CFSG.Open.pRank p Ã := by
    rw [← pRank_top_eq_of_mulEquiv hp.one_lt e, hÃrank]
    exact hmax
  have hÃ3 : 3 ≤ CFSG.Open.pRank p Ã := by
    rw [hÃrank]
    exact hA3
  have hÃSC : ∀ g ∈ Subgroup.centralizer (Ã : Set ↥(adjointGroup .E8 F)),
      orderOf g = p → g ∈ Ã := by
    intro g hg hgord
    obtain ⟨x, rfl⟩ := e.surjective g
    refine Subgroup.mem_map_of_mem e.toMonoidHom (hASC x ?_ ?_)
    · rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro a ha
      have h2 := hg (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha)
      exact e.injective (by simpa only [map_mul] using h2)
    · have hxp : x ^ p = 1 := by
        apply e.injective
        rw [map_pow, map_one, ← hgord]
        exact pow_orderOf_eq_one (e x)
      have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
      have hxne : x ≠ 1 := by
        intro hx1
        rw [hx1, map_one] at hgord
        simp at hgord
        exact hp.ne_one hgord.symm
      exact (Nat.dvd_prime hp).1 hdvd |>.resolve_left
        (fun h1 => hxne (orderOf_eq_one_iff.1 h1))
  have hmodel : Concl165 ↥(adjointGroup .E8 F) p q Ã := by
    rcases hm with hm3 | hm4' | hm6
    · exact h3 F lab.n p q hCard hlam.1 hp hp2 hm3 hq hq2 hqp hqdiv Ã hÃe hÃSC hÃmax hÃ3
    · exact h4 F lab.n p q hCard hlam.1 hp hp2 hm4' hq hq2 hqp hqdiv Ã hÃe hÃSC hÃmax hÃ3
    · exact h6 F lab.n p q hCard hlam.1 hp hp2 hm6 hq hq2 hqp hqdiv Ã hÃe hÃSC hÃmax hÃ3
  exact concl165_of_mulEquiv hp hq e hmodel

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
