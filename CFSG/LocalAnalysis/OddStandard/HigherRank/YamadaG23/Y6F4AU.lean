module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AP
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AQ
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {Y : Type*} [Group Y] [Finite Y]

private lemma y6f4a_zpowers_eq_one_or_self_of_orderOf {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) : ∀ x ∈ zpowers t, x = 1 ∨ x = t := by
  intro x hx
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [← zpow_mod_orderOf t k, ht, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem y6f4a_solvableRadical_eq_bot (hO : CFSG.Open.standardComponentOddCore Y = ⊥)
    (h2 : ∀ Q : Subgroup Y, Q.Normal → IsPGroup 2 Q → Q = ⊥) :
    CFSG.solvableRadical Y = ⊥ := by
  by_contra hRne
  haveI hRsolv : Group.IsSolvable (CFSG.solvableRadical Y) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := Y)
  obtain ⟨p, hp, U, hUnorm, hUne, _hUR, hUp⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.normal_solvable_subgroup_contains_normal_primeSubgroup
      (normal := CFSG.solvableRadical Y) hRne
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2
    exact hUne (h2 U hUnorm hUp)
  · haveI : Fact p.Prime := ⟨hp⟩
    have hOdd : Odd (Nat.card ↥U) := by
      obtain ⟨n, hn⟩ := hUp.exists_card_eq
      rw [hn]
      exact (hp.odd_of_ne_two hp2).pow
    have hle : U ≤ CFSG.Open.standardComponentOddCore Y := le_sSup ⟨hUnorm, hOdd⟩
    exact hUne (le_bot_iff.mp (hO ▸ hle))

theorem y6f4a_ne_bot_inf_centralizer {Q : Subgroup Y} (hQ : Q.Normal) (h2 : IsPGroup 2 Q)
    (hQ1 : Q ≠ ⊥) {τ : Y} (hτ : orderOf τ = 2) : Q ⊓ centralizer ({τ} : Set Y) ≠ ⊥ := by
  haveI : Q.Normal := hQ
  let φ : ↥(zpowers τ) →* ConjAct Y :=
    (ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp (zpowers τ).subtype
  letI : MulAction ↥(zpowers τ) ↥Q := MulAction.compHom ↥Q φ
  have hG'2 : IsPGroup 2 ↥(zpowers τ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ]; norm_num)
  have hpα : 2 ∣ Nat.card ↥Q := by
    rcases h2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hQ1
    · exact h
  have h1 : (1 : ↥Q) ∈ MulAction.fixedPoints ↥(zpowers τ) ↥Q := by
    rw [MulAction.mem_fixedPoints]
    intro g
    show ConjAct.toConjAct (g : Y) • (1 : ↥Q) = 1
    apply Subtype.ext
    rw [ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul]
    simp
  obtain ⟨b, hb, hbne⟩ :=
    hG'2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥Q) hpα h1
  have hb_smul : ConjAct.toConjAct τ • b = b := by
    show (⟨τ, Subgroup.mem_zpowers τ⟩ : ↥(zpowers τ)) • b = b
    exact (MulAction.mem_fixedPoints.mp hb) ⟨τ, Subgroup.mem_zpowers τ⟩
  have hval : τ * (b : Y) * τ⁻¹ = (b : Y) := by
    have hv := ConjAct.Subgroup.val_conj_smul (ConjAct.toConjAct τ) b
    rw [hb_smul, ConjAct.toConjAct_smul] at hv
    exact hv.symm
  have hbne' : (b : Y) ≠ 1 := fun h => hbne (Subtype.ext h.symm)
  have hb_cent : (b : Y) ∈ centralizer ({τ} : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    calc τ * (b : Y) = (τ * (b : Y) * τ⁻¹) * τ := by group
      _ = (b : Y) * τ := by rw [hval]
  intro hbot
  have hb_bot : (b : Y) ∈ (⊥ : Subgroup Y) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨b.2, hb_cent⟩
  exact hbne' (Subgroup.mem_bot.mp hb_bot)

theorem y6f4a_normal_two_le_zpowers {τ : Y} {J : Subgroup Y} (hJ : IsSimpleGroup ↥J)
    (hJna : ¬ IsMulCommutative ↥J) (hN : centralizer ({τ} : Set Y) ≤ normalizer (J : Set Y))
    (hC : centralizer (J : Set Y) ⊓ centralizer ({τ} : Set Y) = zpowers τ) {P : Subgroup Y}
    (hPD : P ≤ centralizer ({τ} : Set Y)) (hP2 : IsPGroup 2 P)
    (hPn : ∀ d ∈ centralizer ({τ} : Set Y), ∀ x ∈ P, d * x * d⁻¹ ∈ P) : P ≤ zpowers τ := by
  haveI : IsSimpleGroup ↥J := hJ
  have hτCJ : τ ∈ centralizer (J : Set Y) := by
    have hmem : τ ∈ zpowers τ := Subgroup.mem_zpowers τ
    rw [← hC] at hmem
    exact (Subgroup.mem_inf.mp hmem).1
  have hJD : J ≤ centralizer ({τ} : Set Y) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact (Subgroup.mem_centralizer_iff.mp hτCJ j hj).symm
  have hInorm : ((P ⊓ J).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (H := P ⊓ J) (K := J) inf_le_right]
    intro h k hh hk
    exact Subgroup.mem_inf.mpr
      ⟨hPn k (hJD hk) h hh.1, J.mul_mem (J.mul_mem hk hh.2) (J.inv_mem hk)⟩
  have hPJbot : P ⊓ J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P ⊓ J).subgroupOf J) with hbot | htop
    · rw [← le_bot_iff]
      intro x hx
      have hx' : x ∈ (P ⊓ J) ⊓ J := ⟨hx, hx.2⟩
      exact (disjoint_iff_inf_le.mp (Subgroup.subgroupOf_eq_bot.mp hbot)) hx'
    · exfalso
      have hJP : J ≤ P := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left
      have hJ2 : IsPGroup 2 ↥J := hP2.to_le hJP
      have hctr : Nontrivial (Subgroup.center ↥J) := IsPGroup.center_nontrivial hJ2
      have hctr_ne : Subgroup.center ↥J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hctr
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
      · exact hctr_ne h
      · exact hJna (Subgroup.center_eq_top_iff.mp h)
  intro x hx
  have hxCJ : x ∈ centralizer (J : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hcP : j * x * j⁻¹ * x⁻¹ ∈ P :=
      P.mul_mem (hPn j (hJD hj) x hx) (P.inv_mem hx)
    have hxN : x ∈ normalizer (J : Set Y) := hN (hPD hx)
    have hcJ : j * x * j⁻¹ * x⁻¹ ∈ J := by
      have hxj : x * j⁻¹ * x⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hxN j⁻¹).mp (J.inv_mem hj)
      have hmem := J.mul_mem hj hxj
      simpa [mul_assoc] using hmem
    have hc : j * x * j⁻¹ * x⁻¹ ∈ P ⊓ J := Subgroup.mem_inf.mpr ⟨hcP, hcJ⟩
    have hc1 : j * x * j⁻¹ * x⁻¹ = 1 := by
      have : j * x * j⁻¹ * x⁻¹ ∈ (⊥ : Subgroup Y) := by rwa [← hPJbot]
      simpa using this
    have h1 : j * x * j⁻¹ = x := mul_inv_eq_one.mp hc1
    calc j * x = (j * x * j⁻¹) * j := by group
      _ = x * j := by rw [h1]
  have hxCD : x ∈ centralizer ({τ} : Set Y) := hPD hx
  have : x ∈ centralizer (J : Set Y) ⊓ centralizer ({τ} : Set Y) :=
    Subgroup.mem_inf.mpr ⟨hxCJ, hxCD⟩
  rwa [hC] at this

theorem y6f4a_tau_not_central {τ : Y} {M : Subgroup Y}
    (hM : Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4))))
    (hMτ : ∀ m ∈ M, τ * m * τ⁻¹ = m⁻¹) : τ ∉ center Y := by
  intro hcen
  obtain ⟨m, _hmT, hmM, hm4⟩ :=
    y6f4a_exists_order_four (M := M) (K := ⊤) hM
      (by rw [Subgroup.relIndex_top_left]; norm_num)
  have hcomm : τ * m = m * τ := (Subgroup.mem_center_iff.mp hcen m).symm
  have hfix : τ * m * τ⁻¹ = m := by rw [hcomm]; group
  have hminv : m = m⁻¹ := hfix.symm.trans (hMτ m hmM)
  have hm2 : m ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hminv]
    exact inv_mul_cancel m
  have hdvd : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
  rw [hm4] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem y6f4a_normal_two_eq_bot {τ : Y} (hτ : orderOf τ = 2) {J : Subgroup Y}
    (hJ : IsSimpleGroup ↥J) (hJna : ¬ IsMulCommutative ↥J)
    (hN : centralizer ({τ} : Set Y) ≤ normalizer (J : Set Y))
    (hC : centralizer (J : Set Y) ⊓ centralizer ({τ} : Set Y) = zpowers τ)
    (hcen : τ ∉ center Y) {Q : Subgroup Y} (hQ : Q.Normal) (h2 : IsPGroup 2 Q) : Q = ⊥ := by
  by_contra hQ1
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ
    omega
  have hP2 : IsPGroup 2 (Q ⊓ centralizer ({τ} : Set Y) : Subgroup Y) := h2.to_inf_left
  have hPD : (Q ⊓ centralizer ({τ} : Set Y) : Subgroup Y) ≤ centralizer ({τ} : Set Y) :=
    inf_le_right
  have hPn : ∀ d ∈ centralizer ({τ} : Set Y),
      ∀ x ∈ (Q ⊓ centralizer ({τ} : Set Y) : Subgroup Y),
      d * x * d⁻¹ ∈ (Q ⊓ centralizer ({τ} : Set Y) : Subgroup Y) := by
    intro d hd x hx
    obtain ⟨hxQ, hxD⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hQ.conj_mem x hxQ d, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxD ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have hdt : d * τ = τ * d := (hd τ (Set.mem_singleton τ)).symm
    have hconj : MulAut.conj d τ = τ := by
      rw [MulAut.conj_apply, hdt]
      group
    have hcomm_conj : MulAut.conj d x * τ = τ * MulAut.conj d x := by
      calc MulAut.conj d x * τ
          = MulAut.conj d x * MulAut.conj d τ := by rw [hconj]
        _ = MulAut.conj d (x * τ) := by rw [map_mul]
        _ = MulAut.conj d (τ * x) := by rw [hxD τ (Set.mem_singleton τ)]
        _ = MulAut.conj d τ * MulAut.conj d x := by rw [map_mul]
        _ = τ * MulAut.conj d x := by rw [hconj]
    simpa [MulAut.conj_apply] using hcomm_conj.symm
  have hPz : (Q ⊓ centralizer ({τ} : Set Y) : Subgroup Y) ≤ zpowers τ :=
    y6f4a_normal_two_le_zpowers hJ hJna hN hC hPD hP2 hPn
  have hPne : (Q ⊓ centralizer ({τ} : Set Y) : Subgroup Y) ≠ ⊥ :=
    y6f4a_ne_bot_inf_centralizer hQ h2 hQ1 hτ
  have hτQ : τ ∈ Q := by
    obtain ⟨p, hpne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
    have hpz : (p : Y) ∈ zpowers τ := hPz p.2
    rcases y6f4a_zpowers_eq_one_or_self_of_orderOf hτ (p : Y) hpz with h | h
    · exact absurd (Subtype.ext h) hpne
    · rw [← h]
      exact (Subgroup.mem_inf.mp p.2).1
  have hQeq : Q = zpowers τ := by
    refine y6f4a_eq_zpowers_of_cent h2 hτQ hτ ?_
    intro x hxQ hxcomm
    apply hPz
    exact Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_centralizer_iff.mpr (fun s hs => by
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hxcomm.symm)⟩
  apply hcen
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y * τ * y⁻¹ ∈ zpowers τ := by
    rw [← hQeq]
    exact hQ.conj_mem τ hτQ y
  have hyne : y * τ * y⁻¹ ≠ 1 := by
    intro h
    apply hτ1
    have := congrArg (fun w => y⁻¹ * w * y) h
    simpa [mul_assoc] using this
  rcases y6f4a_zpowers_eq_one_or_self_of_orderOf hτ (y * τ * y⁻¹) hy with h | h
  · exact absurd h hyne
  · calc y * τ = (y * τ * y⁻¹) * y := by group
      _ = τ * y := by rw [h]

end CFSG.OddStandard.HigherRank.YamadaG23
