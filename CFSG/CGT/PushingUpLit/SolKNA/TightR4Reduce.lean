module

public import CFSG.ClassicalInvolution.Q3.TL3C11R

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic

namespace R4

theorem tightTopRestrictSR (r : ℕ) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
      (∃ a b : genFittingFStar G, a * b ≠ b * a) →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
      ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
        Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) →
        ∃ (H : Subgroup G) (R' : Subgroup H) (S' : Sylow 2 R') (t' : H),
          TightDatum R' S' t' ∧ TightClsR r H R' S' t' ∧ ¬ TightInO2 t' ∧
          IsSimpleGroup ↥(genFittingFStar H) ∧ (∃ a b : genFittingFStar H, a * b ≠ b * a) ∧
          ¬ TwoSubgroupsFourGenerated (genFittingFStar H) := by
  intro G _ _ _ hnab hlarge R S t hd hq
  obtain ⟨hC, hO⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hnab
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
  have htK : t ∈ tightCore R := Subgroup.subset_closure ⟨hd.mem_right, ht2⟩
  have hK0ne : tightCore R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at htK
    have := hd.order
    rw [htK, orderOf_one] at this
    norm_num at this
  have hSK : (S : Subgroup R).map R.subtype ≤ tightCore R := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.subset_closure ⟨s.2, ?_⟩
    have h1 : IsPGroup 2 ↥(Subgroup.zpowers s) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hs)
    have h2 : IsPGroup 2 ↥((Subgroup.zpowers s).map R.subtype) := h1.map _
    rw [MonoidHom.map_zpowers] at h2
    exact h2
  set H := subnormalClosure (tightCore R) with hH
  have hHsub : IsSubnormal H ⊤ := isSubnormal_subnormalClosure _
  have hKH : tightCore R ≤ H := le_subnormalClosure _
  have hFH : genFittingFStar G ≤ H :=
    le_subnormalClosure_of_isComponentOf (isComponentOf_top_of_normal_simple _ hnab) hC hK0ne
  have hSH : (S : Subgroup R).map R.subtype ≤ H := hSK.trans hKH
  obtain ⟨S', hd', ⟨eS⟩⟩ := hd.restrict hSH
  have hord : orderOf (⟨t, hSH hd.mem⟩ : H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hd.order
  obtain ⟨eF⟩ := nonempty_equiv_genFittingFStar_subgroup hnab hFH
  refine ⟨H, R.subgroupOf H, S', ⟨t, hSH hd.mem⟩, hd', ⟨⟨eS.trans hq.some⟩, ?_, ?_⟩, ?_,
    eF.isSimpleGroup, ?_, ?_⟩
  · unfold TightSelfGen
    rw [tightCore_subgroupOf hKH]
    exact iSup_conjSub_eq_top_of_subnormalClosure (subnormalClosure_subgroupOf_subnormalClosure _)
  · exact CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hHsub
  · exact not_inO2_of_fstar_le hnab hFH hord
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  · exact not_twoSubgroupsFourGenerated_subgroup hnab hlarge hFH

section Class

variable {r : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem le_center_of_normal_two_R (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    {N : Subgroup Y} (hNn : N.Normal) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    N ≤ Subgroup.center Y := by
  have htop : Subgroup.centralizer (N : Set Y) = ⊤ :=
    hd.eq_top_of_conj hc.2.1 fun y x hx => by
      rw [mem_conjSub_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : y⁻¹ * p * y ∈ N := by simpa using hNn.conj_mem p hp y⁻¹
      have := hd.commute_of_normal_two hNn hN2 htN hx hp'
      calc p * x = y * ((y⁻¹ * p * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * x * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [← this]
        _ = x * p := by group
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (N : Set Y) := htop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg p hp).symm

theorem not_tightE4_R (hd : TightDatum R S t) (hc : TightClsR r Y R S t) (hE2 : ¬ TightInO2 t)
    (hZ : Subgroup.center Y = ⊥) : ¬ TightE4 Y := by
  rintro ⟨Q, _, f, -, hf2, hf1, -⟩
  have hle := le_center_of_normal_two_R hd hc (MonoidHom.normal_ker f) hf2
    fun h => hE2 ⟨_, MonoidHom.normal_ker f, hf2, h⟩
  rw [hZ, le_bot_iff] at hle
  exact hf1 hle

end Class

end R4

section Cit3

@[expose] def R4.TightLargeEdgeSR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowR r n → ∀ (Y : Type) [Group Y] [Finite Y]
    [IsSimpleGroup (genFittingFStar Y)], Nat.card Y = n →
    (∃ a b : genFittingFStar Y, a * b ≠ b * a) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightClsR r Y R S t →
      ¬ TightInO2 t → ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R

theorem tightR4_of_below
    (hbelow : ∀ r, 4 ≤ r → ∀ n, CIT3Below n → TightBelowR r n)
    (hedge : ∀ r, 4 ≤ r → ∀ n, R4.TightLargeEdgeSR r n) : TightR4 := by
  intro n hA G _ _ _ hlt hnab hlarge R S t hd
  obtain ⟨r, hr3, ⟨e⟩⟩ := hd.quat
  by_cases hr : r = 3
  · subst hr
    exact ⟨by simpa using e⟩
  · exfalso
    have hr4 : 4 ≤ r := by omega
    obtain ⟨H, R', S', t', hd', hcls, hE2, hFs, hnabH, hlargeH⟩ :=
      R4.tightTopRestrictSR r G hnab hlarge R S t hd ⟨e⟩
    have hHn : Nat.card H < n :=
      lt_of_le_of_lt (Nat.card_le_card_of_injective _ H.subtype_injective) hlt
    have hb : TightBelowR r n := hbelow r hr4 n hA
    have hedgeH := hedge r hr4 (Nat.card H)
      (fun Z _ _ hZ Λ hΛ => hA Z (lt_of_lt_of_le hZ hHn.le) Λ hΛ)
      (fun Z _ _ hZ => hb Z (lt_of_lt_of_le hZ hHn.le)) H rfl hnabH R' S' t' hd' hcls hE2 hlargeH
    rcases hb H hHn R' S' t' hd' hcls with (h2 | ⟨he3, -⟩ | ⟨he3, -⟩ | h4) | hgood
    · exact hE2 h2
    · exact hedgeH he3
    · exact hedgeH he3
    · have hZ : Subgroup.center ↥H = ⊥ :=
        le_bot_iff.mp ((centralizer_fstar_eq_bot_and_oddCore_eq_bot hnabH).1 ▸
          Subgroup.center_le_centralizer _)
      exact R4.not_tightE4_R hd' hcls hE2 hZ h4
    · obtain ⟨x, k, hxC, hx3, hxR, -⟩ := hgood
      obtain ⟨e8⟩ := tl3_nonempty_mulEquiv_q8 S' hd'.quat hd'.twoGroup hd'.le_normalizer hxC hx3
        hxR
      obtain ⟨e'⟩ := hcls.1
      have hcard := Nat.card_congr (e8.symm.trans e').toEquiv
      have hne : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, QuaternionGroup.card,
        QuaternionGroup.card] at hcard
      have h2 : 2 ^ (r - 2) = 2 ^ 1 := by omega
      have := Nat.pow_right_injective (le_refl 2) h2
      omega

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA
