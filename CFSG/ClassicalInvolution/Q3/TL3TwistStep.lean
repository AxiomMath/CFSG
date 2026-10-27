module

public import CFSG.ClassicalInvolution.Q3.TL3TwistQuot
public import CFSG.ClassicalInvolution.Q3.Q3TLT3Fusion
public import CFSG.ClassicalInvolution.Q3.TL3DichMain

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem mem_zpowers_of_orderOf_two {c m : Y} (hc : orderOf c = 2)
    (hm : m ∈ Subgroup.zpowers c) : m = 1 ∨ m = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  rw [← zpow_mod_orderOf, hc]
  have h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem TightDatum.not_acts3_of_index_two (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hgen : TightSelfGen R)
    {M : Subgroup Y} (hMn : M.Normal) (htM : t ∈ M) (hM : M ≠ ⊤)
    (h2 : ∀ a b : Y, a ∉ M → b ∉ M → a * b ∈ M) : ¬ TightActs3 R t := by
  intro h3
  have hfus := (hd.threeAct_iff_fusion hq8).mp h3
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have ht1 : t ≠ 1 := by
    intro h
    have := hd.order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hcyc : ∀ s ∈ S₀, s * s = t → IsCyclic ↥(Subgroup.zpowers s) ∧
      Nat.card ↥(Subgroup.zpowers s) = 4 := by
    intro s _ hss
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_zpowers]
    have h4 : s ^ 4 = 1 := by
      calc s ^ 4 = (s * s) * (s * s) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [hss, t_mul_t hd]
    have e : orderOf s = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · rw [pow_one, pow_two, hss]
        exact ht1
      · show s ^ 4 = 1
        exact h4
    rw [e]
    norm_num
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2', h12⟩ := hd.exists_S₀_pair hq8
  have hu : ∃ u ∈ S₀, u * u = t ∧ u ∈ M := by
    by_cases hm1 : r₁ ∈ M
    · exact ⟨r₁, hr₁, h1, hm1⟩
    by_cases hm2 : r₂ ∈ M
    · exact ⟨r₂, hr₂, h2', hm2⟩
    exact ⟨r₁ * r₂, S₀.mul_mem hr₁ hr₂, h12, h2 _ _ hm1 hm2⟩
  obtain ⟨u, huS, huu, huM⟩ := hu
  have hSM : S₀ ≤ M := by
    intro s hs
    rcases hd.S₀_cases hq8 hs with h | h | h
    · rw [h]
      exact M.one_mem
    · rw [h]
      exact htM
    · obtain ⟨cu, hcu⟩ := hcyc u huS huu
      obtain ⟨cs, hcs⟩ := hcyc s hs h
      obtain ⟨g, -, hg⟩ := hfus _ _ (Subgroup.zpowers_le.mpr huS) (Subgroup.zpowers_le.mpr hs)
        cu hcu cs hcs
      have hsg : s ∈ (Subgroup.zpowers u).map (MulAut.conj g).toMonoidHom := by
        rw [hg]
        exact Subgroup.mem_zpowers s
      obtain ⟨v, hv, rfl⟩ := hsg
      have hvM : v ∈ M := (Subgroup.zpowers_le.mpr huM) hv
      exact hMn.conj_mem v hvM g
  apply hM
  exact hd.eq_top_of_conj hgen fun y x hx => by
    rw [mem_conjSub_iff] at hx
    have := hMn.conj_mem _ (hSM hx) y
    rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at this

theorem TightDatum.not_edgeless_of_twin (hd : TightDatum R S t) {c y : Y}
    (hcZ : c ∈ Subgroup.center Y) (hc1 : c ≠ 1) (hy : y * t * y⁻¹ = t * c) :
    ¬ TightEdgeless R := by
  intro hE
  have hJΩ : conjSub y (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨y, rfl⟩
  refine hE _ (CoreAssembly.mem_conjClass_self (tightCore R)) _ hJΩ
    (Or.inl ⟨hJΩ, ?_, conjSub y ((S : Subgroup R).map R.subtype), ?_, ?_, ?_⟩)
  · intro heq
    have hmem : y * t * y⁻¹ ∈ tightCore R := by
      rw [← heq]
      exact conj_mem_conjSub hd.isUniqueInvolution_core.mem
    have hinv : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
      calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [t_mul_t hd]; group
    rcases hd.isUniqueInvolution_core.unique _ hmem hinv with h1 | h1
    · apply hd.isUniqueInvolution_core.ne_one
      calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    · rw [hy] at h1
      exact hc1 (by simpa using h1)
  · exact mem_RSet_of_isSylow2In hJΩ (hd.sylow_core.conj y)
  · exact conjSub_mono hd.sylow_core.1
  · intro x hx
    apply hd.le_normalizer_core
    rw [mem_conjSub_iff] at hx
    have hs := Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (hd.S₀_le hx))
    have hct : ∀ a : Y, a * c = c * a := Subgroup.mem_center_iff.mp hcZ
    have hxtc : x * (t * c) = (t * c) * x := by
      rw [← hy]
      calc x * (y * t * y⁻¹) = y * ((y⁻¹ * x * y) * t) * y⁻¹ := by group
        _ = y * (t * (y⁻¹ * x * y)) * y⁻¹ := by rw [hs]
        _ = y * t * y⁻¹ * x := by group
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * t = x * (t * c) * c⁻¹ := by group
      _ = (t * c) * x * c⁻¹ := by rw [hxtc]
      _ = t * (c * x) * c⁻¹ := by group
      _ = t * (x * c) * c⁻¹ := by rw [hct x]
      _ = t * x := by group

theorem TightTwisted.exists_central_involution (hO : classicalInvolutionOddCore Y = ⊥)
    (h : TightTwisted Y t) : ∃ c ∈ Subgroup.center Y, orderOf c = 2 := by
  obtain ⟨L, -, -, -, -, -, hFZ, hFL⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hO
  have hne : genFittingFitting Y ≠ ⊥ := fun h1 => hFL (h1 ▸ bot_le)
  obtain ⟨m, hm⟩ := hF2.exists_card_eq
  have hm0 : m ≠ 0 := by
    intro h1
    rw [h1, pow_zero] at hm
    exact hne (Subgroup.card_eq_one.mp hm)
  have hdvd : 2 ∣ Nat.card ↥(genFittingFitting Y) := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨c, hFZ c.2, by rw [Subgroup.orderOf_coe]; exact hc⟩

theorem tightExOrGood_of_central {n : ℕ} (hb : TightBelow n) (hn : Nat.card Y = n)
    (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t) {c : Y}
    (hcZ : c ∈ Subgroup.center Y) (hc2 : orderOf c = 2) (hnt : ∀ y : Y, y * t * y⁻¹ ≠ t * c) :
    TightEx Y R S t ∨ GoodThreeElement R t := by
  set N : Subgroup Y := Subgroup.zpowers c with hNdef
  have hNc : N ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr hcZ
  have hNn : N.Normal := ⟨fun m hm g => by
    rw [Subgroup.mem_center_iff.mp (hNc hm) g, mul_inv_cancel_right]
    exact hm⟩
  have hN2 : IsPGroup 2 ↥N :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
  have htN : t ∉ N := fun h => hE2 ⟨N, hNn, hN2, h⟩
  have hntN : ∀ y : Y, ∀ m ∈ N, y * t * y⁻¹ = t * m → m = 1 := by
    intro y m hm hy
    rcases mem_zpowers_of_orderOf_two hc2 hm with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hy) (hnt y)
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hN1 : N ≠ ⊥ := fun h1 => hc1 (by
    have : c ∈ N := Subgroup.mem_zpowers c
    rwa [h1, Subgroup.mem_bot] at this)
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hd' := TwistQ.datum hd hN2 htN hntN
  have hc' := TwistQ.cls hd hNc hN2 htN hc
  have hlt : Nat.card (Y ⧸ N) < n := hn ▸ TwistQ.card_lt hN1
  rcases hb (Y ⧸ N) hlt _ _ _ hd' hc' with hex | hgood
  · rcases hex with h2 | ⟨hedgeless, hnot3⟩ | ⟨hedgeless, f, hfs, hfk⟩ | h4
    · exact absurd (TwistQ.inO2_of hN2 h2) hE2
    · refine Or.inl (Or.inr (Or.inl ⟨?_, fun h3 => hnot3 (TwistQ.acts3_map hd hRN h3)⟩))
      by_contra hne
      exact TwistQ.not_edgeless_map hd hNc hN2 htN hntN hne hedgeless
    · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨?_, f.comp (QuotientGroup.mk' N),
        hfs.comp (QuotientGroup.mk'_surjective N), ?_⟩)))
      · by_contra hne
        exact TwistQ.not_edgeless_map hd hNc hN2 htN hntN hne hedgeless
      · rw [← MonoidHom.comap_ker]
        exact hfk.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
    · exact Or.inl (Or.inr (Or.inr (Or.inr (h4.of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hN2)))))
  · exact Or.inr (TwistQ.good_of hd hNc hN2 htN hntN hgood)

section Cit3


@[expose] def TightTwistAllTwin (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightTwisted Y t →
      (∀ c ∈ Subgroup.center Y, orderOf c = 2 → ∃ y : Y, y * t * y⁻¹ = t * c) →
        ¬ TightEdgeless R → ¬ TightE4 Y → GoodThreeElement R t

theorem tightTwistStep_of_allTwin (h : ∀ n, TightTwistAllTwin n) (n : ℕ) : TightTwistStep n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 htw
  by_cases hall : ∀ c ∈ Subgroup.center Y, orderOf c = 2 → ∃ y : Y, y * t * y⁻¹ = t * c
  · by_cases hE4 : TightE4 Y
    · exact Or.inl (Or.inr (Or.inr (Or.inr hE4)))
    refine Or.inr (h n hA hb Y hn R S t hd hc hE2 htw hall ?_ hE4)
    obtain ⟨c, hcZ, hc2⟩ := htw.exists_central_involution hc.2.2
    obtain ⟨y, hy⟩ := hall c hcZ hc2
    have hc1 : c ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hc2
      exact absurd hc2 (by norm_num)
    exact hd.not_edgeless_of_twin hcZ hc1 hy
  push Not at hall
  obtain ⟨c, hcZ, hc2, hnt⟩ := hall
  exact tightExOrGood_of_central hb hn hd hc hE2 hcZ hc2 hnt

theorem tightStep_of_parts₃ (htw : ∀ n, TightTwistAllTwin n) (h1 : TightSmallBase)
    (h2 : ∀ n, TightLargeEdge n) (h3 : ∀ n, TightLargeLift n) : ∀ n, TightStep n :=
  tightStep_of_parts₂ (tightTwistStep_of_allTwin htw) h1 h2 h3

end Cit3

end CFSG.ClassicalInvolution.Q3
