module

public import CFSG.GH74.Generic.JMaxShapes
public import CFSG.GH74.Generic.JStar2Defs
public import CFSG.GH74.Generic.S45.Defs
public import CFSG.GH74.KGroups.L3EpsSylow
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.HN

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

section Basic

variable {K K' : Type} [Group K] [Group K']

theorem inG2Depth_index_mem {i : ℕ} (h : InG2Depth i K) : 1 ≤ i ∧ i ≤ 8 := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    omega

theorem inG2Depth_eq_six_or_seven_of_ofLieType {i : ℕ} (hK : OfLieType K) (h : InG2Depth i K) :
    i = 6 ∨ i = 7 := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hn, -⟩
  · exact absurd hK hn
  · exact absurd hK hn
  · exact absurd hK hn
  · exact absurd hK hn
  · exact absurd hK hn
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hK hn

theorem ofLieType_of_inG2Depth_six_or_seven {i : ℕ} (hi : i = 6 ∨ i = 7) (h : InG2Depth i K') :
    OfLieType K' := by
  obtain ⟨hG, h⟩ := h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, hl, -⟩ |
    ⟨-, p, f, hp, hp2, hq, hmod⟩ | ⟨rfl, -⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact hl
  · exact ofLieType_of_lieModel_L3 hG.1.1 hmod
  · omega

theorem hAltD_of_ofLieType (hK : OfLieType K) :
    ∀ (K' : Type) [Group K'], InG2Depth (d2 K) K' → ¬ IsAltQuot K' := by
  intro K' _ hK'
  have hpos : 1 ≤ d2 K := (inG2Depth_index_mem hK').1
  have hne : {i : ℕ | InG2Depth i K}.Nonempty := Nat.nonempty_of_pos_sInf hpos
  have hKd : InG2Depth (d2 K) K := Nat.sInf_mem hne
  have h67 := inG2Depth_eq_six_or_seven_of_ofLieType hK hKd
  exact fun hA => hA.2 (ofLieType_of_inG2Depth_six_or_seven h67 hK')

theorem ofLieType_of_lieModel_simple (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel K t n p f) : OfLieType K := by
  have hc : center K = ⊥ := by
    obtain ⟨a, b, hab⟩ := hnab
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hb | ht
    · exact hb
    · exfalso
      have ha : a ∈ center K := by rw [ht]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.1 ha b).symm)
  exact ⟨t, n, p, f, lieModel_of_mulEquiv (mulEquivOfCenterBot hc) h⟩

theorem hAltD_of_lieModel (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel K t n p f) :
    ∀ (K' : Type) [Group K'], InG2Depth (d2 K) K' → ¬ IsAltQuot K' :=
  hAltD_of_ofLieType (ofLieType_of_lieModel_simple hs hnab h)

theorem hAltD_S1 (h : IsSL4Model K) :
    ∀ (K' : Type) [Group K'], InG2Depth (d2 K) K' → ¬ IsAltQuot K' :=
  hAltD_of_ofLieType (ofLieType_of_isSL4Model h)

theorem hAltD_ree (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) {f : ℕ}
    (h : LieModel K .twistedG2 0 3 f) :
    ∀ (K' : Type) [Group K'], InG2Depth (d2 K) K' → ¬ IsAltQuot K' :=
  hAltD_of_lieModel hs hnab h

end Basic

section Orders

theorem factorial_half_ne_sporadic_order {n : ℕ} (hn : 5 ≤ n) :
    n.factorial / 2 ≠ 175560 ∧ n.factorial / 2 ≠ 4030387200 ∧ n.factorial / 2 ≠ 495766656000 ∧
      n.factorial / 2 ≠ 898128000 ∧ n.factorial / 2 ≠ 51765179004000000 ∧
      n.factorial / 2 ≠ 460815505920 ∧ n.factorial / 2 ≠ 273030912000000 := by
  by_cases h20 : 20 ≤ n
  · have h1 : (20 : ℕ).factorial ≤ n.factorial := Nat.factorial_le h20
    have h2 : (20 : ℕ).factorial = 2432902008176640000 := by decide
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · have hn20 : n < 20 := by omega
    interval_cases n <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem not_isAltQuot_of_simple_card {K : Type} [Group K] (hs : IsSimpleGroup K)
    (hq : IsQuasisimple K) {N : ℕ} (hN : Nat.card K = N)
    (hne : ∀ n : ℕ, 5 ≤ n → n.factorial / 2 ≠ N) : ¬ IsAltQuot K := by
  rintro ⟨⟨n, hn, ⟨e⟩⟩, -⟩
  have hc : center K = ⊥ := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple_aux hq
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hb | ht
    · exact hb
    · exfalso
      have ha : a ∈ center K := by rw [ht]; exact Subgroup.mem_top _
      exact hab ((Subgroup.mem_center_iff.1 ha b).symm)
  have h1 : Nat.card (K ⧸ center K) = Nat.card K := by
    rw [← Nat.card_congr (mulEquivOfCenterBot hc).toEquiv]
  have h2 : Nat.card (K ⧸ center K) = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv]
    have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact hne n hn (by rw [← h2, h1, hN])

theorem center_eq_bot_of_simple_quasisimple {K : Type} [Group K] (hs : IsSimpleGroup K)
    (hq : IsQuasisimple K) : center K = ⊥ := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple_aux hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hb | ht
  · exact hb
  · exfalso
    have ha : a ∈ center K := by rw [ht]; exact Subgroup.mem_top _
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

@[expose] def SporadicDepthFacts : Prop :=
  ∀ (K : Type) [Group K],
    (NativeSporadic.IsSporadic K .J1 → IsSimpleGroup K ∧ Nat.card K = 175560) ∧
    (NativeSporadic.IsSporadic K .He → IsSimpleGroup K ∧ Nat.card K = 4030387200) ∧
    (NativeSporadic.IsSporadic K .Co3 → IsSimpleGroup K ∧ Nat.card K = 495766656000) ∧
    (NativeSporadic.IsSporadic K .McL → IsSimpleGroup K ∧ Nat.card K = 898128000) ∧
    (NativeSporadic.IsSporadic K .Ly → IsSimpleGroup K ∧ Nat.card K = 51765179004000000) ∧
    (NativeSporadic.IsSporadic K .ONan → IsSimpleGroup K ∧ Nat.card K = 460815505920) ∧
    (NativeSporadic.IsSporadic K .HN → IsSimpleGroup K ∧ Nat.card K = 273030912000000)

theorem simple_card_of_mulEquiv {K C : Type} [Group K] [Group C] (e : K ≃* C) (hs : IsSimpleGroup C)
    {N : ℕ} (hN : Nat.card C = N) : IsSimpleGroup K ∧ Nat.card K = N :=
  ⟨@MulEquiv.isSimpleGroup _ _ _ _ hs e, by rw [Nat.card_congr e.toEquiv, hN]⟩

theorem sporadicDepthFacts :
    SporadicDepthFacts := by
  intro K _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨e⟩
    exact simple_card_of_mulEquiv e CFSG.Sporadic.J1.isSimpleGroup_J1 CFSG.Sporadic.J1.card_J1
  · rintro ⟨e⟩
    exact simple_card_of_mulEquiv e CFSG.Sporadic.He.isSimpleGroup_He CFSG.Sporadic.He.card_He
  · rintro ⟨e⟩
    exact simple_card_of_mulEquiv e CFSG.Sporadic.Co3.isSimpleGroup_Co3 CFSG.Sporadic.Co3.card_Co3
  · rintro ⟨e⟩
    exact simple_card_of_mulEquiv e CFSG.Sporadic.McL.isSimpleGroup_McL CFSG.Sporadic.McL.card_McL
  · rintro ⟨e⟩
    exact simple_card_of_mulEquiv e CFSG.Sporadic.Ly.isSimpleGroup_Ly CFSG.Sporadic.Ly.card_Ly
  · rintro ⟨e⟩
    exact simple_card_of_mulEquiv e CFSG.Sporadic.ON.isSimpleGroup_ON CFSG.Sporadic.ON.card_ON
  · rintro ⟨e⟩
    exact simple_card_of_mulEquiv e CFSG.Sporadic.HN.isSimpleGroup_HN CFSG.Sporadic.HN.card_HN

end Orders

section J1

variable {K K' : Type} [Group K] [Group K']

theorem J1_not_alt_class (hF : SporadicDepthFacts) (hJ1 : NativeSporadic.IsSporadic K .J1) {i : ℕ}
    (h : InG2Depth i K) : i ≠ 1 ∧ i ≠ 3 ∧ i ≠ 5 ∧ i ≠ 8 := by
  obtain ⟨hsK, hcK⟩ := (hF K).1 hJ1
  obtain ⟨hG, h⟩ := h
  have hqK : IsQuasisimple K := hG.1.1
  have hKc : center K = ⊥ := center_eq_bot_of_simple_quasisimple hsK hqK
  have hne := fun (n : ℕ) (hn : 5 ≤ n) => (factorial_half_ne_sporadic_order hn)
  have hcardAlt : ∀ n : ℕ, 5 ≤ n → Nonempty (K ≃* alternatingGroup (Fin n)) → False := by
    rintro n hn ⟨e⟩
    have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    have h1 : Nat.card K = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    exact (hne n hn).1 (by rw [← h1, hcK])
  rcases h with ⟨rfl, hn, n, hn12, hdc⟩ | ⟨rfl, -⟩ | ⟨rfl, hn, hA | hH⟩ | ⟨rfl, -⟩ | ⟨rfl, hn, hA⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hn, hA | hA⟩
  · exfalso
    have h2 := hdc.2.1
    rw [hKc, Subgroup.card_bot] at h2
    omega
  · omega
  · exfalso
    obtain ⟨n, hn12, hA⟩ := hA
    exact hcardAlt n (by omega) hA
  · exfalso
    obtain ⟨-, hcH⟩ := (hF K).2.2.2.2.2.2 hH
    rw [hcK] at hcH
    omega
  · omega
  · exfalso
    exact hcardAlt 11 (by norm_num) hA
  · omega
  · omega
  · exfalso
    exact hcardAlt 9 (by norm_num) hA
  · exfalso
    exact hcardAlt 10 (by norm_num) hA

theorem inG2Depth_two_sporadic (h : InG2Depth 2 K') :
    NativeSporadic.IsSporadic K' .McL ∨ NativeSporadic.IsSporadic K' .Ly ∨
      NativeSporadic.IsSporadic K' .ONan := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨hi, -⟩ | ⟨-, -, h⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ <;>
    first | exact h | omega

theorem inG2Depth_four_sporadic (h : InG2Depth 4 K') :
    NativeSporadic.IsSporadic K' .J1 ∨ NativeSporadic.IsSporadic K' .He ∨
      NativeSporadic.IsSporadic K' .Co3 := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨-, -, h⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ <;>
    first | exact h | omega

theorem not_isAltQuot_of_inG2Depth_two_four (hF : SporadicDepthFacts) {i : ℕ} (hi : i = 2 ∨ i = 4)
    (h : InG2Depth i K') : ¬ IsAltQuot K' := by
  have hq : IsQuasisimple K' := h.1.1.1
  have hne := fun (n : ℕ) (hn : 5 ≤ n) => (factorial_half_ne_sporadic_order hn)
  rcases hi with rfl | rfl
  · rcases inG2Depth_two_sporadic h with hsp | hsp | hsp
    · obtain ⟨hs, hc⟩ := (hF K').2.2.2.1 hsp
      exact not_isAltQuot_of_simple_card hs hq hc fun n hn => (hne n hn).2.2.2.1
    · obtain ⟨hs, hc⟩ := (hF K').2.2.2.2.1 hsp
      exact not_isAltQuot_of_simple_card hs hq hc fun n hn => (hne n hn).2.2.2.2.1
    · obtain ⟨hs, hc⟩ := (hF K').2.2.2.2.2.1 hsp
      exact not_isAltQuot_of_simple_card hs hq hc fun n hn => (hne n hn).2.2.2.2.2.1
  · rcases inG2Depth_four_sporadic h with hsp | hsp | hsp
    · obtain ⟨hs, hc⟩ := (hF K').1 hsp
      exact not_isAltQuot_of_simple_card hs hq hc fun n hn => (hne n hn).1
    · obtain ⟨hs, hc⟩ := (hF K').2.1 hsp
      exact not_isAltQuot_of_simple_card hs hq hc fun n hn => (hne n hn).2.1
    · obtain ⟨hs, hc⟩ := (hF K').2.2.1 hsp
      exact not_isAltQuot_of_simple_card hs hq hc fun n hn => (hne n hn).2.2.1

theorem hAltD_J1 (hF : SporadicDepthFacts) (hJ1 : NativeSporadic.IsSporadic K .J1) :
    ∀ (K' : Type) [Group K'], InG2Depth (d2 K) K' → ¬ IsAltQuot K' := by
  intro K' _ hK'
  obtain ⟨h1, hi8⟩ := inG2Depth_index_mem hK'
  have hKd : InG2Depth (d2 K) K := Nat.sInf_mem (Nat.nonempty_of_pos_sInf h1)
  obtain ⟨n1, n3, n5, n8⟩ := J1_not_alt_class hF hJ1 hKd
  have hcls : d2 K = 2 ∨ d2 K = 4 ∨ d2 K = 6 ∨ d2 K = 7 := by omega
  rcases hcls with h | h | h | h
  · exact not_isAltQuot_of_inG2Depth_two_four hF (Or.inl h) hK'
  · exact not_isAltQuot_of_inG2Depth_two_four hF (Or.inr h) hK'
  · exact fun hA => hA.2 (ofLieType_of_inG2Depth_six_or_seven (Or.inl h) hK')
  · exact fun hA => hA.2 (ofLieType_of_inG2Depth_six_or_seven (Or.inr h) hK')

end J1

section DepthNeZero

variable {K : Type} [Group K]

theorem d2_ne_zero_of_inG2Depth {i : ℕ} (h : InG2Depth i K) : d2 K ≠ 0 := by
  have hne : {j : ℕ | InG2Depth j K}.Nonempty := ⟨i, h⟩
  have hd : InG2Depth (d2 K) K := Nat.sInf_mem hne
  have := (inG2Depth_index_mem hd).1
  omega

theorem inG2Depth_six_of_ofLieType (hg2 : InG2 K) (hl : OfLieType K) (hn : ¬ IsL3Odd K) :
    InG2Depth 6 K :=
  ⟨hg2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hl, hn⟩)))))⟩

theorem hd0_S1 (h : IsSL4Model K) (hg2 : InG2 K) : d2 K ≠ 0 :=
  d2_ne_zero_of_inG2Depth
    (inG2Depth_six_of_ofLieType hg2 (ofLieType_of_isSL4Model h) (not_isL3Odd_of_isSL4Model hg2.1.1 h))

theorem not_isL3Odd_of_elemAb_sylow {K : Type} [Group K] [Finite K]
    (hK : ∀ R : Sylow 2 K, (∀ a b : (R : Subgroup K), a * b = b * a) ∧
      (∀ a : (R : Subgroup K), a * a = 1) ∧ Nat.card (R : Subgroup K) = 8) : ¬ IsL3Odd K := by
  rintro ⟨p, f, hp, hp2, hmod⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨hab, hsq, hcard⟩ := hK R
  have hS : IsPGroup 2 (R : Subgroup K) := R.isPGroup'
  have hmax : ∀ T : Subgroup K, IsPGroup 2 T → (R : Subgroup K) ≤ T → T ≤ (R : Subgroup K) :=
    fun T hT hle => (R.is_maximal' hT hle).le
  have hle : (R : Subgroup K) ≤ centralizer ((R : Subgroup K) : Set K) := by
    intro a ha b hb
    exact congrArg Subtype.val (hab ⟨b, hb⟩ ⟨a, ha⟩)
  have hcyc : IsCyclic ↥(R : Subgroup K) := by
    rcases hmod with hm | hm
    · have := (CFSG.GH74.KGroups.L3Eps.l3eps_center_sylow (t := .PSL) (Or.inl rfl) hp2
        (stated_of_lieModel_PSL hm) hS hmax).1
      rwa [inf_eq_left.2 hle] at this
    · have := (CFSG.GH74.KGroups.L3Eps.l3eps_center_sylow (t := .PSU) (Or.inr rfl) hp2
        (stated_of_lieModel_PSU hm) hS hmax).1
      rwa [inf_eq_left.2 hle] at this
  obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard
  rw [hcard] at hg
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq g)
  rw [hg] at h2
  omega

theorem hd0_S45 [Finite K] (hKB : S45.KBase K) (hg2 : InG2 K) (hK : S45.IsJ1OrRee K) : d2 K ≠ 0 := by
  have hnL3 : ¬ IsL3Odd K :=
    not_isL3Odd_of_elemAb_sylow fun R => ⟨(hKB.2.2 R).1, (hKB.2.2 R).2.1, (hKB.2.2 R).2.2.1⟩
  by_cases hl : OfLieType K
  · exact d2_ne_zero_of_inG2Depth (inG2Depth_six_of_ofLieType hg2 hl hnL3)
  · rcases hK with hJ1 | ⟨f, h⟩
    · exact d2_ne_zero_of_inG2Depth (i := 4)
        ⟨hg2, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hl, Or.inl hJ1⟩)))⟩
    · exact absurd (ofLieType_of_lieModel_simple hKB.1 (exists_noncomm_of_isQuasisimple_aux hg2.1.1) h) hl

end DepthNeZero

theorem hAltD_S45 (hF : SporadicDepthFacts) {K : Type} [Group K] (hq : IsQuasisimple K)
    (hs : IsSimpleGroup K) (hK : S45.IsJ1OrRee K) :
    ∀ (K' : Type) [Group K'], InG2Depth (d2 K) K' → ¬ IsAltQuot K' := by
  rcases hK with hJ1 | ⟨f, h⟩
  · exact hAltD_J1 hF hJ1
  · exact hAltD_ree hs (exists_noncomm_of_isQuasisimple_aux hq) h

end CFSG.GH74.Generic
