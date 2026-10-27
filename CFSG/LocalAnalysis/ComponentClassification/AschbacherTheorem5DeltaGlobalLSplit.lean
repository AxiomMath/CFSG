module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLRoot
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalResidual
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalWeakU

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem swap_conj_mem {a : Fin r} (d d'' : DeltaDatum D Abar a) {P : Subgroup G}
    (hU'' : AschbacherTheorem3.omegaOne d''.T = rightConjugate (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) d.g⁻¹)
    (hS'' : d''.S = rightConjugate P d.g⁻¹) {c : G}
    (hc : c ∈ aschbacherThm5Preimage D (Abar a)) :
    d.g⁻¹ * c * d.g ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ∧
      rightConjugate (AschbacherTheorem3.omegaOne d''.T) c =
        rightConjugate (rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
            (d.g⁻¹ * c * d.g)) d.g⁻¹ ∧
      (rightConjugate (AschbacherTheorem3.omegaOne d''.T) c ≤
          d''.S ⊔ AschbacherTheorem3.omegaOne d''.T ↔
        rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
            (d.g⁻¹ * c * d.g) ≤ P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
              (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) := by
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
    (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) with hVdef
  have hcz : c = d.g * (d.g⁻¹ * c * d.g) * d.g⁻¹ := by group
  have hconj : rightConjugate (AschbacherTheorem3.omegaOne d''.T) c =
      rightConjugate (rightConjugate V (d.g⁻¹ * c * d.g)) d.g⁻¹ := by
    rw [hU'']
    conv_lhs => rw [hcz]
    exact rightConjugate_conj_inv V d.g _
  refine ⟨?_, hconj, ?_⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hc
  · rw [hconj, hS'', hU'', ← rightConjugate_sup]
    constructor
    · intro h
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate h d.g
      rwa [rightConjugate_inv_rightConjugate, rightConjugate_inv_rightConjugate] at h1
    · intro h
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate h _

theorem false_of_L_weaklyClosed (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)))
    (hclosed : ∀ z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g,
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) →
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z =
        AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) : False := by
  obtain ⟨d'', -, hT'', hS''⟩ := exists_swap_datum hloc hC d hW hP hWP hPH
  have hU'' : AschbacherTheorem3.omegaOne d''.T = rightConjugate (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) d.g⁻¹ := by
    rw [hT'', omegaOne_rightConjugate]
  refine false_of_weaklyClosed_U hloc hC d'' fun c hc hle => ?_
  obtain ⟨hz, hconj, hiff⟩ := swap_conj_mem d d'' hU'' hS'' hc
  rw [hconj, hclosed _ hz (hiff.mp hle), hU'']

theorem false_of_sylow_le (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)))
    (hPT : P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T)
    (hPle : P ≤ Subgroup.normalizer (D : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d'', hg'', hT'', hS''⟩ := exists_swap_datum hloc hC d hW hP hWP hPH
  obtain ⟨hU'', hW''⟩ := swap_datum_facts d d'' hg'' hT'' hS'' hPT
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  set Z := factorZStar D Abar a with hZdef
  have hV'' : AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G)) = rightConjugate U d.g⁻¹ := by
    rw [hW'', omegaOne_rightConjugate]
  have hT''ab : IsMulCommutative d''.T := by
    rw [hT'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hWab _
  have hW''ab : IsMulCommutative (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G) : Subgroup G) := by
    rw [hW'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hT _
  have hS''H : d''.S ≤ rightConjugate H d''.g := by
    rw [hS'', hg'']
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hPle _
  by_cases hZ' : AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G)) ⊓ Z = ⊥
  ·
    have hUZ : ∀ t ∈ U, t ∈ rightConjugate Z d.g → t = 1 := by
      intro t htU htZ
      have h1 : d.g * t * d.g⁻¹ ∈ AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
          (rightConjugate A d''.g : Set G)) ⊓ Z := by
        refine Subgroup.mem_inf.mpr ⟨?_, (mem_rightConjugate_iff _ _ _).mp htZ⟩
        rw [hV'', mem_rightConjugate_iff]
        simpa [mul_assoc] using htU
      rw [hZ', Subgroup.mem_bot] at h1
      calc t = d.g⁻¹ * (d.g * t * d.g⁻¹) * d.g := by group
        _ = 1 := by rw [h1]; group
    have hnot : ¬ 2 ^ (Nat.card (A ⊓ Subgroup.normalizer (L : Set G) :
        Subgroup G)).factorization 2 ≤ Nat.card d.T := by
      intro h
      obtain ⟨t, htU, htZ, ht1⟩ := exists_U_inf_zStar hloc hC hr d h
      exact ht1 (hUZ t htU htZ)
    rw [← hW.card_eq] at hnot
    push Not at hnot
    have hsz := card_S_le_of_le hC hr d d'' hg'' hS''H
    obtain ⟨k, hk⟩ := d.sylowT.isPGroup.exists_card_eq
    obtain ⟨j, hj⟩ := hW.isPGroup.exists_card_eq
    have hkj : k < j := by
      rw [hk, hj] at hnot
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hnot
    have h2T : 2 * Nat.card d.T ≤ Nat.card W := by
      rw [hk, hj, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) hkj
    have hWS : W = d.S := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hSH (hWS ▸ inf_le_right.trans (normalizer_conj_le hC a d.g))
  ·
    have hne : 1 < Nat.card (AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
        (rightConjugate A d''.g : Set G)) ⊓ Z : Subgroup G) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ'
    have hΩ'' := omegaOne_eq_of_le hloc hC hr d'' hS''H
    apply end_of_6_4 hin hC d''
    apply endHyp_of_le hloc hC hr d'' hT''ab hW''ab hS''H
    rw [hΩ'', hV'', hU'', rightConjugate_card, rightConjugate_card, ← hcard]
    rw [hV''] at hne
    have hpos : 0 < Nat.card U := Nat.card_pos
    nlinarith

theorem false_of_L_wcl (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hWT : Nat.card (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G) ≤
        Nat.card d.T)
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)))
    (hPT : P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T)
    (hPnot : ¬ P ≤ Subgroup.normalizer (D : Set G))
    (hwcl : ∀ z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g,
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) →
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d'', hg'', hT'', hS''⟩ := exists_swap_datum hloc hC d hW hP hWP hPH
  obtain ⟨hU'', hW''⟩ := swap_datum_facts d d'' hg'' hT'' hS'' hPT
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  set Z := factorZStar D Abar a with hZdef
  have hV'' : AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G)) = rightConjugate U d.g⁻¹ := by
    rw [hW'', omegaOne_rightConjugate]
  have hT''ab : IsMulCommutative d''.T := by
    rw [hT'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hWab _
  have hW''ab : IsMulCommutative (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G) : Subgroup G) := by
    rw [hW'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hT _
  have hW''syl : IsSylowOf 2 (d''.S ⊓ Subgroup.normalizer (rightConjugate A d''.g : Set G))
      (A ⊓ Subgroup.normalizer (rightConjugate A d''.g : Set G)) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate d.sylowT d.g⁻¹
    rw [AschbacherTheorem3.rightConjugate_inf, rightConjugate_rightConjugate_inv,
      AschbacherTheorem3.rightConjugate_normalizer] at h1
    rw [hW'', hg'']
    exact h1
  have hTW'' : Nat.card d''.T ≤ Nat.card (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G) : Subgroup G) := by
    rw [hT'', hW'', rightConjugate_card, rightConjugate_card]
    exact hWT
  have hΔ'' := datum_mem_delta d''
  obtain ⟨y, hy, hyN⟩ := exists_not_normalizer_of_card_le hloc hC hΔ'' a d''.sylowT hW''syl hTW''
  have hLH'' : ¬ rightConjugate A d''.g ⊓ H ≤ Subgroup.normalizer (A : Set G) :=
    fun h => hyN (h hy)
  obtain ⟨s, hsWZ, hs1, hs2⟩ := exists_involution_factorZStar hloc hC hr hΔ'' a d''.sylowT
    hW''syl hTW''
  have hVZ'' : 2 ≤ Nat.card (AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G)) ⊓ Z : Subgroup G) := by
    have hne : (AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
        (rightConjugate A d''.g : Set G)) ⊓ Z : Subgroup G) ≠ ⊥ := by
      intro hb
      have hmem : s ∈ AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
          (rightConjugate A d''.g : Set G)) ⊓ Z := ⟨mem_omegaOne hsWZ.1 hs2, hsWZ.2⟩
      rw [hb, Subgroup.mem_bot] at hmem
      exact hs1 hmem
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hSH'' : ¬ d''.S ≤ rightConjugate H d''.g := by
    rw [hS'', hg'']
    intro h
    apply hPnot
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate h d.g
    rwa [rightConjugate_inv_rightConjugate, rightConjugate_inv_rightConjugate] at h1
  have hcard'' : Nat.card (AschbacherTheorem3.omegaOne d''.T) =
      Nat.card (AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
        (rightConjugate A d''.g : Set G))) := by
    rw [hU'', hV'', rightConjugate_card, rightConjugate_card]
    exact hcard.symm
  refine false_of_wcl hin hloc hC hr d'' hW''syl hLH'' hT''ab hW''ab hSH'' hcard'' hVZ''
    fun c hc hle => ?_
  obtain ⟨hz, hconj, hiff⟩ := swap_conj_mem d d'' (by rw [hT'', omegaOne_rightConjugate]) hS'' hc
  rw [hconj, hV'', hU'']
  rw [← rightConjugate_sup, sup_comm]
  exact AschbacherTheorem3.rightConjugate_le_rightConjugate (hwcl _ hz (hiff.mp hle)) _

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
