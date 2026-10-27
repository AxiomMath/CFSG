module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalL1Cent
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalL1
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalL1Bar

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.SignalizerFunctor.Helpers

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix SectionSix.BarTools DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem le_of_bar_centralizes (hC : Counterexample G D r Abar) {a : Fin r}
    (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g)
    (hU1 : AschbacherTheorem3.omegaOne d.T ≠ ⊥)
    (hcent : ∀ t ∈ bar D (AschbacherTheorem3.omegaOne d.T), ∀ s ∈ bar D d.S, t * s = s * t) :
    d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g := by
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hUH : U ≤ Subgroup.normalizer (D : Set G) := EndHyp.U_le_H hC
  have hSH : d.S ≤ Subgroup.normalizer (D : Set G) := d.sylowS.le.trans EndHyp.A_le_H
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  intro s hs
  refine centralizer_le_of_mem_zStar_conj hC d.g (hUZ hu) (twoElt_of_mem hU2 hu) hu1'
    (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  have h1 := hcent _ (toBar_mem_bar D (h := ⟨u, hUH hu⟩) hu) _
    (toBar_mem_bar D (h := ⟨s, hSH hs⟩) hs)
  have h2 := (commutator_mem_core_iff D ⟨u, hUH hu⟩ ⟨s, hSH hs⟩).mpr h1
  have h3 : u⁻¹ * s⁻¹ * u * s ∈ d.S := by
    have h4 : u⁻¹ * s⁻¹ * u ∈ d.S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _
        (EndHyp.U_le_normalizer_S hu)) s⁻¹).mp (d.S.inv_mem hs)
      simpa [mul_assoc] using this
    exact d.S.mul_mem h4 hs
  have h5 : u⁻¹ * s⁻¹ * u * s = 1 := eq_one_of_mem_core h2 (twoElt_of_mem d.sylowS.isPGroup h3)
  calc s * u = s * u * (u⁻¹ * s⁻¹ * u * s) := by rw [h5, mul_one]
    _ = u * s := by group

theorem false_of_wcl_zStar (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g)
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hwcl : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
    (rightConjugate A d.g : Set G)) with hVdef
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hUH : U ≤ H := EndHyp.U_le_H hC
  have hU4 : 4 ≤ Nat.card U := four_le_card_U hloc hC d
  have hU1 : U ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hU4; omega
  have hUel : IsElemAbelian 2 U := isElemAbelian_omegaOne hT
  obtain ⟨b, hbS, hbH, hbU⟩ := exists_conj_of_not_le d hSH
  have hKeq : U ⊔ V = U ⊔ rightConjugate U b := sup_conj_eq hloc hC d hT hWab hcard hbS hbH hbU
  have hwcl' : ∀ c ∈ A, rightConjugate U c ≤ d.S ⊔ U → rightConjugate U c ≤
      U ⊔ rightConjugate U b := fun c hc hle => hKeq ▸ hwcl c hc hle
  have hcomm := UV_comm hC d hT hWab
  rw [hKeq] at hcomm
  set b' : H := ⟨b, EndHyp.A_le_H (d.sylowS.le hbS)⟩ with hb'def
  have hSF := sylowFrame_bar_U hC d hUZ hU1
  have h43 := hyp43_bar_U hC d hUZ
  have hT1 : bar D U ≠ ⊥ := fun h => hU1 ((bar_eq_bot_iff_of_isPGroup hU2 hUH).mp h)
  have hO : CFSG.oddCore (bar D A) = ⊥ := oddCore_bar_eq_bot (preimage_le D _)
    (le_normalizer_factor hC a)
  have hg : toBar D b' ∈ bar D A := toBar_mem_bar D (d.sylowS.le hbS)
  have hWC := weakClosure_bar_U hC d hbS hwcl'
  have hUbH : rightConjugate U b ≤ H :=
    (AschbacherTheorem3.rightConjugate_le_rightConjugate hUH b).trans (le_of_eq
      ((rightConjugate_eq_self_iff H b).mpr (Subgroup.le_normalizer b'.2)))
  have hUbN : rightConjugate U b ≤ Subgroup.normalizer (U : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      congrArg Subtype.val (hcomm.is_comm.comm ⟨u, Subgroup.mem_sup_left hu⟩
        ⟨x, Subgroup.mem_sup_right hx⟩))
  have hN : rightConjugate (bar D U) (toBar D b') ≤
      Subgroup.normalizer (bar D U : Set (Bar D)) := by
    rw [← bar_rightConjugate U b']
    exact bar_le_normalizer hUbN hUH
  have hbarS : bar D d.S ≤ bar D (d.S ⊔ U) ⊓ bar D A :=
    le_inf (bar_mono D le_sup_left) (bar_mono D d.sylowS.le)
  obtain ⟨m, K, -, hK, hKcomm, hKgen⟩ := bar_factor_components hC.hyp a
  have hT2 : ∀ t ∈ bar D U, t ^ 2 = 1 := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := (mem_bar_iff D U t).mp ht
    rw [← map_pow]
    have hu2 : u ^ 2 = 1 := Subtype.ext (by simpa using hUel.2 _ hu)
    rw [hu2, map_one]
  rcases hin.lemma_4_6 (Bar D) (bar D A) (bar D U) (bar D (d.S ⊔ U)) _ _ (toBar D b') hSF h43
      hT1 hO hg hWC hN with h1 | h2 | h3
  ·
    have hel : IsElemAbelian 2 (bar D U) := isElemAbelian_map_subgroupOf hUel (toBar D)
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hcardT : Nat.card (bar D U) = 2 ^ k := by rw [card_bar_of_isPGroup hU2 hUH, hk]
    have := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hel hcardT
    omega
  ·
    rw [hWC] at h2
    have hWeq : bar D U ⊔ rightConjugate (bar D U) (toBar D b') =
        bar D (U ⊔ rightConjugate U b) := by
      rw [bar_sup hUH hUbH, bar_rightConjugate U b']
    have hWab' : ∀ x ∈ bar D U ⊔ rightConjugate (bar D U) (toBar D b'),
        ∀ y ∈ bar D U ⊔ rightConjugate (bar D U) (toBar D b'), x * y = y * x := by
      rw [hWeq]
      intro x hx y hy
      obtain ⟨k, hk, rfl⟩ := (mem_bar_iff D _ x).mp hx
      obtain ⟨k', hk', rfl⟩ := (mem_bar_iff D _ y).mp hy
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h1 := congrArg Subtype.val (hcomm.is_comm.comm ⟨(k : G), hk⟩ ⟨(k' : G), hk'⟩)
      simpa using h1
    have hcentA := centralizes_of_normal (fun l => (hK l).1) hKcomm hKgen hSF.toFrame hWab'
      le_sup_left (le_sup_left.trans h2)
    exact hSH (le_of_bar_centralizes hC d hUZ hU1 fun t ht s hs =>
      hcentA t ht s (hbarS hs).2)
  ·
    obtain ⟨n, hdec, -, hcommEB, hel, -, hB⟩ := h3
    have hcentS := centralizes_sylow_of_bender (fun l => (hK l).1) hKcomm hKgen hSF hT2 hdec
      hcommEB hel hB
    exact hSH (le_of_bar_centralizes hC d hUZ hU1 fun t ht s hs => hcentS t ht s (hbarS hs))

theorem lemma613L1_holds : Lemma613L1 := by
  intro hin hloc G _ _ D r Abar hC a d _ _ hW _ _ hTab hWab _ _ heq hVZ _ _ P hP hWP hPH hPT
    hPnot hwclL _
  obtain ⟨d'', hg'', hT'', hS''⟩ := exists_swap_datum hloc hC d hW hP hWP hPH
  obtain ⟨hU'', hW''⟩ := swap_datum_facts d d'' hg'' hT'' hS'' hPT
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  have hV'' : AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G)) = rightConjugate U d.g⁻¹ := by
    rw [hW'', omegaOne_rightConjugate]
  have hT''ab : IsMulCommutative d''.T := by
    rw [hT'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hWab _
  have hW''ab : IsMulCommutative (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G) : Subgroup G) := by
    rw [hW'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hTab _
  have hcard'' : Nat.card (AschbacherTheorem3.omegaOne d''.T) =
      Nat.card (AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
        (rightConjugate A d''.g : Set G))) := by
    rw [hU'', hV'', rightConjugate_card, rightConjugate_card]
    exact heq.symm
  have hUZ'' : AschbacherTheorem3.omegaOne d''.T ≤ rightConjugate (zStar D Abar) d''.g := by
    rw [hU'', hg'']
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate
      (hVZ.trans (factorZStar_le_zStar hC.hyp a)) _
  have hSH'' : ¬ d''.S ≤ rightConjugate H d''.g := by
    rw [hS'', hg'']
    intro h
    apply hPnot
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate h d.g
    rwa [rightConjugate_inv_rightConjugate, rightConjugate_inv_rightConjugate] at h1
  refine false_of_wcl_zStar hin hloc hC d'' hT''ab hW''ab hcard'' hUZ'' hSH'' fun c hc hle => ?_
  obtain ⟨hz, hconj, hiff⟩ := swap_conj_mem d d'' hU'' hS'' hc
  rw [hconj, hV'', hU'', ← rightConjugate_sup, sup_comm]
  exact AschbacherTheorem3.rightConjugate_le_rightConjugate (hwclL _ hz (hiff.mp hle)) _

end DeltaGlobal

theorem theorem_6_4 (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hC : Counterexample G D r Abar) :
    deltaConjugates (Subgroup.normalizer (D : Set G)) = ∅ :=
  theorem_6_4_of_L1 hin hloc DeltaGlobal.lemma613L1_holds hC

end CFSG.ComponentClassification.AschbacherTheorem5
