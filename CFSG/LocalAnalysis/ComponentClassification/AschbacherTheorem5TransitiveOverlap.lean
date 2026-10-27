module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveStrong
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveApply
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveComponents

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped MatrixGroups

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem isSylowOf_ne_bot_of_even {P Y : Subgroup G} (hP : IsSylowOf 2 P Y)
    (heven : Even (Nat.card Y)) : P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have h1 := hP.card_eq
  rw [hbot, Subgroup.card_bot] at h1
  have hf : (Nat.card Y).factorization 2 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne'
      (even_iff_two_dvd.mp heven)).ne'
  have := Nat.one_lt_two_pow hf
  omega

theorem exists_nontrivial_overlap (hC : Counterexample G D r Abar) (hin : SectionSixInputs)
    {Q : Subgroup G} {k j : Fin r} (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q)
    (hQj : Q ≤ centralizing D (Abar j))
    (hHQ : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    ∃ g ∉ Subgroup.normalizer (D : Set G), ∃ T : Subgroup G,
      IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (D : Set G)) ∧ T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hN, htight⟩ := tightlyEmbedded_of_le_centralizing hC hkQ hQj hHQ
  by_contra hcon
  push Not at hcon
  have hodd : OddNormalizerOverlaps Q := by
    intro g hg
    rw [hN] at hg ⊢
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 (rightConjugate Q g ⊓ Subgroup.normalizer (D : Set G))
    exact isSylowOf_ne_bot_of_even hT heven (hcon g hg T hT)
  rcases hin.theorem_2_part_two Q htight hodd with hnormal | hSE
  · apply hC.proper
    rw [← hN]
    exact Subgroup.normalizer_eq_top_iff.mpr hnormal
  · exact not_stronglyEmbedded hC hin hkQ hQj hSE

@[expose] def Thm3AltOne {X : Type} [Group X] (Q T S : Subgroup X) : Prop :=
  IsCyclic T ∧
    (IsCyclic (S ⊓ Q : Subgroup X) ∨ AschbacherTheorem3.IsQuaternionTwoGroup (S ⊓ Q) ∨
      AschbacherTheorem3.IsDihedralTwoGroup (S ⊓ Q)) ∧
    (AschbacherTheorem3.IsDihedralTwoGroup S ∨ AschbacherTheorem3.IsSemidihedralTwoGroup S ∨
      AschbacherTheorem3.IsWreathedTwoGroup S)

@[expose] def Thm3AltThree {X : Type} [Group X] (Q T : Subgroup X) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧
    AschbacherTheorem3.oTwoPrime (Q ⊔ T) =
      pCoreOf 2 (Q ⊔ T) ⊔ AschbacherTheorem3.oTwoPrime Q ∧
    pCoreOf 2 (Q ⊔ T) ⊓ AschbacherTheorem3.oTwoPrime Q = ⊥ ∧
    ⁅pCoreOf 2 (Q ⊔ T), AschbacherTheorem3.oTwoPrime Q⁆ = ⊥ ∧
    IsElemAbelian 2 (pCoreOf 2 (Q ⊔ T)) ∧ Nat.card (pCoreOf 2 (Q ⊔ T)) = 2 ^ n ∧
    Nonempty (AschbacherTheorem3.oTwoPrime Q ≃* PSL(2, GaloisField 2 n))

theorem overlap_alternatives (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) {Q : Subgroup G} {k j : Fin r}
    (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q) (hQj : Q ≤ centralizing D (Abar j))
    (hHQ : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G)) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (D : Set G))) (hT1 : T ≠ ⊥) :
    ∃ S : Subgroup G, IsSylowOf 2 S (Q ⊔ T) ∧ T ≤ S ∧ T ⊓ Q = ⊥ ∧
      Nat.card (S ⊓ Subgroup.normalizer (T : Set G) ⊓ Q : Subgroup G) = Nat.card T ∧
      S ⊓ Subgroup.normalizer (T : Set G) ⊓ Q ≤
        rightConjugate (Subgroup.normalizer (D : Set G)) g ∧
      (Thm3AltOne (bar D Q) (bar D T) (bar D S) ∨ Thm3AltThree (bar D Q) (bar D T)) := by
  obtain ⟨S, hS, hTS, hbot, hcard, hle, hconc⟩ := exists_thm3_of_overlap hC h3 hkQ hQj hHQ hg hT hT1
  obtain ⟨m, K, -, hK, -, hKgen⟩ := bar_factor_components hC.hyp k
  have hTH : T ≤ Subgroup.normalizer (D : Set G) := hT.le.trans inf_le_right
  have hTnc : ∃ l, ⁅K l, bar D T⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have hcentr : bar D T ≤
        Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar k)) : Set (Bar D)) := by
      rw [Subgroup.le_centralizer_iff, ← hKgen]
      exact iSup_le fun l => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall l)
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    have htk : aschbacherThm5Centralizes (aschbacherThm5Core D)
        (aschbacherThm5Preimage D (Abar k)) (t : G) :=
      (centralizes_iff_mem_centralizer D _ (preimage_le D _) ⟨t, hTH t.2⟩).mpr
        (hcentr (toBar_mem_bar D t.2))
    have hgt : g * t * g⁻¹ ∈ Q := (mem_rightConjugate_iff Q g t).mp (hT.le t.2).1
    obtain ⟨e, he⟩ := hT.isPGroup t
    apply hg
    refine mem_normalizer_of_fusion hC j k (t := g * t * g⁻¹) (g := g) ⟨e, ?_⟩ ?_
      (centralizes_of_mem_centralizing (hQj hgt)) ?_
    · rw [conj_pow, show ((t : G) ^ 2 ^ e) = 1 from congrArg Subtype.val he]
      group
    · intro h1
      apply ht1
      apply Subtype.ext
      calc (t : G) = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · rwa [show g⁻¹ * (g * (t : G) * g⁻¹) * g = t by group]
  obtain ⟨l, hl⟩ := hTnc
  refine ⟨S, hS, hTS, hbot, hcard, hle, ?_⟩
  exact thm3_one_or_three (isPGroup_bar hT.isPGroup) (bar_mono D hTS) (isPGroup_bar hS.isPGroup)
    (hK l).1 ((hK l).2.trans (bar_mono D hkQ)) hl hconc

omit [Finite G] in
theorem bar_iSup {ι : Sort*} {Y : ι → Subgroup G}
    (hY : ∀ i, Y i ≤ Subgroup.normalizer (D : Set G)) :
    bar D (⨆ i, Y i) = ⨆ i, bar D (Y i) := by
  have hsub : (⨆ i, Y i).subgroupOf (Subgroup.normalizer (D : Set G)) =
      ⨆ i, (Y i).subgroupOf (Subgroup.normalizer (D : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (D : Set G)).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_iSup, inf_eq_left.mpr (iSup_le hY)]
    congr 1
    ext i : 1
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hY i)]
  rw [bar, hsub, Subgroup.map_iSup]
  rfl

theorem components_commute {X : Type} [Group X] [Finite X] {L M : Subgroup X}
    (hL : IsComponentOf L ⊤) (hM : IsComponentOf M ⊤) (hne : L ≠ M) :
    ∀ x ∈ L, ∀ y ∈ M, x * y = y * x := by
  have h := AschbacherComponentAction.layer_full_central_product.2.1 L M hL hM hne
  intro x hx y hy
  have hmem := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem orbit_singleton (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs) {I : Set (Fin r)}
    (hI : IsInvariant D Abar I) {k j : Fin r} (hk : k ∈ I) (hj : j ∉ I) :
    I = {k} ∧ CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar k))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := orbitProduct D Abar I with hQdef
  have hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q := factor_le_orbitProduct hk
  have hQj : Q ≤ centralizing D (Abar j) := orbitProduct_le_centralizing hC.hyp.hcomm hj
  have hHQ := normalizer_le_normalizer_orbitProduct hC.hyp.hperm hI
  have hQH : Q ≤ Subgroup.normalizer (D : Set G) :=
    (orbitProduct_le_D I).trans Subgroup.le_normalizer
  obtain ⟨g, hg, T, hT, hT1⟩ := exists_nontrivial_overlap hC hin hkQ hQj hHQ
  obtain ⟨S, hS, -, -, -, -, halt⟩ := overlap_alternatives hC h3 hkQ hQj hHQ hg hT hT1
  have hTH : T ≤ Subgroup.normalizer (D : Set G) := hT.le.trans inf_le_right
  let ι := {L : Subgroup (Bar D) // IsComponentOf L ⊤ ∧ L ≤ bar D Q}
  have hcomm : ∀ i i' : ι, i ≠ i' → ∀ x ∈ i.val, ∀ y ∈ i'.val, x * y = y * x :=
    fun i i' hii' => components_commute i.2.1 i'.2.1 (fun h => hii' (Subtype.ext h))
  have hfactor : ∀ k' ∈ I, ∃ (m : ℕ) (K : Fin m → ι), 0 < m ∧
      ⨆ l, (K l).val = bar D (aschbacherThm5Preimage D (Abar k')) := by
    intro k' hk'
    obtain ⟨m, K, hm, hK, -, hKgen⟩ := bar_factor_components hC.hyp k'
    exact ⟨m, fun l => ⟨K l, (hK l).1, (hK l).2.trans (bar_mono D (factor_le_orbitProduct hk'))⟩,
      hm, hKgen⟩
  have hbarQ : bar D Q = ⨆ k', ⨆ (_ : k' ∈ I), bar D (aschbacherThm5Preimage D (Abar k')) := by
    rw [hQdef, orbitProduct, bar_iSup (fun k' => iSup_le fun _ =>
      (preimage_le D _).trans Subgroup.le_normalizer)]
    congr 1
    ext k' : 1
    rw [bar_iSup (fun _ => (preimage_le D _).trans Subgroup.le_normalizer)]
  have hQgen : ⨆ i : ι, i.val = bar D Q := by
    apply le_antisymm (iSup_le fun i => i.2.2)
    calc bar D Q = ⨆ k', ⨆ (_ : k' ∈ I), bar D (aschbacherThm5Preimage D (Abar k')) := hbarQ
      _ ≤ ⨆ i : ι, i.val := by
        refine iSup_le fun k' => iSup_le fun hk' => ?_
        obtain ⟨m, K, -, hKgen⟩ := hfactor k' hk'
        rw [← hKgen]
        exact iSup_le fun l => le_iSup (fun i : ι => i.val) (K l)
  have hsub : ∀ i i' : ι, i = i' := by
    rcases halt with ⟨-, hSQ, -⟩ | ⟨n, hn, -, -, -, -, -, ⟨e⟩⟩
    · have hSbar : IsSylowOf 2 (bar D S) (bar D Q ⊔ bar D T) := by
        rw [← bar_sup hQH hTH]
        exact isSylowOf_bar hS (sup_le hQH hTH)
      have hR := hSbar.inf_of_le_normalizer (N := bar D Q) le_sup_left
        (sup_le Subgroup.le_normalizer (bar_le_normalizer (hTH.trans hHQ) hQH))
      exact components_subsingleton_of_sylow (fun i : ι => i.val) (fun i => i.2.1)
        (fun i => i.2.2) hcomm hR (by tauto)
    · have : IsSimpleGroup PSL(2, GaloisField 2 n) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [GaloisField.card 2 n (by omega)]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
      have hsimple : IsSimpleGroup (AschbacherTheorem3.oTwoPrime (bar D Q)) := e.isSimpleGroup
      exact components_subsingleton_of_simple (fun i : ι => i.val) (fun i => i.2.1)
        (fun i => i.2.2) hcomm hQgen hsimple
  obtain ⟨m₀, K₀, hm₀, -⟩ := hfactor k hk
  set i₀ : ι := K₀ ⟨0, hm₀⟩
  have hbarA : ∀ k' ∈ I, bar D (aschbacherThm5Preimage D (Abar k')) = i₀.val := by
    intro k' hk'
    obtain ⟨m, K, hm, hKgen⟩ := hfactor k' hk'
    rw [← hKgen]
    have hK : ∀ l, (K l).val = i₀.val := fun l => congrArg Subtype.val (hsub (K l) i₀)
    simp only [hK]
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact iSup_const
  refine ⟨?_, ?_⟩
  · ext k'
    rw [Set.mem_singleton_iff]
    refine ⟨fun hk' => ?_, fun h => h ▸ hk⟩
    apply hC.hyp.hdistinct
    apply Subgroup.map_injective (quotientEmbedding_injective D)
    rw [map_quotientEmbedding, map_quotientEmbedding, hbarA k' hk', hbarA k hk]
  · rw [hbarA k hk]
    exact i₀.2.1.2.2

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
