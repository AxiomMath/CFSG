module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixFactor
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal

open SectionSix SectionSix.BarTools RankOne

namespace SixConj

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem isPGroup_of_quaternion {Q : Subgroup G} (hQ : AschbacherTheorem3.IsQuaternionTwoGroup Q) :
    IsPGroup 2 Q := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hQ
  have hcard : Nat.card Q = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  exact IsPGroup.of_card hcard

omit [Finite G] in
theorem bar_inf_centralizer_eq_bot {Y : Subgroup G} (i : Fin r)
    (hYf : ∀ y ∈ Y, y ≠ 1 → ¬ aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) y) :
    bar D Y ⊓ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar i)) : Set (Bar D)) =
      ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxY, hxC⟩
  obtain ⟨y, hyY, rfl⟩ := (mem_bar_iff D Y x).mp hxY
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hy1' : (y : G) ≠ 1 := fun h => hy1 (by rw [show y = 1 from Subtype.ext h, map_one])
  exact hYf _ hyY hy1' ((centralizes_iff_mem_centralizer D _ (preimage_le D _) y).mpr hxC)

theorem no_faithful_quaternion (hC : Counterexample G D r Abar) (hin : SectionSixInputs)
    {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {V : Subgroup G} (hV : V ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g)) (i : Fin r)
    (hr : CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) ≤ 1)
    {X E : Subgroup G} (hX : AschbacherTheorem3.IsQuaternionTwoGroup X)
    (hXH : X ≤ Subgroup.normalizer (D : Set G))
    (hXN : X ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (hXf : ∀ x ∈ X, x ≠ 1 → ¬ aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) x)
    (hEel : IsElemAbelian 2 E) (hE4 : Nat.card E = 4)
    (hEH : E ≤ Subgroup.normalizer (D : Set G))
    (hEN : E ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (hEf : ∀ e ∈ E, e ≠ 1 → ¬ aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) e)
    (hEX : E ≤ Subgroup.centralizer (X : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hLr := pRank_bar_le hAH hr
  have hLq := quasisimple_of_rank_one hC.hyp i hLr
  obtain ⟨hVH, hVel, hV4, -⟩ := id hV
  have hVb4 := isFourGroup_bar hVH hVel hV4
  have hVbL := bar_le_normalizer (lemma_6_5_one hC hg hV i) hAH
  obtain ⟨-, h3, -⟩ :=
    lemma_3_5_sub hin.knownGroups hLq hLr hVb4 hVbL (not_le_centralizerJoin hC hg hV i)
  have hX2 := isPGroup_of_quaternion hX
  refine h3 (bar D X) (bar D E) ?_ (bar_le_normalizer hXN hAH)
    (bar_inf_centralizer_eq_bot i hXf) (isFourGroup_bar hEH hEel hE4)
    (bar_le_normalizer hEN hAH) (bar_inf_centralizer_eq_bot i hEf) ?_
  · obtain ⟨n, hn, ⟨e⟩⟩ := hX
    exact ⟨n, hn, ⟨(barEquiv hX2 hXH).symm.trans e⟩⟩
  · intro y hy
    obtain ⟨e, he, rfl⟩ := (mem_bar_iff D E y).mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨x', hx', rfl⟩ := (mem_bar_iff D X x).mp hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hEX he)) _ hx')

omit [Finite G] in
theorem isElemAbelian_of_le {W E : Subgroup G} (hWE : W ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 W := CFSG.Open.IsElemAbelian.mono hE hWE

theorem no_elemAbelian_eight (hC : Counterexample G D r Abar) (hin : SectionSixInputs)
    {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {V : Subgroup G} (hV : V ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g)) (i : Fin r)
    (hr : CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) ≤ 1)
    {E : Subgroup G} (hEel : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hEH : E ≤ Subgroup.normalizer (D : Set G))
    (hEC : ∀ e ∈ E, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hW : ∀ W ≤ E, AschbacherKnownGroup.IsFourGroup W →
      W ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
        (rightConjugate (Subgroup.normalizer (D : Set G)) g) :=
    fun W hWE hW4 => ⟨hWE.trans hEH, hW4.1, hW4.2, fun w hw hw1 => hEC w (hWE hw) hw1⟩
  have hEN : E ≤ Subgroup.normalizer (A : Set G) := by
    intro e he
    obtain ⟨W, hWE, hW4, heW⟩ :=
      AschbacherKnownGroup.Lemma35.exists_fourGroup_of_mem hEel (by rw [hE8]; norm_num) he
    exact lemma_6_5_one hC hg (hW W hWE hW4) i heW
  have hLr := pRank_bar_le hAH hr
  have hLq := quasisimple_of_rank_one hC.hyp i hLr
  obtain ⟨hVH, hVel, hV4, -⟩ := id hV
  obtain ⟨-, -, h4⟩ := lemma_3_5_sub hin.knownGroups hLq hLr (isFourGroup_bar hVH hVel hV4)
    (bar_le_normalizer (lemma_6_5_one hC hg hV i) hAH) (not_le_centralizerJoin hC hg hV i)
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  have hEbel : IsElemAbelian 2 (bar D E) :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hEel _) (toBar D)
  have hEb8 : Nat.card (bar D E) = 8 := by rw [card_bar_of_isPGroup hE2 hEH, hE8]
  obtain ⟨Wb, hWbE, hWb4, hLW⟩ := h4 (bar D E) (bar_le_normalizer hEN hAH) hEbel hEb8
  have hWb2 : IsPGroup 2 Wb := IsPGroup.of_card (n := 2) (by rw [hWb4.2]; norm_num)
  obtain ⟨W, hWE, hW2, hWWb⟩ := lift_two_subgroup hEH hWb2 hWbE
  have hW4 : AschbacherKnownGroup.IsFourGroup W := ⟨isElemAbelian_of_le hWE hEel, by
    rw [← card_bar_of_isPGroup hW2 (hWE.trans hEH), hWWb, hWb4.2]⟩
  exact not_le_centralizerJoin hC hg (hW W hWE hW4) i (hWWb ▸ hLW)

end SixConj

end DeltaLocal

end CFSG.ComponentClassification.AschbacherTheorem5
