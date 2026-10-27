module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma35
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherKnownGroup

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal

variable {B : Type} [Group B]

theorem centralizerJoin_map_le (N : Subgroup B) (U L : Subgroup N) :
    (centralizerJoin U L).map N.subtype ≤
      centralizerJoin (U.map N.subtype) (L.map N.subtype) := by
  rw [centralizerJoin, Subgroup.map_iSup]
  refine iSup_le fun u => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hu => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hu1 => ?_
  have hu' : (u : B) ∈ U.map N.subtype := Subgroup.mem_map_of_mem _ hu
  have hu1' : (u : B) ≠ 1 := fun h => hu1 (Subtype.ext h)
  refine le_iSup_of_le (u : B) (le_iSup_of_le hu' (le_iSup_of_le hu1' ?_))
  rintro _ ⟨x, ⟨hxL, hxC⟩, rfl⟩
  refine ⟨Subgroup.mem_map_of_mem _ hxL, ?_⟩
  have hxC' : x ∈ Subgroup.centralizer ({u} : Set N) := hxC
  rw [Subgroup.mem_centralizer_singleton_iff] at hxC'
  change (x : B) ∈ Subgroup.centralizer ({(u : B)} : Set B)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val hxC'

theorem isElemAbelian_subgroupOf {E : Subgroup B} (hE : IsElemAbelian 2 E) (N : Subgroup B) :
    IsElemAbelian 2 (E.subgroupOf N) := CFSG.Open.IsElemAbelian.subgroupOf hE N

theorem map_subgroupOf {N V : Subgroup B} (hVN : V ≤ N) : (V.subgroupOf N).map N.subtype = V := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVN]

theorem card_subgroupOf_of_le {N V : Subgroup B} (hVN : V ≤ N) :
    Nat.card (V.subgroupOf N) = Nat.card V :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv

variable [Finite B]

theorem lemma_3_5_sub (hK : AschbacherKnownGroupFacts) {L U : Subgroup B}
    (hLq : CFSG.Open.IsQuasisimple L) (hr : CFSG.Open.pRank 2 L ≤ 1) (hU : IsFourGroup U)
    (hUL : U ≤ Subgroup.normalizer (L : Set B)) (hgen : ¬ L ≤ centralizerJoin U L) :
    U ≤ L ⊔ Subgroup.centralizer (L : Set B) ∧
    (∀ X E : Subgroup B, AschbacherTheorem3.IsQuaternionTwoGroup X →
      X ≤ Subgroup.normalizer (L : Set B) → X ⊓ Subgroup.centralizer (L : Set B) = ⊥ →
      IsFourGroup E → E ≤ Subgroup.normalizer (L : Set B) →
      E ⊓ Subgroup.centralizer (L : Set B) = ⊥ → E ≤ Subgroup.centralizer (X : Set B) →
      False) ∧
    (∀ V : Subgroup B, V ≤ Subgroup.normalizer (L : Set B) → IsElemAbelian 2 V →
      Nat.card V = 8 → ∃ W : Subgroup B, W ≤ V ∧ IsFourGroup W ∧ L ≤ centralizerJoin W L) := by
  set N := Subgroup.normalizer (L : Set B) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  set L' := L.subgroupOf N with hL'def
  set U' := U.subgroupOf N with hU'def
  have : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr le_rfl
  have hmapL : L'.map N.subtype = L := map_subgroupOf hLN
  have hmapU : U'.map N.subtype = U := map_subgroupOf hUL
  have hLq' : CFSG.Open.IsQuasisimple L' :=
    Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hLN) hLq
  have hr' : CFSG.Open.pRank 2 L' ≤ 1 := by
    have h := CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 2) N.subtype N.subtype_injective L'
    rw [hmapL] at h
    exact h.trans hr
  have hU' : IsFourGroup U' := ⟨isElemAbelian_subgroupOf hU.1 N, by
    rw [card_subgroupOf_of_le hUL, hU.2]⟩
  have hgen' : ¬ L' ≤ centralizerJoin U' L' := by
    intro h
    apply hgen
    have h1 := Subgroup.map_mono (f := N.subtype) h
    rw [hmapL] at h1
    refine h1.trans ((centralizerJoin_map_le N U' L').trans ?_)
    rw [hmapU, hmapL]
  obtain ⟨-, h2, h3, h4⟩ := lemma_3_5 hK L' U' hLq' hr' hU' hgen'
  have hCmap : (Subgroup.centralizer (L' : Set N)).map N.subtype ≤
      Subgroup.centralizer (L : Set B) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hc) ⟨l, hLN hl⟩ hl)
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Subgroup.map_mono (f := N.subtype) h2
    rw [hmapU, Subgroup.map_sup, hmapL] at h1
    exact h1.trans (sup_le_sup_left hCmap L)
  · intro X E hX hXN hXf hE hEN hEf hEX
    set C' := Subgroup.centralizer (L' : Set N) with hC'def
    set π := QuotientGroup.mk' C' with hπdef
    have hinj : ∀ {Y : Subgroup B}, Y ≤ N → Y ⊓ Subgroup.centralizer (L : Set B) = ⊥ →
        Function.Injective (π.comp (Y.subgroupOf N).subtype) := by
      intro Y hYN hYf
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      have hyC : ((y : N) : B) ∈ Subgroup.centralizer (L : Set B) := hCmap ⟨y, hy, rfl⟩
      have hmem : ((y : N) : B) ∈ Y ⊓ Subgroup.centralizer (L : Set B) := ⟨y.2, hyC⟩
      rw [hYf, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subtype.ext hmem)
    set X'' := (π.comp (X.subgroupOf N).subtype).range with hX''def
    set E'' := (π.comp (E.subgroupOf N).subtype).range with hE''def
    obtain ⟨n, hn, ⟨e⟩⟩ := hX
    have hX''e : X'' ≃* QuaternionGroup (2 ^ (n - 2)) :=
      ((MonoidHom.ofInjective (hinj hXN hXf)).symm.trans
        (Subgroup.subgroupOfEquivOfLe hXN)).trans e
    have hrank := h3 X'' (n - 2) (by omega) ⟨hX''e⟩
    have hE''C : E'' ≤ Subgroup.centralizer (X'' : Set (N ⧸ C')) := by
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_iff.mp (hEX y.2)) _ x.2)
    have hE''el : IsElemAbelian 2 E'' := by
      have h := CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hE.1 N) π
      have heq : (E.subgroupOf N).map π = E'' := by
        rw [hE''def, MonoidHom.range_comp, Subgroup.range_subtype]
      rwa [heq] at h
    have hE''card : Nat.card E'' = 2 ^ 2 := by
      rw [hE''def, ← Nat.card_congr (MonoidHom.ofInjective (hinj hEN hEf)).toEquiv,
        card_subgroupOf_of_le hEN, hE.2]
      norm_num
    have := CFSG.SectionRank.le_pRank (by norm_num) hE''C hE''el hE''card
    omega
  · intro V hVN hV hV8
    have h3V : 3 ≤ CFSG.Open.pRank 2 (V.subgroupOf N) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_subgroupOf hV N)
        (by rw [card_subgroupOf_of_le hVN, hV8]; norm_num)
    obtain ⟨W', hW'V, hW', hLW'⟩ := h4 (V.subgroupOf N) h3V
    refine ⟨W'.map N.subtype, ?_, ?_, ?_⟩
    · rw [← map_subgroupOf hVN]
      exact Subgroup.map_mono hW'V
    · refine ⟨CFSG.SectionRank.isElemAbelian_map hW'.1 N.subtype, ?_⟩
      rw [Subgroup.card_map_of_injective N.subtype_injective, hW'.2]
    · have h1 := Subgroup.map_mono (f := N.subtype) hLW'
      rw [hmapL] at h1
      exact h1.trans ((centralizerJoin_map_le N W' L').trans (le_of_eq (by rw [hmapL])))

end DeltaLocal

end CFSG.ComponentClassification.AschbacherTheorem5
