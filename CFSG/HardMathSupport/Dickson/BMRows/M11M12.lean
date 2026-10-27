module

public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Mathieu.M12
public import Certificates.Certificate17702
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence CFSG.Monster.AxisCount
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.Sporadic.Bridge

theorem nonempty_m12Presentation_mulEquiv :
    Nonempty (TauCeti.Sporadic.m12Presentation.Group ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Bridge.M12.finite_card_le
  exact ⟨MulEquiv.ofBijective CFSG.Sporadic.Bridge.M12.toNative
    (CFSG.Sporadic.Bridge.M12.toNative_surjective.bijective_of_nat_card_le
      (hcard.trans CFSG.Sporadic.Bridge.M12.le_card_native))⟩

theorem isSimpleGroup_m12Presentation :
    IsSimpleGroup TauCeti.Sporadic.m12Presentation.Group := by
  obtain ⟨e⟩ := nonempty_m12Presentation_mulEquiv
  have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  exact e.isSimpleGroup

theorem card_m12Presentation : Nat.card TauCeti.Sporadic.m12Presentation.Group = 95040 := by
  obtain ⟨e⟩ := nonempty_m12Presentation_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M12.finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M12.le_card_native
  have h3 := Nat.card_congr e.toEquiv
  omega

@[expose] noncomputable def m12KImg (i : ℕ) : Gmat := if i = 0 then gw m12aW else gw m12bW

section Words


theorem m12Check_parts :
    agreeAll m12Pairs = true ∧ EdgeNoncomm.moveCheck m12aW (aV ()) = true := by
  have h := Certificates.certificate17702
  rw [m12Check, Bool.and_eq_true] at h
  exact h

theorem m12_word_facts :
    gw m12biW * gw m12bW = 1 ∧
      gw m12biW * gw m12aW * gw m12biW * gw m12aW * gw m12biW * gw m12aW = 1 ∧
      gw m12aW * gw m12aW * gw m12aW * gw m12aW * gw m12aW = 1 ∧
      gw m12bW * gw m12bW * gw m12bW * gw m12bW * gw m12bW * gw m12bW = 1 ∧
      gw m12aW * gw m12bW * gw m12bW * gw m12aW * gw m12biW * gw m12aW * gw m12aW * gw m12bW *
        gw m12aW * gw m12aW * gw m12bW * gw m12bW = 1 ∧
      gw gen11W0 * gw m12aW = gw m12aW * gw gen11W0 ∧
      gw gen11W0 * gw m12bW = gw m12bW * gw gen11W0 := by
  have hp := agreeAll_sound m12Check_parts.1
  have p : ∀ i, (hi : i < m12Pairs.length) → gw (m12Pairs[i]).1 = gw (m12Pairs[i]).2 :=
    fun i hi => hp _ (List.getElem_mem hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [m12Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_nil,
      mul_assoc] using p 0 (by decide)
  · simpa only [m12Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_nil,
      mul_assoc] using p 1 (by decide)
  · simpa only [m12Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_nil,
      mul_assoc] using p 2 (by decide)
  · simpa only [m12Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_nil,
      mul_assoc] using p 3 (by decide)
  · simpa only [m12Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_nil,
      mul_assoc] using p 4 (by decide)
  · simpa only [m12Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_nil,
      mul_assoc] using p 5 (by decide)
  · simpa only [m12Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_nil,
      mul_assoc] using p 6 (by decide)

theorem m12a_ne_one : gw m12aW ≠ 1 :=
  gw_ne_one_of_moveCheck m12Check_parts.2

theorem m12KImg_relators :
    ∀ v ∈ TauCeti.Sporadic.m12Presentation.relatorLetters, wordProd m12KImg v = 1 := by
  obtain ⟨p0, p1, p2, p3, p4, -, -⟩ := m12_word_facts
  have hbi : gw m12biW = (gw m12bW)⁻¹ := eq_inv_of_mul_eq_one_left p0
  rw [hbi] at p1 p4
  rw [TauCeti.Sporadic.m12Presentation_relatorLetters]
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · simpa only [wordProd, m12KImg, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, one_ne_zero, ↓reduceIte, Bool.false_eq_true, mul_assoc] using p1
  · have e : wordProd m12KImg [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true),
        (1, true), (1, true), (1, true), (1, true), (1, true)] =
        (gw m12aW * gw m12aW * gw m12aW * gw m12aW * gw m12aW) *
          (gw m12bW * gw m12bW * gw m12bW * gw m12bW * gw m12bW * gw m12bW) := by
      simp only [wordProd, m12KImg, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, one_ne_zero, ↓reduceIte, mul_assoc]
    rw [e, p2, p3, one_mul]
  · simpa only [wordProd, m12KImg, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, one_ne_zero, ↓reduceIte, Bool.false_eq_true, mul_assoc] using p4

theorem m12KImg_mem_centralizer (i : ℕ) :
    m12KImg i ∈ Subgroup.centralizer ({gw gen11W0} : Set Gmat) := by
  obtain ⟨-, -, -, -, -, ha, hb⟩ := m12_word_facts
  rw [Subgroup.mem_centralizer_singleton_iff, m12KImg]
  split
  · exact ha.symm
  · exact hb.symm

end Words

section Hom


@[expose] noncomputable def m12KHom : TauCeti.Sporadic.m12Presentation.Group →* Gmat :=
  PresentedGroup.toGroup (lift_relator _ m12KImg m12KImg_relators)

theorem m12KHom_of (i : Fin TauCeti.Sporadic.m12Presentation.generatorCount) :
    m12KHom (PresentedGroup.of i) = m12KImg i.val :=
  PresentedGroup.toGroup.of (lift_relator _ m12KImg m12KImg_relators)

theorem m12KHom_injective : Function.Injective m12KHom := by
  have := isSimpleGroup_m12Presentation
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal m12KHom.ker with h | h
  · exact h
  · exfalso
    have hgen : 0 < TauCeti.Sporadic.m12Presentation.generatorCount := by
      rw [CFSG.Sporadic.Bridge.M12.generatorCount_eq]; norm_num
    have h0 : m12KHom (PresentedGroup.of ⟨0, hgen⟩) = 1 := by
      rw [← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top _
    rw [m12KHom_of] at h0
    exact m12a_ne_one h0

@[expose] noncomputable def m12K : Subgroup Gmat := m12KHom.range

theorem m12K_le_centralizer : m12K ≤ Subgroup.centralizer ({gw gen11W0} : Set Gmat) := by
  rw [m12K, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, m12KHom_of]
  exact m12KImg_mem_centralizer _

@[expose] noncomputable def m12KEquiv :
    m12K ≃* TauCeti.Sporadic.m12Presentation.Group :=
  (MonoidHom.ofInjective m12KHom_injective).symm

theorem nonempty_m12K_mulEquiv_native :
    Nonempty (m12K ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  obtain ⟨e⟩ := nonempty_m12Presentation_mulEquiv
  exact ⟨m12KEquiv.trans e⟩

theorem nonempty_m12K_mulEquiv :
    Nonempty (m12K ≃* (TauCeti.CFSGIndex.sporadic .M12).Group) := by
  obtain ⟨e⟩ := nonempty_m12K_mulEquiv_native
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  exact ⟨e.trans f⟩

theorem isSimpleGroup_m12K : IsSimpleGroup m12K := by
  have := isSimpleGroup_m12Presentation
  exact m12KEquiv.isSimpleGroup

theorem card_m12K : Nat.card m12K = 95040 := by
  rw [Nat.card_congr m12KEquiv.toEquiv]
  exact card_m12Presentation

end Hom

end CFSG.HardMathSupport.Dickson.BMRows.M11
