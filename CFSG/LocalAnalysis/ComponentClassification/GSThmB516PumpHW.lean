module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerHW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma57HW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Sylow

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Hyp59W

variable {H : Type} [Group H] [Finite H] (h : Hyp59W H)

theorem exists_pumpUp_component (hS : SchreierFor Blueprint.Catalog) (hPump : CF516PumpUp)
    (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) (hBc : IsCyclic h.B) {b : H}
    (hbB : b ∈ h.B) (hb2 : orderOf b = 2) (habK : h.a * b ∈ h.K)
    (hXne : centralizer ({b} : Set H) ≠ ⊤) :
    ∃ L : Subgroup H, h.K ≤ L ∧ L ≤ h.K ⊔ oddCoreIn (centralizer ({b} : Set H)) ∧
      L ≤ centralizer ({b} : Set H) ∧
        IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer ({b} : Set H) with hXdef
  obtain ⟨-, p, f, hp, hp2, hf, hJlie, hKtype⟩ :=
    CatFactsL4U4HW.inner_structure h.toHyp52W hrow hin
  obtain ⟨-, -, -, -, -, -, hKa, -⟩ := hrow
  obtain ⟨⟨β, hβB⟩, hgen⟩ := hBc.exists_generator
  have hBz : h.B = zpowers β := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr hβB)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
    exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hBX : h.B ≤ X := fun x hx =>
    mem_centralizer_singleton_iff.mpr (commute_of_mem_isCyclic hBc hx hbB)
  have hbX : b ∈ X := hBX hbB
  have hβX : β ∈ X := hBX hβB
  have haX : h.a ∈ X :=
    mem_centralizer_singleton_iff.mpr (h.toHyp52W.comm_a (h.toHyp52W.B_le_S hbB)).symm
  have hCB : centralizer (h.B : Set H) = centralizer ({β} : Set H) := by
    rw [hBz, centralizer_zpowers_eq]
  have hCβX : centralizer ({β} : Set H) ≤ X := by
    rw [← hCB]
    exact centralizer_le (Set.singleton_subset_iff.mpr hbB)
  have hKCB : h.K ≤ centralizer (h.B : Set H) :=
    h.toHyp52W.K_le_layer_W.trans h.toHyp52W.V_le_centralizer_B
  have hKCβ : h.K ≤ centralizer ({β} : Set H) := hCB ▸ hKCB
  have hKX : h.K ≤ X := hKCβ.trans hCβX
  have hKβ : IsPComponent 2 (h.K.subgroupOf (centralizer ({β} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKCβ
      (hCB ▸ centralizer_le_normalizer _) h.isPComponent_K.2
  have hJq := B5aHW.isQuasisimple_J h.toHyp52W
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hb2g : IsPGroup 2 (zpowers b) := isPGroup_zpowers_of_sq_eq_one (by rw [pow_two, hbb])
  have hbJ : zpowers b ≤ coreActionKernel h.J := (zpowers_le.mpr hbB).trans hBJ
  have hbCa : zpowers b ≤ centralizer ({h.a} : Set H) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (h.toHyp52W.comm_a
      (h.toHyp52W.B_le_S hbB)))
  obtain ⟨-, -, hJs, -, -⟩ := id h.isPComponent_J
  set Jb := GSLit.fixedLayer h.J (zpowers b) with hJbdef
  set JB := GSLit.fixedLayer h.J h.B with hJBdef
  have hJb : IsPComponent 2 (Jb.subgroupOf (centralizer ({h.a} : Set H) ⊓ X)) := by
    have h1 := GSLit.fixedLayer_isPComponent h.J_le hJs hbCa hbJ hb2g hJq
    rwa [centralizer_zpowers_eq] at h1
  have hJbJ : Jb ≤ h.J := (GSLit.fixedLayer_le_inf _ _).trans inf_le_left
  have hJbC : Jb ≤ centralizer ({h.a} : Set H) ⊓ X := by
    refine le_inf (hJbJ.trans h.J_le) ?_
    have h1 := (GSLit.fixedLayer_le_inf h.J (zpowers b)).trans inf_le_right
    rwa [centralizer_zpowers_eq] at h1
  obtain ⟨hJBJb, hJbsup⟩ := GSLit.fixedLayer_nested hJq hBJ h.toHyp52W.isPGroup_B
    (zpowers_le.mpr hbB)
  have hJBK : JB ≤ h.K := CatFactsL4U4HW.fixedLayer_le_K h.toHyp52W hKa
  have hJBp : ⁅JB, JB⁆ = JB := Subgroup.isPerfect_iff.mp
    (B5a.isPerfect_of_isPComponent_subgroupOf
      ((GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_inf_right _ h.J_le))
      (B5aHW.isPComponent_fixedLayer h.toHyp52W))
  have hJB1 : JB ≠ ⊥ := B5aHW.fixedLayer_ne_bot h.toHyp52W
  have hXK : SectionRank.IsKGroupCat X := isKGroupCat_of_ne_top' h.kProper hXne
  have hXS := schreierSections_of_isKGroupCat hS hXK
  set a' : X := ⟨h.a, haX⟩ with ha'
  set b' : X := ⟨b, hbX⟩ with hb'
  set β' : X := ⟨β, hβX⟩ with hβ'
  have hβ2 : ∃ n : ℕ, β' ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := h.toHyp52W.isPGroup_B ⟨β, hβB⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  have ha2 : a' * a' = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]; rfl)
  have hbZ : b' ∈ center X := mem_center_iff.mpr fun y => Subtype.ext
    (mem_centralizer_singleton_iff.mp y.2)
  have hKC' : h.K.subgroupOf X ≤ centralizer ({β'} : Set X) := by
    rw [← Pump516.centralizer_subgroupOf_eq hβX]
    exact fun x hx => hKCβ hx
  have hK' : IsPComponent 2 ((h.K.subgroupOf X).subgroupOf (centralizer ({β'} : Set X))) := by
    rw [← Pump516.centralizer_subgroupOf_eq hβX]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hCβX 2 Nat.prime_two).mpr hKβ
  have hCaX : (centralizer ({h.a} : Set H) ⊓ X).subgroupOf X =
      centralizer ({a'} : Set X) := by
    rw [← Pump516.centralizer_subgroupOf_eq haX]
    ext x
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, and_true]
  have hJC' : Jb.subgroupOf X ≤ centralizer ({a'} : Set X) := by
    rw [← hCaX]
    exact fun x hx => hJbC hx
  have hJ' : IsPComponent 2 ((Jb.subgroupOf X).subgroupOf (centralizer ({a'} : Set X))) := by
    rw [← hCaX]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two).mpr hJb
  have habK' : a' * b' ∈ h.K.subgroupOf X := habK
  have hab2 : orderOf (a' * b') = 2 := by
    rw [← Subgroup.orderOf_coe]
    refine orderOf_eq_prime ?_ fun h1 => h.toHyp52W.a_not_mem_B ?_
    · show (h.a * b) ^ 2 = 1
      rw [pow_two, show h.a * b * (h.a * b) = h.a * h.a * (b * b) by
        rw [mul_assoc, mul_assoc, ← mul_assoc b h.a b,
          (h.toHyp52W.comm_a (h.toHyp52W.B_le_S hbB)), mul_assoc, ← mul_assoc]]
      rw [← pow_two h.a, ← h.orderOf_a, pow_orderOf_eq_one, hbb, mul_one]
    · have h2 : h.a * b = 1 := h1
      rw [show h.a = b by rw [← mul_one h.a, ← hbb, ← mul_assoc, h2, one_mul]]
      exact hbB
  have hJBX : JB ≤ X := hJBK.trans hKX
  have hJbX : Jb ≤ X := hJbC.trans inf_le_right
  have hJBK' : JB.subgroupOf X ≤ h.K.subgroupOf X := fun x hx => hJBK hx
  have hJBJ' : JB.subgroupOf X ≤ Jb.subgroupOf X := fun x hx => hJBJb hx
  have hJBp' : ⁅JB.subgroupOf X, JB.subgroupOf X⁆ = JB.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJBX, hJBp]
  have hJB1' : JB.subgroupOf X ≠ ⊥ := by
    intro hbot
    apply hJB1
    rw [← map_subgroupOf_eq_of_le hJBX, hbot, Subgroup.map_bot]
  have hJsup' : Jb.subgroupOf X ≤ JB.subgroupOf X ⊔ oddCoreIn (Jb.subgroupOf X) := by
    rw [← map_le_map_iff_of_injective X.subtype_injective, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hJbX, map_subgroupOf_eq_of_le hJBX, oddCoreIn,
      pPrimeCore_map_subgroupOf 2 Jb X hJbX]
    exact hJbsup.ge
  have hβJb : β ∈ coreActionKernel Jb := by
    have hβJ := hBJ hβB
    have hβN : β ∈ normalizer (Jb : Set H) := GSLit.mem_normalizer_fixedLayer
      (mem_coreActionKernel.mp hβJ).1 (centralizer_le_normalizer _ (by
        rw [centralizer_zpowers_eq]
        exact mem_centralizer_singleton_iff.mpr (commute_of_mem_isCyclic hBc hβB hbB)))
    refine mem_coreActionKernel.mpr ⟨hβN, fun j hj => ?_⟩
    rw [(GSLit.fixedLayer_sup_pPrimeCore hJq hbJ hb2g).2]
    refine mem_inf.mpr ⟨?_, (mem_coreActionKernel.mp hβJ).2 j (hJbJ hj)⟩
    have h1 : β⁻¹ * j * β ∈ Jb := by
      have := (mem_normalizer_iff.mp (inv_mem hβN) j).mp hj
      rwa [inv_inv] at this
    rw [show j⁻¹ * β⁻¹ * j * β = j⁻¹ * (β⁻¹ * j * β) by group]
    exact mul_mem (inv_mem hj) h1
  have hβJ' : β' ∈ coreActionKernel (Jb.subgroupOf X) := by
    refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      rw [mem_subgroupOf, mem_subgroupOf]
      exact mem_normalizer_iff.mp (mem_coreActionKernel.mp hβJb).1 y
    · rw [← mem_map_iff_mem X.subtype_injective, pPrimeCore_map_subgroupOf 2 Jb X hJbX]
      exact (mem_coreActionKernel.mp hβJb).2 j hj
  have eK : ↥(h.K.subgroupOf X) ⧸ pPrimeCore 2 ↥(h.K.subgroupOf X) ≃* OddBar h.K :=
    UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hKX)
  have hKt : (p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
        Fintype.card F = p ^ f ∧ Nonempty (↥(h.K.subgroupOf X) ⧸ pPrimeCore 2
          ↥(h.K.subgroupOf X) ≃* StatedProj (StatedSL 4 F))) ∨
      (p ^ f % 4 = 1 ∧ ∃ (F : Type) (_ : Field F), UnitaryFieldData p f F ∧
        Nonempty (↥(h.K.subgroupOf X) ⧸ pPrimeCore 2 ↥(h.K.subgroupOf X) ≃*
          StatedProj (StatedSU 4 (p ^ f) F))) := by
    rcases hKtype with ⟨h4, F, i1, i2, hF, ⟨e⟩⟩ | ⟨h4, F, i1, hF, ⟨e⟩⟩
    · exact Or.inl ⟨h4, F, i1, i2, hF, ⟨eK.trans e⟩⟩
    · exact Or.inr ⟨h4, F, i1, hF, ⟨eK.trans e⟩⟩
  have hJt : Blueprint.LieModel (↥(Jb.subgroupOf X) ⧸ pPrimeCore 2 ↥(Jb.subgroupOf X))
      .PSL 2 p (2 * f) := by
    obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hJbJ
      (GSLit.fixedLayer_sup_pPrimeCore hJq hbJ hb2g).1
    exact OddQuot.lieModel_of_equiv
      (((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
        (subgroupOfEquivOfLe hJbX)).trans e).symm) hJlie
  have hAt : ∀ L₀ : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent L₀ →
      QuotientGroup.mk' (pPrimeCore 2 X) β' ∈ normalizer (L₀ : Set (X ⧸ pPrimeCore 2 X)) →
        CF516PumpUpAt (X ⧸ pPrimeCore 2 X) L₀ (QuotientGroup.mk' (pPrimeCore 2 X) β') := by
    intro L₀ hL₀ hN
    obtain ⟨n, hn⟩ := hβ2
    exact hPump _ (hXK.quotient _) L₀ hL₀ _ ⟨n, by rw [← map_pow, hn, map_one]⟩ hN
  obtain ⟨L', hL', hKL', hL'K⟩ := Pump516.exists_pComponent_of_pumpUp hXS hAt hβ2 ha2 hbZ
    hKC' hK' hJC' hJ' habK' hab2 hJBK' hJBJ' hJBp' hJB1' hJsup' hβJ' hp hp2 hf hKt hJt
  refine ⟨L'.map X.subtype, fun k hk => ⟨⟨k, hKX hk⟩, hKL' hk, rfl⟩, ?_, map_subtype_le _, ?_⟩
  · refine (map_mono hL'K).trans ?_
    rw [Subgroup.map_sup, subgroupOf_map_subtype]
    exact sup_le_sup_right inf_le_left _
  · rwa [show (L'.map X.subtype).subgroupOf X = L' from
      comap_map_eq_self_of_injective X.subtype_injective L']

end Hyp59W

theorem row516CentralizerStatementHW_of_pumpUp (hS : SchreierFor Blueprint.Catalog)
    (hPump : CF516PumpUp) : Row516CentralizerStatementHW :=
  fun _ _ _ h hrow hin hBc _ hbB hb2 habK hXne =>
    h.exists_pumpUp_component hS hPump hrow hin hBc hbB hb2 habK hXne

end CFSG.ComponentClassification.GSThmB
