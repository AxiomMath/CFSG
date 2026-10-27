module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LocalAnalysis.StandardType.GGJ4eComm
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcW1

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.HardMathSupport.Timmesfeld.Torality

private theorem exists_rootChar_ne_one_of_ne_zero {τ : Tag} {L : Type} [Field L] [Infinite L]
    {v : Fin τ.rank → ℤ} (hv : v ≠ 0) : ∃ t : Fin τ.rank → Lˣ, rootChar t v ≠ 1 := by
  by_contra h
  push Not at h
  refine hv (CFSG.HardMathSupport.C14W1.eq_of_rootChar_eq (K := L) fun t => ?_)
  rw [h t, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_zero]

theorem mem_torusGroup_of_forall_commute_rootDiagUnit
    {τ : Tag} {L : Type} [Field L] [Infinite L] {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hT : ∀ t : Fin τ.rank → Lˣ, Commute g (rootDiagUnit τ t)) :
    g ∈ torusGroup τ L := by
  classical
  have hgC : g ∈ familyCentralizer τ L (fun t : Fin τ.rank → Lˣ => t) := by
    rw [mem_familyCentralizer]
    refine ⟨hg, fun t => ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact (hT t).eq.symm
  obtain ⟨w, hw, m, hm, hgm⟩ := familyCentralizer_le_mul τ L (fun t => t) hgC
  have hker : familyKernel (fun t : Fin τ.rank → Lˣ => t) = ∅ := by
    ext α
    constructor
    · rintro ⟨hα, hall⟩
      obtain ⟨t, ht⟩ := exists_rootChar_ne_one_of_ne_zero (L := L) (τ := τ) hα.ne_zero
      exact absurd (hall t) ht
    · intro h
      exact absurd h (Set.notMem_empty α)
  have hfix : ∀ v : Fin τ.rank → ℤ, w • v = v := by
    intro v
    by_contra hne
    have hμ : w • v - v ≠ 0 := sub_ne_zero.2 hne
    obtain ⟨t, ht⟩ := exists_rootChar_ne_one_of_ne_zero (L := L) (τ := τ) hμ
    have h1 : rootChar t (w • v) = rootChar t v := hw t v
    have h2 : rootChar t v * rootChar t (w • v - v) = rootChar t v * 1 := by
      rw [mul_one, ← rootChar_add, add_sub_cancel]
      exact h1
    exact ht (mul_left_cancel h2)
  have hw1 : w = 1 :=
    FaithfulSMul.eq_of_smul_eq_smul fun v => by rw [one_smul]; exact hfix v
  have hge : g = m := by
    rw [hgm, hw1, canonicalRep_one, mul_one]
  have hbot : rootSpan τ L (∅ : Set (Fin τ.rank → ℤ)) = ⊥ :=
    le_bot_iff.1 (iSup₂_le fun α hα => absurd hα (Set.notMem_empty α))
  have hsub : familyGroup (K := L) (fun t : Fin τ.rank → Lˣ => t) ≤ torusGroup τ L := by
    rw [familyGroup, hker, hbot, sup_bot_eq]
  rw [hge]
  exact hsub hm

private theorem exists_rootDiagUnit_conj_inv
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {Q : ModGL τ L} (hQ : Q ∈ adjointGroup τ L)
    (hT : ∀ t : Fin τ.rank → Lˣ, Q * rootDiagUnit τ t * Q⁻¹ ∈ familyGroup (K := L) a)
    (i : ι) : ∃ b : Fin τ.rank → Lˣ, Q⁻¹ * rootDiagUnit τ (a i) * Q = rootDiagUnit τ b := by
  have hTC : torusGroup τ L ≤ adjointGroup τ L :=
    le_sup_left.trans ((triangular_borel_structure.{0, 0} τ L).2.2.2.2.2.2.2.2.2.2.2 L).1
  have hdC : rootDiagUnit τ (a i) ∈ adjointGroup τ L :=
    hTC (rootDiagUnit_mem_torusGroup (a i))
  have hgC : Q⁻¹ * rootDiagUnit τ (a i) * Q ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem hQ) hdC) hQ
  refine exists_rootDiagUnit_eq_of_mem_torusGroup
    (mem_torusGroup_of_forall_commute_rootDiagUnit hgC fun t => ?_)
  have hcent : rootDiagUnit τ (a i) * (Q * rootDiagUnit τ t * Q⁻¹) =
      (Q * rootDiagUnit τ t * Q⁻¹) * rootDiagUnit τ (a i) := by
    have h := (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer a (hT t))).2 i
    rwa [mul_inv_eq_iff_eq_mul] at h
  rw [Commute, SemiconjBy]
  calc Q⁻¹ * rootDiagUnit τ (a i) * Q * rootDiagUnit τ t =
      Q⁻¹ * (rootDiagUnit τ (a i) * (Q * rootDiagUnit τ t * Q⁻¹)) * Q := by group
    _ = Q⁻¹ * ((Q * rootDiagUnit τ t * Q⁻¹) * rootDiagUnit τ (a i)) * Q := by rw [hcent]
    _ = rootDiagUnit τ t * (Q⁻¹ * rootDiagUnit τ (a i) * Q) := by group

private theorem canonicalRep_mul_inv_mem_familyCentralizer
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {Q : ModGL τ L} (hQ : Q ∈ adjointGroup τ L)
    {b : ι → Fin τ.rank → Lˣ}
    (hb : ∀ i, Q⁻¹ * rootDiagUnit τ (a i) * Q = rootDiagUnit τ (b i))
    {w : WeylGroup τ}
    (hd : ∀ i, rootDiagUnit τ (a i) = canonicalRep (coxeterSystem τ) L w *
      rootDiagUnit τ (b i) * (canonicalRep (coxeterSystem τ) L w)⁻¹) :
    canonicalRep (coxeterSystem τ) L w * Q⁻¹ ∈ familyCentralizer τ L a := by
  rw [mem_familyCentralizer]
  refine ⟨mul_mem (canonicalRep_mem_adjointGroup _ L w) (inv_mem hQ), fun i => ?_⟩
  have hcomm : canonicalRep (coxeterSystem τ) L w * Q⁻¹ * rootDiagUnit τ (a i) =
      rootDiagUnit τ (a i) * (canonicalRep (coxeterSystem τ) L w * Q⁻¹) := by
    calc canonicalRep (coxeterSystem τ) L w * Q⁻¹ * rootDiagUnit τ (a i) =
        canonicalRep (coxeterSystem τ) L w * (Q⁻¹ * rootDiagUnit τ (a i) * Q) * Q⁻¹ := by
          group
      _ = canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ (b i) * Q⁻¹ := by rw [hb i]
      _ = (canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ (b i) *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) * canonicalRep (coxeterSystem τ) L w *
            Q⁻¹ := by group
      _ = rootDiagUnit τ (a i) * (canonicalRep (coxeterSystem τ) L w * Q⁻¹) := by
          rw [← hd i]; group
  rw [mul_inv_eq_iff_eq_mul]
  exact hcomm.symm

private theorem canonicalRep_mul_inv_mem_normalizer
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {Q : ModGL τ L} (hQ : Q ∈ adjointGroup τ L)
    {b : ι → Fin τ.rank → Lˣ}
    (hb : ∀ i, Q⁻¹ * rootDiagUnit τ (a i) * Q = rootDiagUnit τ (b i))
    {w : WeylGroup τ}
    (hd : ∀ i, rootDiagUnit τ (a i) = canonicalRep (coxeterSystem τ) L w *
      rootDiagUnit τ (b i) * (canonicalRep (coxeterSystem τ) L w)⁻¹) :
    canonicalRep (coxeterSystem τ) L w * Q⁻¹ ∈
      Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) := by
  obtain ⟨w', hw', m, hm, hR⟩ :=
    familyCentralizer_le_mul τ L a (canonicalRep_mul_inv_mem_familyCentralizer a hQ hb hd)
  rw [hR]
  exact mul_mem (Subgroup.le_normalizer hm) (canonicalRep_mem_normalizer_familyGroup hw')

private theorem smul_mem_familyKernel
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {Q : ModGL τ L} {b : ι → Fin τ.rank → Lˣ}
    {w : WeylGroup τ}
    (hd : ∀ i, rootDiagUnit τ (a i) = canonicalRep (coxeterSystem τ) L w *
      rootDiagUnit τ (b i) * (canonicalRep (coxeterSystem τ) L w)⁻¹)
    (hX : ∀ α ∈ familyKernel a, Q * pinnedX τ L α 1 * Q⁻¹ ∈ familyGroup (K := L) a)
    (hR : canonicalRep (coxeterSystem τ) L w * Q⁻¹ ∈
      Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)))
    {α : Fin τ.rank → ℤ} (hα : α ∈ familyKernel a) :
    w • α ∈ familyKernel a := by
  have hXd : Q * pinnedX τ L α 1 * Q⁻¹ ∈ familyGroup (K := L) a := hX α hα
  have hNX : canonicalRep (coxeterSystem τ) L w * pinnedX τ L α 1 *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ familyGroup (K := L) a := by
    have h := (Subgroup.mem_normalizer_iff.1 hR (Q * pinnedX τ L α 1 * Q⁻¹)).1 hXd
    rwa [show canonicalRep (coxeterSystem τ) L w * Q⁻¹ * (Q * pinnedX τ L α 1 * Q⁻¹) *
      (canonicalRep (coxeterSystem τ) L w * Q⁻¹)⁻¹ =
      canonicalRep (coxeterSystem τ) L w * pinnedX τ L α 1 *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ from by group] at h
  refine ⟨IsRoot.smul hα.1 w, fun i => ?_⟩
  have hcommM : Commute (rootDiagUnit τ (a i))
      (canonicalRep (coxeterSystem τ) L w * pinnedX τ L α 1 *
        (canonicalRep (coxeterSystem τ) L w)⁻¹) := by
    have h := (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer a hNX)).2 i
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [Commute, SemiconjBy]
    exact h
  have hcommX : Commute (rootDiagUnit τ (b i)) (pinnedX τ L α 1) := by
    have hcm := hcommM.eq
    have hbd : rootDiagUnit τ (b i) =
        (canonicalRep (coxeterSystem τ) L w)⁻¹ * rootDiagUnit τ (a i) *
          canonicalRep (coxeterSystem τ) L w := by
      rw [hd i]; group
    rw [Commute, SemiconjBy, hbd]
    calc (canonicalRep (coxeterSystem τ) L w)⁻¹ * rootDiagUnit τ (a i) *
          canonicalRep (coxeterSystem τ) L w * pinnedX τ L α 1 =
        (canonicalRep (coxeterSystem τ) L w)⁻¹ * (rootDiagUnit τ (a i) *
          (canonicalRep (coxeterSystem τ) L w * pinnedX τ L α 1 *
            (canonicalRep (coxeterSystem τ) L w)⁻¹)) *
          canonicalRep (coxeterSystem τ) L w := by group
      _ = (canonicalRep (coxeterSystem τ) L w)⁻¹ *
          ((canonicalRep (coxeterSystem τ) L w * pinnedX τ L α 1 *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) * rootDiagUnit τ (a i)) *
          canonicalRep (coxeterSystem τ) L w := by rw [hcm]
      _ = pinnedX τ L α 1 * ((canonicalRep (coxeterSystem τ) L w)⁻¹ *
          rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) L w) := by group
  exact ((rootDiagUnit_eq_conj_canonicalRep_iff (a i) (b i) w).1 (hd i) α).trans
    (rootChar_eq_one_of_commute_rootDiagUnit_pinnedX (b i) hα.1 hcommX)

theorem mem_normalizer_familyGroup_of_conj_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {Q : ModGL τ L} (hQ : Q ∈ adjointGroup τ L)
    (hT : ∀ t : Fin τ.rank → Lˣ, Q * rootDiagUnit τ t * Q⁻¹ ∈ familyGroup (K := L) a)
    (hX : ∀ α ∈ familyKernel a, Q * pinnedX τ L α 1 * Q⁻¹ ∈ familyGroup (K := L) a) :
    Q ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) := by
  classical
  choose b hb using fun i => exists_rootDiagUnit_conj_inv a hQ hT i
  obtain ⟨w, hwQ⟩ : ∃ w : WeylGroup τ, Q ∈ bruhatCell τ L w := by
    have h : Q ∈ (adjointGroup τ L : Set (ModGL τ L)) := hQ
    rw [(bruhat_decomposition τ L).1, Set.mem_iUnion] at h
    exact h
  have hd : ∀ i, rootDiagUnit τ (a i) =
      canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ (b i) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
    intro i
    refine rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell (a i) (b i) hwQ ?_
    rw [← hb i]
    group
  have hRnorm := canonicalRep_mul_inv_mem_normalizer a hQ hb hd
  have hfin : (familyKernel a).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1
  have hmap : Set.MapsTo (fun α => w • α) (familyKernel a) (familyKernel a) :=
    fun α hα => smul_mem_familyKernel a hd hX hRnorm hα
  have hinj : Set.InjOn (fun α => w • α) (familyKernel a) := by
    intro α _ β _ h
    have := congrArg (fun v => w⁻¹ • v) h
    simpa using this
  have himage : (fun α => w • α) '' familyKernel a = familyKernel a :=
    ((Set.Finite.injOn_iff_bijOn_of_mapsTo hfin hmap).1 hinj).image_eq
  have hQeq : Q = (canonicalRep (coxeterSystem τ) L w * Q⁻¹)⁻¹ *
      canonicalRep (coxeterSystem τ) L w := by
    group
  rw [hQeq]
  exact mul_mem (inv_mem hRnorm) (canonicalRep_mem_normalizer_of_image himage)

end CFSG.HardMathSupport.Timmesfeld.Torality
