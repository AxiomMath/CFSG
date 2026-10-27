module

public import CFSG.LieType.Ree.FixedBruhatDecomposition
public import CFSG.LieType.Ree.FixedPositiveBlocks
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem reeFixedTorus_le_normalizer_reeFixedNegUnipotent :
    t.reeFixedTorus K a ≤
      Subgroup.normalizer (t.reeFixedNegUnipotent K a : Set (ModGL t.tag K)) := fun _ hh =>
  Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨torusGroup_le_normalizer_negUnipotent (Subgroup.mem_inf.1 hh).1,
      Subgroup.le_normalizer (Subgroup.mem_inf.1 hh).2⟩)

theorem reeFixedBorel_eq_sup :
    t.reeFixedBorel K a = t.reeFixedTorus K a ⊔ t.reeFixedPosUnipotent K a := by
  refine le_antisymm (fun b hb => ?_)
    (sup_le reeFixedTorus_le_reeFixedBorel reeFixedPosUnipotent_le_reeFixedBorel)
  have hb' : b ∈ (t.reeFixedBorel K a : Set (ModGL t.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)

theorem reeFixedOrbitUnipotent_le_reeFixedPosUnipotent
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedOrbitUnipotent K a j ≤ t.reeFixedPosUnipotent K a :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent fun _ h => fixedOrbitRoots_subset j h)

theorem reeFixedBorel_inf_reeFixedNegUnipotent :
    t.reeFixedBorel K a ⊓ t.reeFixedNegUnipotent K a = ⊥ := by
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  obtain ⟨-, -, -, hinf⟩ := opposite_Borel_intersection t.tag K w₀ hmax
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxB, hxU⟩ := Subgroup.mem_inf.1 hx
  rw [← hinf]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxB).1, (Subgroup.mem_inf.1 hxU).1⟩

section Longest

variable {w₀ : WeylGroup t.tag}
  (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
include hw₀

theorem canonicalRep_longest_mem_reeFixedMonomial :
    canonicalRep (coxeterSystem t.tag) K w₀ ∈ t.reeFixedMonomial K a :=
  canonicalRep_mem_reeFixedMonomial t K a (longest_mem_relWeylRee hw₀)

theorem map_conj_reeFixedPosUnipotent :
    (t.reeFixedPosUnipotent K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedNegUnipotent K a := by
  have hn := (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  have hU := (canonical_weyl_root_transport t.tag K).1 w₀ {α | IsRoot t.tag α ∧ 0 < height α}
    fun α hα => hα.1
  rw [image_smul_posRoots_of_reversesSigns (reversesSigns_of_forall_length_le hw₀)] at hU
  rw [reeFixedPosUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective]
  change (posUnipotent t.tag K).map _ ⊓ _ = negUnipotent t.tag K ⊓ _
  rw [posUnipotent, hU, map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rfl

theorem map_conj_reeFixedTorus :
    (t.reeFixedTorus K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedTorus K a :=
  map_conj_eq_of_mem_normalizer (Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨(canonical_weyl_root_transport t.tag K).2.2 w₀,
      Subgroup.le_normalizer (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩))

theorem map_conj_reeFixedBorel :
    (t.reeFixedBorel K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a := by
  rw [reeFixedBorel_eq_sup, Subgroup.map_sup, map_conj_reeFixedTorus hw₀,
    map_conj_reeFixedPosUnipotent hw₀]

theorem reeFixedBorel_inf_map_conj :
    t.reeFixedBorel K a ⊓ (t.reeFixedBorel K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedTorus K a := by
  obtain ⟨-, hmap, hinf, -⟩ := opposite_Borel_intersection t.tag K w₀ hw₀
  have hH : t.reeFixedTorus K a ≤ (t.reeFixedBorel K a).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← map_conj_reeFixedTorus (K := K) (a := a) hw₀]
    exact Subgroup.map_mono reeFixedTorus_le_reeFixedBorel
  refine le_antisymm (fun x hx => ?_) (le_inf reeFixedTorus_le_reeFixedBorel hH)
  obtain ⟨hxB, hxB'⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxB₀, hxΓ⟩ := Subgroup.mem_inf.1 hxB
  have hxB'' : x ∈ (borelGroup t.tag K).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom :=
    Subgroup.map_mono (fun b hb => (Subgroup.mem_inf.1 hb).1) hxB'
  rw [hmap] at hxB''
  have hxH : x ∈ torusGroup t.tag K := by
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨hxB₀, hxB''⟩
  exact Subgroup.mem_inf.2 ⟨hxH, hxΓ⟩

end Longest

theorem coe_reeFixedTorus_sup_reeFixedNegUnipotent :
    ((t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) =
      (t.reeFixedTorus K a : Set (ModGL t.tag K)) *
        (t.reeFixedNegUnipotent K a : Set (ModGL t.tag K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    reeFixedTorus_le_normalizer_reeFixedNegUnipotent

theorem exists_ne_one_mem_reeFixedOrbitUnipotent
    (j : Fin t.fixedOrbitCount) :
    ∃ u ∈ t.reeFixedOrbitUnipotent K a j, u ≠ 1 := by
  cases t with
  | G2 =>
    fin_cases j
    exact ⟨_, (g2_fixedBlock K a).1, (g2_fixedBlock K a).2⟩
  | F4 =>
    fin_cases j
    · exact ⟨_, (f4_fixedBlock_one K a).1, (f4_fixedBlock_one K a).2⟩
    · exact ⟨_, (f4_fixedBlock_two K a).1, (f4_fixedBlock_two K a).2⟩

theorem eq_one_of_conj_reeFixedOrbitUnipotent_le
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (h : ∀ j, ∀ u ∈ t.reeFixedOrbitUnipotent K a j,
      canonicalRep (coxeterSystem t.tag) K w * u * (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
        t.reeFixedBorel K a) : w = 1 := by
  by_contra h1
  obtain ⟨j, hj⟩ := exists_fixedOrbitRoots_neg hw h1
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
  obtain ⟨hS, hΓ⟩ := Subgroup.mem_inf.1 hu
  have hmap := (canonical_weyl_root_transport t.tag K).1 w (t.fixedOrbitRoots j)
    fun α hα => (mem_fixedOrbitRoots_iff.1 hα).1
  have hS' : canonicalRep (coxeterSystem t.tag) K w * u *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
        rootSpan t.tag K ((fun α => w • α) '' t.fixedOrbitRoots j) := by
    rw [← hmap]
    exact ⟨u, hS, rfl⟩
  have hn : canonicalRep (coxeterSystem t.tag) K w ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a hw).2
  have hU : canonicalRep (coxeterSystem t.tag) K w * u *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ t.reeFixedNegUnipotent K a := by
    refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hS', mul_mem (mul_mem hn hΓ) (inv_mem hn)⟩
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul (mem_fixedOrbitRoots_iff.1 hα).1 w, hj α hα⟩
  have h₁ : canonicalRep (coxeterSystem t.tag) K w * u *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
        t.reeFixedBorel K a ⊓ t.reeFixedNegUnipotent K a := Subgroup.mem_inf.2 ⟨h j u hu, hU⟩
  rw [reeFixedBorel_inf_reeFixedNegUnipotent, Subgroup.mem_bot, mul_inv_eq_one,
    mul_eq_left] at h₁
  exact hu1 h₁

theorem mem_reeFixedBorel_of_conj
    {g : ModGL t.tag K} (hg : g ∈ t.reeGamma K a)
    (H : ∀ b ∈ t.reeFixedBorel K a, ∀ b' ∈ t.reeFixedBorel K a, ∀ w ∈ t.relWeylRee,
      b * canonicalRep (coxeterSystem t.tag) K w * b' = g → ∀ j,
        ∀ u ∈ t.reeFixedOrbitUnipotent K a j,
          canonicalRep (coxeterSystem t.tag) K w * u *
            (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ t.reeFixedBorel K a) :
    g ∈ t.reeFixedBorel K a := by
  have hg' : g ∈ (t.reeGamma K a : Set (ModGL t.tag K)) := hg
  rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hgw
  have h1 := eq_one_of_conj_reeFixedOrbitUnipotent_le hw (H b hb b' hb' w hw rfl)
  subst h1
  rw [canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem reeGamma_inf_normalizer_reeFixedPosUnipotent :
    t.reeGamma K a ⊓
        Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) =
      t.reeFixedBorel K a := by
  have hBN : t.reeFixedBorel K a ≤
      Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer reeFixedPosUnipotent_le_reeFixedBorel).1
      reeFixedPosUnipotent_subgroupOf_normal
  refine le_antisymm (fun g hg => ?_) (le_inf reeFixedBorel_le_reeGamma hBN)
  obtain ⟨hgΓ, hgN⟩ := Subgroup.mem_inf.1 hg
  refine mem_reeFixedBorel_of_conj hgΓ fun b hb b' hb' w _ hgw j u hu => ?_
  have hn : canonicalRep (coxeterSystem t.tag) K w = b⁻¹ * g * b'⁻¹ := by
    rw [← hgw]
    group
  have hnN : canonicalRep (coxeterSystem t.tag) K w ∈
      Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) := by
    rw [hn]
    exact mul_mem (mul_mem (inv_mem (hBN hb)) hgN) (inv_mem (hBN hb'))
  exact reeFixedPosUnipotent_le_reeFixedBorel ((Subgroup.mem_normalizer_iff.1 hnN _).1
    (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j hu))

theorem reeGamma_inf_normalizer_reeFixedBorel :
    t.reeGamma K a ⊓ Subgroup.normalizer (t.reeFixedBorel K a : Set (ModGL t.tag K)) =
      t.reeFixedBorel K a := by
  refine le_antisymm (fun g hg => ?_) (le_inf reeFixedBorel_le_reeGamma Subgroup.le_normalizer)
  obtain ⟨hgΓ, hgN⟩ := Subgroup.mem_inf.1 hg
  refine mem_reeFixedBorel_of_conj hgΓ fun b hb b' hb' w _ hgw j u hu => ?_
  have hn : canonicalRep (coxeterSystem t.tag) K w = b⁻¹ * g * b'⁻¹ := by
    rw [← hgw]
    group
  have hnN : canonicalRep (coxeterSystem t.tag) K w ∈
      Subgroup.normalizer (t.reeFixedBorel K a : Set (ModGL t.tag K)) := by
    rw [hn]
    exact mul_mem (mul_mem (inv_mem (Subgroup.le_normalizer hb)) hgN)
      (inv_mem (Subgroup.le_normalizer hb'))
  exact (Subgroup.mem_normalizer_iff.1 hnN _).1 (reeFixedPosUnipotent_le_reeFixedBorel
    (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j hu))

theorem ree_Borel_self_normalizers
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (w₀ : WeylGroup t.tag)
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    canonicalRep (coxeterSystem t.tag) K w₀ ∈ t.reeFixedMonomial K a ∧
    (t.reeFixedBorel K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a ∧
    ((t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) =
      (t.reeFixedTorus K a : Set (ModGL t.tag K)) *
        (t.reeFixedNegUnipotent K a : Set (ModGL t.tag K)) ∧
    t.reeFixedBorel K a ⊓ (t.reeFixedBorel K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedTorus K a ∧
    t.reeFixedBorel K a ⊓ t.reeFixedNegUnipotent K a = ⊥ ∧
    t.reeGamma K a ⊓
        Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) =
      t.reeFixedBorel K a ∧
    t.reeGamma K a ⊓ Subgroup.normalizer (t.reeFixedBorel K a : Set (ModGL t.tag K)) =
      t.reeFixedBorel K a :=
  ⟨canonicalRep_longest_mem_reeFixedMonomial hw₀, map_conj_reeFixedBorel hw₀,
    coe_reeFixedTorus_sup_reeFixedNegUnipotent, reeFixedBorel_inf_map_conj hw₀,
    reeFixedBorel_inf_reeFixedNegUnipotent, reeGamma_inf_normalizer_reeFixedPosUnipotent,
    reeGamma_inf_normalizer_reeFixedBorel⟩

end ReeTag

end CFSG.LieType.Ree
