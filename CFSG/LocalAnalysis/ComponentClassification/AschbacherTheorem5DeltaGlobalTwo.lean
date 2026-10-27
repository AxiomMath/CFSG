module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Preimages
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem eq_of_ne_of_ne (hr : r = 2) {i j k : Fin r} (hj : j ≠ i) (hk : k ≠ i) : j = k := by
  have hi := i.isLt
  have hj' := j.isLt
  have hk' := k.isLt
  have h1 : j.val ≠ i.val := fun h => hj (Fin.ext h)
  have h2 : k.val ≠ i.val := fun h => hk (Fin.ext h)
  exact Fin.ext (by omega)

theorem exists_conj_eq (hC : Counterexample G D r Abar) {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) (i : Fin r) :
    ∃ j, (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar j) :=
  hC.hyp.hperm h hh i

theorem factor_injective (hC : Counterexample G D r Abar) {i j : Fin r}
    (h : aschbacherThm5Preimage D (Abar i) = aschbacherThm5Preimage D (Abar j)) : i = j :=
  hC.hyp.hdistinct (preimage_injective D h)

theorem conj_other_eq (hC : Counterexample G D r Abar) (hr : r = 2) {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) {i j : Fin r} (hji : j ≠ i)
    (hn : h ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    (aschbacherThm5Preimage D (Abar j)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar i) := by
  obtain ⟨k, hk⟩ := exists_conj_eq hC hh i
  obtain ⟨l, hl⟩ := exists_conj_eq hC hh j
  have hki : k ≠ i := by
    rintro rfl
    exact hn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hk)
  have hlk : l ≠ k := by
    rintro rfl
    apply hji
    apply factor_injective hC
    have := hk.trans hl.symm
    exact (Subgroup.map_injective (MulAut.conj h).injective this).symm
  have hli : l = i := by
    by_contra hli
    exact hlk (eq_of_ne_of_ne hr hli hki)
  rw [hl, hli]

theorem mul_mem_normalizer (hC : Counterexample G D r Abar) (hr : r = 2) {i : Fin r}
    {h₁ h₂ : G} (hh₁ : h₁ ∈ Subgroup.normalizer (D : Set G))
    (hh₂ : h₂ ∈ Subgroup.normalizer (D : Set G))
    (hn₁ : h₁ ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (hn₂ : h₂ ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    h₁ * h₂ ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) := by
  obtain ⟨j, hk⟩ := exists_conj_eq hC hh₂ i
  have hji : j ≠ i := by
    rintro rfl
    exact hn₂ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hk)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hcomp : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj (h₁ * h₂)).toMonoidHom =
      ((aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h₂).toMonoidHom).map
        (MulAut.conj h₁).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hfin : ((aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h₂).toMonoidHom).map
      (MulAut.conj h₁).toMonoidHom = aschbacherThm5Preimage D (Abar i) := by
    rw [hk, conj_other_eq hC hr hh₁ hji hn₁]
  exact hcomp.trans hfin


theorem relIndex_normalizer_le_two (hC : Counterexample G D r Abar) (hr : r = 2) (i : Fin r)
    {X : Subgroup G} (hXH : X ≤ Subgroup.normalizer (D : Set G)) :
    (Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)).relIndex X ≤ 2 := by
  set N := Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)
  set K := N.subgroupOf X
  change K.index ≤ 2
  by_cases htop : K = ⊤
  · rw [htop, Subgroup.index_top]
    norm_num
  · obtain ⟨a, -, ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr htop)
    have h2 : K.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨a, fun b => ?_⟩
      have haN : (a : G) ∉ N := ha
      by_cases hb : b ∈ K
      · refine Or.inr ⟨hb, fun hba => haN ?_⟩
        have hmem : b⁻¹ * (b * a) ∈ K := K.mul_mem (K.inv_mem hb) hba
        rw [inv_mul_cancel_left] at hmem
        exact hmem
      · refine Or.inl ⟨?_, hb⟩
        have hbN : (b : G) ∉ N := hb
        exact mul_mem_normalizer hC hr (hXH b.2) (hXH a.2) hbN haN
    rw [h2]

theorem card_le_two_mul (hC : Counterexample G D r Abar) (hr : r = 2) (i : Fin r)
    {X : Subgroup G} (hXH : X ≤ Subgroup.normalizer (D : Set G)) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ Subgroup.normalizer
      (aschbacherThm5Preimage D (Abar i) : Set G) : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card
    (Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) X
  rw [inf_comm] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ (relIndex_normalizer_le_two hC hr i hXH)

theorem card_eq_two_mul (hC : Counterexample G D r Abar) (hr : r = 2) (i : Fin r)
    {X : Subgroup G} (hXH : X ≤ Subgroup.normalizer (D : Set G))
    (hXN : ¬ X ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    Nat.card X = 2 * Nat.card (X ⊓ Subgroup.normalizer
      (aschbacherThm5Preimage D (Abar i) : Set G) : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card
    (Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) X
  rw [inf_comm] at h1
  rw [← h1]
  congr 1
  have h1' := h1
  have hle := relIndex_normalizer_le_two hC hr i hXH
  have hne : (Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)).relIndex X ≠ 1 :=
    fun h => hXN (Subgroup.relIndex_eq_one.mp h)
  have hpos : (Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)).relIndex X ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1'
    exact (Nat.card_pos (α := X)).ne h1'
  omega

theorem sylow_card_le_two_mul (hC : Counterexample G D r Abar) (hr : r = 2) (i : Fin r)
    {X P Q : Subgroup G} (hXH : X ≤ Subgroup.normalizer (D : Set G)) (hP : IsSylowOf 2 P X)
    (hQ : IsSylowOf 2 Q (X ⊓ Subgroup.normalizer
      (aschbacherThm5Preimage D (Abar i) : Set G))) :
    Nat.card P ≤ 2 * Nat.card Q := by
  have h1 := card_le_two_mul hC hr i (hP.le.trans hXH)
  have h2 := AschbacherTheorem3.card_le_of_isSylowOf hQ hP.isPGroup.to_inf_left
    (inf_le_inf_right _ hP.le)
  omega


theorem mem_normalizer_of_mem_normalizer (hC : Counterexample G D r Abar) (hr : r = 2) {x : G}
    (hxH : x ∈ Subgroup.normalizer (D : Set G)) {i j : Fin r}
    (hx : x ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    x ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar j) : Set G) := by
  by_cases hji : j = i
  · rwa [hji]
  by_contra hxj
  have h1 := conj_other_eq hC hr hxH (Ne.symm hji) hxj
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  exact hji (factor_injective hC (h2.symm.trans h1)).symm

theorem conj_mem_inf_normalizer (hC : Counterexample G D r Abar) (hr : r = 2) (i : Fin r)
    {h x : G} (hh : h ∈ Subgroup.normalizer (D : Set G))
    (hx : x ∈ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    h * x * h⁻¹ ∈ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) := by
  set H := Subgroup.normalizer (D : Set G)
  refine ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), ?_⟩
  by_cases hhN : h ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hx.2) (Subgroup.inv_mem _ hhN)
  · have hhN' : h⁻¹ ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) :=
      fun h' => hhN (by simpa using Subgroup.inv_mem _ h')
    obtain ⟨k, hk⟩ := exists_conj_eq hC (H.inv_mem hh) i
    have hki : k ≠ i := by
      rintro rfl
      exact hhN' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hk)
    have hxk : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj x).toMonoidHom =
        aschbacherThm5Preimage D (Abar k) := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (mem_normalizer_of_mem_normalizer hC hr hx.1 (j := k) hx.2)
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hcomp : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj (h * x * h⁻¹)).toMonoidHom =
        (((aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h⁻¹).toMonoidHom).map
          (MulAut.conj x).toMonoidHom).map (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    have hfin : (((aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h⁻¹).toMonoidHom).map
          (MulAut.conj x).toMonoidHom).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar i) := by
      rw [hk, hxk, conj_other_eq hC hr hh hki hhN]
    exact hcomp.trans hfin

theorem le_normalizer_inf_normalizer (hC : Counterexample G D r Abar) (hr : r = 2) (i : Fin r) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer
      ((Subgroup.normalizer (D : Set G) ⊓
        Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_inf_normalizer hC hr i hh
  · intro hx
    have h1 := conj_mem_inf_normalizer hC hr i
      ((Subgroup.normalizer (D : Set G)).inv_mem hh) hx
    simpa [mul_assoc] using h1

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
