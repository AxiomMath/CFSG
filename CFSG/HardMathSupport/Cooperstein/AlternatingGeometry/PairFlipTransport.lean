module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KleinEightPoints
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.MatchingEquiv
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairPreserving

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm PairFlip

section Transport

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

@[expose] def blkPsi (e : Ω ≃ ι × Bool) : Perm (ι × Bool) ≃* Perm Ω := e.permCongrHom.symm

theorem blkPsi_apply (e : Ω ≃ ι × Bool) (w : Perm (ι × Bool)) (x : Ω) :
    blkPsi e w x = e.symm (w (e x)) := rfl

theorem blkPsi_swap (e : Ω ≃ ι × Bool) (a b : ι × Bool) :
    blkPsi e (swap a b) = swap (e.symm a) (e.symm b) := by
  apply Equiv.ext
  intro x
  rw [blkPsi_apply, swap_apply_def, swap_apply_def]
  by_cases h1 : e x = a
  · have : x = e.symm a := by rw [← h1]; simp
    subst this
    simp
  · by_cases h2 : e x = b
    · have : x = e.symm b := by rw [← h2]; simp
      subst this
      have hne : e.symm b ≠ e.symm a := fun h => h1 (by simpa using e.symm.injective h)
      simp [hne]
    · have hx1 : x ≠ e.symm a := fun h => h1 (by rw [h]; simp)
      have hx2 : x ≠ e.symm b := fun h => h2 (by rw [h]; simp)
      simp [h1, h2, hx1, hx2]

theorem card_filter_fst (e : Ω ≃ ι × Bool) (T : Finset ι) :
    (Finset.univ.filter fun x : Ω => (e x).1 ∈ T).card = 2 * T.card := by
  classical
  rw [← Finset.card_map e.toEmbedding]
  have : (Finset.univ.filter fun x : Ω => (e x).1 ∈ T).map e.toEmbedding =
      T ×ˢ (Finset.univ : Finset Bool) := by
    ext z
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_toEmbedding,
      Finset.mem_product, and_true]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hz; exact ⟨e.symm z, by simpa using hz, by simp⟩
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]

theorem mem_normalizer_blkPsi (e : Ω ≃ ι × Bool) (W : Subgroup (Perm Ω)) (g : Perm (ι × Bool)) :
    blkPsi e g ∈ Subgroup.normalizer (W : Set (Perm Ω)) ↔
      g ∈ Subgroup.normalizer ((W.comap (blkPsi e).toMonoidHom : Subgroup (Perm (ι × Bool))) :
        Set (Perm (ι × Bool))) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h w
    have := h (blkPsi e w)
    simpa using this
  · intro h w
    obtain ⟨w', rfl⟩ := (blkPsi e).surjective w
    have := h w'
    simpa using this

open scoped Classical in
theorem exists_normal_two_group_of_matching (hΩ : 8 < Fintype.card Ω) (σ : Perm Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (W : Subgroup (Perm Ω))
    (hle : W ≤ pairPres σ hσ1 hσ2)
    (hD : ∀ x y, y ≠ x → y ≠ σ x → swap x (σ x) ∉ W → swap y (σ y) ∉ W →
      swap x (σ x) * swap y (σ y) ∈ W)
    (hN1 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∉ W).card ≠ 2 * 1)
    (h8 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∉ W).card = 2 * 4 ∨
      (Finset.univ.filter fun x : Ω => swap x (σ x) ∈ W).card = 2 * 4) :
    ∃ (U : Subgroup (Perm Ω)) (Δ : Finset Ω), IsPGroup 2 U ∧
      U ≤ Subgroup.normalizer (W : Set (Perm Ω)) ∧
      (∀ h ∈ Subgroup.normalizer (W : Set (Perm Ω)), ∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧
      (∀ u ∈ U, sign u = 1) ∧ 5 ≤ Δ.card ∧ (∃ k, k ∉ Δ) ∧
      (∀ u ∈ U, ∀ i, i ∉ Δ → u i = i) ∧ (∀ i ∈ Δ, ∀ j ∈ Δ, ∃ u ∈ U, u i = j) := by
  obtain ⟨ι, _, _, e, hcard, hσe⟩ := exists_blockEquiv σ hσ1 hσ2
  let W' : Subgroup (Perm (ι × Bool)) := W.comap (blkPsi e).toMonoidHom
  have hW' : ∀ w, w ∈ W' ↔ blkPsi e w ∈ W := fun w => Iff.rfl
  have heσ' : ∀ z : ι × Bool, e.symm (z.1, !z.2) = σ (e.symm z) := by
    intro z
    apply e.injective
    rw [Equiv.apply_symm_apply, hσe, Equiv.apply_symm_apply]
  have hψtp : ∀ i, blkPsi e (tp i) = swap (e.symm (i, true)) (σ (e.symm (i, true))) := by
    intro i
    have : tp i = swap (i, true) (i, false) := rfl
    rw [this, blkPsi_swap]
    have h := heσ' (i, true)
    simp only [Bool.not_true] at h
    rw [h]
  have hmemtp : ∀ x, swap x (σ x) ∈ W ↔ tp (e x).1 ∈ W' := by
    intro x
    rw [hW', hψtp]
    have : swap (e.symm ((e x).1, true)) (σ (e.symm ((e x).1, true))) = swap x (σ x) := by
      rcases hb : (e x).2 with _ | _
      · have h1 : e.symm ((e x).1, true) = σ x := by
          have := heσ' (e x)
          rw [Equiv.symm_apply_apply, hb] at this
          simpa using this
        rw [h1, hσ2, swap_comm]
      · have h1 : e.symm ((e x).1, true) = x := by
          have : e x = ((e x).1, true) := Prod.ext rfl hb
          rw [← this]; simp
        rw [h1]
    rw [this]
  have hle' : W' ≤ J0 ι := by
    intro w hw
    refine mem_J0.2 fun z => ?_
    have h : blkPsi e w (e.symm z) = e.symm z ∨ blkPsi e w (e.symm z) = σ (e.symm z) :=
      mem_pairPres.1 (hle hw) (e.symm z)
    rw [blkPsi_apply, Equiv.apply_symm_apply] at h
    rcases h with h | h
    · left; exact e.symm.injective h
    · right
      apply e.symm.injective
      rw [h, heσ']
  have hD' : ∀ i j, i ≠ j → tp i ∉ W' → tp j ∉ W' → tp i * tp j ∈ W' := by
    intro i j hij hi hj
    have hxi : swap (e.symm (i, true)) (σ (e.symm (i, true))) ∉ W := by
      have := hmemtp (e.symm (i, true))
      rw [Equiv.apply_symm_apply] at this
      exact fun h => hi (this.1 h)
    have hxj : swap (e.symm (j, true)) (σ (e.symm (j, true))) ∉ W := by
      have := hmemtp (e.symm (j, true))
      rw [Equiv.apply_symm_apply] at this
      exact fun h => hj (this.1 h)
    have hne1 : e.symm (j, true) ≠ e.symm (i, true) := fun h => hij (by
      have := e.symm.injective h
      exact (congrArg Prod.fst this).symm)
    have hne2 : e.symm (j, true) ≠ σ (e.symm (i, true)) := by
      rw [← heσ']
      intro h
      exact hij (by
        have := e.symm.injective h
        exact (congrArg Prod.fst this).symm)
    have := hD _ _ hne1 hne2 hxi hxj
    rw [hW', map_mul, hψtp, hψtp]
    exact this
  have hout : (Finset.univ.filter fun x : Ω => swap x (σ x) ∉ W) =
      Finset.univ.filter fun x : Ω => (e x).1 ∈ outSet W' := by
    ext x; simp [hmemtp x, mem_outSet]
  have hin : (Finset.univ.filter fun x : Ω => swap x (σ x) ∈ W) =
      Finset.univ.filter fun x : Ω => (e x).1 ∈ (outSet W')ᶜ := by
    ext x; simp [hmemtp x, mem_outSet]
  rw [hout, card_filter_fst] at hN1
  have hT1 : (outSet W').card ≠ 1 := fun h => hN1 (by rw [h])
  have h8' : (outSet W').card = 4 ∨ (outSet W')ᶜ.card = 4 := by
    rcases h8 with h | h
    · rw [hout, card_filter_fst] at h; left; omega
    · rw [hin, card_filter_fst] at h; right; omega
  have hι : 5 ≤ Fintype.card ι := by omega
  obtain ⟨B, hB, hBT⟩ : ∃ B : Finset ι, ∃ _ : B.card = 4, B = outSet W' ∨ B = (outSet W')ᶜ := by
    rcases h8' with h | h
    · exact ⟨outSet W', h, Or.inl rfl⟩
    · exact ⟨(outSet W')ᶜ, h, Or.inr rfl⟩
  have hnorm : ∀ g : Perm (ι × Bool), blkPsi e g ∈ Subgroup.normalizer (W : Set (Perm Ω)) ↔
      g ∈ Subgroup.normalizer (W' : Set (Perm (ι × Bool))) := mem_normalizer_blkPsi e W
  refine ⟨(KleinEight.U B hB).map (blkPsi e).toMonoidHom,
    Finset.univ.filter fun x : Ω => (e x).1 ∈ B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (KleinEight.isPGroup_U B hB).map _
  · rintro _ ⟨u', hu', rfl⟩
    exact (hnorm u').2 (KleinEight.U_le_normalizer hle' hD' hB hBT hu')
  · rintro h hh _ ⟨u', hu', rfl⟩
    obtain ⟨h', rfl⟩ := (blkPsi e).surjective h
    have := KleinEight.conj_mem_U hle' hD' hT1 hB hBT ((hnorm h').1 hh) hu'
    exact ⟨h' * u' * h'⁻¹, this, by simp⟩
  · rintro _ ⟨u', hu', rfl⟩
    show sign (blkPsi e u') = 1
    have : sign (blkPsi e u') = sign u' := Equiv.Perm.sign_permCongr e.symm u'
    rw [this]
    exact KleinEight.U_sign B hB hu'
  · rw [card_filter_fst, hB]; omega
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ B := by
      by_contra h
      push Not at h
      have : B = Finset.univ := Finset.eq_univ_of_forall h
      rw [this, Finset.card_univ] at hB
      omega
    exact ⟨e.symm (i, true), by simpa using hi⟩
  · rintro _ ⟨u', hu', rfl⟩ i hi
    have hi' : (e i).1 ∉ B := by simpa using hi
    show blkPsi e u' i = i
    rw [blkPsi_apply, KleinEight.U_fix B hB hu' hi', Equiv.symm_apply_apply]
  · intro i hi j hj
    have hi' : (e i).1 ∈ B := by simpa using hi
    have hj' : (e j).1 ∈ B := by simpa using hj
    obtain ⟨u', hu', h⟩ := KleinEight.U_transitive B hB hi' hj'
    exact ⟨blkPsi e u', ⟨u', hu', rfl⟩, by rw [blkPsi_apply, h, Equiv.symm_apply_apply]⟩

end Transport

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
