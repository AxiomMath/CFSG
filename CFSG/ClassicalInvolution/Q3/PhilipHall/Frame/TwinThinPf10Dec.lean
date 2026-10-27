module

public import CFSG.ClassicalInvolution.Q3.AE.Group

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem conj_ofVec (a : Wr n) (u : Fin n → ZMod 2) :
    a * ofVec u * a⁻¹ = ofVec (fun x => u (a.perm.symm x)) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · show (a.vec x + u (a.perm.symm x)) + a.vec (a.perm (a.perm.symm x)) = u (a.perm.symm x)
    rw [Equiv.apply_symm_apply]
    have := zmod_two_add_self (a.vec x)
    calc (a.vec x + u (a.perm.symm x)) + a.vec x
        = (a.vec x + a.vec x) + u (a.perm.symm x) := by ring
      _ = _ := by rw [this, zero_add]
  · show a.perm * 1 * a.perm⁻¹ = 1
    simp

theorem zOf_eq_ofVec (ι : Fin 4 ↪ Fin n) :
    zOf ι = ofVec (fun x => if x ∈ Set.range ι then 1 else 0) := by
  classical
  refine Wr.ext (funext fun x => zOf_vec_apply ι x) ?_
  show embedPerm ι (1 : Wr 4).perm = 1
  exact embedPerm_one ι

theorem conj_zOf (a : Wr n) (ι : Fin 4 ↪ Fin n) :
    a * zOf ι * a⁻¹ = zOf (ι.trans a.perm.toEmbedding) := by
  classical
  rw [zOf_eq_ofVec ι, conj_ofVec, zOf_eq_ofVec]
  congr 1
  funext x
  have : x ∈ Set.range (ι.trans a.perm.toEmbedding) ↔ a.perm.symm x ∈ Set.range ι := by
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, by simp⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by simp [hi]⟩
  simp only [this]

theorem perm_range_of_conj (hn8 : n ≠ 8) (ι : Fin 4 ↪ Fin n) (a : Wr n)
    (h : mkQ n (a * zOf ι * a⁻¹) = mkQ n (zOf ι)) :
    ∀ x, x ∈ Set.range ι ↔ a.perm x ∈ Set.range ι := by
  rw [conj_zOf] at h
  have hr : Set.range (ι.trans a.perm.toEmbedding) = Set.range ι := range_eq_of_mkQ_zOf_eq hn8 h
  intro x
  constructor
  · rintro ⟨i, rfl⟩
    rw [← hr]
    exact ⟨i, rfl⟩
  · intro hx
    rw [← hr] at hx
    obtain ⟨i, hi⟩ := hx
    have : ι i = x := a.perm.injective hi
    exact ⟨i, this⟩

theorem exists_decomp (ι : Fin 4 ↪ Fin n) (a : Wr n)
    (hp : ∀ x, x ∈ Set.range ι ↔ a.perm x ∈ Set.range ι) :
    ∃ (b : Wr 4) (c : Wr n), a = c * embed ι b ∧ SupportedOn c (Set.range ι)ᶜ := by
  classical
  let τ : Equiv.Perm (Set.range ι) := a.perm.subtypePerm fun x => (hp x).symm
  let bp : Equiv.Perm (Fin 4) := ι.toEquivRange.permCongr.symm τ
  have hbp : ∀ i, ι (bp i) = a.perm (ι i) := fun i => by
    have : bp i = ι.toEquivRange.symm (τ (ι.toEquivRange i)) := rfl
    rw [this]
    have h2 : ι (ι.toEquivRange.symm (τ (ι.toEquivRange i))) =
        ((τ (ι.toEquivRange i) : Set.range ι) : Fin n) := by
      have := ι.toEquivRange.apply_symm_apply (τ (ι.toEquivRange i))
      exact congrArg Subtype.val this
    rw [h2]
    rfl
  let b : Wr 4 := ⟨fun i => a.vec (ι i), bp⟩
  refine ⟨b, a * (embed ι b)⁻¹, by group, ?_⟩
  intro x hx
  have hx' : x ∈ Set.range ι := by simpa using hx
  obtain ⟨i, rfl⟩ := hx'
  have hsymm : a.perm.symm (ι i) = ι (bp.symm i) := by
    apply a.perm.injective
    rw [Equiv.apply_symm_apply, ← hbp, Equiv.apply_symm_apply]
  refine ⟨?_, ?_⟩
  · show a.vec (ι i) + (embed ι b).vec ((embed ι b).perm (a.perm.symm (ι i))) = 0
    rw [hsymm, embed_perm, embed_vec, embedPerm_apply, embedVec_apply]
    show a.vec (ι i) + a.vec (ι (bp (bp.symm i))) = 0
    rw [Equiv.apply_symm_apply]
    exact zmod_two_add_self _
  · show a.perm ((embedPerm ι bp)⁻¹ (ι i)) = ι i
    rw [Equiv.Perm.inv_def, embedPerm_symm_apply, ← hbp, Equiv.apply_symm_apply]

theorem conj_embed (ι : Fin 4 ↪ Fin n) {a : Wr n} {b : Wr 4} {c : Wr n}
    (ha : a = c * embed ι b) (hc : SupportedOn c (Set.range ι)ᶜ) (k : Wr 4) :
    a * embed ι k * a⁻¹ = embed ι (b * k * b⁻¹) := by
  have hcomm : ∀ k : Wr 4, c * embed ι k = embed ι k * c := fun k =>
    comm_of_disjoint hc (embed_supportedOn ι k) (by
      rw [Set.disjoint_left]; intro x hx hx'; exact hx hx')
  subst ha
  have e1 : embed ι b * embed ι k * (embed ι b)⁻¹ = embed ι (b * k * b⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  calc c * embed ι b * embed ι k * (c * embed ι b)⁻¹
      = c * (embed ι b * embed ι k * (embed ι b)⁻¹) * c⁻¹ := by group
    _ = c * embed ι (b * k * b⁻¹) * c⁻¹ := by rw [e1]
    _ = _ := by rw [mul_inv_eq_iff_eq_mul, hcomm]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
