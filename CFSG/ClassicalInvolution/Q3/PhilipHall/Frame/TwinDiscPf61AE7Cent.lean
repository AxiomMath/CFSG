module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent6
public import CFSG.ClassicalInvolution.Q3.TL4D1MAMC
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Pair

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinDisc

namespace AE5

theorem card_outside_le (ι : Fin 4 ↪ Fin 7) (s : Finset (Fin 7))
    (hs : ∀ y ∈ s, y ∉ Set.range ι) : s.card ≤ 3 := by
  classical
  have h1 : s ⊆ (Finset.univ.image ι)ᶜ := by
    intro y hy
    rw [Finset.mem_compl, Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hs y hy ⟨i, hi⟩
  have h2 : (Finset.univ.image ι).card = 4 := by
    rw [Finset.card_image_of_injective _ ι.injective]
    simp
  have h3 := Finset.card_le_card h1
  rw [Finset.card_compl, h2, Fintype.card_fin] at h3
  omega

theorem exists_not_mem_range7 (ι : Fin 4 ↪ Fin 7) : ∃ p, p ∉ Set.range ι := by
  by_contra h
  push Not at h
  have hs : Function.Surjective ι := h
  have := Fintype.card_le_of_surjective ι hs
  simp at this

theorem pairVec_apply {n : ℕ} {p q : Fin n} (hpq : p ≠ q) (y : Fin n) :
    TL4.pairVec p q y = if y = p ∨ y = q then 1 else 0 := by
  by_cases h1 : y = p
  · subst h1
    simp [TL4.pairVec, Pi.single_apply, hpq.symm]
  · by_cases h2 : y = q
    · subst h2
      simp [TL4.pairVec, Pi.single_apply, h1]
    · simp [TL4.pairVec, Pi.single_apply, h1, h2]

theorem cent_sq7_aux {α : Finset (Fin 7)} (hα : α.card = 4) {x : AEQ 7}
    (ht : ∀ a ∈ kList, x * mkQ 7 (embed (emb α hα) a) = mkQ 7 (embed (emb α hα) a) * x)
    (hs : ∀ a ∈ kStarList, x * mkQ 7 (embed (emb α hα) a) = mkQ 7 (embed (emb α hα) a) * x)
    (hx4 : TL4.Mdl117.permQ 7 (x * x * (x * x)) = 1) :
    x * x = 1 ∨ ∃ p q : Fin 7, p ≠ q ∧ p ∉ α ∧ q ∉ α ∧
      x * x = TL4.vbar 7 (TL4.pairVec p q) := by
  classical
  set ι := emb α hα with hι
  have hrange : ∀ y, y ∈ Set.range ι ↔ y ∈ α := fun y => by
    rw [hι, range_emb]
    exact Iff.rfl
  obtain ⟨p₀, hp₀⟩ := exists_not_mem_range7 ι
  obtain ⟨w, rfl, hfix, hV, hpres⟩ := cent_core ι hp₀ ht hs
  have h4 : w.perm * w.perm * (w.perm * w.perm) = 1 := by
    have e : mkQ 7 w * mkQ 7 w * (mkQ 7 w * mkQ 7 w) = mkQ 7 (w * w * (w * w)) := by
      simp only [map_mul]
    rw [e, TL4.Mdl117.permQ_mkQ] at hx4
    simpa only [mul_perm] using hx4
  have hA : ∀ y, y ∉ Set.range ι → w.perm (w.perm y) = y := by
    intro y hy
    by_contra hne
    set σ := w.perm with hσ
    have h1 : σ y ∉ Set.range ι := hpres y hy
    have h2 : σ (σ y) ∉ Set.range ι := hpres _ h1
    have h3 : σ (σ (σ y)) ∉ Set.range ι := hpres _ h2
    have h4y : σ (σ (σ (σ y))) = y := by
      have := congrArg (fun f : Equiv.Perm (Fin 7) => f y) h4
      simpa [Equiv.Perm.mul_apply] using this
    have d01 : y ≠ σ y := fun h => hne ((congrArg σ h.symm).trans h.symm)
    have d02 : y ≠ σ (σ y) := fun h => hne h.symm
    have d03 : y ≠ σ (σ (σ y)) := fun h => d01 (by
      have e := congrArg σ h
      rw [h4y] at e
      exact e.symm)
    have d12 : σ y ≠ σ (σ y) := fun h => d01 (σ.injective h)
    have d13 : σ y ≠ σ (σ (σ y)) := fun h => d02 (σ.injective h)
    have d23 : σ (σ y) ≠ σ (σ (σ y)) := fun h => d12 (σ.injective h)
    have hout : ∀ z ∈ ({y, σ y, σ (σ y), σ (σ (σ y))} : Finset (Fin 7)), z ∉ Set.range ι := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    have hc := card_outside_le ι _ hout
    rw [Finset.card_insert_of_notMem (by simp [d01, d02, d03]),
      Finset.card_insert_of_notMem (by simp [d12, d13]),
      Finset.card_insert_of_notMem (by simp [d23]), Finset.card_singleton] at hc
    omega
  have hinv : ∀ y, w.perm (w.perm y) = y := by
    intro y
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hy
      rw [hfix, hfix]
    · exact hA y hy
  have hsymm : ∀ y, w.perm.symm y = w.perm y := by
    intro y
    apply w.perm.injective
    rw [Equiv.apply_symm_apply, hinv]
  have hww_perm : (w * w).perm = 1 := by
    rw [mul_perm]
    refine Equiv.ext fun y => ?_
    simpa using hinv y
  by_cases hall : ∀ y, y ∉ Set.range ι → w.perm y = y
  · left
    have hid : ∀ y, w.perm y = y := fun y => by
      by_cases hy : y ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hy
        exact hfix i
      · exact hall y hy
    have hw : w * w = 1 := by
      refine Wr.ext (funext fun y => ?_) hww_perm
      rw [mul_vec, hsymm, hid]
      exact zmod_two_add_self _
    rw [← map_mul, hw, map_one]
  · push Not at hall
    obtain ⟨p, hp, hσp⟩ := hall
    have hq' : w.perm p ∉ Set.range ι := hpres p hp
    have hσq : w.perm (w.perm p) = p := hinv p
    set q := w.perm p with hq
    have hqp : q ≠ p := hσp
    have hpα : p ∉ α := fun h => hp ((hrange p).mpr h)
    have hqα : q ∉ α := fun h => hq' ((hrange q).mpr h)
    set c : ZMod 2 := w.vec p + w.vec q with hc
    have hu : ∀ y, (w * w).vec y = if y = p ∨ y = q then c else 0 := by
      intro y
      rw [mul_vec, hsymm]
      by_cases h1 : y = p
      · subst h1
        simp [hq, hc]
      · by_cases h2 : y = q
        · subst h2
          simp only [or_true, if_true, hc]
          rw [hσq, add_comm]
        · rw [if_neg (by tauto)]
          have hy : w.perm y = y := by
            by_cases hyr : y ∈ Set.range ι
            · obtain ⟨i, rfl⟩ := hyr
              exact hfix i
            · by_contra hne
              have hsy : w.perm y ∉ Set.range ι := hpres y hyr
              have hp1 : p ∉ Set.range ι := hp
              have e1 : w.perm y ≠ p := fun h => h2 (w.perm.injective (h.trans hσq.symm))
              have e2 : w.perm y ≠ q := fun h => h1 (w.perm.injective h)
              have hout : ∀ z ∈ ({p, q, y, w.perm y} : Finset (Fin 7)), z ∉ Set.range ι := by
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl | rfl | rfl <;> assumption
              have hcard := card_outside_le ι _ hout
              rw [Finset.card_insert_of_notMem (by simp [hqp.symm, Ne.symm h1, Ne.symm e1]),
                Finset.card_insert_of_notMem (by simp [Ne.symm h2, Ne.symm e2]),
                Finset.card_insert_of_notMem (by simp [Ne.symm hne]), Finset.card_singleton]
                at hcard
              omega
          rw [hy]
          exact zmod_two_add_self _
    have hvec : w * w = ofVec (fun y => if y = p ∨ y = q then c else 0) :=
      Wr.ext (funext hu) hww_perm
    rcases zmod_two_cases c with hc0 | hc1
    · left
      have hw : w * w = 1 := by
        rw [hvec]
        refine Wr.ext (funext fun y => ?_) rfl
        simp [hc0, ofVec]
        rfl
      rw [← map_mul, hw, map_one]
    · right
      refine ⟨p, q, hqp.symm, hpα, hqα, ?_⟩
      have hw : w * w = ofVec (TL4.pairVec p q) := by
        rw [hvec]
        refine Wr.ext (funext fun y => ?_) rfl
        simp only [ofVec]
        rw [pairVec_apply hqp.symm, hc1]
      rw [← map_mul, hw]
      rfl

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
