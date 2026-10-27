
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open AutETable

namespace E69

theorem ncard_filter_range (p : ℕ → Bool) :
    Set.ncard {k : ℕ | k < 32 ∧ p k = true} = ((List.range 32).filter p).length := by
  have h : {k : ℕ | k < 32 ∧ p k = true} = ↑((List.range 32).filter p).toFinset := by
    ext k
    simp
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup (List.nodup_range.filter p)]

section Label

variable {G : Type*} [Group G] {E : Subgroup G} {t : G} {mulE : ℕ → ℕ → ℕ} {tI : ℕ}
  {eltE : ℕ → G}

theorem ncard_label (hL : ELabelling E t mulE tI eltE) {P : G → Prop} {p : ℕ → Bool}
    (hP : ∀ k < 32, P (eltE k) ↔ p k = true) :
    Set.ncard {e : G | e ∈ E ∧ P e} = ((List.range 32).filter p).length := by
  have hset : {e : G | e ∈ E ∧ P e} = eltE '' {k : ℕ | k < 32 ∧ p k = true} := by
    ext e
    constructor
    · rintro ⟨he, hPe⟩
      obtain ⟨k, hk, rfl⟩ := hL.surj e he
      exact ⟨k, ⟨hk, (hP k hk).1 hPe⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hpk⟩, rfl⟩
      exact ⟨hL.mem k hk, (hP k hk).2 hpk⟩
  rw [hset, Set.InjOn.ncard_image fun a ha b hb hab => hL.inj a ha.1 b hb.1 hab,
    ncard_filter_range]

theorem label_lt (hL : ELabelling E t mulE tI eltE) {a b : ℕ} (ha : a < 32) (hb : b < 32) :
    mt (tab2 32 mulE) a b < 32 := by
  rw [mt_tab2 mulE ha hb]
  exact hL.lt a ha b hb

theorem label_mul (hL : ELabelling E t mulE tI eltE) {a b : ℕ} (ha : a < 32) (hb : b < 32) :
    eltE a * eltE b = eltE (mt (tab2 32 mulE) a b) := by
  rw [mt_tab2 mulE ha hb, hL.mul a ha b hb]

theorem realizes_of_labelling (hL : ELabelling E t mulE tI eltE) :
    ∃ elt : ℕ → ↥E, Realizes ↥E 32 (tab2 32 mulE) elt ∧ ∀ k < 32, (elt k : G) = eltE k := by
  classical
  let elt : ℕ → ↥E := fun k => if h : k < 32 then ⟨eltE k, hL.mem k h⟩ else 1
  have helt : ∀ k < 32, (elt k : G) = eltE k := fun k hk => by simp [elt, hk]
  refine ⟨elt, ⟨by norm_num, fun a b ha hb => label_lt hL ha hb, fun a b ha hb => ?_,
    fun a b ha hb hab => ?_, fun x => ?_, ?_⟩, helt⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, helt _ (label_lt hL ha hb), helt a ha, helt b hb, label_mul hL ha hb]
  · apply hL.inj a ha b hb
    rw [← helt a ha, ← helt b hb, hab]
  · obtain ⟨k, hk, hke⟩ := hL.surj x x.2
    exact ⟨k, hk, Subtype.ext (by rw [helt k hk, hke])⟩
  · apply Subtype.ext
    rw [helt 0 (by norm_num), hL.one, Subgroup.coe_one]

end Label

end E69

open E69

end CFSG.EvenSporadicStandard.Fin76b
