module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.FixedThree

open scoped commutatorElement
open CFSG.LieType.Steinberg Subgroup

variable {S L K : Type} [Group S] [Group L] [Group K]

@[expose] def derivedPullback (β : S →* K) (η : L →* K) : Subgroup (S × L) :=
  ⁅pullback β η, pullback β η⁆

theorem derivedPullback_le (β : S →* K) (η : L →* K) : derivedPullback β η ≤ pullback β η := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  rw [commutatorElement_def]
  exact (pullback β η).mul_mem ((pullback β η).mul_mem ((pullback β η).mul_mem hx hy)
    ((pullback β η).inv_mem hx)) ((pullback β η).inv_mem hy)

@[expose] def dpFst (β : S →* K) (η : L →* K) : derivedPullback β η →* S :=
  (MonoidHom.fst S L).comp (derivedPullback β η).subtype

@[expose] def dpSnd (β : S →* K) (η : L →* K) : derivedPullback β η →* L :=
  (MonoidHom.snd S L).comp (derivedPullback β η).subtype

theorem dpFst_surjective {β : S →* K} {η : L →* K} (hη : Function.Surjective η)
    (hS : Group.IsPerfect S) : Function.Surjective (dpFst β η) := by
  have hle : commutator S ≤ (dpFst β η).range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro s _ t _
    obtain ⟨l, hl⟩ := hη (β s)
    obtain ⟨m, hm⟩ := hη (β t)
    have hx : (s, l) ∈ pullback β η := hl.symm
    have hy : (t, m) ∈ pullback β η := hm.symm
    exact ⟨⟨⁅(s, l), (t, m)⁆, Subgroup.commutator_mem_commutator hx hy⟩, by
      simp [dpFst, commutatorElement_def]⟩
  intro s
  exact hle (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top s)

theorem dpSnd_surjective {β : S →* K} {η : L →* K} (hβ : Function.Surjective β)
    (hL : Group.IsPerfect L) : Function.Surjective (dpSnd β η) := by
  have hle : commutator L ≤ (dpSnd β η).range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro l _ m _
    obtain ⟨s, hs⟩ := hβ (η l)
    obtain ⟨t, ht⟩ := hβ (η m)
    have hx : (s, l) ∈ pullback β η := hs
    have hy : (t, m) ∈ pullback β η := ht
    exact ⟨⟨⁅(s, l), (t, m)⁆, Subgroup.commutator_mem_commutator hx hy⟩, by
      simp [dpSnd, commutatorElement_def]⟩
  intro l
  exact hle (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top l)

theorem dpFst_mem_ker {β : S →* K} {η : L →* K} {x : derivedPullback β η}
    (hx : x ∈ (dpFst β η).ker) : dpSnd β η x ∈ η.ker := by
  have h1 : ((x : S × L)).1 = 1 := hx
  have h2 := derivedPullback_le β η x.2
  rw [MonoidHom.mem_ker]
  have := mem_pullback.1 h2
  rw [h1, map_one] at this
  exact this.symm

@[expose] def dpQ (β : S →* K) (η : L →* K) : derivedPullback β η →* K := β.comp (dpFst β η)

theorem dpQ_surjective {β : S →* K} {η : L →* K} (hβ : Function.Surjective β)
    (hη : Function.Surjective η) (hS : Group.IsPerfect S) : Function.Surjective (dpQ β η) :=
  hβ.comp (dpFst_surjective hη hS)

theorem ker_dpQ_le_center {β : S →* K} {η : L →* K} (hβc : β.ker ≤ Subgroup.center S)
    (hηc : η.ker ≤ Subgroup.center L) :
    (dpQ β η).ker ≤ Subgroup.center (derivedPullback β η) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : β (x : S × L).1 = 1 := hx
  have h2 : η (x : S × L).2 = 1 := by
    rw [← (mem_pullback.1 (derivedPullback_le β η x.2)), h1]
  have hxs : (x : S × L).1 ∈ Subgroup.center S := hβc h1
  have hxl : (x : S × L).2 ∈ Subgroup.center L := hηc h2
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · exact Subgroup.mem_center_iff.1 hxs _
  · exact Subgroup.mem_center_iff.1 hxl _

theorem center_le_ker_dpQ {β : S →* K} {η : L →* K} (hq : Function.Surjective (dpQ β η))
    (hKz : Subgroup.center K = ⊥) : Subgroup.center (derivedPullback β η) ≤ (dpQ β η).ker := by
  intro x hx
  have : dpQ β η x ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨y, rfl⟩ := hq k
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx y)]
  rw [hKz] at this
  exact this

theorem isPerfect_derivedPullback {β : S →* K} {η : L →* K} (hη : Function.Surjective η)
    (hS : Group.IsPerfect S) (hηc : η.ker ≤ Subgroup.center L) :
    Group.IsPerfect (derivedPullback β η) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact (derivedPullback β η).mul_mem ((derivedPullback β η).mul_mem
      ((derivedPullback β η).mul_mem hx hy) ((derivedPullback β η).inv_mem hx))
      ((derivedPullback β η).inv_mem hy)
  ·
    have hdec : ∀ x ∈ pullback β η, ∃ z ∈ Subgroup.center (S × L), ∃ q ∈ derivedPullback β η,
        x = z * q := by
      intro x hx
      obtain ⟨q, hq⟩ := dpFst_surjective (β := β) hη hS x.1
      refine ⟨x * (q : S × L)⁻¹, ?_, q, q.2, by group⟩
      have hqE : (q : S × L) ∈ pullback β η := derivedPullback_le β η q.2
      have h1 : (x * (q : S × L)⁻¹).1 = 1 := by
        have : ((q : S × L)).1 = x.1 := hq
        simp [this]
      have h2 : β (x.1) = η x.2 := hx
      have h3 : β ((q : S × L).1) = η (q : S × L).2 := hqE
      have h4 : η ((x * (q : S × L)⁻¹).2) = 1 := by
        have : ((q : S × L)).1 = x.1 := hq
        simp only [Prod.snd_mul, Prod.snd_inv, map_mul, map_inv]
        rw [← h2, ← h3, this, mul_inv_cancel]
      rw [Subgroup.mem_center_iff]
      intro g
      refine Prod.ext ?_ ?_
      · simp [h1]
      · exact Subgroup.mem_center_iff.1 (hηc h4) _
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨z, hz, q, hq, rfl⟩ := hdec x hx
    obtain ⟨z', hz', q', hq', rfl⟩ := hdec y hy
    have := commutatorElement_mul_mul_of_mem_center hz hz' q q'
    rw [this]
    exact Subgroup.commutator_mem_commutator hq hq'

end CFSG.AGLEmbedding.FixedThree
