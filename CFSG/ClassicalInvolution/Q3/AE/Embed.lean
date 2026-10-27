module

public import Mathlib.Logic.Equiv.Fintype
public import CFSG.ClassicalInvolution.Q3.AE.Wreath
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

open Classical in
@[expose] noncomputable def embedVec (ι : Fin 4 ↪ Fin n) (v : Fin 4 → ZMod 2) : Fin n → ZMod 2 :=
  fun x => if h : x ∈ Set.range ι then v (ι.toEquivRange.symm ⟨x, h⟩) else 0

open Classical in
@[expose] noncomputable def embedPerm (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin n) :=
  σ.extendDomain ι.toEquivRange

theorem toEquivRange_apply (ι : Fin 4 ↪ Fin n) (i : Fin 4) :
    (ι.toEquivRange i : Fin n) = ι i := rfl

theorem toEquivRange_symm_apply (ι : Fin 4 ↪ Fin n) (i : Fin 4) :
    ι.toEquivRange.symm ⟨ι i, Set.mem_range_self i⟩ = i := by
  apply ι.toEquivRange.injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem embedVec_apply (ι : Fin 4 ↪ Fin n) (v : Fin 4 → ZMod 2) (i : Fin 4) :
    embedVec ι v (ι i) = v i := by
  classical
  unfold embedVec
  split_ifs with h
  · congr 1
    convert toEquivRange_symm_apply ι i
  · exact absurd (Set.mem_range_self i) h

theorem embedVec_of_not_mem (ι : Fin 4 ↪ Fin n) (v : Fin 4 → ZMod 2) {x : Fin n}
    (hx : x ∉ Set.range ι) : embedVec ι v x = 0 := by
  classical
  simp [embedVec, hx]

theorem embedPerm_apply (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    embedPerm ι σ (ι i) = ι (σ i) := by
  classical
  unfold embedPerm
  have := Equiv.Perm.extendDomain_apply_image σ ι.toEquivRange i
  simpa [toEquivRange_apply] using this

theorem embedPerm_of_not_mem (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin 4)) {x : Fin n}
    (hx : x ∉ Set.range ι) : embedPerm ι σ x = x := by
  classical
  unfold embedPerm
  exact Equiv.Perm.extendDomain_apply_not_subtype σ ι.toEquivRange hx

theorem embedPerm_mul (ι : Fin 4 ↪ Fin n) (σ τ : Equiv.Perm (Fin 4)) :
    embedPerm ι (σ * τ) = embedPerm ι σ * embedPerm ι τ := by
  classical
  unfold embedPerm
  rw [Equiv.Perm.extendDomain_mul]

theorem embedPerm_one (ι : Fin 4 ↪ Fin n) : embedPerm ι 1 = 1 := by
  classical
  unfold embedPerm
  exact Equiv.Perm.extendDomain_one ι.toEquivRange

theorem embedPerm_symm_apply (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (embedPerm ι σ).symm (ι i) = ι (σ.symm i) := by
  apply (embedPerm ι σ).injective
  rw [Equiv.apply_symm_apply, embedPerm_apply, Equiv.apply_symm_apply]

theorem embedPerm_symm_of_not_mem (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin 4)) {x : Fin n}
    (hx : x ∉ Set.range ι) : (embedPerm ι σ).symm x = x := by
  apply (embedPerm ι σ).injective
  rw [Equiv.apply_symm_apply, embedPerm_of_not_mem ι σ hx]

@[expose] noncomputable def embed (ι : Fin 4 ↪ Fin n) : Wr 4 →* Wr n where
  toFun a := ⟨embedVec ι a.vec, embedPerm ι a.perm⟩
  map_one' := by
    refine Wr.ext (funext fun x => ?_) (embedPerm_one ι)
    show embedVec ι (1 : Wr 4).vec x = (1 : Wr n).vec x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply]
      rfl
    · rw [embedVec_of_not_mem ι _ hx]
      rfl
  map_mul' a b := by
    refine Wr.ext (funext fun x => ?_) (embedPerm_mul ι a.perm b.perm)
    show embedVec ι (a * b).vec x = embedVec ι a.vec x +
      embedVec ι b.vec ((embedPerm ι a.perm).symm x)
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_symm_apply, embedVec_apply, embedVec_apply, embedVec_apply, mul_vec]
    · rw [embedPerm_symm_of_not_mem ι _ hx, embedVec_of_not_mem ι _ hx,
        embedVec_of_not_mem ι _ hx, embedVec_of_not_mem ι _ hx, add_zero]

theorem embed_vec (ι : Fin 4 ↪ Fin n) (a : Wr 4) : (embed ι a).vec = embedVec ι a.vec := rfl

theorem embed_perm (ι : Fin 4 ↪ Fin n) (a : Wr 4) : (embed ι a).perm = embedPerm ι a.perm := rfl

theorem embed_injective (ι : Fin 4 ↪ Fin n) : Function.Injective (embed ι) := by
  intro a b h
  have hv : ∀ i, a.vec i = b.vec i := fun i => by
    have := congrFun (congrArg Wr.vec h) (ι i)
    rwa [embed_vec, embed_vec, embedVec_apply, embedVec_apply] at this
  have hp : ∀ i, a.perm i = b.perm i := fun i => by
    have := congrArg (fun c : Wr n => c.perm (ι i)) h
    simp only [embed_perm, embedPerm_apply] at this
    exact ι.injective this
  exact Wr.ext (funext hv) (Equiv.ext hp)

theorem embed_vec_of_not_mem (ι : Fin 4 ↪ Fin n) (a : Wr 4) {x : Fin n}
    (hx : x ∉ Set.range ι) : (embed ι a).vec x = 0 :=
  embedVec_of_not_mem ι _ hx

theorem embed_perm_of_not_mem (ι : Fin 4 ↪ Fin n) (a : Wr 4) {x : Fin n}
    (hx : x ∉ Set.range ι) : (embed ι a).perm x = x :=
  embedPerm_of_not_mem ι _ hx

@[expose] def SupportedOn (a : Wr n) (s : Set (Fin n)) : Prop :=
  ∀ x ∉ s, a.vec x = 0 ∧ a.perm x = x

theorem embed_supportedOn (ι : Fin 4 ↪ Fin n) (a : Wr 4) :
    SupportedOn (embed ι a) (Set.range ι) :=
  fun _ hx => ⟨embed_vec_of_not_mem ι a hx, embed_perm_of_not_mem ι a hx⟩

theorem SupportedOn.perm_symm {a : Wr n} {s : Set (Fin n)} (h : SupportedOn a s) {x : Fin n}
    (hx : x ∉ s) : a.perm.symm x = x := by
  apply a.perm.injective
  rw [Equiv.apply_symm_apply, (h x hx).2]

theorem SupportedOn.perm_mem {a : Wr n} {s : Set (Fin n)} (h : SupportedOn a s) {x : Fin n}
    (hx : x ∈ s) : a.perm.symm x ∈ s := by
  by_contra hy
  apply hy
  have h2 := (h _ hy).2
  rw [Equiv.apply_symm_apply] at h2
  rw [← h2]
  exact hx

theorem comm_of_disjoint {a b : Wr n} {s t : Set (Fin n)} (ha : SupportedOn a s)
    (hb : SupportedOn b t) (hst : Disjoint s t) : a * b = b * a := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [mul_vec, mul_vec]
    by_cases hxs : x ∈ s
    · have hxt : x ∉ t := fun h => Set.disjoint_left.mp hst hxs h
      rw [(hb x hxt).1, hb.perm_symm hxt]
      have : a.perm.symm x ∉ t := fun h => Set.disjoint_left.mp hst (ha.perm_mem hxs) h
      rw [(hb _ this).1]
      ring
    · rw [(ha x hxs).1, ha.perm_symm hxs]
      by_cases hxt : x ∈ t
      · have : b.perm.symm x ∉ s := fun h => Set.disjoint_left.mp hst h (hb.perm_mem hxt)
        rw [(ha _ this).1]
        ring
      · rw [(hb x hxt).1, hb.perm_symm hxt, (ha x hxs).1]
  · show a.perm (b.perm x) = b.perm (a.perm x)
    by_cases hxs : x ∈ s
    · have hxt : x ∉ t := fun h => Set.disjoint_left.mp hst hxs h
      rw [(hb x hxt).2]
      have hax : a.perm x ∈ s := by
        by_contra h
        have h2 := (ha _ h).2
        exact h (by rw [a.perm.injective h2]; exact hxs)
      have : a.perm x ∉ t := fun h => Set.disjoint_left.mp hst hax h
      rw [(hb _ this).2]
    · rw [(ha x hxs).2]
      by_cases hxt : x ∈ t
      · have hbx : b.perm x ∈ t := by
          by_contra h
          have h2 := (hb _ h).2
          exact h (by rw [b.perm.injective h2]; exact hxt)
        have : b.perm x ∉ s := fun h => Set.disjoint_left.mp hst h hbx
        rw [(ha _ this).2]
      · rw [(hb x hxt).2, (ha x hxs).2]

end CFSG.ClassicalInvolution.Q3.AE
