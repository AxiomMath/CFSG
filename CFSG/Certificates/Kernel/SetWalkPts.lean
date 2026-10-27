module

public import CFSG.Certificates.Kernel.SetWalkSound
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Set.Card

public section

namespace CFSG.KC.SetWalk

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Raw CFSG.Monster.B.Co2
open scoped Pointwise

structure Valid (n w k S : Nat) : Prop where
  lt : ∀ i < k, fd w S i < n
  inj : ∀ i < k, ∀ j < k, fd w S i = fd w S j → i = j

@[expose] def fields (w k S : Nat) : Finset Nat := (Finset.range k).image (fd w S)

@[expose] def pts (n w k S : Nat) : Set (Fin n) := {p | (p : Nat) ∈ fields w k S}

theorem mem_pts {n w k S : Nat} {p : Fin n} : p ∈ pts n w k S ↔ ∃ i < k, fd w S i = p := by
  simp [pts, fields]

private theorem leafK (w wr R S lo : Nat) :
    fld(R, Nat.mul wr fld(S, Nat.mul w lo, mask w), mask wr) = fd wr R (fd w S lo) := by
  rw [fld_eq, fld_eq]
  rfl

theorem keyH_eq (k w wr R S : Nat) (d : Nat) : ∀ lo,
    keyH k w (mask w) wr (mask wr) R S d lo =
      ∑ i ∈ Finset.range (2 ^ d), if lo + i < k then fd wr R (fd w S (lo + i)) else 0 := by
  induction d with
  | zero =>
    intro lo
    change nIf(Nat.blt lo k, fld(R, Nat.mul wr fld(S, Nat.mul w lo, mask w), mask wr),
      nat_lit 0) = _
    rw [nIf_eq, leafK]
    simp [Nat.blt_eq]
  | succ d ih =>
    intro lo
    change Nat.add (keyH k w (mask w) wr (mask wr) R S d lo)
      (keyH k w (mask w) wr (mask wr) R S d (Nat.add lo (Nat.shiftLeft 1 d))) = _
    have h1 : Nat.shiftLeft 1 d = 2 ^ d := by simp [Nat.shiftLeft_eq]
    rw [ih, ih, h1]
    simp only [Nat.add_eq]
    rw [Nat.pow_succ, Nat.mul_two, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_assoc]

theorem keyS_eq_sum {k w wr R d : Nat} (hk : k ≤ 2 ^ d) (S : Nat) :
    keyS k w (mask w) wr (mask wr) R d S = ∑ i ∈ Finset.range k, fd wr R (fd w S i) := by
  unfold keyS
  rw [keyH_eq]
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ d = k + r := ⟨2 ^ d - k, by omega⟩
  rw [hr, Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range r, (if 0 + (k + x) < k then fd wr R (fd w S (0 + (k + x)))
      else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => if_neg (by omega)
  rw [h2, Nat.add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_pos (by simpa using hi), Nat.zero_add]

theorem sum_fields {n w k S : Nat} (hS : Valid n w k S) (f : Nat → Nat) :
    ∑ i ∈ Finset.range k, f (fd w S i) = ∑ p ∈ fields w k S, f p := by
  unfold fields
  rw [Finset.sum_image]
  intro i hi j hj e
  exact hS.inj i (by simpa using hi) j (by simpa using hj) e

theorem fields_eq_of_pts {n w k S S' : Nat} (hS : Valid n w k S) (hS' : Valid n w k S')
    (h : pts n w k S = pts n w k S') : fields w k S = fields w k S' := by
  have lt : ∀ {T}, Valid n w k T → ∀ x ∈ fields w k T, x < n := by
    intro T hT x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact hT.lt i (by simpa using hi)
  ext x
  constructor
  · intro hx
    have : (⟨x, lt hS x hx⟩ : Fin n) ∈ pts n w k S := hx
    rw [h] at this
    exact this
  · intro hx
    have : (⟨x, lt hS' x hx⟩ : Fin n) ∈ pts n w k S' := hx
    rw [← h] at this
    exact this

theorem keyS_eq_of_pts {n w k wr R d S S' : Nat} (hk : k ≤ 2 ^ d) (hS : Valid n w k S)
    (hS' : Valid n w k S') (h : pts n w k S = pts n w k S') :
    keyS k w (mask w) wr (mask wr) R d S = keyS k w (mask w) wr (mask wr) R d S' := by
  rw [keyS_eq_sum hk, keyS_eq_sum hk, sum_fields hS, sum_fields hS', fields_eq_of_pts hS hS' h]

theorem fd_of_rep {n w G : Nat} {σ : Equiv.Perm (Fin n)} (h : Rep n (unpack n w G) σ) {p : Nat}
    (hp : p < n) : fd w G p = σ ⟨p, hp⟩ := by
  have e := h ⟨p, hp⟩
  simp only at e
  rw [unpack, getElem!_ofFn_nat _ hp, pg_eq] at e
  exact e

theorem pcomp_pts {n w k G S : Nat} {σ : Equiv.Perm (Fin n)} (hk : k < 2 ^ 32)
    (h : Rep n (unpack n w G) σ) (hS : Valid n w k S) :
    Valid n w k (pcomp k w (mask w) G S) ∧
      pts n w k (pcomp k w (mask w) G S) = σ • pts n w k S := by
  have hf : ∀ i (hi : i < k), fd w (pcomp k w (mask w) G S) i = σ ⟨fd w S i, hS.lt i hi⟩ :=
    fun i hi => by rw [fd_pcomp hk _ _ _ hi, fd_of_rep h]
  refine ⟨⟨fun i hi => by rw [hf i hi]; exact Fin.isLt _, fun i hi j hj e => ?_⟩, ?_⟩
  · rw [hf i hi, hf j hj] at e
    exact hS.inj i hi j hj (congrArg Fin.val (σ.injective (Fin.ext e)))
  · ext p
    rw [mem_pts, Set.mem_smul_set]
    constructor
    · rintro ⟨i, hi, e⟩
      refine ⟨⟨fd w S i, hS.lt i hi⟩, mem_pts.2 ⟨i, hi, rfl⟩, Fin.ext ?_⟩
      rw [← e, hf i hi]
      rfl
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨i, hi, e⟩ := mem_pts.1 hq
      refine ⟨i, hi, ?_⟩
      rw [hf i hi]
      have : (⟨fd w S i, hS.lt i hi⟩ : Fin n) = q := Fin.ext e
      rw [this]
      rfl

theorem act_pts {n w k G0 G1 S : Nat} {σ₀ σ₁ : Equiv.Perm (Fin n)} (hk : k < 2 ^ 32)
    (h0 : Rep n (unpack n w G0) σ₀) (h1 : Rep n (unpack n w G1) σ₁) (hS : Valid n w k S) :
    ∀ l : List Bool, Valid n w k (act k w (mask w) G0 G1 l S) ∧
      ∃ g ∈ Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin n))),
        pts n w k (act k w (mask w) G0 G1 l S) = g • pts n w k S
  | [] => ⟨hS, 1, Subgroup.one_mem _, by rw [one_smul]; rfl⟩
  | b :: l => by
    obtain ⟨hv, g, hg, e⟩ := act_pts hk h0 h1 hS l
    have mem0 : σ₀ ∈ Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin n))) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have mem1 : σ₁ ∈ Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin n))) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    cases b
    · obtain ⟨hv', e'⟩ := pcomp_pts hk h0 hv
      exact ⟨hv', σ₀ * g, Subgroup.mul_mem _ mem0 hg, by rw [act, cond_false, e', e, mul_smul]⟩
    · obtain ⟨hv', e'⟩ := pcomp_pts hk h1 hv
      exact ⟨hv', σ₁ * g, Subgroup.mul_mem _ mem1 hg, by rw [act, cond_true, e', e, mul_smul]⟩

theorem listK_pts {n w : Nat} {l : List Nat} {S : Nat} (h : listK w (mask w) l S = true)
    (hlt : ∀ q ∈ l, q < n) (hnd : l.Nodup) :
    Valid n w l.length S ∧ pts n w l.length S = {p : Fin n | (p : Nat) ∈ l} := by
  have hf : ∀ i (hi : i < l.length), fd w S i = l[i] := by
    intro i hi
    have e := (listK_spec h).1 i hi
    rw [fld_eq, getElem!_pos l i hi] at e
    exact e
  refine ⟨⟨fun i hi => by rw [hf i hi]; exact hlt _ (List.getElem_mem hi),
    fun i hi j hj e => ?_⟩, ?_⟩
  · rw [hf i hi, hf j hj] at e
    exact (hnd.getElem_inj_iff).1 e
  · ext p
    rw [mem_pts]
    simp only [Set.mem_setOf_eq, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, e⟩
      exact ⟨i, hi, by rw [← hf i hi, e]⟩
    · rintro ⟨i, hi, e⟩
      exact ⟨i, hi, by rw [hf i hi, e]⟩

theorem fixOK_pts {n w k G S : Nat} {σ : Equiv.Perm (Fin n)} (h : fixOK k w (mask w) G S = true)
    (hr : Rep n (unpack n w G) σ) (hS : Valid n w k S) : σ • pts n w k S = pts n w k S := by
  have hsub : σ • pts n w k S ⊆ pts n w k S := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨i, hi, e⟩ := mem_pts.1 hq
    obtain ⟨j, hj, e'⟩ := fixOK_spec h i hi
    rw [fld_eq, fld_eq, pg_eq] at e'
    change fd w G (fd w S i) = fd w S j at e'
    refine mem_pts.2 ⟨j, hj, ?_⟩
    rw [← e', fd_of_rep hr (hS.lt i hi)]
    have : (⟨fd w S i, hS.lt i hi⟩ : Fin n) = q := Fin.ext e
    rw [this]
    rfl
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [← Set.image_smul, Set.ncard_image_of_injective _ (MulAction.injective σ)]

end CFSG.KC.SetWalk

end
