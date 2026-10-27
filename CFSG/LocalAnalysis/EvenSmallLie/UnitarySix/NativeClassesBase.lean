
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeModelBase

@[expose] public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Fischer
open CFSG.ComponentClassification.M12Cover
open scoped Pointwise

private theorem ncard_finSet {n : ℕ} {l : List ℕ} (hl : PointList n l) :
    (finSet n l).ncard = l.length := by
  have hnd : l.Nodup := hl.sorted.nodup
  let f : Fin l.length → Fin n := fun k => ⟨l.get k, hl.lt _ (List.get_mem l k)⟩
  have hf : Function.Injective f := fun a b h =>
    (List.Nodup.get_inj_iff hnd).1 (congrArg Fin.val h)
  have hrange : Set.range f = finSet n l := by
    ext p
    simp only [Set.mem_range, finSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, rfl⟩
      exact List.get_mem l k
    · intro hp
      obtain ⟨k, hk⟩ := List.get_of_mem hp
      exact ⟨k, Fin.ext hk⟩
  rw [← hrange, Set.ncard_range_of_injective hf, Nat.card_fin]

theorem ncard_fixed (g : Equiv.Perm (Fin 693)) :
    {p : Fin 693 | g p = p}.ncard = (fixedList 693 (arrOf g)).length := by
  rw [← finSet_fixedList (rep_arrOf g), ncard_finSet (pointList_fixedList _)]

theorem fixed_conj (c g : Equiv.Perm (Fin 693)) :
    {p : Fin 693 | (c * g * c⁻¹) p = p} = c '' {p | g p = p} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image, Equiv.Perm.mul_apply]
  constructor
  · intro h
    refine ⟨c⁻¹ p, ?_, perm_apply_inv_self c p⟩
    have h' := congrArg (fun x => c⁻¹ x) h
    simp only [perm_inv_apply_self] at h'
    exact h'
  · rintro ⟨q, hq, rfl⟩
    rw [perm_inv_apply_self, hq]

theorem ncard_fixed_conj (c g : Equiv.Perm (Fin 693)) :
    {p : Fin 693 | (c * g * c⁻¹) p = p}.ncard = {p : Fin 693 | g p = p}.ncard := by
  rw [fixed_conj, Set.ncard_image_of_injective _ c.injective]

theorem ncard_fixed_of_isConj {g h : Equiv.Perm (Fin 693)} (hgh : IsConj g h) :
    {p : Fin 693 | g p = p}.ncard = {p : Fin 693 | h p = p}.ncard := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hgh
  rw [← hc, ncard_fixed_conj]

theorem exists_conj_of_repsOK_normalizing {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (N : Subgroup (Equiv.Perm (Fin n)))
    (hN : ∀ c ∈ N, ∀ h ∈ Q.originalSubgroup, c * h * c⁻¹ ∈ Q.originalSubgroup)
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ N)
    {m : ℕ} (hm : 0 < m) (reps : List (Equiv.Perm (Fin n)))
    (hreps : ∀ r ∈ reps, r ∈ Q.originalSubgroup ∧ orderOf r = m) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q 1 m) (reps.map toTable) cap = true) :
    (∀ u ∈ Q.originalSubgroup, orderOf u = m → ∃ r ∈ reps, ∃ c ∈ N, u = c * r * c⁻¹) ∧
    ∀ r ∈ reps, (conjClosure n gens gensInv (toTable r) cap).1.size ≤ (conjClass N r).ncard := by
  set H := Q.originalSubgroup
  set L := enumeration Q
  have hmem : ∀ g, g ∈ L ↔ g ∈ H := mem_enumeration_iff Q hQ
  set XG := (L.map ((1 : Equiv.Perm (Fin n)) * ·)).filter fun h => decide (orderOf h = m)
  have hX := forall₂_cosetOrderTables hn Q 1 hm
  have hXG : ∀ u, u ∈ XG ↔ u ∈ H ∧ orderOf u = m := by
    intro u
    simp only [XG, List.mem_filter, List.mem_map, hmem, decide_eq_true_eq, one_mul]
    constructor
    · rintro ⟨⟨h, hh, rfl⟩, ho⟩
      exact ⟨hh, ho⟩
    · rintro ⟨hu, ho⟩
      exact ⟨⟨u, hu, rfl⟩, ho⟩
  have hclosed : ∀ c ∈ N, ∀ u, u ∈ H → orderOf u = m →
      c * u * c⁻¹ ∈ H ∧ orderOf (c * u * c⁻¹) = m := fun c hc u hu ho =>
    ⟨hN c hc u hu, (MulEquiv.orderOf_eq (MulAut.conj c) u).trans ho⟩
  simp only [repsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨htree, hdist⟩, hsum⟩ := hok
  set cl := (reps.map toTable).map fun r => (r, conjClosure n gens gensInv r cap)
  have hcl : ∀ c ∈ cl, ∃ r ∈ reps, c.1 = toTable r ∧
      c.2 = conjClosure n gens gensInv (toTable r) cap := by
    intro c hc
    simp only [cl, List.map_map, List.mem_map, Function.comp] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    exact ⟨r, hr, rfl, rfl⟩
  have hentries : ∀ c ∈ cl, ∀ T ∈ c.2.1.toList, ∃ r ∈ reps, Rep n c.1 r ∧
      ∃ d ∈ N, Rep n T (d * r * d⁻¹) := by
    intro c hc T hT
    obtain ⟨r, hr, h1, -⟩ := hcl c hc
    have hrep : Rep n c.1 r := h1 ▸ rep_toTable hn r
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrepd⟩ := conjTreeOK_spec N hg hrep (htree c hc) k hk
    refine ⟨r, hr, hrep, d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos c.2.1 k hk] at hrepd
  set U := cl.flatMap fun c => c.2.1.toList
  have hU : List.Forall₂ (Rep n) U (U.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, -, -, d, -, hrep⟩ := hentries c hc T hT
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup : (U.map (tablePerm n)).Nodup := nodup_of_keysDistinct hU hdist
  have hUmem : ∀ T ∈ U, ∃ r ∈ reps, ∃ d ∈ N, tablePerm n T = d * r * d⁻¹ := by
    intro T hT
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, hr, -, d, hd, hrep⟩ := hentries c hc T hT
    exact ⟨r, hr, d, hd, tablePerm_eq hrep⟩
  have hsub : U.map (tablePerm n) ⊆ XG := by
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
    obtain ⟨r, hr, d, hd, heq⟩ := hUmem T hT
    rw [heq, hXG]
    exact hclosed d hd r (hreps r hr).1 (hreps r hr).2
  have hlen : XG.length ≤ (U.map (tablePerm n)).length := by
    rw [List.length_map, List.length_flatMap, ← List.length_reverse, ← hX.length_eq, ← hsum]
    simp
  have hperm := (hnodup.subperm hsub).perm_of_length_le hlen
  refine ⟨fun u hu ho => ?_, fun r hr => ?_⟩
  · have huU : u ∈ U.map (tablePerm n) := hperm.symm.subset ((hXG u).2 ⟨hu, ho⟩)
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 huU
    obtain ⟨r, hr, d, hd, heq⟩ := hUmem T hT
    exact ⟨r, hr, d, hd, heq⟩
  · set c : Table × Array Table × Array ℕ × Array ℕ :=
      (toTable r, conjClosure n gens gensInv (toTable r) cap)
    have hc : c ∈ cl := by
      simp only [cl, List.map_map, List.mem_map, Function.comp]
      exact ⟨r, hr, rfl⟩
    set E := c.2.1.toList.map (tablePerm n)
    have hEnodup : E.Nodup := by
      have := (List.nodup_flatMap.1 (by
        have h' : (U.map (tablePerm n)).Nodup := hnodup
        rwa [List.map_flatMap] at h')).1
      exact this c hc
    have hEcls : ∀ y ∈ E, y ∈ conjClass N r := by
      intro y hy
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
      obtain ⟨r', hr', hrep', d, hd, hrep⟩ := hentries c hc T hT
      have hrr : r' = r := (tablePerm_eq hrep').symm.trans (tablePerm_eq (rep_toTable hn r))
      subst hrr
      exact ⟨d, hd, tablePerm_eq hrep⟩
    have hlenE : E.length = (conjClosure n gens gensInv (toTable r) cap).1.size := by
      simp [E, c]
    rw [← hlenE, ← List.toFinset_card_of_nodup hEnodup, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun y hy => hEcls y (List.mem_toFinset.1 hy))
      (conjClass_finite N r)

theorem tblEq_true_iff {S T : Table} {g h : Equiv.Perm (Fin 693)} (hS : Rep 693 S g)
    (hT : Rep 693 T h) : tblEq 693 S T = true ↔ g = h := by
  constructor
  · intro e
    exact rep_unique hS (rep_of_tblEq hT e)
  · rintro rfl
    rw [tblEq_iff]
    intro i hi
    rw [hS i hi, hT i hi]

theorem exists_of_forall₂_mem_right {α β : Type*} {R : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ R l₁ l₂) {y : β} (hy : y ∈ l₂) : ∃ x ∈ l₁, R x y := by
  induction h with
  | nil => simp at hy
  | @cons a b l₁ l₂ hab _ ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨x, hx, hxy⟩ := ih hy
      exact ⟨x, by simp [hx], hxy⟩

theorem exists_table_of_mem (Q : RawSchreierDatum 693) (hQ : ValidSchreier Q)
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ Q.originalSubgroup) :
    ∃ T ∈ allTables Q, Rep 693 T x :=
  exists_of_forall₂_mem_right (forall₂_allTables hn693 Q)
    (List.mem_reverse.2 ((mem_enumeration_iff Q hQ x).2 hx))

theorem smul_fixed_of_comm {g x : Equiv.Perm (Fin 693)} (h : g * x = x * g) :
    g • {p : Fin 693 | x p = p} = {p | x p = p} := by
  have hc : g * x * g⁻¹ = x := by rw [h, mul_inv_cancel_right]
  rw [← Set.image_smul]
  have hfun : (fun p : Fin 693 => g • p) = g := funext fun p => Equiv.Perm.smul_def g p
  rw [hfun]
  have := fixed_conj g x
  rw [hc] at this
  exact this.symm

end CFSG.EvenSmallLie.UnitarySix
