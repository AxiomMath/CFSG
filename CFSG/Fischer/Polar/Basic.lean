module

public import CFSG.Fischer.Polar.Defs
public import CFSG.Fischer.T46Simple
public import CFSG.Fischer.TransvectionPoints
public import CFSG.Fischer.Uniq.Xi
public import Certificates.Data.CFSGNative.Fischer.HyperovalSearch

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs

theorem perp_comm {p q : Fin 693} : perp p q ↔ perp q p := by
  rw [perp_iff, perp_iff, hermStd_swap (uVec p) (uVec q)]
  constructor
  · intro h; rw [h]; ring
  · exact fun h => pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h

theorem perp_self (p : Fin 693) : perp p p := uVec_iso ptsFacts p.2

theorem tvP_inv (p : Fin 693) : (tvP p)⁻¹ = tvP p :=
  inv_eq_of_mul_eq_one_right (tvP_mul_self p)

theorem tvP_symm (p : Fin 693) : (tvP p).symm = tvP p := by
  rw [← Equiv.Perm.inv_def, tvP_inv]

theorem tvP_comm_iff_perp (p q : Fin 693) : tvP p * tvP q = tvP q * tvP p ↔ perp p q :=
  tvP_comm_iff p q

theorem tvP_apply_eq_self_iff {x y : Fin 693} : tvP x y = y ↔ perp x y := by
  rw [← tvP_comm_iff_perp]
  constructor
  · intro h
    have h1 := tvP_conj x y
    rw [h] at h1
    calc tvP x * tvP y = tvP x * tvP y * tvP x * tvP x := by
          rw [mul_assoc (tvP x * tvP y), tvP_mul_self, mul_one]
      _ = tvP y * tvP x := by rw [h1]
  · intro h
    apply tvP_injective
    rw [← tvP_conj, h, mul_assoc, tvP_mul_self, mul_one]

theorem tvP_eq_conj (p q : Fin 693) : tvP (tvP p q) = tvP p * tvP q * (tvP p)⁻¹ := by
  rw [tvP_inv, tvP_conj]

theorem perp_tvP (x a b : Fin 693) : perp (tvP x a) (tvP x b) ↔ perp a b := by
  rw [← tvP_comm_iff_perp, ← tvP_comm_iff_perp, tvP_eq_conj, tvP_eq_conj]
  exact conj_commute_iff _ _ _

theorem tvP_apply_tvP (p a b : Fin 693) : tvP p (tvP a b) = tvP (tvP p a) (tvP p b) := by
  rw [← tvP_conj, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, tvP_tvP]

theorem t46G_mem_closure_tvP (z : ℤ) : t46G z ∈ Subgroup.closure (Set.range tvP) := by
  by_cases hz : z.natAbs - 1 < 46
  · set c := tvGens[z.natAbs - 1]!
    have hc : c ∈ uPts := tvGens_facts.2 _ hz
    obtain ⟨hc1, hc2, hc3, hc4⟩ := mem_uPts.1 hc
    set v := vecOfCode c
    have hcv : codeOf v = c := codeOf_vecOfCode hc1
    have hv0 : v ≠ 0 := fun h => hc2 (by rw [← hcv, h]; decide)
    have hiso : hermStd v v = 0 := (code_eq_zero_iff _).1 (by rw [← hermC_codeOf, hcv]; exact hc3)
    have hlt := ptIdx_lt ptsFacts hv0 hiso
    have hnorm : normV v = v := by
      apply codeOf_injective
      rw [← normC_codeOf, hcv, hc4]
    have hu : uVec (ptIdx v) = v := by rw [uVec_ptIdx ptsFacts hv0 hiso, hnorm]
    refine Subgroup.subset_closure ⟨⟨ptIdx v, hlt⟩, ?_⟩
    rw [t46G_eq_tv]
    show piGU (Subgroup.inclusion SU0_le_GU0 (tvSU' ⟨ptIdx v, hlt⟩)) = piGU (tvGU v _)
    congr 1
    apply Subtype.ext
    apply Units.ext
    show tvM (uVec (ptIdx v)) = tvM v
    rw [hu]
  · rw [t46G_eq_one (by omega)]
    exact Subgroup.one_mem _

theorem T46_eq_closure :
    T46 = Subgroup.closure (Set.range tvP) := by
  refine le_antisymm (T46_le_closure.trans ((Subgroup.closure_le _).2 ?_)) ?_
  · rintro _ (rfl | rfl)
    · exact Subgroup.pow_mem _ (t46_wordG_mem t46G_mem_closure_tvP _) 3
    · exact Subgroup.pow_mem _ (t46_wordG_mem t46G_mem_closure_tvP _) 2
  · rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact tvP_mem p

theorem perm_apply_inv_self {α : Type*} (g : Equiv.Perm α) (x : α) : g (g⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem perm_inv_apply_self {α : Type*} (g : Equiv.Perm α) (x : α) : g⁻¹ (g x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

structure IsPolarAut (g : Equiv.Perm (Fin 693)) : Prop where
  map_perp : ∀ a b, perp (g a) (g b) ↔ perp a b
  map_tvP : ∀ a b, g (tvP a b) = tvP (g a) (g b)

theorem isPolarAut_tvP (p : Fin 693) : IsPolarAut (tvP p) :=
  ⟨perp_tvP p, tvP_apply_tvP p⟩

theorem IsPolarAut.mul {g h : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) (hh : IsPolarAut h) :
    IsPolarAut (g * h) :=
  ⟨fun a b => by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg.map_perp, hh.map_perp],
    fun a b => by rw [Equiv.Perm.mul_apply, hh.map_tvP, hg.map_tvP]; rfl⟩

theorem IsPolarAut.inv {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) : IsPolarAut g⁻¹ := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [← hg.map_perp, perm_apply_inv_self, perm_apply_inv_self]
  · apply g.injective
    rw [perm_apply_inv_self, hg.map_tvP, perm_apply_inv_self, perm_apply_inv_self]

theorem isPolarAut_one : IsPolarAut 1 := ⟨fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem isPolarAut_of_mem
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) : IsPolarAut g := by
  rw [T46_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact isPolarAut_tvP p
  | one => exact isPolarAut_one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem perp_apply_of_mem
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) (a b : Fin 693) :
    perp (g a) (g b) ↔ perp a b :=
  (isPolarAut_of_mem hg).map_perp a b

theorem apply_tvP_of_mem
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) (a b : Fin 693) :
    g (tvP a b) = tvP (g a) (g b) :=
  (isPolarAut_of_mem hg).map_tvP a b

theorem IsPolarAut.mul_tvP_mul_inv {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) (p : Fin 693) :
    g * tvP p * g⁻¹ = tvP (g p) := by
  ext q
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg.map_tvP, perm_apply_inv_self]

theorem perpTab_spec (x y : Fin 693) : ((perpTab ())[x.val]!)[y.val]! = true ↔ perp x y := by
  unfold perpTab
  rw [getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
  simp only
  rw [getElem!_pos _ y.val (by simp), Array.getElem_ofFn, beq_iff_eq, rep_tvP x y.val y.2,
    idx_of_lt _ y.2, ← tvP_apply_eq_self_iff, Fin.ext_iff]
  rfl

theorem filterRange_eq (p : ℕ → Bool) (n : ℕ) (acc : List ℕ) :
    filterRange p n acc = (List.range n).filter p ++ acc := by
  induction n generalizing acc with
  | zero => simp [filterRange]
  | succ n ih =>
    rw [filterRange, ih, List.range_succ, List.filter_append]
    split <;> simp_all

theorem mem_filterRange {p : ℕ → Bool} {n i : ℕ} : i ∈ filterRange p n [] ↔ i < n ∧ p i = true := by
  rw [filterRange_eq, List.append_nil, List.mem_filter, List.mem_range]

theorem nodup_filterRange (p : ℕ → Bool) (n : ℕ) : (filterRange p n []).Nodup := by
  rw [filterRange_eq, List.append_nil]
  exact List.nodup_range.filter _

@[expose] def flagSet (F : Flags) : Set (Fin 693) := {p | F[p.val]! = true}

theorem mem_flagSet {F : Flags} {p : Fin 693} : p ∈ flagSet F ↔ F[p.val]! = true := Iff.rfl

theorem mem_members {F : Flags} {i : ℕ} : i ∈ members F ↔ i < 693 ∧ F[i]! = true :=
  mem_filterRange

theorem nodup_members (F : Flags) : (members F).Nodup := nodup_filterRange _ _

theorem ncard_setOf_mem_list {l : List ℕ} (hl : l.Nodup) (hlt : ∀ i ∈ l, i < 693) :
    {p : Fin 693 | p.val ∈ l}.ncard = l.length := by
  have h : (Fin.val '' {p : Fin 693 | p.val ∈ l}) = (l.toFinset : Set ℕ) := by
    ext i
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hi; exact ⟨⟨i, hlt i hi⟩, hi, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, h, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hl]

theorem ncard_setOf_mem_list_nat {l : List ℕ} (hl : l.Nodup) :
    {i : ℕ | i ∈ l}.ncard = l.length := by
  rw [show {i : ℕ | i ∈ l} = (l.toFinset : Set ℕ) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hl]

theorem flagSet_eq_members (F : Flags) : flagSet F = {p : Fin 693 | p.val ∈ members F} := by
  ext p
  simp only [mem_flagSet, Set.mem_ofPred_eq, mem_members, p.2, true_and]

theorem ncard_flagSet (F : Flags) : (flagSet F).ncard = (members F).length := by
  rw [flagSet_eq_members, ncard_setOf_mem_list (nodup_members F)
    (fun i hi => (mem_members.1 hi).1)]

theorem filterRange_congr {p q : ℕ → Bool} {n : ℕ} (h : ∀ i < n, p i = q i) (acc : List ℕ) :
    filterRange p n acc = filterRange q n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [filterRange, filterRange, h n (Nat.lt_succ_self n)]
    exact ih (fun i hi => h i (Nat.lt_succ_of_lt hi)) _

theorem members_congr {F G : Flags} (h : flagSet F = flagSet G) : members F = members G := by
  unfold members
  refine filterRange_congr (fun i hi => ?_) []
  have := congrArg (fun S => (⟨i, hi⟩ : Fin 693) ∈ S) h
  simp only [mem_flagSet, eq_iff_iff] at this
  exact Bool.eq_iff_iff.2 this

theorem flagSet_imgFlags {Ti : Table} {g : Equiv.Perm (Fin 693)} (h : Rep 693 Ti g⁻¹)
    (F : Flags) : flagSet (imgFlags Ti F) = ⇑g '' flagSet F := by
  ext q
  rw [Set.mem_image_equiv, mem_flagSet, mem_flagSet]
  unfold imgFlags
  rw [getElem!_pos _ q.val (by simp), Array.getElem_ofFn]
  simp only
  rw [h q.val q.2, idx_of_lt _ q.2]
  rfl

@[expose] noncomputable def tvPn (p : ℕ) : Equiv.Perm (Fin 693) :=
  if h : p < 693 then tvP ⟨p, h⟩ else 1

@[expose] noncomputable def wordP (w : List ℕ) : Equiv.Perm (Fin 693) :=
  w.foldr (fun p g => tvPn p * g) 1

theorem wordTab_nil : tvWordTab [] = idT 693 := List.foldr_nil

theorem wordTab_cons (p : ℕ) (w : List ℕ) :
    tvWordTab (p :: w) = compT 693 tvTabs[p]! (tvWordTab w) := List.foldr_cons

theorem wordP_nil : wordP [] = 1 := List.foldr_nil

theorem wordP_cons (p : ℕ) (w : List ℕ) : wordP (p :: w) = tvPn p * wordP w := List.foldr_cons

theorem wordP_mem (w : List ℕ) : wordP w ∈ T46 := by
  induction w with
  | nil => exact T46.one_mem
  | cons p w ih =>
    rw [wordP_cons]
    refine T46.mul_mem ?_ ih
    unfold tvPn
    split
    · exact tvP_mem _
    · exact T46.one_mem

theorem rep_tvPn {p : ℕ} (hp : p < 693) : Rep 693 tvTabs[p]! (tvPn p) := by
  have h : tvPn p = tvP ⟨p, hp⟩ := dite_eq_left hp
  rw [h]
  exact rep_tvP ⟨p, hp⟩

theorem rep_wordTab (w : List ℕ) (hw : ∀ p ∈ w, p < 693) : Rep 693 (tvWordTab w) (wordP w) := by
  induction w with
  | nil => rw [wordTab_nil, wordP_nil]; exact Rep.idT (by norm_num)
  | cons p w ih =>
    rw [wordTab_cons, wordP_cons]
    exact Rep.compT (rep_tvPn (hw p (List.mem_cons_self ..)))
      (ih fun q hq => hw q (List.mem_cons_of_mem _ hq))

end CFSG.Fischer
