module

public import Certificates.Data.Kernel.SporSch.SporXCent
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KS.SporXE

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Schreier Subgroup

variable {n : Nat}

theorem allF_iff (p : (Nat → Nat) → Bool) (fs : List (Nat → Nat)) :
    allF p fs = true ↔ ∀ f ∈ fs, p f = true := by
  induction fs with
  | nil => simp [allF]
  | cons f fs ih =>
    change Bool.rec (motive := fun _ => Bool) false (allF p fs) (p f) = true ↔ _
    rw [bAnd_iff, ih, List.forall_mem_cons]

theorem ltW_iff (nl : Nat) (words : List (List Nat × Nat)) :
    ltW nl words = true ↔ ∀ we ∈ words, ∀ l ∈ we.1, l < nl := by
  induction words with
  | nil => simp [ltW]
  | cons we words ih =>
    obtain ⟨w, e⟩ := we
    change Bool.rec (motive := fun _ => Bool) false (ltW nl words)
      (List.rec (motive := fun _ => Bool) true (fun l _ ih' => bAnd(Nat.blt l nl, ih')) w) = true ↔ _
    rw [bAnd_iff, ih, List.forall_mem_cons]
    refine and_congr_left fun _ => ?_
    change _ ↔ ∀ l ∈ w, l < nl
    induction w with
    | nil => simp
    | cons l w ihw =>
      change Bool.rec (motive := fun _ => Bool) false _ (Nat.blt l nl) = true ↔ _
      rw [bAnd_iff, ihw, List.forall_mem_cons, Nat.blt_eq]

@[expose] def subP {G : Type*} [Group G] : List G → List G
  | [] => [1]
  | x :: xs => subP xs ++ (subP xs).map fun y => y * x

theorem length_subP {G : Type*} [Group G] : ∀ xs : List G, (subP xs).length = 2 ^ xs.length
  | [] => rfl
  | x :: xs => by
    rw [subP, List.length_append, List.length_map, length_subP xs, List.length_cons, pow_succ]
    ring

theorem mem_closure_of_mem_subP {G : Type*} [Group G] :
    ∀ (xs : List G), ∀ y ∈ subP xs, y ∈ closure {x | x ∈ xs}
  | [], y, hy => by
    rw [subP, List.mem_singleton] at hy
    rw [hy]
    exact one_mem _
  | x :: xs, y, hy => by
    have hmono : closure {z | z ∈ xs} ≤ closure {z | z ∈ x :: xs} :=
      closure_mono fun z hz => List.mem_cons_of_mem _ hz
    rw [subP, List.mem_append, List.mem_map] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact hmono (mem_closure_of_mem_subP xs y hy)
    · exact mul_mem (hmono (mem_closure_of_mem_subP xs z hz)) (subset_closure List.mem_cons_self)

theorem forall₂_sF {fs : List (Nat → Nat)} {ps : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (RepF n) fs ps) : List.Forall₂ (RepF n) (sF fs) (subP ps) := by
  induction h with
  | nil => exact List.Forall₂.cons RepF.one List.Forall₂.nil
  | @cons f x fs ps hf _ ih =>
    change List.Forall₂ (RepF n) (sF fs ++ List.map (fun h x => h (f x)) (sF fs)) _
    rw [subP]
    refine List.rel_append ih ?_
    exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (List.Forall₂.imp (fun _ _ hy => hy.comp hf) ih))

theorem exists_of_forall₂_mem {fs : List (Nat → Nat)} {ps : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (RepF n) fs ps) {p : Equiv.Perm (Fin n)} (hp : p ∈ ps) :
    ∃ f ∈ fs, RepF n f p := by
  induction h with
  | nil => simp at hp
  | @cons f x fs ps hf _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨f, List.mem_cons_self, hf⟩
    · obtain ⟨f', hf', h'⟩ := ih hp
      exact ⟨f', List.mem_cons_of_mem _ hf', h'⟩

theorem nodup_of_distB {bs : List Nat} (hbs : ∀ b ∈ bs, b < n) {hs : List (Nat → Nat)}
    {qs : List (Equiv.Perm (Fin n))} (h : List.Forall₂ (RepF n) hs qs)
    (hd : distB bs hs = true) : qs.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons f q hs qs hf hrest ih =>
    have hd' : Bool.rec (motive := fun _ => Bool) false (distB bs hs)
      (allF (fun h' => bIf(eqOnL bs f h', false, true)) hs) = true := hd
    rw [bAnd_iff, allF_iff] at hd'
    refine List.nodup_cons.mpr ⟨fun hq => ?_, ih hd'.2⟩
    obtain ⟨f', hf', hr⟩ := exists_of_forall₂_mem hrest hq
    have he := eqOnL_of_eq hbs hf hr
    have := hd'.1 f' hf'
    rw [he] at this
    exact Bool.false_ne_true this

theorem card_ge_of_nodup {K : Subgroup (Equiv.Perm (Fin n))} {L : List (Equiv.Perm (Fin n))}
    (hL : L.Nodup) (hK : ∀ x ∈ L, x ∈ K) : L.length ≤ Nat.card K := by
  classical
  have : L.length = (L.toFinset : Set (Equiv.Perm (Fin n))).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
  rw [this, show Nat.card K = (K : Set (Equiv.Perm (Fin n))).ncard from Nat.card_coe_set_eq _]
  exact Set.ncard_le_ncard (fun x hx => hK x (List.mem_toFinset.mp hx)) (Set.toFinite _)

theorem rep_wF {L : Nat → Nat → Nat} {g : Nat → Equiv.Perm (Fin n)} {nl : Nat}
    (hL : ∀ l < nl, RepF n (L l) (g l)) :
    ∀ w : List Nat, (∀ l ∈ w, l < nl) → RepF n (wF L w) (w.map g).prod
  | [], _ => RepF.one
  | l :: w, hw => by
    rw [List.map_cons, List.prod_cons]
    exact (hL l (hw l List.mem_cons_self)).comp
      (rep_wF hL w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))

theorem elem_of_ckE_le {H K C : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}
    (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) (hK : K ≤ H)
    {L : Nat → Nat → Nat} {g : Nat → Equiv.Perm (Fin n)} {nl : Nat}
    (hL : ∀ l < nl, RepF n (L l) (g l)) (hg : ∀ l < nl, g l ∈ K)
    {words : List (List Nat × Nat)} (hC : ∀ we ∈ words, (we.1.map g).prod ^ we.2 ∈ C)
    (h : ckE bs L nl words = true) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), E ≤ K ⊓ C ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ words.length ≤ Nat.card E := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (distB bs (sF (words.map (eF L))))
        (csB bs (words.map (eF L)))) (ltW nl words) = true := h
  rw [bAnd_iff, bAnd_iff, ltW_iff] at h'
  obtain ⟨hlt, hcs, hd⟩ := h'
  let perm : List Nat × Nat → Equiv.Perm (Fin n) := fun we => (we.1.map g).prod ^ we.2
  have hrep : ∀ we ∈ words, RepF n (eF L we) (perm we) := fun we hwe => by
    obtain ⟨w, e⟩ := we
    exact (rep_wF hL w (hlt _ hwe)).powF e
  have hmem : ∀ we ∈ words, perm we ∈ K := fun we hwe => by
    refine pow_mem (list_prod_mem fun y hy => ?_) _
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
    exact hg l (hlt we hwe l hl)
  set ps := words.map perm with hps
  have h2 : List.Forall₂ (RepF n) (words.map (eF L)) ps := by
    rw [hps, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr hrep
  rw [csB, allF_iff] at hcs
  have hcs' : ∀ we ∈ words, eqOnL bs (fun x => eF L we (eF L we x)) (fun x => x) = true ∧
      ∀ we' ∈ words, eqOnL bs (fun x => eF L we (eF L we' x)) (fun x => eF L we' (eF L we x)) =
        true := fun we hwe => by
    have := hcs _ (List.mem_map_of_mem hwe)
    rw [bAnd_iff, allF_iff] at this
    exact ⟨this.1, fun we' hwe' => this.2 _ (List.mem_map_of_mem hwe')⟩
  have hc : ∀ x ∈ ps, ∀ y ∈ ps, x * y = y * x := by
    intro x hx y hy
    obtain ⟨we, hwe, rfl⟩ := List.mem_map.mp hx
    obtain ⟨we', hwe', rfl⟩ := List.mem_map.mp hy
    exact eq_of_eqOnL hH ((hrep we hwe).comp (hrep we' hwe')) ((hrep we' hwe').comp (hrep we hwe))
      (hK (mul_mem (hmem we hwe) (hmem we' hwe'))) (hK (mul_mem (hmem we' hwe') (hmem we hwe)))
      ((hcs' we hwe).2 we' hwe')
  have hs : ∀ x ∈ ps, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨we, hwe, rfl⟩ := List.mem_map.mp hx
    rw [sq]
    exact eq_of_eqOnL hH ((hrep we hwe).comp (hrep we hwe)) RepF.one
      (hK (mul_mem (hmem we hwe) (hmem we hwe))) (one_mem _) (hcs' we hwe).1
  have hcl : IsMulCommutative ↥(closure {x | x ∈ ps}) :=
    isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  have hEc : ∀ a ∈ closure {x | x ∈ ps}, ∀ b ∈ closure {x | x ∈ ps}, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hcl.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨closure {x | x ∈ ps}, ?_, hEc, fun a ha => ?_, ?_⟩
  · rw [closure_le]
    rintro _ hx
    obtain ⟨we, hwe, rfl⟩ := List.mem_map.mp hx
    exact ⟨hmem we hwe, hC we hwe⟩
  · induction ha using Subgroup.closure_induction with
    | mem x hx => exact hs x hx
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy => rw [Commute.mul_pow (hEc x hx y hy) 2, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  · have hnd := nodup_of_distB hbs (forall₂_sF h2) hd
    have hle := card_ge_of_nodup hnd (mem_closure_of_mem_subP ps)
    rwa [length_subP, hps, List.length_map] at hle

theorem elem_of_ckE {H K : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}
    (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) (hK : K ≤ H)
    {L : Nat → Nat → Nat} {g : Nat → Equiv.Perm (Fin n)} {nl : Nat}
    (hL : ∀ l < nl, RepF n (L l) (g l)) (hg : ∀ l < nl, g l ∈ K)
    {words : List (List Nat × Nat)} (h : ckE bs L nl words = true) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), E ≤ K ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ words.length ≤ Nat.card E := by
  obtain ⟨E, hE, hc, hs, hcard⟩ :=
    elem_of_ckE_le (C := ⊤) hH hbs hK hL hg (fun _ _ => mem_top _) h
  exact ⟨E, hE.trans inf_le_left, hc, hs, hcard⟩

theorem cent_of_cmB {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}
    (hH : BaseFaithful H bs) {L : Nat → Nat → Nat} {g : Nat → Equiv.Perm (Fin n)} {nl : Nat}
    (hL : ∀ l < nl, RepF n (L l) (g l)) {t : Nat → Nat} {τ : Equiv.Perm (Fin n)}
    (ht : RepF n t τ) {words : List (List Nat × Nat)} (hlt : ∀ we ∈ words, ∀ l ∈ we.1, l < nl)
    (hmem : ∀ we ∈ words,
      ((we.1.map g).prod ^ we.2 * τ)⁻¹ * (τ * (we.1.map g).prod ^ we.2) ∈ H)
    (h : cmB bs t (words.map (eF L)) = true) :
    ∀ we ∈ words, (we.1.map g).prod ^ we.2 ∈ centralizer {τ} := by
  intro we hwe
  rw [cmB, allF_iff] at h
  have hrep : RepF n (eF L we) ((we.1.map g).prod ^ we.2) := by
    obtain ⟨w, e⟩ := we
    exact (rep_wF hL w (hlt _ hwe)).powF e
  have he := (eqOnL_iff _ _ _).1 (h _ (List.mem_map_of_mem hwe))
  have h1 := hH _ (hmem we hwe) fun x hx => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    refine Fin.ext ?_
    rw [← (hrep.comp ht) x x.2, ← (ht.comp hrep) x x.2]
    exact (he x hx).symm
  rw [mem_centralizer_singleton_iff]
  exact inv_mul_eq_one.1 h1

end CFSG.KS.SporXE

end
