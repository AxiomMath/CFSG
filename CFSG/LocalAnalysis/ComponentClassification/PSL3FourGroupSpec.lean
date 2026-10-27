module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native
open scoped commutatorElement

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}

theorem exists_elt_pos {T : Array Tab} (hH : Enumerates H T.toList) :
    ∃ (elt : ℕ → H) (pos : H → ℕ), (∀ k < T.size, TabRep T[k]! (elt k : Equiv.Perm (Fin n))) ∧
      (∀ g : H, pos g < T.size) ∧ (∀ g : H, TabRep T[pos g]! (g : Equiv.Perm (Fin n))) ∧
      (∀ g : H, elt (pos g) = g) ∧ (∀ k < T.size, pos (elt k) = k) ∧
      (∀ (g : H) k, k < T.size → TabRep T[k]! (g : Equiv.Perm (Fin n)) → pos g = k) := by
  classical
  have helt : ∀ k < T.size, ∃ g : H, TabRep T[k]! (g : Equiv.Perm (Fin n)) := fun k hk => by
    obtain ⟨g, hg, hr⟩ := hH.exists_elt hk
    exact ⟨⟨g, hg⟩, hr⟩
  have hpos : ∀ g : H, ∃ k < T.size, TabRep T[k]! (g : Equiv.Perm (Fin n)) :=
    fun g => hH.exists_pos g.2
  let elt : ℕ → H := fun k => if hk : k < T.size then (helt k hk).choose else 1
  have elt_rep : ∀ k < T.size, TabRep T[k]! (elt k : Equiv.Perm (Fin n)) := fun k hk => by
    simp only [elt, hk, ↓reduceDIte]
    exact (helt k hk).choose_spec
  let pos : H → ℕ := fun g => (hpos g).choose
  have pos_lt : ∀ g : H, pos g < T.size := fun g => (hpos g).choose_spec.1
  have pos_rep : ∀ g : H, TabRep T[pos g]! (g : Equiv.Perm (Fin n)) :=
    fun g => (hpos g).choose_spec.2
  have pos_eq : ∀ (g : H) k, k < T.size → TabRep T[k]! (g : Equiv.Perm (Fin n)) → pos g = k :=
    fun g k hk hr => hH.pos_unique (pos_lt g) hk (pos_rep g) hr
  exact ⟨elt, pos, elt_rep, pos_lt, pos_rep,
    fun g => Subtype.ext ((elt_rep _ (pos_lt g)).perm_eq (pos_rep g)),
    fun k hk => pos_eq _ k hk (elt_rep k hk), pos_eq⟩

theorem card_pos_filter {T : Array Tab} {pos : H → ℕ} {elt : ℕ → H}
    (pos_lt : ∀ g : H, pos g < T.size) (elt_pos : ∀ g : H, elt (pos g) = g)
    (pos_elt : ∀ k < T.size, pos (elt k) = k) (f : ℕ → Bool) :
    Nat.card {g : H // f (pos g) = true} = countBelow T.size f := by
  classical
  rw [countBelow_eq]
  have e : {g : H // f (pos g) = true} ≃ ((Finset.range T.size).filter fun k => f k = true) :=
    { toFun := fun g => ⟨pos g.1, by simpa using ⟨pos_lt g.1, g.2⟩⟩
      invFun := fun k => ⟨elt k.1, by
        have hk := k.2
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        rw [pos_elt _ hk.1]
        exact hk.2⟩
      left_inv := fun g => Subtype.ext (elt_pos g.1)
      right_inv := fun k => by
        have hk := k.2
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        exact Subtype.ext (pos_elt _ hk.1) }
  rw [Nat.card_congr e, Nat.card_eq_finsetCard]

theorem classOK_spec {T inv : Array Tab} {C : ClassData} {sizes : Array ℕ}
    (h : classOK n T inv C sizes = true) :
    invsOK n T inv = true ∧
      (∀ k < T.size, ∀ a < T.size,
        found (indexOf T) T (conjTab n T[a]! inv[a]! T[k]!) = true ∧
          C.lab[posOf (indexOf T) T (conjTab n T[a]! inv[a]! T[k]!)]! = C.lab[k]!) ∧
      (∀ l < sizes.size, C.reps[l]! < T.size ∧ C.lab[C.reps[l]!]! = l) ∧
      (∀ k < T.size, C.lab[k]! < sizes.size ∧ C.wit[k]! < T.size ∧
        conjTab n T[C.wit[k]!]! inv[C.wit[k]!]! T[C.reps[C.lab[k]!]!]! = T[k]!) ∧
      (∀ l < sizes.size, countBelow T.size (fun k => C.lab[k]! == l) = sizes[l]!) ∧
      0 < T.size ∧ T[0]! = idTab n ∧ C.lab[0]! = 0 := by
  simp only [classOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_eq_true,
    and_assoc] at h
  obtain ⟨h1, -, h3, -, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, fun k hk a ha => h3 k hk a ha, h5, h6, h7, h8, h9, h10⟩

theorem classes_of_classOK {T inv : Array Tab} {C : ClassData} {sizes : Array ℕ}
    (hH : Enumerates H T.toList) (h : classOK n T inv C sizes = true) :
    ∃ e : Fin sizes.size ≃ ConjClasses H, (∀ l, Nat.card (e l).carrier = sizes[l.val]!) ∧
      ∃ l₀ : Fin sizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 := by
  classical
  obtain ⟨hinv, hconj, hreps, hwit, hcount, hm, hT0, hlab0⟩ := classOK_spec h
  obtain ⟨elt, pos, elt_rep, pos_lt, pos_rep, elt_pos, pos_elt, pos_eq⟩ := exists_elt_pos hH
  have inv_rep : ∀ g : H, TabRep inv[pos g]! ((g : Equiv.Perm (Fin n))⁻¹) :=
    fun g => invsOK_spec hinv (pos_lt g) (pos_rep g)
  let labG : H → ℕ := fun g => C.lab[pos g]!
  have hlab_conj : ∀ c x : H, labG (c * x * c⁻¹) = labG x := by
    intro c x
    obtain ⟨hf, hl⟩ := hconj (pos x) (pos_lt x) (pos c) (pos_lt c)
    have hrep : TabRep (conjTab n T[pos c]! inv[pos c]! T[pos x]!)
        ((c * x * c⁻¹ : H) : Equiv.Perm (Fin n)) := by
      simpa using (pos_rep c).conjTab (pos_rep x) (inv_rep c)
    obtain ⟨hp, hpe⟩ := found_spec hf
    have hposc : pos (c * x * c⁻¹) = posOf (indexOf T) T (conjTab n T[pos c]! inv[pos c]! T[pos x]!)
        := pos_eq _ _ hp (by rw [hpe]; exact hrep)
    simp only [labG]
    rw [hposc, hl]
  have hconj_lab : ∀ x y : H, IsConj x y → labG x = labG y := by
    intro x y hxy
    obtain ⟨c, hc⟩ := isConj_iff.1 hxy
    rw [← hc, hlab_conj]
  have hlab_lt : ∀ x : H, labG x < sizes.size := fun x => (hwit _ (pos_lt x)).1
  let rep : ℕ → H := fun l => elt (C.reps[l]!)
  have hrep_lab : ∀ l < sizes.size, labG (rep l) = l := fun l hl => by
    simp only [labG, rep]
    rw [pos_elt _ (hreps l hl).1]
    exact (hreps l hl).2
  have hconj_rep : ∀ x : H, IsConj (rep (labG x)) x := by
    intro x
    obtain ⟨hl, hw, he⟩ := hwit _ (pos_lt x)
    have hr := (elt_rep _ hw).conjTab (elt_rep _ (hreps _ hl).1)
      (invsOK_spec hinv hw (elt_rep _ hw))
    rw [he] at hr
    refine isConj_iff.2 ⟨elt (C.wit[pos x]!), Subtype.ext ?_⟩
    have := hr.perm_eq (pos_rep x)
    simpa [rep, labG] using this
  have hlab_conj' : ∀ x y : H, labG x = labG y → IsConj x y := fun x y hxy =>
    (hconj_rep x).symm.trans (hxy ▸ hconj_rep y)
  let e : Fin sizes.size → ConjClasses H := fun l => ConjClasses.mk (rep l.val)
  have he_inj : Function.Injective e := by
    intro l l' hll
    have := hconj_lab _ _ (ConjClasses.mk_eq_mk_iff_isConj.1 hll)
    rw [hrep_lab _ l.2, hrep_lab _ l'.2] at this
    exact Fin.ext this
  have he_surj : Function.Surjective e := by
    intro c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    exact ⟨⟨labG x, hlab_lt x⟩, ConjClasses.mk_eq_mk_iff_isConj.2 (hconj_rep x)⟩
  have hpos1 : pos 1 = 0 := pos_eq 1 0 hm (by rw [hT0]; simpa using TabRep.idTab)
  have hsize : 0 < sizes.size := by
    have := (hwit 0 hm).1
    rwa [hlab0] at this
  refine ⟨Equiv.ofBijective e ⟨he_inj, he_surj⟩, fun l => ?_, ⟨0, hsize⟩, rfl, ?_⟩
  · have hset : ∀ x : H, x ∈ (e l).carrier ↔ (C.lab[pos x]! == l.val) = true := by
      intro x
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, beq_iff_eq]
      constructor
      · intro hx
        have := hconj_lab _ _ hx
        rwa [hrep_lab _ l.2] at this
      · intro hx
        apply hlab_conj'
        rw [hrep_lab _ l.2]
        exact hx
    have hcard := card_pos_filter pos_lt elt_pos pos_elt (fun k => C.lab[k]! == l.val)
    rw [hcount _ l.2] at hcard
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hset)
  · show ConjClasses.mk (rep 0) = ConjClasses.mk 1
    rw [ConjClasses.mk_eq_mk_iff_isConj]
    apply hlab_conj'
    rw [hrep_lab _ hsize]
    simp only [labG, hpos1, hlab0]

theorem isSimpleGroup_of_classes {G : Type*} [Group G] [Finite G] {c : ℕ}
    (e : Fin c ≃ ConjClasses G) (s : Fin c → ℕ) (hs : ∀ l, Nat.card (e l).carrier = s l)
    (l₀ : Fin c) (hl₀ : e l₀ = ConjClasses.mk 1) (hG : 1 < Nat.card G)
    (hsums : ∀ U : Finset (Fin c), l₀ ∈ U → (∑ l ∈ U, s l) ∣ Nat.card G →
      U = {l₀} ∨ U = Finset.univ) :
    IsSimpleGroup G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hG
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  let cls : G → Fin c := fun g => e.symm (ConjClasses.mk g)
  have hcls : ∀ g l, cls g = l ↔ ConjClasses.mk g = e l := fun g l =>
    Equiv.symm_apply_eq e
  let U : Finset (Fin c) := Finset.univ.filter fun l => ∃ g, cls g = l ∧ g ∈ N
  have hmemU : ∀ g, g ∈ N ↔ cls g ∈ U := by
    intro g
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hg => ⟨g, rfl, hg⟩, ?_⟩
    rintro ⟨g', hg', hg'N⟩
    have hmk : ConjClasses.mk g' = ConjClasses.mk g := by
      rw [(hcls g' _).1 hg', ← (hcls g _).1 rfl]
    obtain ⟨d, hd⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hmk)
    rw [← hd]
    exact hN.conj_mem _ hg'N d
  have hfiber : ∀ l, (Finset.univ.filter fun g => cls g = l).card = s l := by
    intro l
    rw [← hs l, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcls,
      ConjClasses.mem_carrier_iff_mk_eq]
  have hcardN : Nat.card N = ∑ l ∈ U, s l := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_eq_sum_card_fiberwise (f := cls) (t := U)
      (fun g hg => (hmemU g).1 (by simpa using hg))]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← hfiber l]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨(hmemU g).2 (h ▸ hl), h⟩
  have hl₀U : l₀ ∈ U := by
    rw [← (hcls 1 l₀).2 hl₀.symm]
    exact (hmemU 1).1 N.one_mem
  rcases hsums U hl₀U (hcardN ▸ Subgroup.card_subgroup_dvd_card N) with hU | hU
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have h1 := (hmemU g).1 hg
    rw [hU, Finset.mem_singleton, hcls, hl₀, ConjClasses.mk_eq_mk_iff_isConj] at h1
    exact isConj_one_right.1 h1.symm
  · right
    rw [Subgroup.eq_top_iff']
    intro g
    rw [hmemU, hU]
    exact Finset.mem_univ _

theorem derivedOK_spec {T inv D : Array Tab} {W : Array (ℕ × ℕ × ℕ × ℕ)}
    (h : derivedOK n T inv D W = true) :
    invsOK n T inv = true ∧ (∀ a < D.size, posOf (indexOf D) D D[a]! = a) ∧
      found (indexOf D) D (idTab n) = true ∧
      (∀ a < D.size, ∀ b < D.size, found (indexOf D) D (comp n D[a]! D[b]!) = true) ∧
      (∀ a < D.size, found (indexOf D) D (invTab n D[a]!) = true ∧
        comp n (invTab n D[a]!) D[a]! = idTab n) ∧
      (∀ a < T.size, ∀ b < T.size,
        found (indexOf D) D (commTab n T[a]! T[b]! inv[a]! inv[b]!) = true) ∧
      (∀ a < D.size, W[a]!.1 < T.size ∧ W[a]!.2.1 < T.size ∧ W[a]!.2.2.1 < T.size ∧
        W[a]!.2.2.2 < T.size ∧
        D[a]! = comp n (commTab n T[W[a]!.1]! T[W[a]!.2.1]! inv[W[a]!.1]! inv[W[a]!.2.1]!)
          (commTab n T[W[a]!.2.2.1]! T[W[a]!.2.2.2]! inv[W[a]!.2.2.1]! inv[W[a]!.2.2.2]!)) := by
  simp only [derivedOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_eq_true,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h8⟩

theorem enumerates_commutator {T inv D : Array Tab} {W : Array (ℕ × ℕ × ℕ × ℕ)}
    (hH : Enumerates H T.toList) (h : derivedOK n T inv D W = true) :
    Enumerates ⁅H, H⁆ D.toList := by
  classical
  obtain ⟨hinv, hposD, hid, hmul, hinvD, hcomm, hW⟩ := derivedOK_spec h
  obtain ⟨elt, pos, elt_rep, pos_lt, pos_rep, elt_pos, -, -⟩ := exists_elt_pos hH
  have inv_rep : ∀ k < T.size, TabRep inv[k]! ((elt k : Equiv.Perm (Fin n))⁻¹) :=
    fun k hk => invsOK_spec hinv hk (elt_rep k hk)
  have comm_rep : ∀ a < T.size, ∀ b < T.size, TabRep (commTab n T[a]! T[b]! inv[a]! inv[b]!)
      ⁅(elt a : Equiv.Perm (Fin n)), (elt b : Equiv.Perm (Fin n))⁆ := fun a ha b hb =>
    TabRep.commTab (elt_rep a ha) (elt_rep b hb) (inv_rep a ha) (inv_rep b hb)
  have soundD : ∀ a < D.size, ∃ g ∈ ⁅H, H⁆, TabRep D[a]! g := by
    intro a ha
    obtain ⟨h1, h2, h3, h4, he⟩ := hW a ha
    refine ⟨_, Subgroup.mul_mem _
      (Subgroup.commutator_mem_commutator (elt W[a]!.1).2 (elt W[a]!.2.1).2)
      (Subgroup.commutator_mem_commutator (elt W[a]!.2.2.1).2 (elt W[a]!.2.2.2).2), ?_⟩
    rw [he]
    exact (comm_rep _ h1 _ h2).comp (comm_rep _ h3 _ h4)
  have hrepD : ∀ x, found (indexOf D) D x = true → ∃ a < D.size, D[a]! = x := fun x hx =>
    ⟨_, (found_spec hx).1, (found_spec hx).2⟩
  let Dsub : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {g | ∃ a < D.size, TabRep D[a]! g}
      one_mem' := by
        obtain ⟨a, ha, he⟩ := hrepD _ hid
        exact ⟨a, ha, he ▸ TabRep.idTab⟩
      mul_mem' := by
        rintro g g' ⟨a, ha, hga⟩ ⟨b, hb, hgb⟩
        obtain ⟨p, hp, he⟩ := hrepD _ (hmul a ha b hb)
        exact ⟨p, hp, he ▸ hga.comp hgb⟩
      inv_mem' := by
        rintro g ⟨a, ha, hga⟩
        obtain ⟨hf, hc⟩ := hinvD a ha
        obtain ⟨p, hp, he⟩ := hrepD _ hf
        obtain ⟨k, -, hk⟩ := soundD p hp
        have h1 : k * g = 1 := ((hk.comp hga).eq_iff TabRep.idTab).1 (by rw [he, hc])
        exact ⟨p, hp, by rwa [eq_inv_of_mul_eq_one_left h1] at hk⟩ }
  have hle : ⁅H, H⁆ ≤ Dsub := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have ex := elt_pos ⟨x, hx⟩
    have ey := elt_pos ⟨y, hy⟩
    obtain ⟨p, hp, he⟩ := hrepD _ (hcomm _ (pos_lt ⟨x, hx⟩) _ (pos_lt ⟨y, hy⟩))
    refine ⟨p, hp, ?_⟩
    rw [he]
    have := comm_rep _ (pos_lt ⟨x, hx⟩) _ (pos_lt ⟨y, hy⟩)
    rwa [ex, ey] at this
  refine ⟨fun t ht => ?_, fun g hg => ?_, nodup_of_posOf hposD⟩
  · obtain ⟨a, ha, rfl⟩ := exists_getElem!_of_mem ht
    exact soundD a ha
  · obtain ⟨a, ha, hr⟩ := hle hg
    exact ⟨_, getElem!_mem ha, hr⟩

@[expose] def ambientDerived {G : Type*} [Group G] (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | k + 1 => ⁅ambientDerived H k, ambientDerived H k⁆

theorem map_derivedSeries {G : Type*} [Group G] (H : Subgroup G) (k : ℕ) :
    (derivedSeries H k).map H.subtype = ambientDerived H k := by
  induction k with
  | zero =>
    rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  | succ k ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator, ih]
    rfl

theorem card_derivedSeries {G : Type*} [Group G] (H : Subgroup G) (k : ℕ) :
    Nat.card (derivedSeries H k) = Nat.card (ambientDerived H k) := by
  rw [← map_derivedSeries, Subgroup.card_map_of_injective H.subtype_injective]

end CFSG.ComponentClassification.PSL3Four
