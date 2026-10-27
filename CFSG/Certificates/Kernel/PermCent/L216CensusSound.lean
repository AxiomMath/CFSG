module

public import Certificates.Data.Kernel.PermCent.L216Census
public import Certificates.Data.Seitz77Sec27L216
public import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

namespace CFSG.Certificates.Kernel.PkCV.L216C

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates
  CFSG.Sporadic.Schreier

@[expose] noncomputable def censusL (EP L : List (CV 17)) (a b : Nat) : Bool :=
  L.all fun t => !(decide (t * t = 1) && decide (t ≠ 1)) ||
    (if t ∈ EP then (centL EP t).length == a else (centL EP t).length == b)

theorem census_eq :
    Certificates.Seitz77Sec27.l216CensusCheck = censusL (elemsC QP) (elemsC QA) 16 60 := by
  rw [Certificates.Seitz77Sec27.l216CensusCheck.eq_1, censusL.eq_1, elemsT_eq_elemsC QA,
    elemsT_eq_elemsC QP]
  simp only [List.all_map, Function.comp_def, Certificates.Seitz77Sec27.l216CommCount.eq_1, cent_C,
    List.length_map, ev_mul', one_eq_ev, ne_eq, ev_eq_iff, mem_map_ev]

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictLN_eq (l : List Nat) (k : List Nat → Bool) : strictLN l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | zero => exact ih (fun t => k (0 :: t))
    | succ m => exact ih (fun t => k (m.succ :: t))

theorem memN_iff (x : Nat) (L : List Nat) : memN x L = true ↔ x ∈ L := by
  induction L with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | cons a t ih =>
    change Bool.rec (motive := fun _ => Bool) (memN x t) true (Nat.beq a x) = true ↔ x ∈ a :: t
    rw [List.mem_cons]
    cases h : Nat.beq a x
    · change memN x t = true ↔ _
      rw [ih]
      have hne : x ≠ a := fun e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h
      exact ⟨Or.inr, fun h' => h'.resolve_left hne⟩
    · change true = true ↔ _
      exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h).symm, fun _ => rfl⟩

theorem all_of_blocks {α : Type*} (f : α → Bool) (c : Nat) :
    ∀ (k : Nat) (L : List α), (∀ j < k, ((L.drop (j * c)).take c).all f = true) →
      (L.drop (k * c)).all f = true → L.all f = true
  | 0, L, _, ht => by simpa using ht
  | k + 1, L, hb, ht => by
    rw [← List.take_append_drop c L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using hb 0 (Nat.succ_pos k), all_of_blocks f c k (L.drop c) ?_ ?_⟩
    · intro j hj
      have h := hb (j + 1) (by omega)
      rwa [List.drop_drop, show c + j * c = (j + 1) * c by rw [Nat.succ_mul, Nat.add_comm]]
    · rwa [List.drop_drop, show c + k * c = (k + 1) * c by rw [Nat.succ_mul, Nat.add_comm]]

theorem clsOK_of_blocks (k : Nat) (hb : ∀ j < k, clsBlk 2040 j = true)
    (ht : clsOK ((elemsC QA).drop (k * 2040)) (clsV r1) (clsV r2) = true) :
    clsOK (elemsC QA) (clsV r1) (clsV r2) = true := by
  refine all_of_blocks _ 2040 k (elemsC QA) (fun j hj => ?_) ht
  have h := hb j hj
  unfold clsBlk at h
  rw [strictLN_eq, strictLN_eq] at h
  exact h

theorem centL_conj (hQ : ValidSchreier QP) {g : CV 17} (hg : g ∈ elemsC QP) (r : CV 17) :
    (centL (elemsC QP) (g * r * g⁻¹)).length = (centL (elemsC QP) r).length := by
  set L := elemsC QP with hL
  have hg' : g⁻¹ ∈ L := by
    rw [hL, mem_elemsC QP hQ] at hg ⊢
    rw [← ev_inv']
    exact QP.originalSubgroup.inv_mem hg
  have hφ : ∀ x, eq22C x (g * r * g⁻¹) (g * r * g⁻¹) x =
      eq22C (g⁻¹ * x * g⁻¹⁻¹) r r (g⁻¹ * x * g⁻¹⁻¹) := by
    intro x
    rw [eq22C_eq, eq22C_eq, decide_eq_decide]
    constructor
    · intro h
      calc g⁻¹ * x * g⁻¹⁻¹ * r = g⁻¹ * (x * (g * r * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * r * g⁻¹) * x) * g := by rw [h]
        _ = r * (g⁻¹ * x * g⁻¹⁻¹) := by group
    · intro h
      calc x * (g * r * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * r) * g⁻¹ := by group
        _ = g * (r * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
        _ = g * r * g⁻¹ * x := by group
  have hmem : ∀ y, y ∈ L ↔ y ∈ L.map fun z => g⁻¹ * z * g⁻¹⁻¹ := by
    intro y
    rw [List.mem_map]
    constructor
    · intro hy
      exact ⟨g * y * g⁻¹, conj_mem_elemsC QP hQ hg hy, by group⟩
    · rintro ⟨z, hz, rfl⟩
      exact conj_mem_elemsC QP hQ hg' hz
  have hnd : L.Nodup := nodup_elemsC QP hQ
  have hnd' : (L.map fun z => g⁻¹ * z * g⁻¹⁻¹).Nodup :=
    hnd.map fun a b h => by simpa using h
  have hp : (L.map fun z => g⁻¹ * z * g⁻¹⁻¹).Perm L :=
    (List.perm_ext_iff_of_nodup hnd' hnd).2 fun y => (hmem y).symm
  unfold centL
  simp only [hφ]
  rw [← (hp.filter (fun y => eq22C y r r y)).length_eq, List.filter_map, List.length_map]
  rfl

theorem census_of (hQ : ValidSchreier QP) (hc : clsOK (elemsC QA) (clsV r1) (clsV r2) = true)
    (h1 : (centL (elemsC QP) r1).length = 16) (h2 : (centL (elemsC QP) r2).length = 60)
    (m1 : r1 ∈ elemsC QP) (m2 : r2 ∉ elemsC QP) :
    censusL (elemsC QP) (elemsC QA) 16 60 = true := by
  have hinv : ∀ {g : CV 17}, g ∈ elemsC QP → g⁻¹ ∈ elemsC QP := fun {g} hg => by
    rw [mem_elemsC QP hQ] at hg ⊢
    rw [← ev_inv']
    exact QP.originalSubgroup.inv_mem hg
  have key : ∀ (t r : CV 17), t.1 ∈ clsV r → ∃ g ∈ elemsC QP, t = g * r * g⁻¹ := by
    intro t r hr
    obtain ⟨g, hg, e⟩ := List.mem_map.1 hr
    exact ⟨g, hg, Subtype.ext e.symm⟩
  unfold censusL
  unfold clsOK at hc
  rw [List.all_eq_true] at hc ⊢
  intro t ht
  have h := hc t ht
  by_cases hi : t * t = 1 ∧ t ≠ 1
  · obtain ⟨hsq, hne⟩ := hi
    have hp : powOneC t 2 = true := by rw [← sq_fast]; exact decide_eq_true hsq
    rw [hp, Bool.not_true, Bool.false_or, decide_eq_false hne, Bool.false_or, strictB_eq,
      Bool.or_eq_true, memN_iff, memN_iff] at h
    have hd : (decide (t * t = 1) && decide (t ≠ 1)) = true := by
      rw [decide_eq_true hsq, decide_eq_true hne]
      rfl
    rw [hd, Bool.not_true, Bool.false_or]
    rcases h with h | h
    · obtain ⟨g, hg, rfl⟩ := key t r1 h
      rw [if_pos (conj_mem_elemsC QP hQ hg m1), centL_conj hQ hg, h1]
      rfl
    · obtain ⟨g, hg, rfl⟩ := key t r2 h
      have hn : g * r2 * g⁻¹ ∉ elemsC QP := fun hm => m2 (by
        have h' := conj_mem_elemsC QP hQ (hinv hg) hm
        have e : g⁻¹ * (g * r2 * g⁻¹) * g⁻¹⁻¹ = r2 := by group
        rwa [e] at h')
      rw [if_neg hn, centL_conj hQ hg, h2]
      rfl
  · have hd : (decide (t * t = 1) && decide (t ≠ 1)) = false := by
      rw [← Bool.decide_and]
      exact decide_eq_false hi
    rw [hd]
    rfl

theorem mem_of_memN {r : CV 17} {L : List (CV 17)} (h : memN r.1 (L.map Subtype.val) = true) :
    r ∈ L := by
  obtain ⟨g, hg, e⟩ := List.mem_map.1 ((memN_iff _ _).1 h)
  rwa [← Subtype.ext e]

theorem not_mem_of_memN {r : CV 17} {L : List (CV 17)}
    (h : memN r.1 (L.map Subtype.val) = false) : r ∉ L := fun hr => by
  rw [(memN_iff _ _).2 (List.mem_map.2 ⟨r, hr, rfl⟩)] at h
  exact Bool.noConfusion h

end CFSG.Certificates.Kernel.PkCV.L216C

end
