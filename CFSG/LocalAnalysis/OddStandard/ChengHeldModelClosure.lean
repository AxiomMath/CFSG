module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelBase
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelLoop

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

theorem closure_eq_bfsRun (M : RegModel) (gs : List ℕ) :
    M.closure gs = (bfsRun M.N gs (fun g y => M.m y g) 0).1 := by
  unfold RegModel.closure bfsRun
  rfl

theorem orbitOf_eq_bfsRun (M : RegModel) (maps : List (Array ℕ)) (x : ℕ) :
    M.orbitOf maps x = (bfsRun M.N maps (fun f y => f[y]!) x).2.toList := by
  unfold RegModel.orbitOf bfsRun
  rfl

theorem orbitOf_spec {M : RegModel} (maps : List (Array ℕ)) {x : ℕ} (hx : x < M.N)
    (hmaps : ∀ f ∈ maps, ∀ y < M.N, f[y]! < M.N) :
    (M.orbitOf maps x).Nodup ∧ (∀ z ∈ M.orbitOf maps x, z < M.N) ∧ x ∈ M.orbitOf maps x ∧
      (∀ y ∈ M.orbitOf maps x, ∀ f ∈ maps, f[y]! ∈ M.orbitOf maps x) ∧
      (∀ P : ℕ → Prop, P x → (∀ f ∈ maps, ∀ y, P y → P f[y]!) → ∀ z ∈ M.orbitOf maps x, P z) := by
  rw [orbitOf_eq_bfsRun]
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := bfsRun_spec maps (fun f y => f[y]!) hx hmaps
  exact ⟨h3, h4, h5, h6, h7⟩

theorem closure_subset_of_right_mul {H : Type} [Group H] [Finite H] (S Q : Set H)
    (h1 : (1 : H) ∈ Q) (hS : ∀ q ∈ Q, ∀ a ∈ S, q * a ∈ Q) :
    (Subgroup.closure S : Set H) ⊆ Q := by
  intro k hk
  have key : ∀ x ∈ Subgroup.closure S, ∀ q ∈ Q, q * x ∈ Q := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun q hq => hS q hq x hx
    | one => exact fun q hq => by simpa using hq
    | mul x y _ _ ihx ihy => exact fun q hq => by rw [← mul_assoc]; exact ihy _ (ihx q hq)
    | inv x _ ihx =>
      intro q hq
      have hpow : ∀ n : ℕ, q * x ^ n ∈ Q := by
        intro n
        induction n with
        | zero => simpa using hq
        | succ n ih => rw [pow_succ, ← mul_assoc]; exact ihx _ ih
      have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
        have hpos := orderOf_pos x
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
      rw [hinv]
      exact hpow _
  simpa using key k hk 1 h1

theorem foldl_set_size (l : List ℕ) (init : Array Bool) :
    (l.foldl (fun (bm : Array Bool) c => bm.set! c true) init).size = init.size := by
  induction l generalizing init with
  | nil => rfl
  | cons c l ih => rw [List.foldl_cons, ih, Array.size_set!]

theorem foldl_set_getElem (l : List ℕ) (init : Array Bool) (hl : ∀ c ∈ l, c < init.size) (z : ℕ) :
    (l.foldl (fun (bm : Array Bool) c => bm.set! c true) init)[z]! = true ↔
      init[z]! = true ∨ z ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih (init.set! c true)
      (by simpa only [Array.size_set!] using fun d hd => hl d (List.mem_cons_of_mem _ hd))]
    by_cases hz : z = c
    · subst hz
      rw [Array.getElem!_set!_self _ _ _ (hl z (List.mem_cons_self))]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hz)]
      simp [hz]

theorem mem_elems_iff (B : Array Bool) (a : ℕ) :
    a ∈ RegModel.elems B ↔ a < B.size ∧ B[a]! = true := by
  simp [RegModel.elems]

@[expose] def commBitmap (M : RegModel) (A B : Array Bool) : Array Bool :=
  ((RegModel.elems A).flatMap fun a => (RegModel.elems B).map fun b => M.cm a b).foldl
    (fun (bm : Array Bool) c => bm.set! c true) (Array.replicate M.N false)

theorem commSub_eq (M : RegModel) (A B : Array Bool) :
    M.commSub A B = M.closure (RegModel.elems (commBitmap M A B)) := rfl

theorem commBitmap_size (M : RegModel) (A B : Array Bool) : (commBitmap M A B).size = M.N := by
  rw [commBitmap, foldl_set_size, Array.size_replicate]

namespace Rep

variable {M : RegModel} {H : Type} [Group H]

theorem m_lt_of_lt (R : Rep M H) {a b : ℕ} (ha : a < M.N) (hb : b < M.N) : M.m a b < M.N := by
  obtain ⟨x, rfl⟩ := R.pt_surj a ha
  obtain ⟨y, rfl⟩ := R.pt_surj b hb
  rw [← R.pt_mul]
  exact R.pt_lt _

theorem zero_lt_N (R : Rep M H) : 0 < M.N := by
  have := R.pt_lt 1
  rwa [R.pt_one] at this

theorem closure_size (R : Rep M H) {gs : List ℕ} (hgs : ∀ g ∈ gs, g < M.N) :
    (M.closure gs).size = M.N := by
  rw [closure_eq_bfsRun]
  exact (bfsRun_spec gs (fun g y => M.m y g) (x0 := 0) R.zero_lt_N
    (fun g hg y hy => R.m_lt_of_lt hy (hgs g hg))).1

theorem set_closure (R : Rep M H) {gs : List ℕ} (hgs : ∀ g ∈ gs, g < M.N) :
    R.set (M.closure gs) = (Subgroup.closure {h : H | R.pt h ∈ gs} : Set H) := by
  have := R.finite
  obtain ⟨-, hmem, -, -, h0mem, hclosed, hmin⟩ := bfsRun_spec gs (fun g y => M.m y g) (x0 := 0)
    R.zero_lt_N (fun g hg y hy => R.m_lt_of_lt hy (hgs g hg))
  rw [closure_eq_bfsRun]
  ext h
  rw [R.mem_set, hmem]
  constructor
  · intro hh
    obtain ⟨k, hk, hkh⟩ := hmin (fun z => ∃ k ∈ Subgroup.closure {h : H | R.pt h ∈ gs}, R.pt k = z)
      ⟨1, one_mem _, R.pt_one⟩ (by
        rintro g hg y ⟨k, hk, rfl⟩
        obtain ⟨a, ha⟩ := R.pt_surj g (hgs g hg)
        refine ⟨k * a, mul_mem hk (Subgroup.subset_closure (by simpa [ha] using hg)), ?_⟩
        rw [R.pt_mul, ha]) _ hh
    rw [← R.pt_inj hkh]
    exact hk
  · intro hh
    refine closure_subset_of_right_mul {h : H | R.pt h ∈ gs}
      {h | R.pt h ∈ (bfsRun M.N gs (fun g y => M.m y g) 0).2.toList} ?_ ?_ hh
    · rw [Set.mem_ofPred_eq, R.pt_one]
      exact h0mem
    · intro q hq a ha
      rw [Set.mem_ofPred_eq, R.pt_mul]
      exact hclosed _ hq _ ha

theorem mem_commPts_iff (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N)
    (hB : B.size = M.N) {c : ℕ} :
    c ∈ (RegModel.elems A).flatMap (fun a => (RegModel.elems B).map fun b => M.cm a b) ↔
      ∃ a ∈ R.set A, ∃ b ∈ R.set B, R.pt (a⁻¹ * b⁻¹ * a * b) = c := by
  simp only [List.mem_flatMap, List.mem_map, RegModel.elems, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨a, ⟨ha, haT⟩, b, ⟨hb, hbT⟩, rfl⟩
    obtain ⟨a', rfl⟩ := R.pt_surj a (hA ▸ ha)
    obtain ⟨b', rfl⟩ := R.pt_surj b (hB ▸ hb)
    exact ⟨a', haT, b', hbT, R.pt_cm a' b'⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨R.pt a, ⟨hA ▸ R.pt_lt a, ha⟩, R.pt b, ⟨hB ▸ R.pt_lt b, hb⟩, (R.pt_cm a b).symm⟩

theorem getElem_commBitmap (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N)
    (hB : B.size = M.N) (z : ℕ) :
    (commBitmap M A B)[z]! = true ↔
      ∃ a ∈ R.set A, ∃ b ∈ R.set B, R.pt (a⁻¹ * b⁻¹ * a * b) = z := by
  rw [commBitmap, foldl_set_getElem _ _ (fun c hc => ?_), getElem!_replicate_false,
    ← R.mem_commPts_iff hA hB]
  · simp
  · rw [Array.size_replicate]
    obtain ⟨a, -, b, -, rfl⟩ := (R.mem_commPts_iff hA hB).1 hc
    exact R.pt_lt _

theorem commBitmap_lt (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) (hB : B.size = M.N) :
    ∀ g ∈ RegModel.elems (commBitmap M A B), g < M.N := fun g hg => by
  obtain ⟨a, -, b, -, rfl⟩ := (R.getElem_commBitmap hA hB g).1 ((mem_elems_iff _ g).1 hg).2
  exact R.pt_lt _

theorem commSub_size (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) (hB : B.size = M.N) :
    (M.commSub A B).size = M.N := by
  rw [commSub_eq]
  exact R.closure_size (R.commBitmap_lt hA hB)

theorem set_commSub (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) (hB : B.size = M.N) :
    R.set (M.commSub A B) =
      (Subgroup.closure {c : H | ∃ a ∈ R.set A, ∃ b ∈ R.set B, c = a⁻¹ * b⁻¹ * a * b} : Set H) := by
  have hset : {h : H | R.pt h ∈ RegModel.elems (commBitmap M A B)} =
      {c : H | ∃ a ∈ R.set A, ∃ b ∈ R.set B, c = a⁻¹ * b⁻¹ * a * b} := by
    ext h
    have hlt : R.pt h < (commBitmap M A B).size := by
      rw [commBitmap_size]
      exact R.pt_lt h
    simp only [Set.mem_ofPred_eq, mem_elems_iff, hlt, true_and, R.getElem_commBitmap hA hB]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, ha, b, hb, (R.pt_inj hab).symm⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  rw [commSub_eq, R.set_closure (R.commBitmap_lt hA hB), hset]

end Rep

end CFSG.OddStandard.ChengHeld.Model
