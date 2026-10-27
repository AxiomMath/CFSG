module

public import CFSG.Certificates.Kernel.E7PlaneKit
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KilledPlaneTransport

public noncomputable section

namespace CFSG.KC.E7Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore Finset

@[expose] def gen (W : List (List ℕ)) (l : ℕ) : WeylGroup .E7 :=
  (coxeterSystem .E7).wordProd (toFinWord (W.getD l []))

@[expose] def PlaneGood (p : ℕ) (y : WeylGroup .E7) : Prop :=
  ∀ φ ψ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3, y ∈ charStabilizer φ → y ∈ charStabilizer ψ →
    (∃ α ∈ kernelRoots (φ.prod ψ), 0 < height α ∧ ∑ k ∈ Finset.range p, (y ^ k) • α = 0) ∨
      CyclicTriple .E7 (kernelRoots (φ.prod ψ)) y

@[expose] def PlaneCheckFact (p : ℕ) (y : WeylGroup .E7) : Prop :=
  ∀ f b : Fin Tag.E7.rank → ZMod 3, y ∈ charStabilizer (triChar f) →
    y ∈ charStabilizer (triChar b) →
    (∃ α, IsRoot .E7 α ∧ triPairing f α = 0 ∧ triPairing b α = 0 ∧ 0 < height α ∧
        ∑ k ∈ Finset.range p, (y ^ k) • α = 0) ∨
      ∃ γ : Fin 3 → Fin Tag.E7.rank → ℤ,
        (∀ j, IsRoot .E7 (γ j) ∧ triPairing f (γ j) = 0 ∧ triPairing b (γ j) = 0) ∧
        (∀ α, IsRoot .E7 α → 0 < height α → triPairing f α = 0 → triPairing b α = 0 →
          ∃ j, α = γ j) ∧
        iform (γ 0) (γ 1) = 0 ∧ ∀ j, y • γ j = γ (j + 1) ∨ y • γ j = -γ (j + 1)

@[expose] def SylFacts (p n : ℕ) (W : List (List ℕ)) : Prop :=
  ∃ (y : ℕ → WeylGroup .E7) (d : ℕ → ℕ) (i0 : ℕ), i0 < n ∧ y i0 = 1 ∧
    (∀ i < n, ∀ j < n, y i = y j → i = j) ∧
    (∀ i < n, i ≠ i0 → ∃ q < n, ∃ l < W.length, d i = d q + 1 ∧ y i = gen W l * y q) ∧
    (∀ i < n, ∀ l < W.length, ∃ c < n, y c = gen W l * y i) ∧
    ∀ i < n, y i ^ p = 1 → y i ≠ 1 → PlaneCheckFact p (y i)

theorem roots_length : e7Certificate.roots.length = 126 := rfl

@[expose] def nib (k j : ℕ) : ℕ := e7Certificate.roots.getD k 0 / 16 ^ j % 16

theorem nib_lt (k j : ℕ) : nib k j < 16 := Nat.mod_lt _ (by norm_num)

theorem root_apply (k : ℕ) (j : Fin Tag.E7.rank) :
    e7Certificate.root k j = (nib k j : ℤ) - 8 := rfl

theorem isRoot_root7 {k : ℕ} (hk : k < 126) : IsRoot .E7 (e7Certificate.root k) :=
  RootCertificate.isRoot_root e7Certificate_check k (by rw [roots_length]; exact hk)

theorem root_inj {a b : ℕ} (ha : a < 126) (hb : b < 126)
    (h : e7Certificate.root a = e7Certificate.root b) : a = b := by
  have hn := e7Certificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  exact (List.nodup_map_iff_inj_on List.nodup_range).1 hn a
    (List.mem_range.2 (by rw [roots_length]; exact ha)) b
    (List.mem_range.2 (by rw [roots_length]; exact hb)) (by rw [h])

theorem root_basis (j : Fin Tag.E7.rank) : e7Certificate.root j = Pi.single j 1 := by
  have h := ((RootCertificate.represents_one e7Certificate_check).2 j).2
  rwa [one_smul, List.getD_eq_getElem _ _ (by rw [List.length_range]; exact j.2),
    List.getElem_range] at h

theorem exists_root_idx {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α) :
    ∃ k < 126, e7Certificate.root k = α := by
  obtain ⟨k, hk, e⟩ := RootCertificate.exists_root_eq e7Certificate_check hα
  exact ⟨k, by rw [roots_length] at hk; exact hk, e⟩

theorem sum_E7 {M : Type*} [AddCommMonoid M] (g : Fin Tag.E7.rank → M) :
    ∑ j, g j = g ⟨0, by decide⟩ + g ⟨1, by decide⟩ + g ⟨2, by decide⟩ + g ⟨3, by decide⟩ +
      g ⟨4, by decide⟩ + g ⟨5, by decide⟩ + g ⟨6, by decide⟩ :=
  Fin.sum_univ_seven (M := M) g

theorem vecOf_lt (c : ℕ) : vecOf c < 2 ^ 56 :=
  (orN_spec fun i _ => lt_of_le_of_lt (Nat.and_le_right) (by norm_num)).2

theorem nib_lt8 (k : ℕ) : ∀ i < 7, nib k i < 2 ^ 8 := fun i _ =>
  lt_trans (nib_lt k i) (by norm_num)

theorem nib_add_lt (a b i : ℕ) : nib a i + nib b i < 2 ^ 8 := by
  have := nib_lt a i
  have := nib_lt b i
  norm_num
  omega

theorem vecOf_eq (k : ℕ) : vecOf (e7Certificate.roots.getD k 0) = orN 7 8 (nib k) := by
  unfold vecOf
  congr 1
  funext j
  change (e7Certificate.roots.getD k 0 >>> (4 * j)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem fld_vrt {k : ℕ} (hk : k < 126) :
    fld (vrt e7Certificate.roots) 56 k = orN 7 8 (nib k) := by
  rw [vrt, fld_packL (fun c _ => vecOf_lt c) (by rw [roots_length]; exact hk),
    ← List.getD_eq_getElem _ 0, vecOf_eq]

theorem ln_orN7 {f : ℕ → ℕ} (hf : ∀ i < 7, f i < 2 ^ 8) {j : ℕ} (hj : j < 7) :
    ln (orN 7 8 f) j = f j := by
  rw [ln_eq, orN_digit hf hj]

theorem orN7_add {f g : ℕ → ℕ} (hf : ∀ i < 7, f i < 2 ^ 8) (hg : ∀ i < 7, g i < 2 ^ 8)
    (hfg : ∀ i < 7, f i + g i < 2 ^ 8) :
    orN 7 8 f + orN 7 8 g = orN 7 8 (fun j => f j + g j) := by
  rw [(orN_spec hf).1, (orN_spec hg).1, (orN_spec hfg).1, ← sum_add_distrib]
  simp only [add_mul]

theorem ones8_eq : ones8 = orN 7 8 (fun _ => 1) := by decide

theorem lsum_fact : allN 126 (fun k => Nat.beq (lsum (orN 7 8 (nib k)))
    (nib k 0 + nib k 1 + nib k 2 + nib k 3 + nib k 4 + nib k 5 + nib k 6)) = true := by
  decide +kernel

theorem lsum_nib {k : ℕ} (hk : k < 126) : lsum (orN 7 8 (nib k)) =
    nib k 0 + nib k 1 + nib k 2 + nib k 3 + nib k 4 + nib k 5 + nib k 6 := by
  have h := allN_eq_true.1 lsum_fact k hk
  simp only [Nat.beq_eq] at h
  exact h

theorem height_root (k : ℕ) : height (e7Certificate.root k) =
    (nib k 0 : ℤ) + nib k 1 + nib k 2 + nib k 3 + nib k 4 + nib k 5 + nib k 6 - 56 := by
  rw [height, sum_E7]
  simp only [root_apply]
  ring

theorem vrt_cast {k : ℕ} (hk : k < 126) :
    (fld (vrt e7Certificate.roots) 56 k : ℤ) =
      ∑ j : Fin Tag.E7.rank, (e7Certificate.root k j + 8) * 256 ^ (j : ℕ) := by
  rw [fld_vrt hk, (orN_spec (nib_lt8 k)).1, sum_E7]
  simp only [root_apply, sum_range_succ, sum_range_zero]
  push_cast
  ring

theorem b8_cast : (b8 : ℤ) = ∑ j : Fin Tag.E7.rank, (8 : ℤ) * 256 ^ (j : ℕ) := by
  rw [sum_E7]
  norm_num [b8]

@[expose] def RowRep (X : ℕ) (y : WeylGroup .E7) : Prop :=
  ∀ k < 126, f7 X k < 126 ∧ e7Certificate.root (f7 X k) = y • e7Certificate.root k

@[expose] def KeyRep (t : ℕ) (y : WeylGroup .E7) : Prop :=
  ∀ j < 7, f7 t j < 126 ∧ e7Certificate.root (f7 t j) = y • e7Certificate.root j

theorem f7_mod {X N j : ℕ} (h : 7 * j + 7 ≤ N) : f7 (X % 2 ^ N) j = f7 X j := by
  rw [f7_eq, f7_eq, mod_pow_div_mod h]

theorem land_rowM (X : ℕ) : Nat.land X rowM = X % 2 ^ 882 := land_mask X 882

theorem land_tupM (X : ℕ) : Nat.land X tupM = X % 2 ^ 49 := land_mask X 49

theorem fin7_lt (j : Fin Tag.E7.rank) : (j : ℕ) < 7 := j.2

theorem keyRep_unique {t : ℕ} {y y' : WeylGroup .E7} (h : KeyRep t y) (h' : KeyRep t y') :
    y = y' := by
  refine ext_single fun j => ?_
  have e := (h j (fin7_lt j)).2.symm.trans (h' j (fin7_lt j)).2
  rwa [root_basis] at e

theorem keyRep_of_rowRep {X : ℕ} {y : WeylGroup .E7} (h : RowRep X y) : KeyRep X y :=
  fun j hj => h j (by omega)

theorem rowRep_unique {X : ℕ} {y y' : WeylGroup .E7} (h : RowRep X y) (h' : RowRep X y') :
    y = y' :=
  keyRep_unique (keyRep_of_rowRep h) (keyRep_of_rowRep h')

theorem keyRep_eq {t t' : ℕ} {y : WeylGroup .E7} (h : KeyRep t y) (h' : KeyRep t' y)
    (ht : t < 2 ^ 49) (ht' : t' < 2 ^ 49) : t = t' :=
  eq_of_f7 ht ht' fun j hj => root_inj (h j hj).1 (h' j hj).1 ((h j hj).2.trans (h' j hj).2.symm)

theorem keyRep_mod {X : ℕ} {y : WeylGroup .E7} (h : RowRep X y) : KeyRep (X % 2 ^ 49) y :=
  fun j hj => by
    rw [f7_mod (by omega)]
    exact h j (by omega)

theorem rowRep_mod {X : ℕ} {y : WeylGroup .E7} (h : RowRep (X % 2 ^ 882) y) :
    KeyRep (X % 2 ^ 49) y :=
  fun j hj => by
    have := h j (by omega)
    rw [f7_mod (N := 882) (by omega)] at this
    rw [f7_mod (N := 49) (by omega)]
    exact this

theorem f7_idrow {k : ℕ} (hk : k < 126) : f7 idrow k = k := by
  rw [f7_eq, idrow, orN_digit (fun i hi => by norm_num; omega) hk]

theorem rowRep_idrow : RowRep idrow 1 := fun k hk => by
  rw [f7_idrow hk, one_smul]
  exact ⟨hk, rfl⟩

theorem f7_comp (A B : ℕ) {k : ℕ} (hk : k < 126) : f7 (comp A B) k = f7 A (f7 B k) := by
  rw [f7_eq (comp A B), comp, orN_digit (fun i _ => f7_lt _ _) hk]

theorem comp_lt (A B : ℕ) : comp A B < 2 ^ 882 := by
  have h := (orN_spec (n := 126) (w := 7) (f := fun k => f7 A (f7 B k))
    fun i _ => f7_lt _ _).2
  rwa [show 7 * 126 = 882 by norm_num] at h

theorem compL_eq (A B : ℕ) : compL A B = comp A B := by
  rw [compL, letN_eq, letN_eq]

theorem rowRep_comp {A B : ℕ} {a b : WeylGroup .E7} (hA : RowRep A a) (hB : RowRep B b) :
    RowRep (comp A B) (a * b) := fun k hk => by
  rw [f7_comp A B hk]
  obtain ⟨h1, h2⟩ := hB k hk
  obtain ⟨h3, h4⟩ := hA _ h1
  exact ⟨h3, by rw [h4, h2, mul_smul]⟩

theorem idrow_lt : idrow < 2 ^ 882 := by
  have h := (orN_spec (n := 126) (w := 7) (f := fun k => k) fun i hi => by norm_num; omega).2
  rwa [show 7 * 126 = 882 by norm_num] at h

theorem f7_apT (R t : ℕ) {j : ℕ} (hj : j < 7) : f7 (apT R t) j = f7 R (f7 t j) := by
  rw [f7_eq (apT R t), apT, orN_digit (fun i _ => f7_lt _ _) hj]

theorem apT_lt (R t : ℕ) : apT R t < 2 ^ 49 :=
  (orN_spec (n := 7) (w := 7) fun i _ => f7_lt _ _).2

theorem keyRep_apT {R t : ℕ} {z y : WeylGroup .E7} (hR : RowRep R z) (ht : KeyRep t y) :
    KeyRep (apT R t) (z * y) := fun j hj => by
  rw [f7_apT R t hj]
  obtain ⟨h1, h2⟩ := ht j hj
  obtain ⟨h3, h4⟩ := hR _ h1
  exact ⟨h3, by rw [h4, h2, mul_smul]⟩

theorem powT_succ (row m : ℕ) :
    powT row (m + 1) = Nat.rec (motive := fun _ => ℕ) (Nat.land row tupM)
      (fun _ ih => letN ih fun t => apT row t) m := rfl

theorem keyRep_powT {row : ℕ} {y : WeylGroup .E7} (h : RowRep row y) (m : ℕ) :
    KeyRep (powT row (m + 1)) (y ^ (m + 1)) ∧ powT row (m + 1) < 2 ^ 49 := by
  rw [powT_succ]
  induction m with
  | zero =>
    change KeyRep (Nat.land row tupM) _ ∧ Nat.land row tupM < _
    rw [land_tupM, pow_one]
    exact ⟨keyRep_mod h, Nat.mod_lt _ (by positivity)⟩
  | succ m ih =>
    change KeyRep (letN _ fun t => apT row t) _ ∧ letN _ (fun t => apT row t) < _
    rw [letN_eq, pow_succ']
    exact ⟨keyRep_apT h ih.1, apT_lt _ _⟩

theorem imgt_fact : letB (imgt e7Certificate.table) (fun IM => allN 7 fun i => allN 126 fun k =>
    Nat.beq (f7 (fld IM 882 i) k) (e7Certificate.table.getD k 0 / 256 ^ i % 256)) = true := by
  decide +kernel

theorem rowRep_simple {i : ℕ} (hi : i < 7) :
    RowRep (fld (imgt e7Certificate.table) 882 i) (simple .E7 ⟨i, hi⟩) := fun k hk => by
  have h0 := imgt_fact
  rw [letB_eq] at h0
  have h1 := allN_eq_true.1 h0 i hi
  have h := allN_eq_true.1 h1 k hk
  simp only [Nat.beq_eq] at h
  rw [h]
  obtain ⟨h1, h2⟩ := RootCertificate.image_spec e7Certificate_check
    (by rw [roots_length]; exact hk) ⟨i, hi⟩
  rw [roots_length] at h1
  exact ⟨h1, by rw [simple_smul]; exact h2⟩

theorem rowRep_rowW : ∀ w : List ℕ, (∀ i ∈ w, i < 7) →
    RowRep (rowW (imgt e7Certificate.table) idrow w)
        ((coxeterSystem .E7).wordProd (toFinWord w)) ∧
      rowW (imgt e7Certificate.table) idrow w < 2 ^ 882
  | [], _ => ⟨by
      rw [show toFinWord (τ := .E7) [] = [] from rfl, CoxeterSystem.wordProd_nil]
      exact rowRep_idrow, idrow_lt⟩
  | i :: w, hw => by
    have hi : i < 7 := hw i List.mem_cons_self
    obtain ⟨ih, -⟩ := rowRep_rowW w fun j hj => hw j (List.mem_cons_of_mem i hj)
    have e : toFinWord (τ := .E7) (i :: w) = (⟨i, hi⟩ : Fin Tag.E7.rank) :: toFinWord w := by
      have hi' : i < Tag.E7.rank := hi
      simp [toFinWord, List.filterMap_cons, hi']
    change RowRep (compL _ _) _ ∧ compL _ _ < _
    rw [compL_eq, e, CoxeterSystem.wordProd_cons]
    exact ⟨rowRep_comp (rowRep_simple hi) ih, comp_lt _ _⟩

theorem wordsOK_spec : ∀ W : List (List ℕ), wordsOK W = true → ∀ w ∈ W, ∀ i ∈ w, i < 7
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | w :: W, h => by
    change andB _ (wordsOK W) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro w' hw'
    rcases List.mem_cons.1 hw' with rfl | hw'
    · have key : ∀ v : List ℕ, List.rec (motive := fun _ => Bool) true
          (fun i _ ih' => andB (Nat.blt i 7) ih') v = true → ∀ i ∈ v, i < 7 := by
        intro v
        induction v with
        | nil => exact fun _ i hi => absurd hi List.not_mem_nil
        | cons a v ih =>
          intro hv i hi
          change andB _ _ = true at hv
          rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at hv
          rcases List.mem_cons.1 hi with rfl | hi
          · exact hv.1
          · exact ih hv.2 i hi
      exact key _ h.1
    · exact wordsOK_spec W h.2 w' hw'

theorem orbS_go (VRT row p : ℕ) : ∀ x acc : ℕ,
    Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
      (fun _ ih x acc => letN x fun x => ih (f7 row x) (Nat.add acc (fld VRT 56 x))) p x acc =
      acc + ∑ t ∈ range p, fld VRT 56 ((f7 row)^[t] x) := by
  induction p with
  | zero => intro x acc; simp
  | succ p ih =>
    intro x acc
    change letN x (fun x => Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
      (fun _ ih x acc => letN x fun x => ih (f7 row x) (Nat.add acc (fld VRT 56 x))) p
        (f7 row x) (Nat.add acc (fld VRT 56 x))) = _
    rw [letN_eq, ih, sum_range_succ']
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    change acc + fld VRT 56 x + _ = _
    ring

theorem iterate_rowRep {row : ℕ} {y : WeylGroup .E7} (h : RowRep row y) :
    ∀ t, ∀ k < 126, (f7 row)^[t] k < 126 ∧
      e7Certificate.root ((f7 row)^[t] k) = (y ^ t) • e7Certificate.root k := by
  intro t
  induction t with
  | zero => exact fun k hk => ⟨hk, by simp⟩
  | succ t ih =>
    intro k hk
    obtain ⟨h1, h2⟩ := ih k hk
    rw [Function.iterate_succ_apply']
    obtain ⟨h3, h4⟩ := h _ h1
    exact ⟨h3, by rw [h4, h2, pow_succ', mul_smul]⟩

theorem sum_periodic {M : Type*} [AddCommMonoid M] {φ : ℕ → ℕ} {o x : ℕ}
    (ho : Function.IsPeriodicPt φ o x) (F : ℕ → M) (q : ℕ) :
    ∑ t ∈ range (o * q), F (φ^[t] x) = q • ∑ t ∈ range o, F (φ^[t] x) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih, succ_nsmul]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [add_comm, Function.iterate_add_apply, (ho.mul_const q).eq]

theorem coord_sum_fact : ∀ j : Fin Tag.E7.rank,
    ∑ k ∈ range 126, max (e7Certificate.root k j) 0 ≤ 127 ∧
      ∑ k ∈ range 126, max (-e7Certificate.root k j) 0 ≤ 127 := by
  decide +kernel

theorem sum_distinct_bound {T : Finset ℕ} (hT : T ⊆ range 126) (j : Fin Tag.E7.rank) :
    |∑ k ∈ T, e7Certificate.root k j| ≤ 127 := by
  obtain ⟨h1, h2⟩ := coord_sum_fact j
  rw [abs_le]
  constructor
  · have : ∑ k ∈ T, max (-e7Certificate.root k j) 0 ≤ 127 :=
      le_trans (sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => le_max_right _ _) h2
    have : -∑ k ∈ T, e7Certificate.root k j ≤ ∑ k ∈ T, max (-e7Certificate.root k j) 0 := by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun _ _ => le_max_left _ _
    linarith
  · have : ∑ k ∈ T, max (e7Certificate.root k j) 0 ≤ 127 :=
      le_trans (sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => le_max_right _ _) h1
    have : ∑ k ∈ T, e7Certificate.root k j ≤ ∑ k ∈ T, max (e7Certificate.root k j) 0 :=
      sum_le_sum fun _ _ => le_max_left _ _
    linarith

theorem eq_zero_of_lin {v : Fin Tag.E7.rank → ℤ} (hv : ∀ j, |v j| ≤ 127)
    (h : ∑ j : Fin Tag.E7.rank, v j * 256 ^ (j : ℕ) = 0) : v = 0 := by
  rw [sum_E7] at h
  have h0 := abs_le.1 (hv ⟨0, by decide⟩)
  have h1 := abs_le.1 (hv ⟨1, by decide⟩)
  have h2 := abs_le.1 (hv ⟨2, by decide⟩)
  have h3 := abs_le.1 (hv ⟨3, by decide⟩)
  have h4 := abs_le.1 (hv ⟨4, by decide⟩)
  have h5 := abs_le.1 (hv ⟨5, by decide⟩)
  have h6 := abs_le.1 (hv ⟨6, by decide⟩)
  simp only [Fin.val_mk] at h
  norm_num only at h
  funext j
  match j with
  | ⟨0, _⟩ => simp only [Pi.zero_apply]; omega
  | ⟨1, _⟩ => simp only [Pi.zero_apply]; omega
  | ⟨2, _⟩ => simp only [Pi.zero_apply]; omega
  | ⟨3, _⟩ => simp only [Pi.zero_apply]; omega
  | ⟨4, _⟩ => simp only [Pi.zero_apply]; omega
  | ⟨5, _⟩ => simp only [Pi.zero_apply]; omega
  | ⟨6, _⟩ => simp only [Pi.zero_apply]; omega

theorem lin_sum {ι : Type*} (s : Finset ι) (F : ι → Fin Tag.E7.rank → ℤ) :
    ∑ j : Fin Tag.E7.rank, (∑ t ∈ s, F t) j * 256 ^ (j : ℕ) =
      ∑ t ∈ s, ∑ j : Fin Tag.E7.rank, F t j * 256 ^ (j : ℕ) := by
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.sum_apply, sum_mul]

theorem zorb_sound {row p x : ℕ} {y : WeylGroup .E7} (hrow : RowRep row y) (hyp : y ^ p = 1)
    (hp : 0 < p) (hx : x < 126) (h : zorb (vrt e7Certificate.roots) row p x = true) :
    ∑ t ∈ range p, (y ^ t) • e7Certificate.root x = 0 := by
  rw [zorb, Nat.beq_eq, orbS, orbS_go, zero_add] at h
  change _ = p * b8 at h
  have hit := iterate_rowRep hrow
  have hz : ∑ j : Fin Tag.E7.rank, (∑ t ∈ range p, e7Certificate.root ((f7 row)^[t] x)) j *
      256 ^ (j : ℕ) = 0 := by
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h'
    rw [sum_congr rfl fun t _ => vrt_cast (hit t x hx).1, b8_cast, mul_sum] at h'
    simp only [add_mul, sum_add_distrib] at h'
    rw [sum_const, card_range, nsmul_eq_mul, ← mul_sum] at h'
    have e2 : ∑ i : Fin Tag.E7.rank, (p : ℤ) * (8 * 256 ^ (i : ℕ)) =
        p * (8 * ∑ i : Fin Tag.E7.rank, 256 ^ (i : ℕ)) := by
      rw [mul_sum, mul_sum]
    rw [lin_sum]
    linarith
  set φ := f7 row
  have hsum : ∀ q, ∑ t ∈ range q, (y ^ t) • e7Certificate.root x =
      ∑ t ∈ range q, e7Certificate.root (φ^[t] x) :=
    fun q => sum_congr rfl fun t _ => ((hit t x hx).2).symm
  rw [hsum]
  have hper : Function.IsPeriodicPt φ p x := by
    have := hit p x hx
    rw [hyp, one_smul] at this
    exact root_inj this.1 hx this.2
  set o := Function.minimalPeriod φ x
  have ho : 0 < o := hper.minimalPeriod_pos hp
  obtain ⟨q, hq⟩ := hper.minimalPeriod_dvd
  have hpo := Function.isPeriodicPt_minimalPeriod φ x
  set u := ∑ t ∈ range o, e7Certificate.root (φ^[t] x)
  have hpu : ∑ t ∈ range p, e7Certificate.root (φ^[t] x) = q • u := by
    rw [hq]
    exact sum_periodic hpo _ q
  have hq0 : q ≠ 0 := by
    rintro rfl
    omega
  have hu : ∀ j, |u j| ≤ 127 := by
    intro j
    have hinj : Set.InjOn (fun t => φ^[t] x) (range o) := fun a ha b hb e =>
      Function.iterate_injOn_Iio_minimalPeriod (by simpa using ha) (by simpa using hb) e
    have e : u j = ∑ k ∈ (range o).image (fun t => φ^[t] x), e7Certificate.root k j := by
      rw [sum_image hinj]
      exact Finset.sum_apply _ _ _
    rw [e]
    refine sum_distinct_bound (fun k hk => ?_) j
    obtain ⟨t, -, rfl⟩ := mem_image.1 hk
    exact mem_range.2 (hit t x hx).1
  have hlin : ∑ j : Fin Tag.E7.rank, u j * 256 ^ (j : ℕ) = 0 := by
    rw [hpu] at hz
    simp only [Pi.smul_apply, nsmul_eq_mul, mul_assoc, ← mul_sum] at hz
    exact (mul_eq_zero.1 hz).resolve_left (by exact_mod_cast hq0)
  rw [hpu, eq_zero_of_lin hu hlin, smul_zero]

@[expose] def fv (f : Fin Tag.E7.rank → ZMod 3) (j : ℕ) : ℕ :=
  if h : j < 7 then (f ⟨j, h⟩).val else 0

@[expose] def charN (f : Fin Tag.E7.rank → ZMod 3) : ℕ := ∑ j ∈ range 7, fv f j * 3 ^ j

theorem fv_lt (f : Fin Tag.E7.rank → ZMod 3) (j : ℕ) : fv f j < 3 := by
  unfold fv
  split
  · exact ZMod.val_lt _
  · omega

theorem charN_spec (f : Fin Tag.E7.rank → ZMod 3) :
    charN f < 2187 ∧ ∀ j < 7, charN f / 3 ^ j % 3 = fv f j := by
  have h0 := fv_lt f 0
  have h1 := fv_lt f 1
  have h2 := fv_lt f 2
  have h3 := fv_lt f 3
  have h4 := fv_lt f 4
  have h5 := fv_lt f 5
  have h6 := fv_lt f 6
  simp only [charN, sum_range_succ, sum_range_zero]
  refine ⟨by omega, fun j hj => ?_⟩
  interval_cases j <;> simp <;> omega

theorem triPairing_eq (f : Fin Tag.E7.rank → ZMod 3) (k : ℕ) :
    triPairing f (e7Certificate.root k) =
      ((∑ j ∈ range 7, fv f j * ((nib k j + 1) % 3) : ℕ) : ZMod 3) := by
  rw [triPairing, sum_E7]
  simp only [root_apply, sum_range_succ, sum_range_zero, fv]
  push_cast [ZMod.natCast_mod]
  simp only [ZMod.natCast_zmod_val]
  have e : ∀ z : ZMod 3, z - 8 = z + 1 := fun z => by
    rw [sub_eq_add_neg]
    congr 1
  simp only [e, zero_add]

theorem krt_bit {k r : ℕ} (hk : k < 126) (hr : r < 3) (f : Fin Tag.E7.rank → ZMod 3) :
    (fld (krt (vrt e7Certificate.roots)) 6561 k).testBit (2187 * r + charN f) = true ↔
      (r : ZMod 3) = triPairing f (e7Certificate.root k) := by
  obtain ⟨hN, hd⟩ := charN_spec f
  rw [krt, fld_eq, orN_digit (fun i _ => kq_lt _ le_rfl) hk, testBit_kq, triPairing_eq]
  have hres : ∀ j < 7, res (Nat.add (fld (vrt e7Certificate.roots) 56 k) ones8) j =
      (nib k j + 1) % 3 := fun j hj => by
    change ln _ j % 3 = _
    rw [fld_vrt hk, ones8_eq]
    change ln (orN 7 8 (nib k) + orN 7 8 fun _ => 1) j % 3 = _
    rw [orN7_add (nib_lt8 k) (fun _ _ => by norm_num)
      (fun i _ => by have := nib_lt k i; norm_num; omega),
      ln_orN7 (fun i _ => by have := nib_lt k i; norm_num; omega) hj]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  constructor
  · rintro ⟨r', hr', n', hn', e, hs⟩
    obtain ⟨rfl, rfl⟩ : r = r' ∧ charN f = n' := by omega
    rw [← hs]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [hd j (mem_range.1 hj), hres j (mem_range.1 hj)]
  · intro hs
    refine ⟨r, hr, charN f, hN, rfl, ?_⟩
    rw [hs]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [hd j (mem_range.1 hj), hres j (mem_range.1 hj)]

theorem triPairing_smul_basis {f : Fin Tag.E7.rank → ZMod 3} {y : WeylGroup .E7}
    (hy : y ∈ charStabilizer (triChar f)) (v : Fin Tag.E7.rank → ℤ) :
    triPairing f (y • v) = triPairing f v :=
  Z3.ofAdd_eq_ofAdd_iff.1 (hy v)

theorem raw_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem raw_lor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem raw_xor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
theorem raw_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl
theorem raw_shiftRight (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem raw_add (a b : ℕ) : Nat.add a b = a + b := rfl
theorem raw_mul (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem testBit_one' (i : ℕ) : Nat.testBit 1 i = decide (i = 0) := by
  rw [← pow_zero 2, Nat.testBit_two_pow]
  simp only [eq_comm]

theorem testBit_mask_raw (w b : ℕ) :
    (Nat.sub (Nat.shiftLeft 1 w) 1).testBit b = decide (b < w) := by
  change (1 <<< w - 1).testBit b = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem testBit_full (b : ℕ) : full.testBit b = decide (b < 2187) := testBit_mask_raw 2187 b

theorem testBit_fld (X w i k : ℕ) :
    (fld X w i).testBit k = (decide (k < w) && X.testBit (k + w * i)) := by
  rw [fld_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem testBit_recAnd (X0 : ℕ) (g : ℕ → ℕ) (b : ℕ) : ∀ m,
    (Nat.rec (motive := fun _ => ℕ) X0 (fun j acc => Nat.land acc (g j)) m).testBit b = true ↔
      X0.testBit b = true ∧ ∀ j < m, (g j).testBit b = true
  | 0 => ⟨fun h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩, fun h => h.1⟩
  | m + 1 => by
    change ((Nat.rec (motive := fun _ => ℕ) X0 (fun j acc => Nat.land acc (g j)) m) &&&
      g m).testBit b = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, testBit_recAnd X0 g b m]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨h0, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h1 j hj
      · exact h2
    · rintro ⟨h0, h1⟩
      exact ⟨⟨h0, fun j hj => h1 j (by omega)⟩, h1 m (by omega)⟩

theorem testBit_recOr (g : ℕ → ℕ) (b : ℕ) : ∀ m,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.lor acc (g j)) m).testBit b = true ↔
      ∃ j < m, (g j).testBit b = true
  | 0 => ⟨fun h => by
      change Nat.testBit 0 b = true at h
      rw [Nat.zero_testBit] at h
      exact absurd h (by decide), fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)⟩
  | m + 1 => by
    change ((Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.lor acc (g j)) m) |||
      g m).testBit b = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_recOr g b m]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h

theorem testBit_orN1 {n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2) (k : ℕ) :
    (orN n 1 f).testBit k = true ↔ k < n ∧ f k = 1 := by
  rcases lt_or_ge k n with hk | hk
  · have e := orN_digit (w := 1) (fun i hi => by simpa using hf i hi) hk
    simp only [one_mul, pow_one] at e
    rw [testBit_iff_digit, e]
    simp [hk]
  · have hlt := (orN_spec (w := 1) fun i hi => by simpa using hf i hi).2
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega)
      (by omega)))]
    simp only [Bool.false_eq_true, false_iff, not_and]
    omega

theorem toN_eq_one (b : Bool) : toN b = 1 ↔ b = true := by
  cases b <;> simp [toN]

theorem toN_lt (b : Bool) : toN b < 2 := by
  cases b <;> simp [toN]

theorem isPos_iff (POS k : ℕ) : isPos POS k = true ↔ POS.testBit k = true := by
  change Nat.blt 0 (POS &&& (1 <<< k)) = true ↔ _
  rw [Nat.blt_eq, Nat.one_shiftLeft, Nat.and_two_pow]
  cases POS.testBit k <;> simp

theorem testBit_posm (k : ℕ) : (posm (vrt e7Certificate.roots)).testBit k = true ↔
    k < 126 ∧ 0 < height (e7Certificate.root k) := by
  rw [posm, testBit_orN1 fun i _ => toN_lt _]
  refine and_congr_right fun hk => ?_
  rw [toN_eq_one, Nat.blt_eq, fld_vrt hk, lsum_nib hk, height_root]
  constructor
  · intro h
    push_cast
    omega
  · intro h
    omega

theorem testBit_zmask {row p : ℕ} (k : ℕ) :
    (zmask (vrt e7Certificate.roots) (posm (vrt e7Certificate.roots)) row p).testBit k = true ↔
      k < 126 ∧ 0 < height (e7Certificate.root k) ∧
        zorb (vrt e7Certificate.roots) row p k = true := by
  rw [zmask, testBit_orN1 fun i _ => toN_lt _]
  refine and_congr_right fun hk => ?_
  rw [toN_eq_one, andB_eq, Bool.and_eq_true, isPos_iff, testBit_posm]
  simp [hk]

theorem testBit_flMask (FLs m x : ℕ) :
    (flMask FLs m).testBit x = true ↔ ∃ c < m, fld FLs 12 c = x := by
  rw [flMask, testBit_recOr]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [raw_shiftLeft, Nat.testBit_shiftLeft, testBit_one']
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem testBit_rkf (KRT FLs m : ℕ) {c k : ℕ} (hc : c < m) (hk : k < 126) :
    (rkf KRT FLs m).testBit (126 * c + k) = true ↔
      (fld KRT 6561 k).testBit (fld FLs 12 c) = true := by
  rw [rkf, testBit_recOr]
  constructor
  · rintro ⟨k', hk', h⟩
    rw [letN_eq, testBit_recOr] at h
    obtain ⟨c', hc', h⟩ := h
    simp only [raw_shiftLeft, raw_land, raw_shiftRight, raw_add, raw_mul, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_shiftRight, testBit_one', Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨rfl, rfl⟩ : c = c' ∧ k = k' := by omega
    rwa [h3, add_zero] at h2
  · intro h
    refine ⟨k, hk, ?_⟩
    rw [letN_eq, testBit_recOr]
    refine ⟨c, hc, ?_⟩
    simp only [raw_shiftLeft, raw_land, raw_shiftRight, raw_add, raw_mul, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_shiftRight, testBit_one', Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨le_rfl, by rwa [Nat.sub_self, add_zero], Nat.sub_self _⟩

theorem testBit_fix3 (X n : ℕ) : (fix3 X).testBit n = true ↔
    n < 2187 ∧ ∃ r < 3, X.testBit (2187 * r + n) = true := by
  change ((X ||| (X >>> 2187 ||| X >>> 4374)) &&& full).testBit n = true ↔ _
  rw [Nat.testBit_and, testBit_full, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h | h | h, hn⟩
    · exact ⟨hn, 0, by omega, by simpa using h⟩
    · exact ⟨hn, 1, by omega, by rwa [show 2187 * 1 + n = 2187 + n by omega]⟩
    · exact ⟨hn, 2, by omega, by rwa [show 2187 * 2 + n = 4374 + n by omega]⟩
  · rintro ⟨hn, r, hr, h⟩
    refine ⟨?_, hn⟩
    interval_cases r
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl (by rwa [show 2187 * 1 + n = 2187 + n by omega] at h))
    · exact Or.inr (Or.inr (by rwa [show 2187 * 2 + n = 4374 + n by omega] at h))

theorem fld_kqe (KRT : ℕ) {j : ℕ} (hj : j < 7) : fld (kqe KRT) 6561 j = fld KRT 6561 j := by
  rw [kqe, fld_eq, orN_digit (fun i _ => fld_lt _ _ _) hj]

theorem krt_kill {k : ℕ} (hk : k < 126) (f : Fin Tag.E7.rank → ZMod 3) :
    (fld (krt (vrt e7Certificate.roots)) 6561 k).testBit (charN f) = true ↔
      triPairing f (e7Certificate.root k) = 0 := by
  have h := krt_bit hk (r := 0) (by omega) f
  rw [mul_zero, zero_add, Nat.cast_zero] at h
  rw [h, eq_comm]

theorem fixm_bit {row : ℕ} {y : WeylGroup .E7} (hR : RowRep row y)
    {f : Fin Tag.E7.rank → ZMod 3} (hy : y ∈ charStabilizer (triChar f)) :
    (fixm (krt (vrt e7Certificate.roots)) (kqe (krt (vrt e7Certificate.roots))) row).testBit
      (charN f) = true := by
  obtain ⟨hN, -⟩ := charN_spec f
  rw [fixm, testBit_recAnd]
  refine ⟨by rw [testBit_full]; simpa using hN, fun j hj => ?_⟩
  rw [letN_eq, testBit_fix3]
  refine ⟨hN, (triPairing f (e7Certificate.root j)).val, ZMod.val_lt _, ?_⟩
  obtain ⟨h1, h2⟩ := hR j (by omega)
  rw [raw_land, Nat.testBit_and, Bool.and_eq_true, fld_kqe _ hj, krt_bit h1 (ZMod.val_lt _),
    krt_bit (by omega) (ZMod.val_lt _), ZMod.natCast_zmod_val, h2]
  exact ⟨(triPairing_smul_basis hy _).symm, rfl⟩

theorem fixm_lt {KRT KQE row b : ℕ} (h : (fixm KRT KQE row).testBit b = true) : b < 2187 := by
  rw [fixm, testBit_recAnd, testBit_full] at h
  simpa using h.1

theorem symmetrizedCartan_E7_fact : ∀ p : Fin Tag.E7.rank × Fin Tag.E7.rank,
    Tag.symmetrizedCartan Tag.E7 p.1 p.2 =
      (![![2, 0, -1, 0, 0, 0, 0], ![0, 2, 0, -1, 0, 0, 0], ![-1, 0, 2, -1, 0, 0, 0],
        ![0, -1, -1, 2, -1, 0, 0], ![0, 0, 0, -1, 2, -1, 0], ![0, 0, 0, 0, -1, 2, -1],
        ![0, 0, 0, 0, 0, -1, 2]] : Fin 7 → Fin 7 → ℤ) p.1 p.2 := by
  decide +kernel

theorem dot7_eq (U V : ℕ) : dot7 U V = 0 + ln U 0 * ln V 0 + ln U 1 * ln V 1 + ln U 2 * ln V 2 +
    ln U 3 * ln V 3 + ln U 4 * ln V 4 + ln U 5 * ln V 5 + ln U 6 * ln V 6 := rfl

theorem orthB_sound {a b : ℕ} (ha : a < 126) (hb : b < 126)
    (h : orthB (vrt e7Certificate.roots) a b = true) :
    iform (e7Certificate.root a) (e7Certificate.root b) = 0 := by
  rw [orthB, letB_eq, letB_eq, fld_vrt ha, fld_vrt hb, orthUV, Nat.beq_eq] at h
  have hab := orN7_add (nib_lt8 a) (nib_lt8 b)
    (fun i _ => by have := nib_lt a i; have := nib_lt b i; norm_num; omega)
  have hla : ∀ j, j < 7 → ln (orN 7 8 (nib a)) j = nib a j := fun j hj => ln_orN7 (nib_lt8 a) hj
  have hlb : ∀ j, j < 7 → ln (orN 7 8 (nib b)) j = nib b j := fun j hj => ln_orN7 (nib_lt8 b) hj
  have hlab : ∀ j, j < 7 → ln (orN 7 8 (fun j => nib a j + nib b j)) j = nib a j + nib b j :=
    fun j hj => ln_orN7 (fun i _ => by have := nib_lt a i; have := nib_lt b i; norm_num; omega) hj
  simp only [raw_add, raw_mul, dot7_eq, degS, edgeS, eT, hab, lsum_nib ha, lsum_nib hb] at h
  simp (disch := omega) only [hla, hlb, hlab] at h
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at h'
  have hB : ∀ i j : Fin 7, Tag.symmetrizedCartan Tag.E7 i j =
      (![![2, 0, -1, 0, 0, 0, 0], ![0, 2, 0, -1, 0, 0, 0], ![-1, 0, 2, -1, 0, 0, 0],
        ![0, -1, -1, 2, -1, 0, 0], ![0, 0, 0, -1, 2, -1, 0], ![0, 0, 0, 0, -1, 2, -1],
        ![0, 0, 0, 0, 0, -1, 2]] : Fin 7 → Fin 7 → ℤ) i j := fun i j =>
    symmetrizedCartan_E7_fact (i, j)
  have ra : ∀ j : Fin 7, e7Certificate.root a j = (nib a j : ℤ) - 8 := fun j => rfl
  have rb : ∀ j : Fin 7, e7Certificate.root b j = (nib b j : ℤ) - 8 := fun j => rfl
  change ∑ i : Fin 7, ∑ j : Fin 7, e7Certificate.root a i * Tag.symmetrizedCartan Tag.E7 i j *
    e7Certificate.root b j = 0
  simp [hB, Fin.sum_univ_seven, ra, rb]
  linear_combination h'

theorem two_b8 : Nat.mul 2 b8 = orN 7 8 (fun _ => 16) := by decide

theorem sgnB_sound {row a b : ℕ} (hc : f7 row a < 126) (hb : b < 126)
    (h : sgnB (vrt e7Certificate.roots) row a b = true) :
    e7Certificate.root (f7 row a) = e7Certificate.root b ∨
      e7Certificate.root (f7 row a) = -e7Certificate.root b := by
  rw [sgnB, letB_eq, orB_eq, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · right
    rw [fld_vrt hc, fld_vrt hb, two_b8, raw_add,
      orN7_add (nib_lt8 _) (nib_lt8 _) (fun i _ => nib_add_lt _ _ i)] at h
    have hd : ∀ j < 7, nib (f7 row a) j + nib b j = 16 := fun j hj => by
      rw [← orN_digit (w := 8) (fun i _ => nib_add_lt (f7 row a) b i) hj, h,
        orN_digit (fun i _ => by norm_num) hj]
    funext j
    have := hd j (fin7_lt j)
    rw [Pi.neg_apply, root_apply, root_apply]
    omega

@[expose] def PairGood (p : ℕ) (y : WeylGroup .E7) (f b : Fin Tag.E7.rank → ZMod 3) : Prop :=
  (∃ α, IsRoot .E7 α ∧ triPairing f α = 0 ∧ triPairing b α = 0 ∧ 0 < height α ∧
        ∑ k ∈ Finset.range p, (y ^ k) • α = 0) ∨
      ∃ γ : Fin 3 → Fin Tag.E7.rank → ℤ,
        (∀ j, IsRoot .E7 (γ j) ∧ triPairing f (γ j) = 0 ∧ triPairing b (γ j) = 0) ∧
        (∀ α, IsRoot .E7 α → 0 < height α → triPairing f α = 0 → triPairing b α = 0 →
          ∃ j, α = γ j) ∧
        iform (γ 0) (γ 1) = 0 ∧ ∀ j, y • γ j = γ (j + 1) ∨ y • γ j = -γ (j + 1)

theorem easyB_sound {row p F x : ℕ} {y : WeylGroup .E7} (hR : RowRep row y) (hyp : y ^ p = 1)
    (hp : 0 < p)
    (h : easyB (vrt e7Certificate.roots) (krt (vrt e7Certificate.roots))
      (posm (vrt e7Certificate.roots)) row p F x = true)
    {f b : Fin Tag.E7.rank → ZMod 3} (hf : F.testBit (charN f) = true)
    (hb : F.testBit (charN b) = true) : PairGood p y f b := by
  simp only [easyB, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, isPos_iff,
    testBit_posm] at h
  obtain ⟨hx, ⟨-, hpos⟩, hz, hm⟩ := h
  have kill : ∀ g : Fin Tag.E7.rank → ZMod 3, F.testBit (charN g) = true →
      triPairing g (e7Certificate.root x) = 0 := fun g hg => by
    have e := congrArg (fun z => Nat.testBit z (charN g)) hm
    simp only [raw_land, raw_xor, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, hg,
      testBit_full, Bool.true_and] at e
    rw [← krt_kill hx]
    have hN := (charN_spec g).1
    simp only [hN, decide_true, Bool.and_true] at e
    revert e
    cases (fld (krt (vrt e7Certificate.roots)) 6561 x).testBit (charN g) <;> simp
  exact Or.inl ⟨_, isRoot_root7 hx, kill f hf, kill b hb, hpos, zorb_sound hR hyp hp hx hz⟩

theorem testBit_KB {RKF c d k : ℕ} :
    (Nat.land (Nat.land (fld RKF 126 c) (fld RKF 126 d)) (posm (vrt e7Certificate.roots))).testBit
      k = true ↔ k < 126 ∧ RKF.testBit (126 * c + k) = true ∧
        RKF.testBit (126 * d + k) = true ∧ 0 < height (e7Certificate.root k) := by
  simp only [raw_land, Nat.testBit_and, testBit_fld, Bool.and_eq_true, decide_eq_true_eq,
    testBit_posm]
  rw [add_comm k (126 * c), add_comm k (126 * d)]
  tauto

theorem hardB_sound {row p F H : ℕ} {y : WeylGroup .E7} (hR : RowRep row y) (hyp : y ^ p = 1)
    (hp : 0 < p) (hF : ∀ z, F.testBit z = true → z < 2187)
    (h : hardB (vrt e7Certificate.roots) (krt (vrt e7Certificate.roots))
      (posm (vrt e7Certificate.roots)) row p F H = true)
    {f b : Fin Tag.E7.rank → ZMod 3} (hf : F.testBit (charN f) = true)
    (hb : F.testBit (charN b) = true) : PairGood p y f b := by
  simp only [hardB, letB_eq, andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq,
    allN_eq_true, Nat.blt_eq] at h
  generalize Nat.shiftRight (Nat.shiftRight H 6) (Nat.mul 12 (Nat.land H 63)) = TRI at h
  generalize Nat.shiftRight H 6 = FLs at h
  generalize Nat.land H 63 = m at h
  obtain ⟨hfl, hall⟩ := h
  have hidx : ∀ g : Fin Tag.E7.rank → ZMod 3, F.testBit (charN g) = true →
      ∃ c < m, fld FLs 12 c = charN g := fun g hg => by
    rw [← hfl, testBit_flMask] at hg
    exact hg
  obtain ⟨c, hc, hcf⟩ := hidx f hf
  obtain ⟨d, hd, hdb⟩ := hidx b hb
  set KRT := krt (vrt e7Certificate.roots)
  set RKF := rkf KRT FLs m
  have hKB : ∀ k, (Nat.land (Nat.land (fld RKF 126 c) (fld RKF 126 d))
      (posm (vrt e7Certificate.roots))).testBit k = true ↔ k < 126 ∧
        triPairing f (e7Certificate.root k) = 0 ∧ triPairing b (e7Certificate.root k) = 0 ∧
        0 < height (e7Certificate.root k) := fun k => by
    rw [testBit_KB]
    constructor
    · rintro ⟨hk, h1, h2, h3⟩
      rw [testBit_rkf KRT FLs m hc hk, hcf, krt_kill hk] at h1
      rw [testBit_rkf KRT FLs m hd hk, hdb, krt_kill hk] at h2
      exact ⟨hk, h1, h2, h3⟩
    · rintro ⟨hk, h1, h2, h3⟩
      refine ⟨hk, ?_, ?_, h3⟩
      · rw [testBit_rkf KRT FLs m hc hk, hcf, krt_kill hk]
        exact h1
      · rw [testBit_rkf KRT FLs m hd hk, hdb, krt_kill hk]
        exact h2
  rcases hall c hc d hd with h0 | htri
  ·
    left
    obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero (show Nat.land (Nat.land (Nat.land
      (fld RKF 126 c) (fld RKF 126 d)) (posm (vrt e7Certificate.roots)))
      (zmask (vrt e7Certificate.roots) (posm (vrt e7Certificate.roots)) row p) ≠ 0 by omega)
    rw [raw_land, Nat.testBit_and, Bool.and_eq_true, hKB, testBit_zmask] at hk
    obtain ⟨⟨hk1, h1, h2, h3⟩, -, -, hz⟩ := hk
    exact ⟨_, isRoot_root7 hk1, h1, h2, h3, zorb_sound hR hyp hp hk1 hz⟩
  ·
    right
    rw [triB, letB_eq, letB_eq, letB_eq, andB_eq, andB_eq, andB_eq, andB_eq] at htri
    simp only [Bool.and_eq_true, Nat.beq_eq] at htri
    generalize fld TRI 21 (Nat.add (Nat.mul c m) d) = T at htri
    obtain ⟨hKBe, horth, hs0, hs1, hs2⟩ := htri
    have hmem : ∀ k, (Nat.land (Nat.land (fld RKF 126 c) (fld RKF 126 d))
        (posm (vrt e7Certificate.roots))).testBit k = true ↔
          k = f7 T 0 ∨ k = f7 T 1 ∨ k = f7 T 2 := fun k => by
      rw [hKBe]
      simp only [raw_lor, raw_shiftLeft, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hg : ∀ k, k = f7 T 0 ∨ k = f7 T 1 ∨ k = f7 T 2 → k < 126 ∧
        triPairing f (e7Certificate.root k) = 0 ∧ triPairing b (e7Certificate.root k) = 0 ∧
        0 < height (e7Certificate.root k) := fun k hk => (hKB k).1 ((hmem k).2 hk)
    have g0 := hg _ (Or.inl rfl)
    have g1 := hg _ (Or.inr (Or.inl rfl))
    have g2 := hg _ (Or.inr (Or.inr rfl))
    have hsgn : ∀ {a a' : ℕ}, a < 126 → a' < 126 →
        sgnB (vrt e7Certificate.roots) row a a' = true →
        y • e7Certificate.root a = e7Certificate.root a' ∨
          y • e7Certificate.root a = -e7Certificate.root a' := fun ha ha' hs => by
      rw [← (hR _ ha).2]
      exact sgnB_sound (hR _ ha).1 ha' hs
    refine ⟨![e7Certificate.root (f7 T 0), e7Certificate.root (f7 T 1),
      e7Certificate.root (f7 T 2)], fun j => ?_, fun α hα hpos hfα hbα => ?_,
      orthB_sound g0.1 g1.1 horth, fun j => ?_⟩
    · fin_cases j
      · exact ⟨isRoot_root7 g0.1, g0.2.1, g0.2.2.1⟩
      · exact ⟨isRoot_root7 g1.1, g1.2.1, g1.2.2.1⟩
      · exact ⟨isRoot_root7 g2.1, g2.2.1, g2.2.2.1⟩
    · obtain ⟨k, hk, rfl⟩ := exists_root_idx hα
      rcases (hmem k).1 ((hKB k).2 ⟨hk, hfα, hbα, hpos⟩) with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · fin_cases j
      · exact hsgn g0.1 g1.1 hs0
      · exact hsgn g1.1 g2.1 hs1
      · exact hsgn g2.1 g0.1 hs2

theorem impB_true (a b : Bool) : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [impB]

theorem notB_true (a : Bool) : notB a = true ↔ ¬a = true := by
  cases a <;> simp [notB]

theorem ifB_true (c t e : Bool) :
    ifB c t e = true ↔ if c = true then t = true else e = true := by
  cases c <;> simp [ifB]

theorem mod_882_49 (x : ℕ) : x % 2 ^ 882 % 2 ^ 49 = x % 2 ^ 49 :=
  Nat.mod_mod_of_dvd x (pow_dvd_pow 2 (by norm_num))

theorem walkB_spec {VRT KRT KQE POS GT RT KT DT ID p n i0 ng : ℕ} : ∀ (R : List ℕ) (i prev : ℕ),
    walkB VRT KRT KQE POS GT RT KT DT ID p n i0 ng R i prev = true →
      i + R.length = n ∧ ∀ j < R.length, recB VRT KRT KQE POS GT RT KT DT ID p n i0 ng (i + j)
        (if j = 0 then prev else Nat.land (R.getD (j - 1) 0) tupM) (R.getD j 0) = true
  | [], i, prev, h => by
    change Nat.beq i n = true at h
    rw [Nat.beq_eq] at h
    exact ⟨by simpa using h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | r :: R, i, prev, h => by
    change andB (recB VRT KRT KQE POS GT RT KT DT ID p n i0 ng i prev r)
      (letB (Nat.succ i) fun i' => walkB VRT KRT KQE POS GT RT KT DT ID p n i0 ng R i'
        (Nat.land r tupM)) = true at h
    rw [andB_eq, letB_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨e, ih⟩ := walkB_spec R _ _ h2
    refine ⟨by rw [List.length_cons]; omega, fun j hj => ?_⟩
    cases j with
    | zero => simpa using h1
    | succ j =>
      have := ih j (by rw [List.length_cons] at hj; omega)
      have e' : i + (j + 1) = Nat.succ i + j := by omega
      rw [e']
      cases j with
      | zero => simpa using this
      | succ j => simpa using this

theorem sylK_facts {p n i0 : ℕ} {W : List (List ℕ)} {R : List ℕ} (hp : 0 < p)
    (h : sylK e7Certificate.roots e7Certificate.table p n i0 W R = true) : SylFacts p n W := by
  simp only [sylK, letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, lenL_eq] at h
  obtain ⟨hW, hi0, -, hwalk⟩ := h
  obtain ⟨hlen, hrec⟩ := walkB_spec R 0 0 hwalk
  rw [zero_add] at hlen
  subst hlen
  have hWl := wordsOK_spec W hW
  set GT := packL 882 (rowW (imgt e7Certificate.table) idrow) W with hGTdef
  set RT := packL 882 (fun r => Nat.land r rowM) R with hRTdef
  set KT := packL 49 (fun r => Nat.land r tupM) R with hKTdef
  set DT := packL 9 (fun r => Nat.land (Nat.shiftRight r 897) 511) R with hDTdef
  have hRT : ∀ i < R.length, fld RT 882 i = R.getD i 0 % 2 ^ 882 := fun i hi => by
    rw [hRTdef, fld_packL (fun r _ => by rw [land_rowM]; exact Nat.mod_lt _ (by positivity)) hi,
      land_rowM, List.getD_eq_getElem _ 0 hi]
  have hKT : ∀ i < R.length, fld KT 49 i = R.getD i 0 % 2 ^ 49 := fun i hi => by
    rw [hKTdef, fld_packL (fun r _ => by rw [land_tupM]; exact Nat.mod_lt _ (by positivity)) hi,
      land_tupM, List.getD_eq_getElem _ 0 hi]
  have hDT : ∀ i < R.length, fld DT 9 i = Nat.land (Nat.shiftRight (R.getD i 0) 897) 511 :=
    fun i hi => by
      rw [hDTdef, fld_packL (f := fun r => Nat.land (Nat.shiftRight r 897) 511)
        (fun r _ => lt_of_le_of_lt Nat.and_le_right (by norm_num)) hi,
        List.getD_eq_getElem _ 0 hi]
  have hdep : ∀ i q, q < R.length →
      Nat.land (Nat.shiftRight (Nat.shiftRight (R.getD i 0) 882) 15) 511 = fld DT 9 q + 1 →
      Nat.land (Nat.shiftRight (R.getD i 0) 897) 511 =
        Nat.land (Nat.shiftRight (R.getD q 0) 897) 511 + 1 := fun i q hq hd => by
    rw [← hDT _ hq, ← hd, raw_land, raw_land, raw_shiftRight, raw_shiftRight, raw_shiftRight,
      ← Nat.shiftRight_add]
  have hgen : ∀ l < W.length, RowRep (fld GT 882 l) (gen W l) := fun l hl => by
    have hl' : ∀ i ∈ W.getD l [], i < 7 := hWl _ (by
      rw [List.getD_eq_getElem _ _ hl]
      exact List.getElem_mem hl)
    rw [hGTdef, fld_packL (fun w hw => (rowRep_rowW w (hWl w hw)).2) hl,
      ← List.getD_eq_getElem _ [] hl]
    exact (rowRep_rowW _ hl').1
  have hr := fun i (hi : i < R.length) => hrec i hi
  simp only [zero_add, recB, letB_eq, letN_eq, andB_eq, Bool.and_eq_true, ifB_true, impB_true,
    notB_true, Nat.beq_eq, Nat.blt_eq, allN_eq_true, compL_eq, land_rowM, land_tupM,
    mod_882_49, raw_shiftRight] at hr
  set n := R.length
  have hkey : ∀ a b, a < b → b < n → R.getD a 0 % 2 ^ 49 < R.getD b 0 % 2 ^ 49 := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have h1 := (hr (b + 1) hb).1
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h1
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
      · exact lt_trans (ih hab (by omega)) h1
      · exact h1
  have hex : ∀ D, ∀ i < n, Nat.land (Nat.shiftRight (R.getD i 0) 897) 511 = D →
      ∃ y, RowRep (R.getD i 0 % 2 ^ 882) y := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
      intro i hi hD
      obtain ⟨-, htree, -⟩ := hr i hi
      split_ifs at htree with hii
      · rw [htree]
        exact ⟨1, rowRep_idrow⟩
      · obtain ⟨hl, hq, hd, hrow⟩ := htree
        have hd' := hdep i _ hq hd
        obtain ⟨yq, hyq⟩ := ih _ (by omega) _ hq rfl
        rw [hrow, hRT _ hq]
        exact ⟨_, rowRep_comp (hgen _ hl) hyq⟩
  have hex' : ∀ i, ∃ y : WeylGroup .E7, i < n → RowRep (R.getD i 0 % 2 ^ 882) y := fun i => by
    by_cases hi : i < n
    · obtain ⟨y, hy⟩ := hex _ i hi rfl
      exact ⟨y, fun _ => hy⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose y hy using hex'
  have hkr : ∀ i < n, KeyRep (R.getD i 0 % 2 ^ 49) (y i) := fun i hi => rowRep_mod (hy i hi)
  have hkid : KeyRep (idrow % 2 ^ 49) 1 := keyRep_mod rowRep_idrow
  refine ⟨y, fun i => Nat.land (Nat.shiftRight (R.getD i 0) 897) 511, i0, hi0, ?_, ?_, ?_, ?_,
    ?_⟩
  ·
    have htree := (hr i0 hi0).2.1
    rw [if_pos rfl] at htree
    have := hy i0 hi0
    rw [htree] at this
    exact rowRep_unique this rowRep_idrow
  ·
    intro i hi j hj hij
    have e := keyRep_eq (hkr i hi) (hij ▸ hkr j hj) (Nat.mod_lt _ (by positivity))
      (Nat.mod_lt _ (by positivity))
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e (ne_of_lt (hkey i j h hj))
    · exact h
    · exact absurd e.symm (ne_of_lt (hkey j i h hi))
  ·
    intro i hi hii
    have htree := (hr i hi).2.1
    rw [if_neg hii] at htree
    obtain ⟨hl, hq, hd, hrow⟩ := htree
    refine ⟨_, hq, _, hl, ?_, ?_⟩
    · exact hdep i _ hq hd
    · have := hy i hi
      rw [hrow, hRT _ hq] at this
      exact rowRep_unique this (rowRep_comp (hgen _ hl) (hy _ hq))
  ·
    intro i hi l hl
    obtain ⟨hc, hkc⟩ := (hr i hi).2.2.1 l hl
    refine ⟨_, hc, ?_⟩
    rw [hKT _ hc] at hkc
    have h1 := hkr _ hc
    rw [hkc] at h1
    exact keyRep_unique h1 (keyRep_apT (hgen l hl) (hkr i hi))
  ·
    intro i hi hyp hy1
    have hchk := (hr i hi).2.2.2
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    have hne : ¬R.getD i 0 % 2 ^ 49 = idrow % 2 ^ 49 := fun e => hy1
      (keyRep_unique (e ▸ hkr i hi) hkid)
    have hpw : powT (R.getD i 0 % 2 ^ 882) (m + 1) = idrow % 2 ^ 49 := by
      obtain ⟨h1, h2⟩ := keyRep_powT (hy i hi) m
      rw [hyp] at h1
      exact keyRep_eq h1 hkid h2 (Nat.mod_lt _ (by positivity))
    have hb := hchk ⟨hne, hpw⟩
    intro f b hf hb'
    have hF := fixm_bit (hy i hi) hf
    have hB := fixm_bit (hy i hi) hb'
    split_ifs at hb
    · exact hardB_sound (hy i hi) hyp hp (fun z hz => fixm_lt hz) hb hF hB
    · exact easyB_sound (hy i hi) hyp hp hb hF hB

theorem sylFacts_subgroup {p n : ℕ} {W : List (List ℕ)} (h : SylFacts p n W) :
    ∃ S : Subgroup (WeylGroup .E7), Nat.card S = n ∧
      ∀ y ∈ S, y ^ p = 1 → y ≠ 1 → PlaneCheckFact p y := by
  obtain ⟨y, d, i0, hi0, hy0, hinj, htree, hcl, hgood⟩ := h
  set S : Subgroup (WeylGroup .E7) := Subgroup.closure {g | ∃ l < W.length, g = gen W l} with hS
  have hgenS : ∀ l < W.length, gen W l ∈ S := fun l hl => Subgroup.subset_closure ⟨l, hl, rfl⟩
  have hdep : ∀ k, ∀ i < n, d i ≤ k → y i ∈ S := by
    intro k
    induction k with
    | zero =>
      intro i hi hd
      by_cases h0 : i = i0
      · rw [h0, hy0]
        exact one_mem _
      · obtain ⟨q, -, l, -, hdq, -⟩ := htree i hi h0
        omega
    | succ k ih =>
      intro i hi hd
      by_cases h0 : i = i0
      · rw [h0, hy0]
        exact one_mem _
      · obtain ⟨q, hq, l, hl, hdq, hyi⟩ := htree i hi h0
        rw [hyi]
        exact mul_mem (hgenS l hl) (ih q hq (by omega))
  have hlist : ∀ i < n, y i ∈ S := fun i hi => hdep (d i) i hi le_rfl
  have hpow : ∀ l < W.length, ∀ m : ℕ, ∀ i < n, ∃ c < n, y c = gen W l ^ m * y i := by
    intro l hl m
    induction m with
    | zero => exact fun i hi => ⟨i, hi, by rw [pow_zero, one_mul]⟩
    | succ m ih =>
      intro i hi
      obtain ⟨c, hc, hce⟩ := ih i hi
      obtain ⟨c', hc', hce'⟩ := hcl c hc l hl
      exact ⟨c', hc', by rw [hce', hce, pow_succ', mul_assoc]⟩
  have hcover : ∀ g ∈ S, ∃ i < n, y i = g := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨i0, hi0, hy0⟩
    | mul_left x hx z _ ih =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := ih
      exact hcl i hi l hl
    | inv_mul_cancel x hx z _ ih =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨c, hc, hce⟩ := hpow l hl (orderOf (gen W l) - 1) i hi
      refine ⟨c, hc, ?_⟩
      rw [hce]
      congr 1
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ, Nat.sub_add_cancel (isOfFinOrder_of_finite (gen W l)).orderOf_pos,
        pow_orderOf_eq_one]
  refine ⟨S, ?_, fun g hg hp h1 => ?_⟩
  · have e : Fin n ≃ S := Equiv.ofBijective (fun i => ⟨y i, hlist i i.2⟩)
      ⟨fun i j hij => Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij)), fun g => by
        obtain ⟨i, hi, hig⟩ := hcover g g.2
        exact ⟨⟨i, hi⟩, Subtype.ext hig⟩⟩
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  · obtain ⟨i, hi, rfl⟩ := hcover g hg
    exact hgood i hi hp h1

private theorem iform_neg_left' (x y : Fin Tag.E7.rank → ℤ) : iform (-x) y = -iform x y := by
  have h := iform_smul_left (-1) x y
  rwa [neg_one_smul, neg_one_mul] at h

private theorem iform_neg_right' (x y : Fin Tag.E7.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [iform_comm, iform_neg_left', iform_comm]

private theorem iform_eq_zero_of_pm {u v u' v' : Fin Tag.E7.rank → ℤ} (hu : u = u' ∨ u = -u')
    (hv : v = v' ∨ v = -v') (h : iform u v = 0) : iform u' v' = 0 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    simpa only [iform_neg_left', iform_neg_right', neg_neg, neg_eq_zero] using h

private theorem triPairing_neg_eq_zero {b : Fin Tag.E7.rank → ZMod 3} {v : Fin Tag.E7.rank → ℤ}
    (hv : triPairing b v = 0) : triPairing b (-v) = 0 := by
  have h := triPairing_add b (-v) v
  rw [neg_add_cancel, triPairing_zero, hv, add_zero] at h
  exact h.symm

private theorem mem_kernelRoots_triChar_prod {f b : Fin Tag.E7.rank → ZMod 3}
    {α : Fin Tag.E7.rank → ℤ} :
    α ∈ kernelRoots ((triChar f).prod (triChar b)) ↔
      IsRoot .E7 α ∧ triPairing f α = 0 ∧ triPairing b α = 0 := by
  refine Iff.trans Iff.rfl (and_congr_right fun _ => ?_)
  rw [MonoidHom.prod_apply, Prod.mk_eq_one, triChar_apply, triChar_apply, Z3.ofAdd_eq_one,
    Z3.ofAdd_eq_one]

theorem planeGood_of_fact {p : ℕ} {y : WeylGroup .E7} (hy : PlaneCheckFact p y) :
    PlaneGood p y := by
  intro φ ψ hφ hψ
  obtain ⟨f, rfl⟩ : ∃ f, φ = triChar f := ⟨_, eq_triChar φ⟩
  obtain ⟨b, rfl⟩ : ∃ b, ψ = triChar b := ⟨_, eq_triChar ψ⟩
  rcases hy f b hφ hψ with ⟨α, hα, hf, hb, hpos, hsum⟩ | ⟨γ, hγ, hall, h01, hcyc⟩
  · exact Or.inl ⟨α, mem_kernelRoots_triChar_prod.2 ⟨hα, hf, hb⟩, hpos, hsum⟩
  right
  have c0 : y • γ 0 = γ 1 ∨ y • γ 0 = -γ 1 := hcyc 0
  have c1 : y • γ 1 = γ 2 ∨ y • γ 1 = -γ 2 := hcyc 1
  have c2 : y • γ 2 = γ 0 ∨ y • γ 2 = -γ 0 := hcyc 2
  have h12 : iform (γ 1) (γ 2) = 0 :=
    iform_eq_zero_of_pm c0 c1 (by rw [iform_smul]; exact h01)
  have h20 : iform (γ 2) (γ 0) = 0 :=
    iform_eq_zero_of_pm c1 c2 (by rw [iform_smul]; exact h12)
  have h10 : iform (γ 1) (γ 0) = 0 := by rw [iform_comm]; exact h01
  have h21 : iform (γ 2) (γ 1) = 0 := by rw [iform_comm]; exact h12
  have h02 : iform (γ 0) (γ 2) = 0 := by rw [iform_comm]; exact h20
  refine ⟨γ, fun j => (hγ j).1, fun j j' hjj' => ?_, fun α => ⟨fun hαS => ?_, ?_⟩, hcyc⟩
  · fin_cases j <;> fin_cases j' <;> first | exact absurd rfl hjj' | assumption
  · obtain ⟨hα, hf, hb⟩ := mem_kernelRoots_triChar_prod.1 hαS
    rcases IsRoot.height_pos_or_neg hα with hpos | hneg
    · obtain ⟨j, hj⟩ := hall α hα hpos hf hb
      exact ⟨j, Or.inl hj⟩
    · obtain ⟨j, hj⟩ := hall (-α) (IsRoot.neg hα) (by rw [height_neg]; omega)
        (triPairing_neg_eq_zero hf) (triPairing_neg_eq_zero hb)
      exact ⟨j, Or.inr (by rw [← hj, neg_neg])⟩
  · rintro ⟨j, rfl | rfl⟩
    · exact mem_kernelRoots_triChar_prod.2 (hγ j)
    · obtain ⟨hr, hf, hb⟩ := hγ j
      exact mem_kernelRoots_triChar_prod.2
        ⟨IsRoot.neg hr, triPairing_neg_eq_zero hf, triPairing_neg_eq_zero hb⟩

theorem sylK_sound {RV TB : List ℕ} {p n i0 : ℕ} {W : List (List ℕ)} {R : List ℕ}
    (hRV : RV = e7Certificate.roots) (hTB : TB = e7Certificate.table) (hp : 0 < p)
    (h : sylK RV TB p n i0 W R = true) :
    ∃ S : Subgroup (WeylGroup .E7), Nat.card S = n ∧
      ∀ y ∈ S, y ^ p = 1 → y ≠ 1 → PlaneGood p y := by
  subst hRV hTB
  obtain ⟨S, hS, hgood⟩ := sylFacts_subgroup (sylK_facts hp h)
  exact ⟨S, hS, fun y hy hp1 h1 => planeGood_of_fact (hgood y hy hp1 h1)⟩

end CFSG.KC.E7Plane

end
