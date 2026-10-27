module

public import CFSG.Certificates.Kernel.Spor.RawOrbBfs
public import CFSG.Certificates.NativeValidSchreier
public import Mathlib.Algebra.BigOperators.Intervals

public section

namespace CFSG.KS.Raw.Orb

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Certificates
  CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem chain_card {a m : Nat → Nat} {nb : Nat} (hm : ∀ i < nb, 0 < m i)
    (ha : ∀ i < nb, m i * a (i + 1) ≤ a i) (hlast : 1 ≤ a nb)
    (h0 : a 0 ≤ ∏ i ∈ Finset.range nb, m i) :
    a nb = 1 ∧ ∀ i < nb, a i = m i * a (i + 1) := by
  have hpre : ∀ s ≤ nb, (∏ i ∈ Finset.range s, m i) * a s ≤ a 0 := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hs
      rw [Finset.prod_range_succ, Nat.mul_assoc]
      exact le_trans (Nat.mul_le_mul_left _ (ha s (by omega))) (ih (by omega))
  have hsuf : ∀ d s, s + d = nb → (∏ i ∈ Finset.Ico s nb, m i) * a nb ≤ a s := by
    intro d
    induction d with
    | zero => intro s hs; subst hs; simp
    | succ d ih =>
      intro s hs
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega), Nat.mul_assoc]
      exact le_trans (Nat.mul_le_mul_left _ (ih (s + 1) (by omega))) (ha s (by omega))
  have hpos : ∀ s ≤ nb, 0 < ∏ i ∈ Finset.range s, m i := fun s hs =>
    Finset.prod_pos fun i hi => hm i (by have := Finset.mem_range.1 hi; omega)
  refine ⟨?_, fun i hi => le_antisymm ?_ (ha i hi)⟩
  · have h2 : (∏ i ∈ Finset.range nb, m i) * a nb ≤ (∏ i ∈ Finset.range nb, m i) * 1 := by
      rw [Nat.mul_one]
      exact le_trans (hpre nb le_rfl) h0
    have := Nat.le_of_mul_le_mul_left h2 (hpos nb le_rfl)
    omega
  · have h3 : ∏ j ∈ Finset.Ico (i + 1) nb, m j ≤ a (i + 1) :=
      le_trans (Nat.le_mul_of_pos_right _ hlast) (hsuf (nb - (i + 1)) (i + 1) (by omega))
    have h4 : (∏ j ∈ Finset.range i, m j) * a i ≤
        (∏ j ∈ Finset.range i, m j) * (m i * a (i + 1)) := by
      calc _ ≤ a 0 := hpre i hi.le
        _ ≤ _ := h0
        _ = (∏ j ∈ Finset.range i, m j) * ∏ j ∈ Finset.Ico i nb, m j :=
          (Finset.prod_range_mul_prod_Ico m hi.le).symm
        _ = (∏ j ∈ Finset.range i, m j) * (m i * ∏ j ∈ Finset.Ico (i + 1) nb, m j) := by
          rw [Finset.prod_eq_prod_Ico_succ_bot hi]
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    exact Nat.le_of_mul_le_mul_left h4 (hpos i hi.le)

theorem parLt_of_forall {m chunks : Nat} {p : Nat → Bool} (h : ∀ i < m, p i = true) :
    parLt m chunks p = true := by
  unfold parLt
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply]
  intro c _
  change allLt (m / chunks + 1) (fun k => !(decide (c * (m / chunks + 1) + k < m)) ||
    p (c * (m / chunks + 1) + k)) = true
  rw [allLt_iff]
  intro k _
  by_cases hk : c * (m / chunks + 1) + k < m
  · simp [hk, h _ hk]
  · simp [hk]

structure Hd (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (kO : Nat)
    (W : Array (List Int)) : Prop where
  kO_le : kO ≤ S.size
  inv : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true
  words : ∀ j < S.size, kO ≤ j →
    lettersOK j W[j]! = true ∧ eqA n S[j]! (wordA n S (rawInvs n S) W[j]!) = true
  base_lt : ∀ i < base.size, base[i]! < n

theorem hd_of_head {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}
    (hk : kO ≤ S.size) (hH : rawHeadOK n (S.extract 0 kO) S base W = true) :
    Hd n S base kO W := by
  have hO : (S.extract 0 kO).size = kO := by simp [Array.size_extract, hk]
  unfold rawHeadOK at hH
  simp only [Bool.and_eq_true] at hH
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, h5⟩, _⟩, h7⟩ := hH
  refine ⟨hk, fun j hj => allLt_spec h3 hj, fun j hj hkj => ?_, fun i hi => ?_⟩
  · have := allLt_spec h5 hj
    rw [hO] at this
    simpa [show ¬ j < kO by omega] using this
  · exact of_decide_eq_true (allLt_spec h7 hi)

@[expose] def Gen (n : Nat) (S : Array (Array Nat)) (kO : Nat) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure (Set.range fun j : Fin kO => permOfArr n S[j.val]!)

@[expose] def Fix (n : Nat) (S : Array (Array Nat)) (kO : Nat) (base : Array Nat) (i : Nat) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | g ∈ Gen n S kO ∧ ∀ t < i, ∀ h : base[t]! < n, g ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩}
  mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, fun t ht h => by
    rw [Equiv.Perm.mul_apply, hb.2 t ht h, ha.2 t ht h]⟩
  one_mem' := ⟨Subgroup.one_mem _, fun _ _ _ => rfl⟩
  inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, fun t ht h => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha.2 t ht h).symm⟩

section Chain

variable {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}

theorem mem_Fix {i : Nat} {g : Equiv.Perm (Fin n)} : g ∈ Fix n S kO base i ↔
    g ∈ Gen n S kO ∧ ∀ t < i, ∀ h : base[t]! < n, g ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩ := Iff.rfl

theorem Fix_succ_le {i : Nat} : Fix n S kO base (i + 1) ≤ Fix n S kO base i :=
  fun _ hg => ⟨hg.1, fun t ht h => hg.2 t (by omega) h⟩

theorem Fix_zero : Fix n S kO base 0 = Gen n S kO := by
  ext g
  rw [mem_Fix]
  exact ⟨fun h => h.1, fun h => ⟨h, fun t ht => absurd ht (Nat.not_lt_zero t)⟩⟩

variable (hd : Hd n S base kO W)
include hd

theorem rep_S {j : Nat} (hj : j < S.size) : Rep n S[j]! (permOfArr n S[j]!) :=
  (rep_permOfArr (hd.inv j hj)).1

theorem rep_Si {j : Nat} (hj : j < S.size) : Rep n (rawInvs n S)[j]! (permOfArr n S[j]!)⁻¹ :=
  (rep_permOfArr (hd.inv j hj)).2

theorem S_mem_Gen : ∀ j < S.size, permOfArr n S[j]! ∈ Gen n S kO := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjk : j < kO
    · exact Subgroup.subset_closure ⟨⟨j, hjk⟩, rfl⟩
    · obtain ⟨hl, he⟩ := hd.words j hj (by omega)
      have hrep := rep_wordA (gs := fun h => permOfArr n S[h]!) (j := j)
        (fun h hh => rep_S hd (by omega)) (fun h hh => rep_Si hd (by omega)) _ hl
      rw [eq_of_eqA (rep_S hd hj) hrep he]
      refine Subgroup.closure_le _ |>.2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
      rintro _ ⟨h, rfl⟩
      exact ih h.val (by omega) (by omega)

theorem step_rep {i j : Nat} (hj : j < (rawSteps n S base i).size) :
    ∃ σ, Rep n (rawSteps n S base i)[j]! σ ∧ σ ∈ Fix n S kO base i := by
  have hmem : (rawSteps n S base i)[j]! ∈ levelSteps S (rawInvs n S) base i := by
    rw [getElem!_pos _ j hj]
    exact Array.getElem_mem hj
  unfold levelSteps at hmem
  rw [Array.mem_append, List.mem_toArray, List.mem_toArray, List.mem_map, List.mem_map] at hmem
  have hfix : ∀ idx ∈ levelIdx S base i, idx < S.size ∧
      permOfArr n S[idx]! ∈ Fix n S kO base i := by
    intro idx hidx
    unfold levelIdx at hidx
    rw [List.mem_filter, List.mem_range] at hidx
    obtain ⟨hidx, hf⟩ := hidx
    refine ⟨hidx, S_mem_Gen hd idx hidx, fun t ht h => Fin.ext ?_⟩
    have := allLt_spec hf ht
    rw [beq_iff_eq] at this
    rw [← (rep_S hd hidx).apply h, this]
  rcases hmem with ⟨idx, hidx, e⟩ | ⟨idx, hidx, e⟩
  · obtain ⟨h1, h2⟩ := hfix idx hidx
    exact ⟨_, e ▸ rep_S hd h1, h2⟩
  · obtain ⟨h1, h2⟩ := hfix idx hidx
    exact ⟨_, e ▸ rep_Si hd h1, Subgroup.inv_mem _ h2⟩

theorem steps_lt {i : Nat} : ∀ j < (rawSteps n S base i).size, ∀ x < n,
    ((rawSteps n S base i)[j]!)[x]! < n := fun _ hj _ hx =>
  (step_rep hd hj).choose_spec.1.lt hx

theorem lev_facts {i : Nat} (hi : i < base.size) :
    LevelFacts n base[i]! (rawSteps n S base i) (lev n S base i) := by
  rw [lev, rawLevels_get hi]
  exact levelFacts_of_levelOK (levelOK_of (levelOKT_bfs (hd.base_lt i hi) (steps_lt hd))
    (levelTrOK_bfs fun j hj => ⟨_, (step_rep hd hj).choose_spec.1⟩))

end Chain

@[expose] noncomputable def trP (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i k : Nat) :
    Equiv.Perm (Fin n) :=
  permOfArr n (lev n S base i).tr[k]!

section Chain

variable {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}
variable (hd : Hd n S base kO W)
include hd

theorem rep_tr {i k : Nat} (hi : i < base.size) (hk : k < (lev n S base i).pts.size) :
    Rep n (lev n S base i).tr[k]! (trP n S base i k) :=
  (rep_permOfArr ((lev_facts hd hi).tr_inv k hk)).1

theorem rep_trInv {i k : Nat} (hi : i < base.size) (hk : k < (lev n S base i).pts.size) :
    Rep n (lev n S base i).trInv[k]! (trP n S base i k)⁻¹ :=
  (rep_permOfArr ((lev_facts hd hi).tr_inv k hk)).2

theorem tr_spec {i : Nat} (hi : i < base.size) : ∀ k < (lev n S base i).pts.size,
    trP n S base i k ∈ Fix n S kO base i ∧
      (trP n S base i k ⟨base[i]!, hd.base_lt i hi⟩ : Nat) = (lev n S base i).pts[k]! := by
  have F := lev_facts hd hi
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have e : trP n S base i 0 = 1 := (eqA_iff (rep_tr hd hi hk) rep_idA).1 F.tr_zero
      rw [e, F.root]
      exact ⟨Subgroup.one_mem _, rfl⟩
    · have hp := F.par_lt k hk hk0
      have hl := F.lab_lt k hk hk0
      obtain ⟨σ, hσ, hσm⟩ := step_rep hd hl
      obtain ⟨ih1, ih2⟩ := ih _ hp (by omega)
      have e : trP n S base i k = σ * trP n S base i (lev n S base i).par[k]! :=
        (eqA_iff (rep_tr hd hi hk) (rep_compA hσ (rep_tr hd hi (by omega)))).1 (F.tr_step k hk hk0)
      rw [e]
      refine ⟨Subgroup.mul_mem _ hσm ih1, ?_⟩
      rw [Equiv.Perm.mul_apply, ← hσ, ih2]
      exact F.edge k hk hk0

noncomputable def phi {i : Nat} (hi : i < base.size) :
    Fin (lev n S base i).pts.size × Fix n S kO base (i + 1) → Fix n S kO base i :=
  fun p => ⟨trP n S base i p.1 * p.2, Subgroup.mul_mem _ (tr_spec hd hi p.1 p.1.2).1
    (Fix_succ_le p.2.2)⟩

theorem phi_apply {i : Nat} (hi : i < base.size)
    (p : Fin (lev n S base i).pts.size × Fix n S kO base (i + 1)) :
    ((phi hd hi p : Equiv.Perm (Fin n)) ⟨base[i]!, hd.base_lt i hi⟩ : Nat) =
      (lev n S base i).pts[p.1.val]! := by
  change ((trP n S base i p.1 * p.2) ⟨base[i]!, hd.base_lt i hi⟩ : Nat) = _
  rw [Equiv.Perm.mul_apply, p.2.2.2 i (by omega) (hd.base_lt i hi)]
  exact (tr_spec hd hi p.1 p.1.2).2

theorem phi_inj {i : Nat} (hi : i < base.size) : Function.Injective (phi hd hi) := by
  rintro p q e
  have F := lev_facts hd hi
  have h1 := phi_apply hd hi p
  rw [e, phi_apply hd hi q] at h1
  have hk : p.1 = q.1 := Fin.ext (by
    rw [← F.pos_pts _ p.1.2, ← F.pos_pts _ q.1.2, h1])
  have e2 : trP n S base i p.1 * p.2 = trP n S base i q.1 * q.2 := congrArg Subtype.val e
  rw [hk] at e2
  exact Prod.ext hk (Subtype.ext (mul_left_cancel e2))

theorem card_step {i : Nat} (hi : i < base.size) :
    (lev n S base i).pts.size * Nat.card (Fix n S kO base (i + 1)) ≤
      Nat.card (Fix n S kO base i) := by
  have := Nat.card_le_card_of_injective _ (phi_inj hd hi)
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at this

omit hd in
theorem prod_sizes : (rawOrbitSizes n S base).prod =
    ∏ i ∈ Finset.range base.size, (lev n S base i).pts.size := by
  have e : rawOrbitSizes n S base =
      List.ofFn (fun i : Fin base.size => (lev n S base i.val).pts.size) := by
    apply List.ext_getElem
    · simp [rawOrbitSizes, rawLevels]
    · intro k h1 h2
      have hk : k < base.size := by simpa using h2
      simp only [rawOrbitSizes, List.getElem_map, Array.getElem_toList, List.getElem_ofFn]
      rw [lev, getElem!_pos _ k (by simpa [rawLevels] using hk)]
  rw [e, List.prod_ofFn]
  exact Fin.prod_univ_eq_prod_range (fun i => (lev n S base i).pts.size) base.size

variable (hcard : Nat.card (Gen n S kO) ≤ (rawOrbitSizes n S base).prod)
include hcard

theorem card_facts : Nat.card (Fix n S kO base base.size) = 1 ∧ ∀ i < base.size,
    Nat.card (Fix n S kO base i) =
      (lev n S base i).pts.size * Nat.card (Fix n S kO base (i + 1)) :=
  chain_card (a := fun i => Nat.card (Fix n S kO base i)) (m := fun i => (lev n S base i).pts.size)
    (fun i hi => (lev_facts hd hi).pos) (fun i hi => card_step hd hi) Nat.card_pos
    (by rw [Fix_zero, ← prod_sizes]; exact hcard)

theorem fix_surj {l : Nat} (hl : l < base.size) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ Fix n S kO base l) : ∃ k < (lev n S base l).pts.size,
      (g ⟨base[l]!, hd.base_lt l hl⟩ : Nat) = (lev n S base l).pts[k]! := by
  have hb := (phi_inj hd hl).bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin,
      ← (card_facts hd hcard).2 l hl])
  obtain ⟨p, hp⟩ := hb.2 ⟨g, hg⟩
  refine ⟨p.1, p.1.2, ?_⟩
  rw [← phi_apply hd hl p, hp]

theorem fix_one {g : Equiv.Perm (Fin n)} (hg : g ∈ Fix n S kO base base.size) : g = 1 := by
  obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.1 (card_facts hd hcard).1
  exact congrArg Subtype.val (hs.elim ⟨g, hg⟩ ⟨1, Subgroup.one_mem _⟩)

theorem siftA_fix : ∀ d l, l + d = base.size → ∀ (g : Array Nat) (G : Equiv.Perm (Fin n)),
    Rep n g G → G ∈ Fix n S kO base l → siftA n (rawLevels n S base) base l g = true := by
  intro d
  induction d with
  | zero =>
    intro l hl g G hG hm
    have : l = base.size := by omega
    subst this
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)]
    rw [fix_one hd hcard hm] at hG
    exact (eqA_iff hG rep_idA).2 rfl
  | succ d ih =>
    intro l hl g G hG hm
    have hlb : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hlb
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls]
    have F := lev_facts hd hlb
    have hbl := hd.base_lt l hlb
    obtain ⟨k, hk, hgk⟩ := fix_surj hd hcard hlb hm
    have hgb : g[base[l]!]! = (lev n S base l).pts[k]! := by rw [hG.apply hbl, hgk]
    simp only [hgb, F.pos_pts k hk, hk, decide_true, Bool.true_and]
    have hT := tr_spec hd hlb k hk
    have hTi := Subgroup.inv_mem _ hT.1
    refine ih (l + 1) (by omega) _ _ (rep_compA (rep_trInv hd hlb hk) hG)
      ⟨Subgroup.mul_mem _ hTi.1 hm.1, fun t ht h => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [Equiv.Perm.mul_apply, hm.2 t ht h, hTi.2 t ht h]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      apply Fin.ext
      rw [hT.2]
      exact hgk

theorem schreierOK_level {i : Nat} (hi : i < base.size) (chunks : Nat) :
    CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
      (rawLevels n S base)[i]! chunks = true := by
  change CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
    (lev n S base i) chunks = true
  unfold CFSG.Monster.B.Co2.Native.schreierOK
  apply parLt_of_forall
  intro h hh
  rw [allLt_iff]
  intro j hj
  have F := lev_facts hd hi
  obtain ⟨hk, _⟩ := F.closed h hh j hj
  obtain ⟨σ, hσ, hσm⟩ := step_rep hd hj
  simp only [hk, decide_true, Bool.true_and]
  set z := ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! with hz
  have hzn : z < n := steps_lt hd j hj _ (F.pts_lt h hh)
  have hT := tr_spec hd hi
  refine siftA_fix hd hcard (base.size - (i + 1)) (i + 1) (by omega) _ _
    (rep_compA (rep_trInv hd hi hk) (rep_compA hσ (rep_tr hd hi hh))) ?_
  have hTi := Subgroup.inv_mem _ (hT _ hk).1
  refine ⟨Subgroup.mul_mem _ hTi.1 (Subgroup.mul_mem _ hσm (hT h hh).1).1, fun t ht hb => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, (hT h hh).1.2 t ht hb, hσm.2 t ht hb,
      hTi.2 t ht hb]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [(hT _ hk).2, F.pts_pos z hzn hk, ← hσ, (hT h hh).2]

end Chain

theorem rawChainOK_of_head_card {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} (chunks : Nat) (hk : kO ≤ S.size)
    (hH : rawHeadOK n (S.extract 0 kO) S base W = true)
    (hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin kO => permOfArr n S[j.val]!)) ≤
      (rawOrbitSizes n S base).prod) :
    rawChainOK n (S.extract 0 kO) S base W chunks = true := by
  have hd := hd_of_head hk hH
  have hlv : ∀ i < base.size, levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]! = true := fun i hi => by
    rw [rawLevels_get hi]
    exact levelOK_of (levelOKT_bfs (hd.base_lt i hi) (steps_lt hd))
      (levelTrOK_bfs fun j hj => ⟨_, (step_rep hd hj).choose_spec.1⟩)
  have hsc : ∀ i < base.size, CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! chunks = true :=
    fun i hi => schreierOK_level hd hcard hi chunks
  change (rawHeadOK n (S.extract 0 kO) S base W &&
    allLt base.size (fun i => levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]!) &&
    allLt base.size (fun i => CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! chunks)) = true
  rw [hH, allLt_iff.2 hlv, allLt_iff.2 hsc]
  rfl

end CFSG.KS.Raw.Orb

end
