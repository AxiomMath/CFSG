module

public import CFSG.GH74.BNPair.Building
public import CFSG.GH74.BNPair.Polygon

public noncomputable section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {S : Finset (WeylGroup B N)} {a b : WeylGroup B N} {n : ℕ}

namespace Rank2

variable (R : Rank2 B N S a b n)
include R

theorem sq_gen : ∀ s ∈ (S : Set (WeylGroup B N)), s * s = 1 :=
  fun _ hs => R.tits.mul_self_gen (Finset.mem_coe.1 hs)

omit R in
theorem walk_of_mem_both {u v : rankTwoVertices B N a b} {z : X} (hu : z ∈ (u : Set X))
    (hv : z ∈ (v : Set X)) : ∃ p : (buildingGraph B N a b).Walk u v, p.length ≤ 1 := by
  by_cases huv : u = v
  · subst huv
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · have hadj : (buildingGraph B N a b).Adj u v := ⟨huv, z, Set.mem_inter hu hv⟩
    exact ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, by simp⟩

theorem walk_of_wpos : ∀ (k : ℕ) (w : WeylGroup B N),
    wordLength (S : Set (WeylGroup B N)) w ≤ k →
    ∀ (e e' : X) (u v : rankTwoVertices B N a b), WPos B N w e e' → e ∈ (u : Set X) →
      e' ∈ (v : Set X) → ∃ p : (buildingGraph B N a b).Walk u v, p.length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro w hw e e' u v hee' he he'
    have hw1 : w = 1 :=
      (wordLength_eq_zero_iff R.sq_gen (R.tits.mem_closure w)).1 (by omega)
    subst hw1
    have hB : e' * e⁻¹ ∈ B := wpos_one_iff.1 hee'
    have he'u : e' ∈ (u : Set X) := by
      rw [R.eq_vtx_of_mem he]
      exact mem_vtx.2 (R.B_le_pgen _ hB)
    exact walk_of_mem_both he'u he'
  | succ k ih =>
    intro w hw e e' u v hee' he he'
    by_cases hle : wordLength (S : Set (WeylGroup B N)) w ≤ k
    · obtain ⟨p, hp⟩ := ih w hle e e' u v hee' he he'
      exact ⟨p, by omega⟩
    · have hw1 : w ≠ 1 := by
        rintro rfl
        simp [wordLength_one] at hle
      obtain ⟨s, hs, hsw⟩ := exists_left_descent R.sq_gen (R.tits.mem_closure w) hw1
      obtain ⟨z, hz, hzpos⟩ := WPos.step_down R.tits (Finset.mem_coe.1 hs) hee'
      obtain ⟨i, hi⟩ : ∃ i : Bool, s = gen a b i := by
        have hs' : s ∈ ({a, b} : Set (WeylGroup B N)) := R.gens ▸ hs
        rcases hs' with h | h
        · exact ⟨true, h⟩
        · exact ⟨false, h⟩
      subst hi
      have hzv : z ∈ ((vtx B N a b i e' : rankTwoVertices B N a b) : Set X) := mem_vtx.2 hz
      obtain ⟨p, hp⟩ := ih (gen a b i * w) (by omega) e z u (vtx B N a b i e') hzpos he hzv
      obtain ⟨q, hq⟩ := walk_of_mem_both (z := e') mem_self_vtx he'
      exact ⟨p.append q, by rw [SimpleGraph.Walk.length_append]; omega⟩

theorem exists_walk_le (u v : rankTwoVertices B N a b) :
    ∃ p : (buildingGraph B N a b).Walk u v, p.length ≤ n := by
  obtain ⟨i, x, rfl⟩ := exists_vtx u
  obtain ⟨j, y, rfl⟩ := exists_vtx v
  obtain ⟨w, hw⟩ := exists_wpos R.tits x y
  have hn := R.dih.three_le
  by_cases hlt : wordLength (S : Set (WeylGroup B N)) w ≤ n - 1
  · obtain ⟨p, hp⟩ := walk_of_wpos R (n - 1) w hlt x y _ _ hw mem_self_vtx mem_self_vtx
    exact ⟨p, by omega⟩
  · have hlw : wordLength (S : Set (WeylGroup B N)) w = n := by
      have := R.ell_le w
      omega
    have hwn : w = altWord a b n := by
      obtain ⟨t, htn, ht | ht⟩ := R.dih.exists_altWord w
      · have := R.ell_altWord htn
        rw [ht] at hlw
        have htn' : t = n := by omega
        rw [ht, htn']
      · have := R.ell_altWord' htn
        rw [ht] at hlw
        have htn' : t = n := by omega
        rw [ht, htn']
        exact R.dih.altWord_eq.symm
    obtain ⟨z, hz, hzpos⟩ := WPos.step_down R.tits (R.gen_mem j) hw
    have hzv : z ∈ ((vtx B N a b j y : rankTwoVertices B N a b) : Set X) := mem_vtx.2 hz
    have hlen : wordLength (S : Set (WeylGroup B N)) (gen a b j * w) ≤ n - 1 := by
      have := R.ell_gen_mul_longest (s := gen a b j) (by cases j; exact Or.inr rfl; exact Or.inl rfl)
      rw [hwn]
      omega
    obtain ⟨p, hp⟩ := walk_of_wpos R (n - 1) _ hlen x z _ _ hzpos mem_self_vtx hzv
    exact ⟨p, by omega⟩

theorem not_mem_B_of_mem_dc {s : WeylGroup B N} (hs : s ∈ S) {x : X} (hx : x ∈ dc B N s) :
    x ∉ B := fun hB =>
  R.tits.gen_ne_one hs (R.tits.dc_injective (dc_eq_of_mem hx (mem_dc_one.2 hB)))

theorem three_le_neighbors (v : rankTwoVertices B N a b) :
    3 ≤ ((buildingGraph B N a b).neighborSet v).encard := by
  obtain ⟨i, x, rfl⟩ := exists_vtx v
  obtain ⟨t, ht, htB⟩ := Set.not_subset.1
    (R.tits.bnCore.not_subset (gen a b i) (Finset.mem_coe.2 (R.gen_mem i)))
  obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_mul.1 ht
  have hpB : p ∉ B := R.not_mem_B_of_mem_dc (R.gen_mem i) hp
  have hqB : q ∉ B := R.not_mem_B_of_mem_dc (R.gen_mem i) hq
  have hp' : p ∈ pgen B N a b i := (mem_parabolic_single_iff R.tits (R.gen_mem i)).2 (Or.inr hp)
  have hq' : q ∈ pgen B N a b i := (mem_parabolic_single_iff R.tits (R.gen_mem i)).2 (Or.inr hq)
  have hc1 : (p * x) * x⁻¹ ∈ pgen B N a b i := by simpa using hp'
  have hc2 : (q⁻¹ * x) * x⁻¹ ∈ pgen B N a b i := by
    simpa using (pgen B N a b i).inv_mem hq'
  have hc0 : x * x⁻¹ ∈ pgen B N a b i := by simp
  have hne : ∀ c : X, vtx B N a b i x ≠ vtx B N a b (!i) c := by
    intro c h
    have := R.vtx_type_eq h
    cases i <;> simp at this
  have hadj : ∀ c : X, c * x⁻¹ ∈ pgen B N a b i →
      (buildingGraph B N a b).Adj (vtx B N a b i x) (vtx B N a b (!i) c) := by
    intro c hc
    exact ⟨hne c, c, Set.mem_inter (mem_vtx.2 hc) mem_self_vtx⟩
  have hdist : ∀ c c' : X, c * x⁻¹ ∈ pgen B N a b i → c' * x⁻¹ ∈ pgen B N a b i →
      vtx B N a b (!i) c = vtx B N a b (!i) c' → c * c'⁻¹ ∈ B := by
    intro c c' hc hc' h
    have h1 : c ∈ ((vtx B N a b (!i) c' : rankTwoVertices B N a b) : Set X) := by
      rw [← h]; exact mem_self_vtx
    have h2 : c * c'⁻¹ ∈ pgen B N a b (!i) := mem_vtx.1 h1
    have h3 : c * c'⁻¹ ∈ pgen B N a b i := by
      have := (pgen B N a b i).mul_mem hc ((pgen B N a b i).inv_mem hc')
      simpa [mul_assoc] using this
    exact R.pgen_inter i h3 h2
  have h01 : vtx B N a b (!i) x ≠ vtx B N a b (!i) (p * x) := by
    intro h
    have := hdist _ _ (by simp) hc1 h
    have h' : p⁻¹ ∈ B := by simpa using this
    exact hpB (by simpa using B.inv_mem h')
  have h02 : vtx B N a b (!i) x ≠ vtx B N a b (!i) (q⁻¹ * x) := by
    intro h
    have := hdist _ _ (by simp) hc2 h
    exact hqB (by simpa using this)
  have h12 : vtx B N a b (!i) (p * x) ≠ vtx B N a b (!i) (q⁻¹ * x) := by
    intro h
    have := hdist _ _ hc1 hc2 h
    exact htB (by simpa [mul_assoc] using this)
  have hsub : ({vtx B N a b (!i) x, vtx B N a b (!i) (p * x), vtx B N a b (!i) (q⁻¹ * x)} :
      Set (rankTwoVertices B N a b)) ⊆ (buildingGraph B N a b).neighborSet (vtx B N a b i x) := by
    intro c hc
    rcases hc with rfl | rfl | rfl
    · exact hadj _ hc0
    · exact hadj _ hc1
    · exact hadj _ hc2
  have h3 : ({vtx B N a b (!i) x, vtx B N a b (!i) (p * x), vtx B N a b (!i) (q⁻¹ * x)} :
      Set (rankTwoVertices B N a b)).encard = 3 :=
    Set.encard_eq_three.2 ⟨_, _, _, h01, h02, h12, rfl⟩
  calc (3 : ℕ∞) = _ := h3.symm
    _ ≤ _ := Set.encard_le_encard hsub

theorem no_double_path {f f' : ℕ → rankTwoVertices B N a b} {k k' : ℕ} (hk1 : 1 ≤ k)
    (hk1' : 1 ≤ k') (hk : k + 1 ≤ n) (hk' : k' + 1 ≤ n)
    (hadj : ∀ i, i < k → (buildingGraph B N a b).Adj (f i) (f (i + 1)))
    (hnb : ∀ i, i + 2 ≤ k → f i ≠ f (i + 2))
    (hadj' : ∀ i, i < k' → (buildingGraph B N a b).Adj (f' i) (f' (i + 1)))
    (hnb' : ∀ i, i + 2 ≤ k' → f' i ≠ f' (i + 2))
    (h0 : f 0 = f' 0) (hend : f k = f' k') (h1 : f 1 ≠ f' 1) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', k' = m' + 1 := ⟨k' - 1, by omega⟩
  let g : ℕ → rankTwoVertices B N a b := fun i => if i = 0 then f 1 else f' (i - 1)
  have hg0 : g 0 = f 1 := by simp [g]
  have hgs : ∀ i, g (i + 1) = f' i := fun i => by simp [g]
  have hadjg : ∀ i, i < m' + 1 + 1 → (buildingGraph B N a b).Adj (g i) (g (i + 1)) := by
    intro i hi
    cases i with
    | zero =>
      rw [hg0, hgs, ← h0]
      exact (hadj 0 (by omega)).symm
    | succ i =>
      rw [hgs, hgs]
      exact hadj' i (by omega)
  have hnbg : ∀ i, i + 2 ≤ m' + 1 + 1 → g i ≠ g (i + 2) := by
    intro i hi
    cases i with
    | zero =>
      rw [hg0]
      exact fun h => h1 (by rw [h]; exact (hgs 1).symm ▸ rfl)
    | succ i =>
      rw [hgs, show i + 1 + 2 = (i + 2) + 1 from rfl, hgs]
      exact hnb' i (by omega)
  obtain ⟨x, hx0, hx1⟩ := (hadj 0 (by omega)).2
  obtain ⟨y₀, hy₀0, hy₀1⟩ := (hadj m (by omega)).2
  obtain ⟨y, hy0, hy1⟩ := (hadj' m' (by omega)).2
  have hvt : vtype B N a b (g 0) = !vtype B N a b (f 0) := by
    rw [hg0]; exact R.vtype_not_of_adj (hadj 0 (by omega))
  have hgal := R.gallery g (m' + 1 + 1) hk' hadjg hnbg (m' + 1) (by omega) x y
    (by rw [hg0]; exact hx1) (by rw [show (1 : ℕ) = 0 + 1 from rfl, hgs, ← h0]; exact hx0)
    (by rw [hgs]; exact hy0) (by rw [hgs]; exact hy1)
  rw [hvt, Bool.not_not] at hgal
  have hgal' := R.gallery f (m + 1) (by omega) hadj hnb m (by omega) x y₀ hx0 hx1 hy₀0 hy₀1
  have hyv : y ∈ ((f (m + 1) : rankTwoVertices B N a b) : Set X) := by rw [hend]; exact hy1
  have hyy₀ : y * y₀⁻¹ ∈ pgen B N a b (vtype B N a b (f (m + 1))) := by
    have e := R.eq_vtx_of_mem hy₀1
    have : y ∈ ((vtx B N a b (vtype B N a b (f (m + 1))) y₀ : rankTwoVertices B N a b) :
        Set X) := by
      rw [← e]; exact hyv
    exact mem_vtx.1 this
  have hpar := R.vtype_path hadj (m + 1) (le_refl _)
  have hs := R.gen_mem (vtype B N a b (f (m + 1)))
  have hd := R.dih_gen (!vtype B N a b (f 0))
  rw [Bool.not_not] at hd
  generalize ht : vtype B N a b (f 0) = t at hgal hgal' hpar hd
  by_cases hB : y * y₀⁻¹ ∈ B
  · have h2 := hgal'.congr_right hB
    have e := WPos.unique R.tits h2 hgal
    rcases hd.altWord_eq_swap (by omega) (by omega) e with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · have hlet : gen a b (vtype B N a b (f (m + 1))) *
        altWord (gen a b (!t)) (gen a b t) m = altWord (gen a b (!t)) (gen a b t) (m + 1) := by
      rw [altWord_succ_left, hpar]
      by_cases he : Even m <;> simp [he, Nat.even_add_one]
    have hlen : wordLength (S : Set (WeylGroup B N)) (altWord (gen a b (!t)) (gen a b t) m) <
        wordLength (S : Set (WeylGroup B N)) (gen a b (vtype B N a b (f (m + 1))) *
          altWord (gen a b (!t)) (gen a b t) m) := by
      rw [hlet]
      have h5 := R.ell_alt (!t) (j := m) (by omega)
      have h6 := R.ell_alt (!t) (j := m + 1) (by omega)
      rw [Bool.not_not] at h5 h6
      omega
    have h2 := WPos.step_up R.tits hs hlen hgal' hyy₀ hB
    rw [hlet] at h2
    have e := WPos.unique R.tits h2 hgal
    rcases hd.altWord_eq_swap (by omega) (by omega) e with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

theorem no_closed_path : ∀ (k : ℕ) (f : ℕ → rankTwoVertices B N a b), 1 ≤ k → k + 1 ≤ n →
    (∀ i, i < k → (buildingGraph B N a b).Adj (f i) (f (i + 1))) →
    (∀ i, i + 2 ≤ k → f i ≠ f (i + 2)) → f 0 = f k → False := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f hk1 hkn hadj hnb hclosed
    by_cases hk2 : k = 1
    · subst hk2
      have h := hadj 0 (by omega)
      rw [show (0 : ℕ) + 1 = 1 from rfl, ← hclosed] at h
      exact (buildingGraph B N a b).loopless.irrefl _ h
    by_cases hk3 : k = 2
    · subst hk3
      exact hnb 0 (le_refl _) hclosed
    by_cases h : f 1 = f (k - 1)
    · refine ih (k - 2) (by omega) (fun i => f (i + 1)) (by omega) (by omega) ?_ ?_ ?_
      · intro i hi
        exact hadj (i + 1) (by omega)
      · intro i hi
        exact hnb (i + 1) (by omega)
      · show f (0 + 1) = f (k - 2 + 1)
        rw [show k - 2 + 1 = k - 1 by omega]
        exact h
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      let g : ℕ → rankTwoVertices B N a b := fun i => if i = 0 then f m else f (i - 1)
      have hg0 : g 0 = f m := by simp [g]
      have hgs : ∀ i, g (i + 1) = f i := fun i => by simp [g]
      have hadjg : ∀ i, i < m + 1 + 1 → (buildingGraph B N a b).Adj (g i) (g (i + 1)) := by
        intro i hi
        cases i with
        | zero =>
          rw [hg0, hgs, hclosed]
          exact hadj m (by omega)
        | succ i =>
          rw [hgs, hgs]
          exact hadj i (by omega)
      have hnbg : ∀ i, i + 2 ≤ m + 1 + 1 → g i ≠ g (i + 2) := by
        intro i hi
        cases i with
        | zero =>
          rw [hg0, show (0 : ℕ) + 2 = 1 + 1 from rfl, hgs]
          exact fun h' => h (h'.symm.trans (by rw [show m + 1 - 1 = m by omega]))
        | succ i =>
          rw [hgs, show i + 1 + 2 = (i + 2) + 1 from rfl, hgs]
          exact hnb i (by omega)
      obtain ⟨c, hc0, hc1⟩ := (hadj m (by omega)).2
      have hc1' : c ∈ ((f 0 : rankTwoVertices B N a b) : Set X) := by rw [hclosed]; exact hc1
      have hgal := R.gallery g (m + 1 + 1) (by omega) hadjg hnbg (m + 1) (by omega) c c
        (by rw [hg0]; exact hc0) (by rw [show (1 : ℕ) = 0 + 1 from rfl, hgs]; exact hc1')
        (by rw [hgs]; exact hc0) (by rw [hgs]; exact hc1)
      have h1 := WPos.unique R.tits hgal (WPos.refl (B := B) (N := N) c)
      have h2 : altWord (gen a b (!vtype B N a b (g 0))) (gen a b (vtype B N a b (g 0))) (m + 1) =
          altWord (gen a b (!vtype B N a b (g 0))) (gen a b (vtype B N a b (g 0))) 0 := h1
      have hd := R.dih_gen (!vtype B N a b (g 0))
      rw [Bool.not_not] at hd
      have := hd.altWord_inj (by omega) (by omega) h2
      omega

theorem unique_fun : ∀ (k : ℕ) (f f' : ℕ → rankTwoVertices B N a b) (k' : ℕ), k + 1 ≤ n →
    k' + 1 ≤ n → (∀ i, i < k → (buildingGraph B N a b).Adj (f i) (f (i + 1))) →
    (∀ i, i + 2 ≤ k → f i ≠ f (i + 2)) →
    (∀ i, i < k' → (buildingGraph B N a b).Adj (f' i) (f' (i + 1))) →
    (∀ i, i + 2 ≤ k' → f' i ≠ f' (i + 2)) → f 0 = f' 0 → f k = f' k' →
    k = k' ∧ ∀ i, i ≤ k → f i = f' i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' k' hk hk' hadj hnb hadj' hnb' h0 hend
    by_cases hk0 : k = 0
    · subst hk0
      by_cases hk0' : k' = 0
      · subst hk0'
        refine ⟨rfl, fun i hi => ?_⟩
        have : i = 0 := by omega
        subst this
        exact h0
      · exact (R.no_closed_path k' f' (by omega) hk' hadj' hnb' (h0.symm.trans hend)).elim
    by_cases hk0' : k' = 0
    · subst hk0'
      exact (R.no_closed_path k f (by omega) hk hadj hnb (h0.trans hend.symm)).elim
    by_cases h1 : f 1 = f' 1
    · obtain ⟨hkk, hi⟩ := ih (k - 1) (by omega) (fun i => f (i + 1)) (fun i => f' (i + 1)) (k' - 1)
        (by omega) (by omega)
        (fun i hi => hadj (i + 1) (by omega)) (fun i hi => hnb (i + 1) (by omega))
        (fun i hi => hadj' (i + 1) (by omega)) (fun i hi => hnb' (i + 1) (by omega))
        (by simpa using h1) (by
          show f (k - 1 + 1) = f' (k' - 1 + 1)
          rw [show k - 1 + 1 = k by omega, show k' - 1 + 1 = k' by omega]
          exact hend)
      refine ⟨by omega, fun i hi' => ?_⟩
      cases i with
      | zero => exact h0
      | succ i => exact hi i (by omega)
    · exact (R.no_double_path (by omega) (by omega) hk hk' hadj hnb hadj' hnb' h0 hend h1).elim

theorem unique_path {u v : rankTwoVertices B N a b} {p q : List (rankTwoVertices B N a b)}
    (hp : IsGLSPath (buildingGraph B N a b) p) (hq : IsGLSPath (buildingGraph B N a b) q)
    (hpu : p.head? = some u) (hqu : q.head? = some u) (hpv : p.getLast? = some v)
    (hqv : q.getLast? = some v) (hpn : p.length ≤ n) (hqn : q.length ≤ n) : p = q := by
  obtain ⟨f, k, hk, hf0, hfk, hadj, hnb, hfl⟩ := hp.exists_fun hpu hpv
  obtain ⟨f', k', hk', hf0', hfk', hadj', hnb', hfl'⟩ := hq.exists_fun hqu hqv
  obtain ⟨hkk, hi⟩ := R.unique_fun k f f' k' (by omega) (by omega) hadj hnb hadj' hnb'
    (hf0.trans hf0'.symm) (hfk.trans hfk'.symm)
  refine List.ext_getElem? fun i => ?_
  by_cases hik : i ≤ k
  · rw [hfl i hik, hfl' i (by omega), hi i hik]
  · have h1 : p[i]? = none := List.getElem?_eq_none (by omega)
    have h2 : q[i]? = none := List.getElem?_eq_none (by omega)
    rw [h1, h2]

theorem polyHyp : PolyHyp (buildingGraph B N a b) n where
  three_le := R.dih.three_le
  nonempty := ⟨vtx B N a b true 1⟩
  reach_dist u v := by
    obtain ⟨p, hp⟩ := R.exists_walk_le u v
    exact ⟨⟨p⟩, (SimpleGraph.dist_le p).trans hp⟩
  unique := fun hp hq hpu hqu hpv hqv hpn hqn => R.unique_path hp hq hpu hqu hpv hqv hpn hqn
  color := ⟨vtype B N a b, fun _ _ h => R.vtype_ne_of_adj h⟩
  valency := R.three_le_neighbors

end Rank2

end CFSG.GH74.BNPair
