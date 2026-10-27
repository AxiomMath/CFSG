module

public import CFSG.Certificates.Kernel.TcRes.Math
public import CFSG.Certificates.Kernel.TcRes.Kit
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK

@[expose] noncomputable def vecOf (n V i : ℕ) : Fin n → ℤ :=
  fun m => (fld (fld V (16 * n) i) 16 m : ℤ) - 7

structure DatumRaw (τ : Tag) (N : ℕ) (vec : ℕ → Fin τ.rank → ℤ) (rt : ℕ → ℕ → ℕ)
    (adj : ℕ → ℕ → Bool) (neg : ℕ → ℕ) : Prop where
  rank_le : τ.rank ≤ N
  simple : ∀ k : Fin τ.rank, vec k = Pi.single k 1
  parent : ∀ i < N, τ.rank ≤ i → ∃ i' < i, ∃ k : Fin τ.rank, vec i = reflect τ k (vec i')
  inj : ∀ i < N, ∀ j < N, vec i = vec j → i = j
  refl : ∀ g < N, ∀ v < N, rt g v < N ∧ vec (rt g v) = vec v - iform (vec v) (vec g) • vec g
  adj : ∀ g < N, ∀ v < N, adj g v = true ↔ iform (vec v) (vec g) ≠ 0
  neg : ∀ i < N, neg i < N ∧ vec (neg i) = - vec i
  closed : ∀ k : Fin τ.rank, ∀ v < N, ∃ t < N, vec t = reflect τ k (vec v)

section Decode

open CFSG.KC.TcRes.Lane

theorem root_lanes {n N W : ℕ} {yc rtR : ℕ → ℕ} {V X Y NEG PAR i : ℕ} (hn1 : 1 ≤ n)
    (h : rootOK n N W yc rtR V X Y NEG PAR i = true) :
    (∀ m < n, fld (fld V (16 * n) i) 16 m < 16) ∧
    (∀ m, fld (fld X (2 * (16 * n)) i) 16 m ≤ 7) ∧
    (∀ m, fld (fld Y (2 * (16 * n)) i) 16 m ≤ 3) ∧
    (∀ m < n, (fld (fld V (16 * n) i) 16 m : ℤ) - 7 =
      (fld (fld X (2 * (16 * n)) i) 16 m : ℤ) - fld (fld X (2 * (16 * n)) i) 16 (n + m)) ∧
    (∀ m < n, fld (fld Y (2 * (16 * n)) i) 16 (n - 1 - m) +
        dQ n (fld X (2 * (16 * n)) i * yc m) =
      fld (fld Y (2 * (16 * n)) i) 16 (2 * n - 1 - m) + dP n (fld X (2 * (16 * n)) i * yc m)) ∧
    (fld NEG W i < N ∧ fld V (16 * n) (fld NEG W i) + fld V (16 * n) i = 14 * ones n) ∧
    (i < n → ∀ m < n, fld (fld V (16 * n) i) 16 m = 7 + if m = i then 1 else 0) ∧
    (n ≤ i → parOK n W rtR PAR i = true) := by
  simp only [rootOK, cRowOK, strictB_eq, andB_eq_true, beq_eq_true, blt_eq_true, allLt_iff, nadd,
    nmul, nsub, nland, nshr, nshl, boolRec_true] at h
  obtain ⟨hV, hX, hY, hVX, hC, ⟨hj, hneg⟩, hp1, hp2⟩ := h
  have e2 : 2 * (16 * n) = 16 * (2 * n) := by ring
  have hvi : fld V (16 * n) i < 2 ^ (16 * n) := fld_lt _ _ _
  have hxi : fld X (2 * (16 * n)) i < 2 ^ (16 * (2 * n)) := e2 ▸ fld_lt _ _ _
  have hXl : ∀ m, fld (fld X (2 * (16 * n)) i) 16 m ≤ 7 := by
    intro m
    rcases lt_or_ge m (2 * n) with hm | hm
    · have h1 := lt_of_land_eq_zero (b := 3) (fld_lt _ 16 m) (by norm_num)
        (by intro j h1 h2; interval_cases j <;> first | rfl | decide)
        (fld_land_eq_zero hX (by decide) hm)
      have h2 : fld (fld X (2 * (16 * n)) i) 16 m < 8 := lt_of_lt_of_eq h1 (by norm_num)
      omega
    · rw [fld_eq_zero_of_lt 16 (2 * n) _ hxi hm]
      omega
  have hVl : ∀ m < n, fld (fld V (16 * n) i) 16 m < 16 := fun m hm =>
    lt_of_lt_of_eq (lt_of_land_eq_zero (b := 4) (fld_lt _ 16 m) (by norm_num)
      (by intro j h1 h2; interval_cases j <;> first | rfl | decide)
      (fld_land_eq_zero hV (by decide) hm)) (by norm_num)
  have h7 : 7 * ones n < 2 ^ (16 * n) := by
    rw [mul_ones]
    exact sum_lanes_lt 16 n _ (fun _ _ => by norm_num)
  refine ⟨hVl, hXl, ?_, ?_, fun m hm => (hC m hm), ⟨hj, hneg⟩, ?_, ?_⟩
  · intro m
    have hyi : fld Y (2 * (16 * n)) i < 2 ^ (16 * (2 * n)) := e2 ▸ fld_lt _ _ _
    rcases lt_or_ge m (2 * n) with hm | hm
    · have h1 := lt_of_land_eq_zero (b := 2) (fld_lt _ 16 m) (by norm_num)
        (by intro j h1 h2; interval_cases j <;> first | rfl | decide)
        (fld_land_eq_zero hY (by decide) hm)
      have h2 : fld (fld Y (2 * (16 * n)) i) 16 m < 4 := lt_of_lt_of_eq h1 (by norm_num)
      omega
    · rw [fld_eq_zero_of_lt 16 (2 * n) _ hyi hm]
      omega
  · intro m hm
    have hsh : fld X (2 * (16 * n)) i >>> (16 * n) < 2 ^ (16 * n) := lt_pow_of_lt_mul hxi
    have h1 := congrArg (fun t => fld t 16 m) hVX
    rw [fld_add hvi hsh (fun k hk => by
          rw [fld_shr]
          have a1 := hVl k hk
          have a2 := hXl (n + k)
          have a3 : fld (fld V (16 * n) i) 16 k + fld (fld X (2 * (16 * n)) i) 16 (n + k) ≤ 22 := by
            omega
          exact lt_of_le_of_lt a3 (by norm_num)) hm,
      fld_add (fld_lt _ _ _) h7 (fun k hk => by
          rw [fld_fld _ 16 n 0 k hk, fld_mul_ones 7 n k (by norm_num) hk]
          have a2 := hXl (n * 0 + k)
          have a3 : fld (fld X (2 * (16 * n)) i) 16 (n * 0 + k) + 7 ≤ 14 := by omega
          exact lt_of_le_of_lt a3 (by norm_num)) hm,
      fld_shr, fld_fld _ 16 n 0 m hm, fld_mul_ones 7 n m (by norm_num) hm, mul_zero,
      zero_add] at h1
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    push_cast at h2
    linear_combination h2
  · intro hi m hm
    have hp := hp1 hi
    have hs : 1 <<< (16 * i) < 2 ^ (16 * n) := by
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [hp, fld_add h7 hs (fun k hk => by
        rw [fld_mul_ones 7 n k (by norm_num) hk, fld_two_pow hi]
        split_ifs <;> norm_num) hm, fld_mul_ones 7 n m (by norm_num) hm, fld_two_pow hi]
  · intro hi
    exact hp2 (by
      cases hb : Nat.blt i n
      · rfl
      · exact absurd (blt_eq_true.1 hb) (by omega))

theorem cartan_symm_of (τ : Tag) (hsym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.cartan i j)
    (i j : Fin τ.rank) : τ.cartan i j = τ.cartan j i := by
  revert i j
  cases τ
  · exact absurd (hsym ⟨0, by decide⟩ ⟨0, by decide⟩) (by decide)
  · exact absurd (hsym ⟨0, by decide⟩ ⟨0, by decide⟩) (by decide)
  · change ∀ i j : Fin 4, Tag.cartan Tag.D4 i j = Tag.cartan Tag.D4 j i
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · change ∀ i j : Fin 6, Tag.cartan Tag.E6 i j = Tag.cartan Tag.E6 j i
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · change ∀ i j : Fin 7, Tag.cartan Tag.E7 i j = Tag.cartan Tag.E7 j i
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · change ∀ i j : Fin 8, Tag.cartan Tag.E8 i j = Tag.cartan Tag.E8 j i
    intro i j
    fin_cases i <;> fin_cases j <;> rfl

theorem iform_single (τ : Tag) (hsym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.cartan i j)
    (x : Fin τ.rank → ℤ) (k : Fin τ.rank) :
    iform x (Pi.single k 1) = ∑ j, τ.cartan k j * x j := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym, cartan_symm_of τ hsym j k, mul_comm]

variable (τ : Tag) {N W : ℕ} {yc rtR : ℕ → ℕ} {V X Y NEG PAR : ℕ}

theorem cart_row (hyc : ∀ m k : Fin τ.rank, (fld (yc m) 16 (τ.rank - 1 - k) : ℤ) -
      fld (yc m) 16 (2 * τ.rank - 1 - k) = τ.symmetrizedCartan m k)
    (hycb : ∀ m : Fin τ.rank, yc m < 2 ^ (32 * τ.rank))
    (hycl : ∀ m : Fin τ.rank, ∀ j, fld (yc m) 16 j ≤ 3)
    (hroot : ∀ i < N, rootOK τ.rank N W yc rtR V X Y NEG PAR i = true)
    {i : ℕ} (hi : i < N) (m : Fin τ.rank) :
    (fld (fld Y (2 * (16 * τ.rank)) i) 16 (τ.rank - 1 - m) : ℤ) -
        fld (fld Y (2 * (16 * τ.rank)) i) 16 (2 * τ.rank - 1 - m) =
      ∑ k, τ.symmetrizedCartan m k * vecOf τ.rank V i k := by
  have hn1 : 1 ≤ τ.rank := by cases τ <;> decide
  have hn8 : τ.rank ≤ 8 := by cases τ <;> decide
  obtain ⟨-, hXl, -, hVX, hC, -, -, -⟩ := root_lanes hn1 (hroot i hi)
  have e2 : 2 * (16 * τ.rank) = 16 * (2 * τ.rank) := by ring
  have hxi : fld X (2 * (16 * τ.rank)) i < 2 ^ (16 * (2 * τ.rank)) := e2 ▸ fld_lt _ _ _
  have hy : yc m < 2 ^ (16 * (2 * τ.rank)) := by
    rw [show 16 * (2 * τ.rank) = 32 * τ.rank by ring]
    exact hycb m
  obtain ⟨hd, -, -⟩ := dPQ hn1 hn8 hxi hy hXl (hycl m)
  have hc := congrArg (Nat.cast : ℕ → ℤ) (hC m m.2)
  push_cast at hc
  have h1 : (fld (fld Y (2 * (16 * τ.rank)) i) 16 (τ.rank - 1 - m) : ℤ) -
      fld (fld Y (2 * (16 * τ.rank)) i) 16 (2 * τ.rank - 1 - m) =
      (dP τ.rank (fld X (2 * (16 * τ.rank)) i * yc m) : ℤ) -
        dQ τ.rank (fld X (2 * (16 * τ.rank)) i * yc m) := by linear_combination hc
  rw [h1, hd, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hyc m a, ← hVX a a.2]
  simp only [vecOf]
  ring

theorem iform_lanes (hyc : ∀ m k : Fin τ.rank, (fld (yc m) 16 (τ.rank - 1 - k) : ℤ) -
      fld (yc m) 16 (2 * τ.rank - 1 - k) = τ.symmetrizedCartan m k)
    (hycb : ∀ m : Fin τ.rank, yc m < 2 ^ (32 * τ.rank))
    (hycl : ∀ m : Fin τ.rank, ∀ j, fld (yc m) 16 j ≤ 3)
    (hroot : ∀ i < N, rootOK τ.rank N W yc rtR V X Y NEG PAR i = true)
    {v g : ℕ} (hv : v < N) (hg : g < N) :
    ((dP τ.rank (fld X (2 * (16 * τ.rank)) v * fld Y (2 * (16 * τ.rank)) g) : ℤ) -
        dQ τ.rank (fld X (2 * (16 * τ.rank)) v * fld Y (2 * (16 * τ.rank)) g) =
      iform (vecOf τ.rank V v) (vecOf τ.rank V g)) ∧
    dP τ.rank (fld X (2 * (16 * τ.rank)) v * fld Y (2 * (16 * τ.rank)) g) ≤ 672 ∧
    dQ τ.rank (fld X (2 * (16 * τ.rank)) v * fld Y (2 * (16 * τ.rank)) g) ≤ 336 := by
  have hn1 : 1 ≤ τ.rank := by cases τ <;> decide
  have hn8 : τ.rank ≤ 8 := by cases τ <;> decide
  obtain ⟨-, hXv, -, hVXv, -, -, -, -⟩ := root_lanes hn1 (hroot v hv)
  obtain ⟨-, -, hYg, -, -, -, -, -⟩ := root_lanes hn1 (hroot g hg)
  have e2 : 2 * (16 * τ.rank) = 16 * (2 * τ.rank) := by ring
  have hxv : fld X (2 * (16 * τ.rank)) v < 2 ^ (16 * (2 * τ.rank)) := e2 ▸ fld_lt _ _ _
  have hyg : fld Y (2 * (16 * τ.rank)) g < 2 ^ (16 * (2 * τ.rank)) := e2 ▸ fld_lt _ _ _
  obtain ⟨hd, hp, hq⟩ := dPQ hn1 hn8 hxv hyg hXv hYg
  refine ⟨?_, hp, hq⟩
  rw [hd, ← Fin.sum_univ_eq_sum_range]
  simp only [iform]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cart_row τ hyc hycb hycl hroot hg a, ← hVXv a a.2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [vecOf]
  ring

end Decode

open CFSG.KC.TcRes.Lane in
theorem datumRaw_of_checks (τ : Tag) {N W : ℕ} {yc rtR : ℕ → ℕ} {V X Y NEG PAR SRT ADJ : ℕ}
    (hsym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.cartan i j)
    (hyc : ∀ m k : Fin τ.rank, (fld (yc m) 16 (τ.rank - 1 - k) : ℤ) -
      fld (yc m) 16 (2 * τ.rank - 1 - k) = τ.symmetrizedCartan m k)
    (hycb : ∀ m : Fin τ.rank, yc m < 2 ^ (32 * τ.rank))
    (hn : τ.rank ≤ N)
    (hroot : ∀ i < N, rootOK τ.rank N W yc rtR V X Y NEG PAR i = true)
    (hrow : ∀ g < N, rowOK τ.rank N W rtR V X Y ADJ g = true)
    (hsrt : srtOK τ.rank N W yc V SRT = true) :
    DatumRaw τ N (vecOf τ.rank V) (fun g v => fld (rtR g) W v)
      (fun g v => Nat.beq (fld (fld ADJ N g) 1 v) 1) (fun i => fld NEG W i) := by
  have hn1 : 1 ≤ τ.rank := by cases τ <;> decide
  simp only [srtOK, strictB_eq, andB_eq_true, allLt_iff, beq_eq_true, nmul, nland] at hsrt
  obtain ⟨hyM, hW⟩ := hsrt
  have hycl : ∀ m : Fin τ.rank, ∀ j, fld (yc m) 16 j ≤ 3 := by
    intro m j
    have hy : yc m < 2 ^ (16 * (2 * τ.rank)) := by
      rw [show 16 * (2 * τ.rank) = 32 * τ.rank by ring]
      exact hycb m
    rcases lt_or_ge j (2 * τ.rank) with hj | hj
    · have h1 := lt_of_land_eq_zero (b := 2) (fld_lt _ 16 j) (by norm_num)
        (by intro j h1 h2; interval_cases j <;> first | rfl | decide)
        (fld_land_eq_zero (hyM m m.2) (by decide) hj)
      have h2 : fld (yc m) 16 j < 4 := lt_of_lt_of_eq h1 (by norm_num)
      omega
    · rw [fld_eq_zero_of_lt 16 (2 * τ.rank) _ hy hj]
      omega
  have hR := fun i (hi : i < N) => root_lanes hn1 (hroot i hi)
  have hIF := fun v (hv : v < N) g (hg : g < N) => iform_lanes τ hyc hycb hycl hroot hv hg
  have hE : ∀ g < N, ∀ v < N, fld (rtR g) W v < N ∧
      vecOf τ.rank V (fld (rtR g) W v) =
        vecOf τ.rank V v - iform (vecOf τ.rank V v) (vecOf τ.rank V g) • vecOf τ.rank V g ∧
      (Nat.beq (fld (fld ADJ N g) 1 v) 1 = true ↔
        iform (vecOf τ.rank V v) (vecOf τ.rank V g) ≠ 0) := by
    intro g hg v hv
    have h := hrow g hg
    simp only [rowOK, entryOK, strictB_eq, allLt_iff, andB_eq_true, beq_eq_true, blt_eq_true,
      nadd, nmul, boolRec_nat] at h
    obtain ⟨ht, hEq, hA⟩ := h v hv
    obtain ⟨hIFe, hp, hq⟩ := hIF v hv g hg
    refine ⟨ht, ?_, ?_⟩
    · funext m
      have hlane := lanes_lin (fld_lt _ _ _) (fld_lt _ _ _) (fld_lt _ _ _)
        (fun k hk => by
          have a1 := (hR _ ht).1 k hk
          have a2 := (hR g hg).1 k hk
          have a3 := Nat.mul_le_mul hp (Nat.le_of_lt_succ a2)
          linarith)
        (fun k hk => by
          have a1 := (hR v hv).1 k hk
          have a2 := (hR g hg).1 k hk
          have a3 := Nat.mul_le_mul hq (Nat.le_of_lt_succ a2)
          linarith) hEq m.2
      simp only [vecOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hIFe]
      have h2 := congrArg (Nat.cast : ℕ → ℤ) hlane
      push_cast at h2
      linear_combination h2
    · rw [beq_eq_true, hA, ← hIFe]
      split_ifs with h1
      · simp [h1]
      · exact ⟨fun _ => by omega, fun _ => rfl⟩
  have hsimple : ∀ k : Fin τ.rank, vecOf τ.rank V k = Pi.single k 1 := by
    intro k
    funext m
    have h := (hR k (lt_of_lt_of_le k.2 hn)).2.2.2.2.2.2.1 k.2 m m.2
    simp only [vecOf, h, Pi.single_apply, Fin.val_inj]
    split_ifs <;> norm_num
  have hrefl : ∀ (k : Fin τ.rank), ∀ v < N, vecOf τ.rank V (fld (rtR k) W v) =
      reflect τ k (vecOf τ.rank V v) := by
    intro k v hv
    rw [(hE k (lt_of_lt_of_le k.2 hn) v hv).2.1, hsimple k, iform_single τ hsym, reflect]
  refine ⟨hn, hsimple, ?_, ?_, fun g hg v hv => ⟨(hE g hg v hv).1, (hE g hg v hv).2.1⟩,
    fun g hg v hv => (hE g hg v hv).2.2, ?_, ?_⟩
  ·
    intro i hi hni
    have h := (hR i hi).2.2.2.2.2.2.2 hni
    simp only [parOK, strictB_eq, andB_eq_true, blt_eq_true, beq_eq_true, nland, nshr] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨_, h1, ⟨_, h2⟩, ?_⟩
    rw [← hrefl ⟨_, h2⟩ _ (h1.trans hi)]
    simp only [h3]
  ·
    obtain ⟨hs1, -, hs3⟩ := srtWalk_spec N W (16 * τ.rank) V SRT N 0 0 hW
    have hkey : ∀ i < N, ∀ j < N, vecOf τ.rank V i = vecOf τ.rank V j →
        fld V (16 * τ.rank) i = fld V (16 * τ.rank) j := by
      intro i hi j hj h
      rw [eq_sum_lanes 16 τ.rank (fld V (16 * τ.rank) i) (fld_lt _ _ _),
        eq_sum_lanes 16 τ.rank (fld V (16 * τ.rank) j) (fld_lt _ _ _)]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      have h1 := congrFun h ⟨m, hm⟩
      simp only [vecOf] at h1
      have h2 : fld (fld V (16 * τ.rank) i) 16 m = fld (fld V (16 * τ.rank) j) 16 m := by omega
      rw [h2]
    let f : Fin N → Fin N := fun s => ⟨fld SRT W (0 + s), hs1 s s.2⟩
    have hmono : ∀ s s' : Fin N, fld V (16 * τ.rank) (f s) = fld V (16 * τ.rank) (f s') →
        s = s' := by
      intro s s' h
      rcases lt_trichotomy s s' with hl | he | hl
      · exact absurd h (ne_of_lt (hs3 s s' hl s'.2))
      · exact he
      · exact absurd h (ne_of_gt (hs3 s' s hl s.2))
    have hinj : Function.Injective f := fun s s' h => hmono s s' (by rw [h])
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro i hi j hj h
    obtain ⟨s, hs⟩ := hsurj ⟨i, hi⟩
    obtain ⟨s', hs'⟩ := hsurj ⟨j, hj⟩
    have h1 := hkey i hi j hj h
    have h2 : s = s' := hmono s s' (by rw [hs, hs']; exact h1)
    have h3 := congrArg Fin.val (hs.symm.trans (h2 ▸ hs'))
    exact h3
  ·
    intro i hi
    obtain ⟨hj, hneg⟩ := (hR i hi).2.2.2.2.2.1
    refine ⟨hj, ?_⟩
    funext m
    have h1 := congrArg (fun t => fld t 16 m) hneg
    rw [fld_add (fld_lt _ _ _) (fld_lt _ _ _) (fun k hk => by
        have a1 := (hR _ hj).1 k hk
        have a2 := (hR i hi).1 k hk
        have a3 : fld (fld V (16 * τ.rank) (fld NEG W i)) 16 k + fld (fld V (16 * τ.rank) i) 16 k ≤
          30 := by omega
        exact lt_of_le_of_lt a3 (by norm_num)) m.2,
      fld_mul_ones 14 τ.rank m (by norm_num) m.2] at h1
    simp only [vecOf, Pi.neg_apply]
    omega
  ·
    intro k v hv
    exact ⟨_, (hE k (lt_of_lt_of_le k.2 hn) v hv).1, hrefl k v hv⟩

open CFSG.KC.TcRes.Lane in
theorem iform_of_checks (τ : Tag) {N W : ℕ} {yc rtR : ℕ → ℕ} {V X Y NEG PAR : ℕ}
    (hyc : ∀ m k : Fin τ.rank, (fld (yc m) 16 (τ.rank - 1 - k) : ℤ) -
      fld (yc m) 16 (2 * τ.rank - 1 - k) = τ.symmetrizedCartan m k)
    (hycb : ∀ m : Fin τ.rank, yc m < 2 ^ (32 * τ.rank))
    (hycl : ∀ m : Fin τ.rank, ∀ j, fld (yc m) 16 j ≤ 3)
    (hroot : ∀ i < N, rootOK τ.rank N W yc rtR V X Y NEG PAR i = true) :
    ∀ v < N, ∀ g < N,
      (dP τ.rank (fld X (32 * τ.rank) v * fld Y (32 * τ.rank) g) : ℤ) -
        dQ τ.rank (fld X (32 * τ.rank) v * fld Y (32 * τ.rank) g) =
      iform (vecOf τ.rank V v) (vecOf τ.rank V g) := by
  intro v hv g hg
  have e : 32 * τ.rank = 2 * (16 * τ.rank) := by ring
  rw [e]
  exact (iform_lanes τ hyc hycb hycl hroot hv hg).1

namespace DatumRaw

variable {τ : Tag} {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool}
  {neg : ℕ → ℕ}

theorem isRoot (h : DatumRaw τ N vec rt adj neg) : ∀ i < N, IsRoot τ (vec i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases lt_or_ge i τ.rank with hlt | hge
    · have h1 := h.simple ⟨i, hlt⟩
      simp only at h1
      rw [h1]
      exact IsRoot.basis _
    · obtain ⟨i', hi', k, hk⟩ := h.parent i hi hge
      rw [hk]
      exact IsRoot.reflect k (ih i' hi' (hi'.trans hi))

theorem exists_eq (h : DatumRaw τ N vec rt adj neg) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ i < N, vec i = γ := by
  induction hγ with
  | basis j => exact ⟨j, lt_of_lt_of_le j.isLt h.rank_le, h.simple j⟩
  | reflect k _ ih =>
    obtain ⟨v, hv, rfl⟩ := ih
    exact h.closed k v hv

end DatumRaw

@[expose] def TupleOf {τ : Tag} (vec : ℕ → Fin τ.rank → ℤ) (N t : ℕ) (w : WeylGroup τ) : Prop :=
  ∀ j : Fin τ.rank, tf t j < N ∧ vec (tf t j) = w • (Pi.single j 1 : Fin τ.rank → ℤ)

structure ForestRaw {τ : Tag} (vec : ℕ → Fin τ.rank → ℤ) (N : ℕ) (nrec nrep : ℕ)
    (key repKey : ℕ → ℕ) : Prop where
  rep : ∀ k < nrep, ∃ w, TupleOf vec N (repKey k) w
  recs : ∀ p < nrec, ∃ w, TupleOf vec N (key p) w ∧
    ∃ k < nrep, ∃ w', TupleOf vec N (repKey k) w' ∧ IsConj w' w
  dist : ∀ p < nrec, ∀ q < nrec, (∀ j : Fin τ.rank, tf (key p) j = tf (key q) j) → p = q

section ForestDecode

open CFSG.KC.TcRes.Lane

theorem tf_eq (t j : ℕ) : tf t j = fld t 7 j := by
  rw [fld_eq]
  change (t >>> (j * 7)) &&& 127 = _
  rw [Nat.shiftRight_eq_div_pow, mul_comm j 7]
  exact Nat.and_two_pow_sub_one_eq_mod _ 7

theorem rtv_eq (RT g v : ℕ) (hv : v < 72) : rtv RT g v = fld (fld RT 504 g) 7 v := by
  have h := fld_fld RT 7 72 g v hv
  rw [show 7 * 72 = 504 by norm_num] at h
  rw [h, fld_eq]
  change (RT >>> ((g * 72 + v) * 7)) &&& 127 = _
  rw [Nat.shiftRight_eq_div_pow, show (g * 72 + v) * 7 = 7 * (72 * g + v) by ring]
  exact Nat.and_two_pow_sub_one_eq_mod _ 7

theorem rtv_lt (RT g v : ℕ) : rtv RT g v < 128 := by
  change (RT >>> ((g * 72 + v) * 7)) &&& 127 < 128
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem tf_pack (a : ℕ → ℕ) (ha : ∀ i, a i < 128) {j : ℕ} (hj : j < 6) :
    tf (a 0 ||| (a 1 <<< 7 ||| (a 2 <<< 14 ||| (a 3 <<< 21 ||| (a 4 <<< 28 ||| a 5 <<< 35))))) j =
      a j := by
  have hb : ∀ i k, 7 ≤ k → (a i).testBit k = false := fun i k hk =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (ha i) (by
      calc 128 = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk))
  rw [tf_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld]
  by_cases h7 : b < 7
  · interval_cases j <;> interval_cases b <;>
      simp [Nat.testBit_or, Nat.testBit_shiftLeft, hb]
  · simp [h7, hb j b (by omega)]

variable {vec : ℕ → Fin Tag.E6.rank → ℤ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ} {RT : ℕ}

theorem e6_sym : ∀ i j : Fin Tag.E6.rank, Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
  intro i j
  change ((1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) * Tag.E6.cartan) i j = _
  rw [one_mul]

theorem rt_reflect (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj neg)
    (l : Fin Tag.E6.rank) {v : ℕ} (hv : v < 72) :
    rtv RT l v < 72 ∧ vec (rtv RT l v) = reflect Tag.E6 l (vec v) := by
  rw [rtv_eq RT l v hv]
  obtain ⟨h1, h2⟩ := hD.refl l (by have := l.2; change l.1 < 6 at this; omega) v hv
  refine ⟨h1, ?_⟩
  rw [h2, hD.simple l, iform_single Tag.E6 e6_sym, reflect]

theorem rt_root (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj neg)
    {g v : ℕ} (hg : g < 72) (hv : v < 72) :
    rtv RT g v < 72 ∧ vec (rtv RT g v) = vec v - iform (vec v) (vec g) • vec g := by
  rw [rtv_eq RT g v hv]
  exact hD.refl g hg v hv

theorem tupleOf_lm
    (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj neg)
    {t : ℕ} {w : WeylGroup Tag.E6} (ht : TupleOf vec 72 t w) (l : Fin Tag.E6.rank) :
    TupleOf vec 72 (lm RT l t) (simple Tag.E6 l * w) := by
  intro j
  have e : tf (lm RT l t) j = rtv RT l (tf t j) :=
    tf_pack (fun i => rtv RT l (tf t i)) (fun i => rtv_lt _ _ _) j.2
  obtain ⟨h1, h2⟩ := rt_reflect hD l (ht j).1
  rw [e, h2, (ht j).2, mul_smul, simple_smul]
  exact ⟨h1, rfl⟩

theorem tupleOf_cj
    (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj neg)
    {t : ℕ} {w : WeylGroup Tag.E6} (ht : TupleOf vec 72 t w) (l : Fin Tag.E6.rank) :
    TupleOf vec 72 (cj RT t l) (simple Tag.E6 l * w * simple Tag.E6 l) := by
  intro j
  have e : tf (cj RT t l) j = rtv RT l (rtv RT (tf t l) (tf t j)) := by
    rw [cj, strictN_eq]
    exact tf_pack (fun i => rtv RT l (rtv RT (tf t l) (tf t i))) (fun i => rtv_lt _ _ _) j.2
  obtain ⟨i1, i2⟩ := rt_root hD (ht l).1 (ht j).1
  obtain ⟨o1, o2⟩ := rt_reflect hD l i1
  rw [e]
  refine ⟨o1, ?_⟩
  rw [o2, i2, (ht j).2, (ht l).2, iform_smul, mul_smul, mul_smul, simple_smul, simple_smul]
  congr 1
  rw [reflect, iform_single Tag.E6 e6_sym, smul_sub, smul_comm w]

theorem wordOK_spec
    (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj neg) (goal : ℕ) :
    ∀ c u t (w : WeylGroup Tag.E6), TupleOf vec 72 t w → wordOK RT goal c u t = true →
      ∃ w', TupleOf vec 72 goal w' := by
  intro c
  induction c with
  | zero =>
    intro u t w ht h
    have h' : t = goal := beq_eq_true.1 h
    exact ⟨w, h' ▸ ht⟩
  | succ c ih =>
    intro u t w ht h
    change strictB (u &&& 7) (fun l => andB (Nat.blt l 6)
      (strictB (lm RT l t) fun t' => wordOK RT goal c (u >>> 3) t')) = true at h
    simp only [strictB_eq, andB_eq_true, blt_eq_true] at h
    exact ih _ _ _ (tupleOf_lm hD ht ⟨_, h.1⟩) h.2

theorem walk_succ (LF : ℕ → ℕ) (REPS c rest prev : ℕ) :
    walk RT LF REPS (c + 1) rest prev =
      stepOK RT LF REPS (rest &&& M67) prev (walk RT LF REPS c (rest >>> 67)) := by
  simp only [walk, strictB_eq]
  rfl

theorem fld67_zero (x : ℕ) : x &&& M67 = fld x 67 0 := by
  rw [fld_eq]
  change x &&& (2 ^ 67 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem walk_spec (LF : ℕ → ℕ) (REPS : ℕ) : ∀ c rest prev, walk RT LF REPS c rest prev = true →
    (∀ t < c, recOK RT LF REPS (fld rest 67 t) = true) ∧
    (∀ t < c, prev < keyOf (fld rest 67 t)) ∧
    ∀ t t', t < t' → t' < c → keyOf (fld rest 67 t) < keyOf (fld rest 67 t') := by
  intro c
  induction c with
  | zero => intro rest prev _; exact ⟨fun t h => absurd h (Nat.not_lt_zero _),
      fun t h => absurd h (Nat.not_lt_zero _), fun t t' _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ c ih =>
    intro rest prev h
    rw [walk_succ, stepOK, andB_eq_true, andB_eq_true, blt_eq_true, fld67_zero] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨i1, i2, i3⟩ := ih _ _ h3
    have hs : ∀ t, fld (rest >>> 67) 67 t = fld rest 67 (t + 1) := fun t => by
      have := fld_shr rest 67 1 t
      rw [mul_one] at this
      rw [this, add_comm]
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t t' htt ht' => ?_⟩
    · rcases t with _ | t
      · exact h2
      · rw [← hs]
        exact i1 t (by omega)
    · rcases t with _ | t
      · exact h1
      · rw [← hs]
        exact h1.trans (i2 t (by omega))
    · obtain ⟨t', rfl⟩ : ∃ u, t' = u + 1 := ⟨t' - 1, by omega⟩
      rw [← hs]
      rcases t with _ | t
      · exact i2 t' (by omega)
      · rw [← hs]
        exact i3 t t' (by omega) (by omega)

theorem ent_eq (LF : ℕ → ℕ) {L i : ℕ} (hi : i < 64) : ent LF (64 * L + i) = fld (LF L) 67 i := by
  have h1 : (64 * L + i) >>> 6 = L := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : (64 * L + i) &&& 63 = i := by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    omega
  change (LF ((64 * L + i) >>> 6) >>> (((64 * L + i) &&& 63) * 67)) &&& (2 ^ 67 - 1) = _
  rw [h1, h2, fld_eq, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, mul_comm i 67]

theorem keyOf_lt (e : ℕ) : keyOf e < 2 ^ (7 * 6) := by
  change e &&& M42 < _
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem keys_mono (LF : ℕ → ℕ) (REPS : ℕ) (hleaf : ∀ L < 810, leafOK RT LF REPS L = true) :
    ∀ p q, p < q → q < 51840 → keyOf (ent LF p) < keyOf (ent LF q) := by
  have hstep : ∀ p, p + 1 < 51840 → keyOf (ent LF p) < keyOf (ent LF (p + 1)) := by
    intro p hp
    obtain ⟨L, i, hi, rfl⟩ : ∃ L i, i < 64 ∧ p = 64 * L + i := ⟨p / 64, p % 64, Nat.mod_lt _
      (by norm_num), (Nat.div_add_mod p 64).symm⟩
    rcases lt_or_eq_of_le (by omega : i ≤ 63) with h | h
    · have hw := walk_spec LF REPS 64 (LF L) (prevKey LF L) (hleaf L (by omega))
      rw [show 64 * L + i + 1 = 64 * L + (i + 1) by ring, ent_eq LF hi, ent_eq LF (by omega)]
      exact hw.2.2 i (i + 1) (by omega) (by omega)
    · subst h
      have hw := walk_spec LF REPS 64 (LF (L + 1)) (prevKey LF (L + 1)) (hleaf (L + 1) (by omega))
      have e1 : 64 * L + 63 + 1 = 64 * (L + 1) + 0 := by ring
      rw [e1, ent_eq LF (by norm_num : 0 < 64)]
      have e2 : prevKey LF (L + 1) = keyOf (ent LF (64 * L + 63)) := by
        change keyOf (ent LF (L * 64 + 63)) = _
        rw [mul_comm]
      rw [← e2]
      exact hw.2.1 0 (by norm_num)
  intro p q hpq hq
  induction q with
  | zero => exact absurd hpq (Nat.not_lt_zero _)
  | succ q ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hpq with h | rfl
    · exact (ih h (by omega)).trans (hstep q hq)
    · exact hstep p hq

theorem recOK_of_leaf (LF : ℕ → ℕ) (REPS : ℕ) (hleaf : ∀ L < 810, leafOK RT LF REPS L = true)
    {p : ℕ} (hp : p < 51840) : recOK RT LF REPS (ent LF p) = true := by
  obtain ⟨L, i, hi, rfl⟩ : ∃ L i, i < 64 ∧ p = 64 * L + i := ⟨p / 64, p % 64, Nat.mod_lt _
    (by norm_num), (Nat.div_add_mod p 64).symm⟩
  rw [ent_eq LF hi]
  exact (walk_spec LF REPS 64 (LF L) (prevKey LF L) (hleaf L (by omega))).1 i hi

end ForestDecode

open CFSG.KC.TcRes.Lane in
theorem forestRaw_of_checks
    {vec : ℕ → Fin Tag.E6.rank → ℤ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    {RT REPS WRD : ℕ} {LF : ℕ → ℕ}
    (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj neg)
    (hleaf : ∀ L < 810, leafOK RT LF REPS L = true)
    (hrep : ∀ k < 25, repOK RT REPS WRD k = true) :
    ForestRaw vec 72 51840 25 (fun p => keyOf (ent LF p))
      (fun k => Nat.land (Nat.shiftRight REPS (k * 42)) M42) := by
  have hrep : ∀ k < 25, ∃ w, TupleOf vec 72 (Nat.land (Nat.shiftRight REPS (k * 42)) M42) w := by
    intro k hk
    have h := hrep k hk
    simp only [repOK, strictB_eq] at h
    have h1 : TupleOf vec 72 172878758016 1 := by
      intro j
      have e : tf 172878758016 j = j := by
        have := j.2
        change j.1 < 6 at this
        interval_cases hj : j.1 <;> first | rfl | decide
      rw [e, one_smul]
      exact ⟨by have := j.2; change j.1 < 6 at this; omega, hD.simple j⟩
    exact wordOK_spec hD _ _ _ _ 1 h1 h
  refine ⟨hrep, ?_, ?_⟩
  · intro p hp
    suffices H : ∀ d, ∀ p < 51840, depOf (ent LF p) = d → ∃ w, TupleOf vec 72 (keyOf (ent LF p)) w ∧
        ∃ k < 25, ∃ w', TupleOf vec 72 (Nat.land (Nat.shiftRight REPS (k * 42)) M42) w' ∧
          IsConj w' w from H _ p hp rfl
    intro d
    induction d with
    | zero =>
      intro p hp hd
      have h := recOK_of_leaf LF REPS hleaf hp
      simp only [recOK, boolRec_true, beq_eq_true, beq_eq_false, andB_eq_true, blt_eq_true] at h
      obtain ⟨h1, h2⟩ := h.1 hd
      obtain ⟨w, hw⟩ := hrep _ h1
      exact ⟨w, h2 ▸ hw, _, h1, w, hw, IsConj.refl w⟩
    | succ d ih =>
      intro p hp hd
      have h := recOK_of_leaf LF REPS hleaf hp
      simp only [recOK, boolRec_true, beq_eq_true, beq_eq_false, andB_eq_true, blt_eq_true,
        strictB_eq, fparOK] at h
      obtain ⟨h1, h2, h3, h4⟩ := h.2 (by omega)
      obtain ⟨w, hw, k, hk, w', hw', hc⟩ := ih _ h1 (by omega)
      refine ⟨_, h4 ▸ tupleOf_cj hD hw ⟨_, h3⟩, k, hk, w', hw', hc.trans ?_⟩
      refine isConj_iff.2 ⟨simple Tag.E6 ⟨_, h3⟩, ?_⟩
      rw [CoxeterSystem.inv_simple]
  · intro p hp q hq hpq
    have hk : keyOf (ent LF p) = keyOf (ent LF q) := by
      rw [eq_sum_lanes 7 6 _ (keyOf_lt _), eq_sum_lanes 7 6 (keyOf (ent LF q)) (keyOf_lt _)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have := hpq ⟨j, hj⟩
      simp only [tf_eq] at this
      rw [this]
    rcases lt_trichotomy p q with h | h | h
    · exact absurd hk (ne_of_lt (keys_mono LF REPS hleaf p q h hq))
    · exact h
    · exact absurd hk (ne_of_gt (keys_mono LF REPS hleaf q p h hp))

theorem forall_isConj_rep
    {vec : ℕ → Fin Tag.E6.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool}
    {neg : ℕ → ℕ} {key repKey : ℕ → ℕ} (hD : DatumRaw Tag.E6 72 vec rt adj neg)
    (hF : ForestRaw vec 72 51840 25 key repKey) (hW : Nat.card (WeylGroup Tag.E6) = 51840)
    (g : WeylGroup Tag.E6) : ∃ k < 25, ∃ w', TupleOf vec 72 (repKey k) w' ∧ IsConj w' g := by
  classical
  choose f hf using fun p : Fin 51840 => hF.recs p.1 p.2
  have hinj : Function.Injective f := by
    intro p q hpq
    have hp := (hf p).1
    have hq := (hf q).1
    rw [hpq] at hp
    apply Fin.ext
    apply hF.dist p.1 p.2 q.1 q.2
    intro j
    exact hD.inj _ (hp j).1 _ (hq j).1 ((hp j).2.trans (hq j).2.symm)
  obtain ⟨p, rfl⟩ := surjective_of_injective_card hW f hinj g
  obtain ⟨k, hk, w', hw', hc⟩ := (hf p).2
  exact ⟨k, hk, w', hw', hc⟩

end CFSG.KC.TcRes

end
