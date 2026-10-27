module

public import CFSG.HardMathSupport.C14IdxA2Pair
public import CFSG.HardMathSupport.C14IdxCorootConj
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen
open scoped MatrixGroups

private theorem isRoot_iterate_map {τ : Tag} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθΦ : ∀ γ, IsRoot τ γ → IsRoot τ (θ γ)) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : IsRoot τ ((⇑θ)^[n] γ) := by
  induction n with
  | zero => simpa using hγ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hθΦ _ ih

private theorem pow_two_pow_mul {M : Type*} [Monoid M] (x : M) (a b : ℕ) :
    (x ^ 2 ^ a) ^ 2 ^ b = x ^ 2 ^ (a + b) := by
  rw [← pow_mul, ← pow_add]

private theorem monoidEnd_pow_pinnedX
    {τ : Tag} {L : Type} [Field L] {e : ℕ}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθΦ : ∀ γ, IsRoot τ γ → IsRoot τ (θ γ)) (σ : Monoid.End (ModGL τ L))
    (hσX : ∀ γ, IsRoot τ γ → ∀ c : L,
      σ (pinnedX τ L γ c) = pinnedX τ L (θ γ) (c ^ 2 ^ e))
    (n : ℕ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : L) :
    (σ ^ n) (pinnedX τ L γ c) = pinnedX τ L ((⇑θ)^[n] γ) (c ^ 2 ^ (e * n)) := by
  revert γ hγ c
  induction n with
  | zero => intro γ hγ c; simp [Monoid.End.coe_one]
  | succ n ih =>
    intro γ hγ c
    rw [pow_succ', Monoid.End.coe_mul, Function.comp_apply, ih hγ c,
      hσX _ (isRoot_iterate_map hθΦ n hγ) (c ^ 2 ^ (e * n)),
      Function.iterate_succ_apply', pow_two_pow_mul, Nat.mul_succ]

private theorem list_prod_pow_of_pairwise {M : Type*} [Monoid M] (l : List M) (n : ℕ)
    (h : l.Pairwise Commute) : l.prod ^ n = (l.map (· ^ n)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hp := List.pairwise_cons.1 h
    have ha : Commute a l.prod := Commute.list_prod_right l a hp.1
    rw [List.prod_cons, List.map_cons, List.prod_cons, ha.mul_pow n, ih hp.2]

private theorem list_prod_map_mul_of_commute {ι M : Type*} [Monoid M] (l : List ι)
    (hl : l.Nodup) (a b : ι → M)
    (h : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (a i) (b j)) :
    (l.map fun i => a i * b i).prod = (l.map a).prod * (l.map b).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hnd := List.nodup_cons.1 hl
    have hxnot : x ∉ xs := hnd.1
    have hxsnd : xs.Nodup := hnd.2
    have hx : ∀ i ∈ xs, Commute (b x) (a i) := fun i hi =>
      (h i (List.mem_cons_of_mem x hi) x List.mem_cons_self (by
        intro hix; exact hxnot (hix ▸ hi))).symm
    have hxs : ∀ i ∈ xs, ∀ j ∈ xs, i ≠ j → Commute (a i) (b j) := fun i hi j hj hij =>
      h i (List.mem_cons_of_mem x hi) j (List.mem_cons_of_mem x hj) hij
    rw [List.map_cons, List.prod_cons, ih hxsnd hxs, List.map_cons, List.map_cons,
      List.prod_cons, List.prod_cons]
    have hcomm : Commute (b x) (xs.map a).prod :=
      Commute.list_prod_right (xs.map a) (b x) (by
        intro y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
        exact hx i hi)
    calc (a x * b x) * ((xs.map a).prod * (xs.map b).prod)
        = a x * (b x * (xs.map a).prod) * (xs.map b).prod := by group
      _ = a x * ((xs.map a).prod * b x) * (xs.map b).prod := by rw [hcomm.eq]
      _ = (a x * (xs.map a).prod) * (b x * (xs.map b).prod) := by group

private theorem prod_ofFn_pow_mem_closure {G : Type*} [Group G] (σ : Monoid.End G)
    {k p : ℕ} (H K : Subgroup G)
    (hcomm : ∀ i j : ℕ, i < k → j < k → i ≠ j → ∀ x ∈ H, ∀ y ∈ H,
      Commute ((σ ^ i) x) ((σ ^ j) y))
    (hK : ∀ i < k, ∀ x ∈ H, (σ ^ i) x ∈ K) {x : G}
    (hx : x ∈ Subgroup.closure {y | y ∈ H ∧ (σ ^ k) y = y ∧ ∃ j : ℕ, y ^ p ^ j = 1}) :
    (List.ofFn fun i : Fin k => (σ ^ (i : ℕ)) x).prod ∈
      Subgroup.closure {y | y ∈ K ∧ σ y = y ∧ ∃ j : ℕ, y ^ p ^ j = 1} := by
  classical
  let N : G → G := fun x => (List.ofFn fun i : Fin k => (σ ^ (i : ℕ)) x).prod
  have hN_mul : ∀ x ∈ H, ∀ y ∈ H, N (x * y) = N x * N y := by
    intro x hx y hy
    have h := list_prod_map_mul_of_commute (List.finRange k) (List.nodup_finRange k)
      (fun i : Fin k => (σ ^ (i : ℕ)) x) (fun i : Fin k => (σ ^ (i : ℕ)) y)
      (fun i _ j _ hij => hcomm i j i.isLt j.isLt (fun h => hij (Fin.ext h)) x hx y hy)
    simpa [N, List.ofFn_eq_map, ← map_mul] using h
  have hN_one : N 1 = 1 := by simp [N]
  have hN_fixed : ∀ x ∈ H, (σ ^ k) x = x → σ (N x) = N x := by
    intro x hx hxk
    let f : Fin k → G := fun i => (σ ^ (i : ℕ)) x
    have hNx : N x = (List.ofFn f).prod := rfl
    have hmap : σ (N x) = (List.ofFn fun i : Fin k => σ (f i)).prod := by
      rw [hNx, map_list_prod, List.map_ofFn]
      rfl
    have hσf : ∀ i : Fin k, σ (f i) = f (finRotate k i) := by
      intro i
      dsimp only [f]
      change (σ * σ ^ (i : ℕ)) x = (σ ^ ((finRotate k i : ℕ))) x
      rw [← pow_succ']
      by_cases h : (i : ℕ) + 1 < k
      · rw [show (finRotate k i : ℕ) = (i : ℕ) + 1 by
          simp [finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt h]]
      · have hk' : (i : ℕ) + 1 = k := by have := i.isLt; omega
        rw [show (finRotate k i : ℕ) = 0 by simp [finRotate_apply, Fin.val_add, hk'],
          hk', hxk]
        simp
    have hmap : σ (N x) = (List.ofFn fun i : Fin k => f (finRotate k i)).prod := by
      rw [hNx, map_list_prod, List.map_ofFn]
      congr 1
      exact List.ofFn_inj.2 (funext hσf)
    have hperm : (List.ofFn fun i : Fin k => f (finRotate k i)).Perm (List.ofFn f) :=
      Equiv.Perm.ofFn_comp_perm (finRotate k) f
    have hpairwise : (List.ofFn f).Pairwise Commute := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hi' : i < k := by simpa using hi
      have hj' : j < k := by simpa using hj
      rw [List.getElem_ofFn, List.getElem_ofFn]
      exact hcomm i j hi' hj' (by omega) x hx x hx
    calc σ (N x) = (List.ofFn fun i : Fin k => f (finRotate k i)).prod := hmap
      _ = (List.ofFn f).prod := (hperm.symm.prod_eq' hpairwise).symm
      _ = N x := hNx.symm
  have hN_pow : ∀ x ∈ H, ∀ j : ℕ, x ^ p ^ j = 1 → (N x) ^ p ^ j = 1 := by
    intro x hx j hxpow
    have hpairwise : (List.ofFn fun i : Fin k => (σ ^ (i : ℕ)) x).Pairwise Commute := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hi' : i < k := by simpa using hi
      have hj' : j < k := by simpa using hj
      rw [List.getElem_ofFn, List.getElem_ofFn]
      change Commute ((σ ^ i) x) ((σ ^ j) x)
      exact hcomm i j hi' hj' (by omega) x hx x hx
    have hfac : ∀ i : Fin k, ((σ ^ (i : ℕ)) x) ^ p ^ j = 1 := by
      intro i
      rw [← map_pow (σ ^ (i : ℕ)) x (p ^ j), hxpow, map_one]
    calc (N x) ^ p ^ j
        = ((List.ofFn fun i : Fin k => (σ ^ (i : ℕ)) x).prod) ^ p ^ j := rfl
      _ = ((List.ofFn fun i : Fin k => (σ ^ (i : ℕ)) x).map (· ^ p ^ j)).prod :=
          list_prod_pow_of_pairwise _ _ hpairwise
      _ = 1 := by
          rw [List.map_ofFn]
          simp only [Function.comp_def, hfac, List.ofFn_const, List.prod_replicate, one_pow]
  have hN_K : ∀ x ∈ H, N x ∈ K := by
    intro x hx
    exact Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact hK i i.isLt x hx
  have hND : ∀ z ∈ Subgroup.closure {y | y ∈ H ∧ (σ ^ k) y = y ∧ ∃ j : ℕ, y ^ p ^ j = 1},
      N z ∈ Subgroup.closure {y | y ∈ K ∧ σ y = y ∧ ∃ j : ℕ, y ^ p ^ j = 1} := by
    intro z hz
    have hP : z ∈ H ∧ N z ∈
        Subgroup.closure {y | y ∈ K ∧ σ y = y ∧ ∃ j : ℕ, y ^ p ^ j = 1} := by
      refine Subgroup.closure_induction (p := fun z _ => z ∈ H ∧ N z ∈
        Subgroup.closure {y | y ∈ K ∧ σ y = y ∧ ∃ j : ℕ, y ^ p ^ j = 1}) ?_ ?_ ?_ ?_ hz
      · intro y hy
        obtain ⟨j, hj⟩ := hy.2.2
        exact ⟨hy.1, Subgroup.subset_closure
          ⟨hN_K y hy.1, hN_fixed y hy.1 hy.2.1, j, hN_pow y hy.1 j hj⟩⟩
      · exact ⟨H.one_mem, by rw [hN_one]; exact Subgroup.one_mem _⟩
      · intro y z _ _ hy hz
        refine ⟨H.mul_mem hy.1 hz.1, ?_⟩
        rw [hN_mul y hy.1 z hz.1]
        exact Subgroup.mul_mem _ hy.2 hz.2
      · intro y _ hy
        refine ⟨H.inv_mem hy.1, ?_⟩
        have hmul := hN_mul y⁻¹ (H.inv_mem hy.1) y hy.1
        have hprod : N (y⁻¹) * N y = 1 := by rw [← hmul, inv_mul_cancel, hN_one]
        have hinv : N (y⁻¹) = (N y)⁻¹ := eq_inv_of_mul_eq_one_left hprod
        rw [hinv]
        exact Subgroup.inv_mem _ hy.2
    exact hP.2
  exact hND x hx

theorem rootDiagUnit_coordTuple_mem_closure_of_a2Cycle
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e)
    {Q : ModGL τ L} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (hθΦ : ∀ γ, IsRoot τ γ → IsRoot τ (θ γ))
    (hQX : ∀ γ, IsRoot τ γ → ∀ c : L, Q * pinnedX τ L γ c * Q⁻¹ = pinnedX τ L (θ γ) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    {k : ℕ} (hk : 1 ≤ k) {α : Fin τ.rank → ℤ} (hαβ : OddDerivPair τ α ((⇑θ)^[k] α))
    (hθk : (⇑θ)^[2 * k] α = α)
    (hcomm : ∀ i, 0 < i → i < k → ∀ γ ∈ a2PairRoots α ((⇑θ)^[k] α),
      ∀ δ ∈ a2PairRoots α ((⇑θ)^[k] α), ∀ s t : L,
        Commute (pinnedX τ L γ s) (pinnedX τ L ((⇑θ)^[i] δ) t))
    {O : Finset (Fin τ.rank → ℤ)} (hO : O = (Finset.range (2 * k)).image fun i => (⇑θ)^[i] α)
    (hOcard : O.card = 2 * k) (c : (Fin τ.rank → ℤ) → Lˣ) (hc : ∀ γ ∈ O, c (θ γ) = c γ ^ 2 ^ e) :
    rootDiagUnit τ (coordTuple O c) ∈ Subgroup.closure {x : ModGL τ L |
      x ∈ rootSpan τ L {γ | ∃ i < k, ∃ δ ∈ a2PairRoots α ((⇑θ)^[k] α), (⇑θ)^[i] δ = γ} ∧
        frobTwistGL τ L 2 e Q x = x ∧ ∃ j : ℕ, x ^ 2 ^ j = 1} := by
  classical
  let β : Fin τ.rank → ℤ := (⇑θ)^[k] α
  let R₀ : Set (Fin τ.rank → ℤ) := a2PairRoots α β
  let S_T : Set (Fin τ.rank → ℤ) := {γ | ∃ i < k, ∃ δ ∈ R₀, (⇑θ)^[i] δ = γ}
  let σ : Monoid.End (ModGL τ L) := frobTwistGL τ L 2 e Q
  let d₀ : ModGL τ L := rootDiagUnit τ (coordTuple {α, β} c)
  let N : ModGL τ L → ModGL τ L := fun x =>
    (List.ofFn fun i : Fin k => (σ ^ (i : ℕ)) x).prod
  have hαβ_roots : IsRoot τ α ∧ IsRoot τ β ∧ IsRoot τ (α + β) := by
    have hB : oddDerivPairB τ α β = true := oddDerivPairB_iff.mpr hαβ
    simp only [oddDerivPairB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hB
    exact ⟨RootOps.isRootB_iff.1 hB.1.1.1.1.1.1.1,
      RootOps.isRootB_iff.1 hB.1.1.1.1.1.1.2,
      RootOps.isRootB_iff.1 hB.1.1.1.2⟩
  have hR₀root : ∀ γ ∈ R₀, IsRoot τ γ := by
    intro γ hγ
    simp only [R₀, a2PairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hαβ_roots.1
    · exact hαβ_roots.2.1
    · exact hαβ_roots.2.2
    · exact IsRoot.neg hαβ_roots.1
    · exact IsRoot.neg hαβ_roots.2.1
    · exact IsRoot.neg hαβ_roots.2.2
  have hθk_apply : ∀ n (x : Fin τ.rank → ℤ), (n • θ) x = (⇑θ)^[n] x := by
    intro n
    induction n with
    | zero => simp [AddAut.zero_apply]
    | succ n ih => intro x; rw [succ_nsmul, AddAut.add_apply, ih (θ x),
        Function.iterate_succ_apply]
  have hββ : (⇑θ)^[k] β = α := by
    change (⇑θ)^[k] ((⇑θ)^[k] α) = α
    rw [← Function.iterate_add_apply, show k + k = 2 * k by omega, hθk]
  have hθkα : (k • θ) α = β := by simpa only [β] using hθk_apply k α
  have hθkβ : (k • θ) β = α := by simpa only [hθk_apply] using hββ
  have hθk_iso : ∀ x y, iform ((k • θ) x) ((k • θ) y) = iform x y := by
    have hiter : ∀ n (x y : Fin τ.rank → ℤ),
        iform ((⇑θ)^[n] x) ((⇑θ)^[n] y) = iform x y := by
      intro n
      induction n with
      | zero => intro x y; simp
      | succ n ih =>
        intro x y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hθ]
        exact ih x y
    intro x y
    rw [hθk_apply, hθk_apply]
    exact hiter k x y
  have hσX : ∀ γ, IsRoot τ γ → ∀ c : L,
      σ (pinnedX τ L γ c) = pinnedX τ L (θ γ) (c ^ 2 ^ e) := by
    intro γ hγ c
    change frobTwistGL τ L 2 e Q (pinnedX τ L γ c) = pinnedX τ L (θ γ) (c ^ 2 ^ e)
    rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, iterateFrobenius_def]
    exact hQX γ hγ (c ^ 2 ^ e)
  have hσkX : ∀ γ ∈ R₀, ∀ c : L,
      (σ ^ k) (pinnedX τ L γ c) = pinnedX τ L ((k • θ) γ) (c ^ 2 ^ (e * k)) := by
    intro γ hγ c
    rw [monoidEnd_pow_pinnedX hθΦ σ hσX k (hR₀root γ hγ) c, hθk_apply]
  have hO_mem : ∀ i, i < 2 * k → (⇑θ)^[i] α ∈ O := fun i hi =>
    by rw [hO]; exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  have hβ_iter : ∀ i, (⇑θ)^[i] β = (⇑θ)^[i + k] α := by
    intro i
    change (⇑θ)^[i] ((⇑θ)^[k] α) = (⇑θ)^[i + k] α
    exact (Function.iterate_add_apply (⇑θ) i k α).symm
  have orbit_pow : ∀ (x : Fin τ.rank → ℤ) (n : ℕ), (∀ i < n, (⇑θ)^[i] x ∈ O) →
      c ((⇑θ)^[n] x) = c x ^ 2 ^ (e * n) := by
    intro x n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hx
      rw [Function.iterate_succ_apply', hc _ (hx n (by omega)),
        ih (fun i hi => hx i (by omega)), pow_two_pow_mul, Nat.mul_succ]
  have hcβ : c β = c α ^ 2 ^ (e * k) := by
    change c ((⇑θ)^[k] α) = c α ^ 2 ^ (e * k)
    exact orbit_pow α k fun i hi => hO_mem i (by omega)
  have hcα : c α = c β ^ 2 ^ (e * k) := by
    have h := orbit_pow β k fun i hi => by
      rw [hβ_iter i]
      exact hO_mem (i + k) (by omega)
    rw [hββ] at h
    exact h
  have hek : 1 ≤ e * k := by simpa using Nat.mul_le_mul he hk
  have hpair := rootDiagUnit_coordTuple_mem_closure_of_a2Pair
    (e := e * k) (σ := σ ^ k) (θ := k • θ) hek hαβ hθkα hθkβ hσkX c hcβ hcα
  let G_T : Set (ModGL τ L) :=
    {x | x ∈ rootSpan τ L S_T ∧ frobTwistGL τ L 2 e Q x = x ∧ ∃ j : ℕ, x ^ 2 ^ j = 1}
  let D₀ : Subgroup (ModGL τ L) :=
    Subgroup.closure {x | x ∈ rootSpan τ L R₀ ∧ (σ ^ k) x = x ∧ ∃ j : ℕ, x ^ 2 ^ j = 1}
  let T : Subgroup (ModGL τ L) := Subgroup.closure G_T
  have hd₀ : d₀ ∈ D₀ := by
    change rootDiagUnit τ (coordTuple {α, (⇑θ)^[k] α} c) ∈
      Subgroup.closure {x : ModGL τ L |
        x ∈ rootSpan τ L (a2PairRoots α ((⇑θ)^[k] α)) ∧
          (σ ^ k) x = x ∧ ∃ j : ℕ, x ^ 2 ^ j = 1}
    exact hpair
  have hσ_mem : ∀ n (S : Set (Fin τ.rank → ℤ)), (∀ γ ∈ S, IsRoot τ γ) →
      ∀ x ∈ rootSpan τ L S, (σ ^ n) x ∈ rootSpan τ L ((⇑θ)^[n] '' S) := by
    intro n S hS x hx
    exact CFSG.HardMathSupport.Lang.TwE6Step3.map_mem_rootSpan
      (σ ^ n : ModGL τ L →* ModGL τ L) (fun γ => (⇑θ)^[n] γ)
      (fun γ hγ c => ⟨c ^ 2 ^ (e * n),
        monoidEnd_pow_pinnedX hθΦ σ hσX n (hS γ hγ) c⟩)
      (fun γ hγ => Set.mem_image_of_mem _ hγ) hx
  have rootSpan_commute' : ∀ {A B : Set (Fin τ.rank → ℤ)}
      (h : ∀ γ ∈ A, ∀ δ ∈ B, ∀ s t : L, Commute (pinnedX τ L γ s) (pinnedX τ L δ t))
      {a b : ModGL τ L}, a ∈ rootSpan τ L A → b ∈ rootSpan τ L B → Commute a b := by
    intro A B h a b ha hb
    have hsub : ∀ γ ∈ A, ∀ δ ∈ B, ∀ x ∈ rootSubgroup τ L γ,
        ∀ y ∈ rootSubgroup τ L δ, Commute x y := by
      intro γ hγ δ hδ x hx
      refine Subgroup.closure_induction
        (p := fun x _ => ∀ y ∈ rootSubgroup τ L δ, Commute x y) ?_ ?_ ?_ ?_ hx
      · intro x hx y hy
        obtain ⟨s, rfl⟩ := hx
        refine Subgroup.closure_induction (p := fun y _ => Commute (pinnedX τ L γ s) y)
          ?_ ?_ ?_ ?_ hy
        · intro y hy; obtain ⟨t, rfl⟩ := hy; exact h γ hγ δ hδ s t
        · exact Commute.one_right _
        · intro y z _ _ ihy ihz; exact Commute.mul_right ihy ihz
        · intro y _ ihy; exact ihy.inv_right
      · intro y _; exact Commute.one_left _
      · intro x z _ _ ihx ihz y hy; exact Commute.mul_left (ihx y hy) (ihz y hy)
      · intro x _ ih y hy; exact (ih y hy).inv_left
    exact CFSG.HardMathSupport.Lang.TwE6Step3.rootSpan_commute hsub ha hb
  have hcomm_span : ∀ m, 0 < m → m < k → ∀ a ∈ rootSpan τ L R₀,
      ∀ b ∈ rootSpan τ L ((⇑θ)^[m] '' R₀), Commute a b := by
    intro m hm0 hmk a ha b hb
    exact rootSpan_commute' (h := by
      intro γ hγ δ hδ s t
      obtain ⟨δ₀, hδ₀, rfl⟩ :=
        (Set.mem_image (fun δ => (⇑θ)^[m] δ) R₀ δ).1 hδ
      exact hcomm m hm0 hmk γ hγ δ₀ hδ₀ s t) ha hb
  have hcomm_gen : ∀ i j : ℕ, i < k → j < k → i ≠ j → ∀ x ∈ rootSpan τ L R₀,
      ∀ y ∈ rootSpan τ L R₀, Commute ((σ ^ i) x) ((σ ^ j) y) := by
    have hlt : ∀ {i j : ℕ}, i < j → j < k → ∀ {x y : ModGL τ L},
        x ∈ rootSpan τ L R₀ → y ∈ rootSpan τ L R₀ →
        Commute ((σ ^ i) x) ((σ ^ j) y) := by
      intro i j hij hjk x y hx hy
      have hz : (σ ^ (j - i)) y ∈ rootSpan τ L ((⇑θ)^[j - i] '' R₀) :=
        hσ_mem (j - i) R₀ hR₀root y hy
      have hxy : Commute x ((σ ^ (j - i)) y) :=
        hcomm_span (j - i) (by omega) (by omega) x hx _ hz
      have hpow : σ ^ j = σ ^ i * σ ^ (j - i) := by
        rw [← pow_add, show i + (j - i) = j by omega]
      have hmap : (σ ^ i) (x * ((σ ^ (j - i)) y)) =
          (σ ^ i) (((σ ^ (j - i)) y) * x) := by rw [hxy.eq]
      rw [map_mul, map_mul] at hmap
      have hσj : (σ ^ j) y = (σ ^ i) ((σ ^ (j - i)) y) := by
        rw [hpow, Monoid.End.coe_mul]
        rfl
      rwa [hσj]
    intro i j hi hj hij x hx y hy
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt h hj hx hy
    · exact (hlt h hi hy hx).symm
  have hK_gen : ∀ i < k, ∀ x ∈ rootSpan τ L R₀, (σ ^ i) x ∈ rootSpan τ L S_T := by
    intro i hi x hx
    exact rootSpan_mono (by rintro γ ⟨δ, hδ, rfl⟩; exact ⟨i, hi, δ, hδ, rfl⟩)
      (hσ_mem i R₀ hR₀root x hx)
  have hN_mem : N d₀ ∈ T :=
    prod_ofFn_pow_mem_closure σ (rootSpan τ L R₀) (rootSpan τ L S_T) (p := 2)
      hcomm_gen hK_gen (x := d₀) (by simpa [D₀] using hd₀)
  have hinj : Set.InjOn (fun j : ℕ => (⇑θ)^[j] α) (Finset.range (2 * k)) := by
    rw [← Finset.card_image_iff, ← hO, hOcard, Finset.card_range]
  have hf_ne : ∀ i : Fin k, (⇑θ)^[(i : ℕ)] α ≠ (⇑θ)^[(i : ℕ) + k] α := by
    intro i h
    have h1 : (i : ℕ) ∈ Finset.range (2 * k) := by simp only [Finset.mem_range]; omega
    have h2 : (i : ℕ) + k ∈ Finset.range (2 * k) := by simp only [Finset.mem_range]; omega
    have := hinj h1 h2 h
    omega
  have hstep_d : ∀ i ≤ k, (σ ^ i) d₀ =
      rootDiagUnit τ (coordTuple {((⇑θ)^[i] α), ((⇑θ)^[i] β)} c) := by
    intro i
    induction i with
    | zero => intro _; simp [d₀]
    | succ i ih =>
      intro hi
      have hik : i < k := by omega
      let S : Finset (Fin τ.rank → ℤ) := {((⇑θ)^[i] α), ((⇑θ)^[i] β)}
      have hSc : ∀ γ ∈ S, IsRoot τ γ ∧ c (θ γ) = c γ ^ 2 ^ e := by
        intro γ hγ
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hγ
        rcases hγ with rfl | rfl
        · exact ⟨isRoot_iterate_map hθΦ i hαβ_roots.1, hc _ (hO_mem i (by omega))⟩
        · refine ⟨isRoot_iterate_map hθΦ i hαβ_roots.2.1, ?_⟩
          rw [hβ_iter i]
          exact hc _ (hO_mem (i + k) (by omega))
      have hstep : frobTwistGL τ L 2 e Q (rootDiagUnit τ (coordTuple S c)) =
          rootDiagUnit τ (coordTuple (S.image θ) c) := by
        have hpow : coordTuple S (c ^ 2 ^ e) = (coordTuple S c) ^ 2 ^ e :=
          map_pow (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom S)
            c (2 ^ e)
        have hFr : entrywiseFrobGL τ L 2 e (rootDiagUnit τ (coordTuple S c)) =
            rootDiagUnit τ (coordTuple S (c ^ 2 ^ e)) := by
          rw [entrywiseFrobGL_rootDiagUnit_eq_map, hpow]
          congr 1
        have hgX : ∀ α, IsRoot τ α → ∃ ε : Lˣ, ∀ x : L,
            Q * pinnedX τ L α x * Q⁻¹ = pinnedX τ L (θ α) (ε * x) :=
          fun α hα => ⟨1, fun x => by simpa using hQX α hα x⟩
        have hQd : Q * rootDiagUnit τ (coordTuple S (c ^ 2 ^ e)) * Q⁻¹ =
            rootDiagUnit τ (coordTuple (S.image θ) fun γ => (c ^ 2 ^ e) (θ.symm γ)) :=
          conj_rootDiagUnit_coordTuple (g := Q) (π := θ) hθ hθΦ hgX hQT
            (fun β hβ => (hSc β hβ).1) (c ^ 2 ^ e)
        have hcβ : ∀ β ∈ S.image θ, (c ^ 2 ^ e) (θ.symm β) = c β := by
          intro β hβ
          obtain ⟨γ, hγ, hγβ⟩ := Finset.mem_image.1 hβ
          have hγ' : θ.symm β = γ := by rw [← hγβ, AddEquiv.symm_apply_apply]
          rw [hγ', Pi.pow_apply]
          exact ((hSc γ hγ).2).symm.trans (by rw [hγβ])
        rw [frobTwistGL_apply, hFr, hQd,
          CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordTuple_congr hcβ]
      have himage : S.image ⇑θ =
          {((⇑θ)^[i + 1] α), ((⇑θ)^[i + 1] β)} := by
        simp only [S, Finset.image_insert, Finset.image_singleton,
          Function.iterate_succ_apply']
      calc (σ ^ (i + 1)) d₀ = σ ((σ ^ i) d₀) := by rw [pow_succ', Monoid.End.coe_mul]; rfl
        _ = σ (rootDiagUnit τ (coordTuple S c)) := by rw [ih (by omega)]
        _ = rootDiagUnit τ (coordTuple (S.image θ) c) := hstep
        _ = rootDiagUnit τ (coordTuple {((⇑θ)^[i + 1] α), ((⇑θ)^[i + 1] β)} c) := by
            rw [himage]
  have hN_final : N d₀ = rootDiagUnit τ (coordTuple O c) := by
    let G : (Fin τ.rank → ℤ) → (Fin τ.rank → Lˣ) :=
      fun γ i => c γ ^ corootPair γ (Pi.single i 1)
    have hTprod : (List.ofFn fun i : Fin k =>
        coordTuple {((⇑θ)^[(i : ℕ)] α), ((⇑θ)^[(i : ℕ)] β)} c).prod = coordTuple O c := by
      rw [Fin.prod_ofFn]
      calc ∏ i : Fin k, coordTuple {((⇑θ)^[(i : ℕ)] α), ((⇑θ)^[(i : ℕ)] β)} c
          = ∏ i : Fin k, (G ((⇑θ)^[(i : ℕ)] α) * G ((⇑θ)^[(i : ℕ) + k] α)) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [hβ_iter (i : ℕ), coordTuple_eq_prod, Finset.prod_pair (hf_ne i)]
        _ = (∏ i : Fin k, G ((⇑θ)^[(i : ℕ)] α)) *
              (∏ i : Fin k, G ((⇑θ)^[(i : ℕ) + k] α)) := Finset.prod_mul_distrib
        _ = (∏ i ∈ Finset.range k, G ((⇑θ)^[i] α)) *
              (∏ i ∈ Finset.range k, G ((⇑θ)^[i + k] α)) := by
            rw [Finset.prod_range (fun i => G ((⇑θ)^[i] α)),
              Finset.prod_range (fun i => G ((⇑θ)^[i + k] α))]
        _ = (∏ i ∈ Finset.range k, G ((⇑θ)^[i] α)) *
              (∏ i ∈ Finset.range k, G ((⇑θ)^[k + i] α)) := by
            congr 1
            exact Finset.prod_congr rfl fun i _ => by rw [Nat.add_comm]
        _ = ∏ j ∈ Finset.range (2 * k), G ((⇑θ)^[j] α) := by
            rw [Nat.two_mul, ← Finset.prod_range_add]
        _ = ∏ γ ∈ O, G γ := by
            rw [hO]
            exact (Finset.prod_image (f := G) (g := fun j => (⇑θ)^[j] α)
              (fun i hi j hj hij => hinj hi hj hij)).symm
        _ = coordTuple O c := (coordTuple_eq_prod O c).symm
    calc N d₀ = (List.ofFn fun i : Fin k =>
          rootDiagUnit τ (coordTuple {((⇑θ)^[(i : ℕ)] α), ((⇑θ)^[(i : ℕ)] β)} c)).prod := by
          simp only [N]; congr 1; rw [List.ofFn_inj]; funext i
          exact hstep_d i (Nat.le_of_lt i.isLt)
      _ = ((List.ofFn fun i : Fin k =>
            coordTuple {((⇑θ)^[(i : ℕ)] α), ((⇑θ)^[(i : ℕ)] β)} c).map
              (rootDiagUnitHom τ L)).prod := by
          rw [List.map_ofFn]; rfl
      _ = rootDiagUnit τ ((List.ofFn fun i : Fin k =>
            coordTuple {((⇑θ)^[(i : ℕ)] α), ((⇑θ)^[(i : ℕ)] β)} c).prod) :=
          (map_list_prod (rootDiagUnitHom τ L) _).symm
      _ = rootDiagUnit τ (coordTuple O c) := by rw [hTprod]
  change rootDiagUnit τ (coordTuple O c) ∈ T
  rw [← hN_final]
  exact hN_mem
end CFSG.HardMathSupport.C14Idx
