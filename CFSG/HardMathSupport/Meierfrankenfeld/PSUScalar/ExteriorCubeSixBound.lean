module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.ExteriorCubeSix
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFlagExtension
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups
open Module Matrix
open scoped BigOperators

theorem aSpan_mono {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r ε : ℕ}
    (w : HypIndex r ε → V) {i j : ℕ} (hij : i ≤ j) :
    aSpan (K := K) w i ≤ aSpan (K := K) w j := by
  unfold aSpan
  refine Submodule.span_mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

theorem crossProduct_sum_sum {K : Type} [CommRing K] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → Fin 3 → K) (v : κ → Fin 3 → K) (c : ι → K) (d : κ → K) :
    crossProduct (∑ i, c i • u i) (∑ j, d j • v j) =
      ∑ i, ∑ j, (c i * d j) • crossProduct (u i) (v j) := by
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

section WedgeHelpers

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem wedge3_smul_first (c : K) (a b d : V) :
    wedge3 (K := K) (c • a) b d = c • wedge3 (K := K) a b d := by
  rw [wedge3, wedge3]
  have h : (![c • a, b, d] : Fin 3 → V) = Function.update ![a, b, d] 0 (c • a) := by
    funext i
    fin_cases i <;> simp
  rw [h]
  have h' := (exteriorPower.ιMulti (R := K) (M := V) 3).map_update_smul
    (![a, b, d] : Fin 3 → V) 0 c a
  have h1 : Function.update ![a, b, d] 0 a = ![a, b, d] := by
    funext i
    fin_cases i <;> simp
  rw [h1] at h'
  exact h'

theorem wedge3_smul_second (c : K) (a b d : V) :
    wedge3 (K := K) a (c • b) d = c • wedge3 (K := K) a b d := by
  rw [wedge3, wedge3]
  have h : (![a, c • b, d] : Fin 3 → V) = Function.update ![a, b, d] 1 (c • b) := by
    funext i
    fin_cases i <;> simp
  rw [h]
  have h' := (exteriorPower.ιMulti (R := K) (M := V) 3).map_update_smul
    (![a, b, d] : Fin 3 → V) 1 c b
  have h1 : Function.update ![a, b, d] 1 b = ![a, b, d] := by
    funext i
    fin_cases i <;> simp
  rw [h1] at h'
  exact h'

theorem wedge3_sum_first {ι : Type*} [Fintype ι] (u : ι → K) (e : ι → V) (b d : V) :
    wedge3 (K := K) (∑ i, u i • e i) b d =
      ∑ i, u i • wedge3 (K := K) (e i) b d := by
  classical
  let s := (Finset.univ : Finset ι)
  change wedge3 (K := K) (∑ i ∈ s, u i • e i) b d =
    ∑ i ∈ s, u i • wedge3 (K := K) (e i) b d
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h0 : (0 : V) = (0 : K) • (0 : V) := (zero_smul K (0 : V)).symm
      rw [h0, wedge3_smul_first]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, wedge3_add_first,
        wedge3_smul_first, ih]

theorem wedge3_sum_second {ι : Type*} [Fintype ι] (u : ι → K) (e : ι → V) (a d : V) :
    wedge3 (K := K) a (∑ i, u i • e i) d =
      ∑ i, u i • wedge3 (K := K) a (e i) d := by
  classical
  let s := (Finset.univ : Finset ι)
  change wedge3 (K := K) a (∑ i ∈ s, u i • e i) d =
    ∑ i ∈ s, u i • wedge3 (K := K) a (e i) d
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h0 : (0 : V) = (0 : K) • (0 : V) := (zero_smul K (0 : V)).symm
      rw [h0, wedge3_smul_second]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, wedge3_add_second,
        wedge3_smul_second, ih]

theorem wedge3_swap_first (a b d : V) :
    wedge3 (K := K) b a d = - wedge3 (K := K) a b d := by
  have hzero : wedge3 (K := K) (a + b) (a + b) d = 0 :=
    wedge3_eq_zero_of_eq (Or.inl rfl)
  rw [wedge3_add_first, wedge3_add_second, wedge3_add_second,
    wedge3_eq_zero_of_eq (Or.inl rfl), wedge3_eq_zero_of_eq (Or.inl rfl),
    zero_add, add_zero] at hzero
  rw [add_comm] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

theorem wedge3_swap_second (a b d : V) :
    wedge3 (K := K) a d b = - wedge3 (K := K) a b d := by
  have hzero : wedge3 (K := K) a (b + d) (b + d) = 0 :=
    wedge3_eq_zero_of_eq (Or.inr (Or.inr rfl))
  rw [wedge3_add_second, wedge3_add_third, wedge3_add_third,
    wedge3_eq_zero_of_eq (Or.inr (Or.inr rfl)),
    wedge3_eq_zero_of_eq (Or.inr (Or.inr rfl)),
    zero_add, add_zero] at hzero
  rw [add_comm] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

theorem wedge3_swap_first_third (a b d : V) :
    wedge3 (K := K) d b a = - wedge3 (K := K) a b d := by
  have hzero : wedge3 (K := K) (a + d) b (a + d) = 0 :=
    wedge3_eq_zero_of_eq (Or.inr (Or.inl rfl))
  have hexp : wedge3 (K := K) (a + d) b (a + d) =
      wedge3 (K := K) a b a + wedge3 (K := K) a b d +
        (wedge3 (K := K) d b a + wedge3 (K := K) d b d) := by
    simp only [wedge3_add_first, wedge3_add_third]
    abel
  rw [hexp, wedge3_eq_zero_of_eq (Or.inr (Or.inl rfl)),
    wedge3_eq_zero_of_eq (Or.inr (Or.inl rfl)), zero_add, add_zero] at hzero
  rw [add_comm] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

end WedgeHelpers

theorem card_le_sq_of_exteriorPower_three_of_le_statedSU {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {A : Subgroup (GL (Fin 6) K)}
    (hAS : A ≤ CFSG.Open.StatedSU 6 (2 ^ f) K) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hq : ∀ a ∈ A, ∀ b ∈ A,
      (exteriorPower.map 3 (Matrix.toLin' (a : Matrix (Fin 6) (Fin 6) K)) - 1) *
        (exteriorPower.map 3 (Matrix.toLin' (b : Matrix (Fin 6) (Fin 6) K)) - 1) = 0) :
    Nat.card A ≤ (2 ^ f) ^ 2 := by
  classical
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero, one_pow] at hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    omega
  have h : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, Nat.mul_comm]⟩
  have : CharP K 2 := h.charP
  let V := Fin 6 → K
  let B : V →ₛₗ[h.bar] V →ₗ[K] K := stdHermForm h 6
  let T : A → Module.End K V := fun a =>
    Matrix.toLin' ((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  let N : A → Module.End K V := fun a => T a - 1
  have hsquare : ∀ a : A, (a : GL (Fin 6) K) * (a : GL (Fin 6) K) = 1 := by
    intro a
    simpa [pow_two] using hA.2 (a : GL (Fin 6) K) a.2
  have hT_mul : ∀ a b : A, T a * T b = T (a * b) := by
    intro a b
    ext x
    simp [T, Module.End.mul_apply, Matrix.toLin'_apply]
  have hT_sq : ∀ a : A, T a * T a = 1 := by
    intro a
    have hmul : (a * a : A) = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hsquare a
    rw [hT_mul, hmul]
    change Matrix.toLin' (1 : Matrix (Fin 6) (Fin 6) K) = 1
    rw [Matrix.toLin'_one]
    rfl
  have hT_comm : ∀ a b : A, T a * T b = T b * T a := by
    intro a b
    calc T a * T b = T (a * b) := hT_mul a b
      _ = T (b * a) := by rw [hA.1.is_comm.comm a b]
      _ = T b * T a := (hT_mul b a).symm
  have hN_mul : ∀ a b : A, N a * N b = 0 := by
    intro a b
    have h := sub_one_mul_sub_one_eq_zero_of_exteriorPower_three (K := K) (V := V)
      (x := T a) (y := T b) (hT_sq a) (hT_sq b) (hT_comm a b)
      (hq (a : GL (Fin 6) K) a.2 (b : GL (Fin 6) K) b.2)
    simpa [N] using h
  have hT_invol : ∀ (a : A) (z : V), T a (T a z) = z := by
    intro a z
    have h := congrArg (fun f : Module.End K V => f z) (hT_sq a)
    simpa [Module.End.mul_apply] using h
  have huni : ∀ (a : A) (x y : V), B (T a x) (T a y) = B x y := by
    intro a x y
    have h := ((mem_unitarySU_iff_isometry h).mp (hAS a.2)).2 x y
    have hT : ∀ z : V, T a z = ((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ z :=
      fun z => Matrix.toLin'_apply _ z
    rw [hT x, hT y]
    exact h
  have hself : ∀ (a : A) (x y : V), B (N a x) y = B x (N a y) := by
    intro a x y
    have h1 : B (T a x) y = B x (T a y) := by
      conv_lhs => rw [← hT_invol a y]
      exact huni a x (T a y)
    simp only [N, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [h1]
  let U : Submodule K V := Submodule.span K (⋃ a : A, (LinearMap.range (N a) : Set V))
  have hU_mem : ∀ (a : A) (x : V), N a x ∈ U := by
    intro a x
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨a, ⟨x, rfl⟩⟩)
  have hUiso : ∀ x ∈ U, ∀ y ∈ U, B x y = 0 := by
    intro x hx y hy
    refine Submodule.span_induction₂ (p := fun x y _ _ => B x y = 0)
      (s := ⋃ a : A, (LinearMap.range (N a) : Set V))
      (t := ⋃ a : A, (LinearMap.range (N a) : Set V)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro x y hx hy
      obtain ⟨a, u, hu⟩ := Set.mem_iUnion.mp hx
      obtain ⟨b, v, hv⟩ := Set.mem_iUnion.mp hy
      rw [← hu, ← hv]
      calc B (N a u) (N b v) = B u (N a (N b v)) := hself a u (N b v)
        _ = B u ((N a * N b) v) := by rw [Module.End.mul_apply]
        _ = 0 := by rw [hN_mul a b]; simp
    · intro y hy
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz ihx ihy
      simp [map_add, ihx, ihy]
    · intro x y z hx hy hz ihy ihz
      simp [map_add, ihy, ihz]
    · intro r x y hx hy ih
      simp [ih]
    · intro r x y hx hy ih
      simp [ih]
  obtain ⟨C, hC, hCU⟩ := exists_isotropicChain_eq (B := B) U hUiso
  obtain ⟨hk3, w, hw, hspan⟩ := exists_hypBasis_of_isotropicChain h (Module.finrank K U)
    (stdHermForm_isSymm h 6) (stdHermForm_separatingLeft h 6) (r := 3) (ε := 0)
    (by omega)
    (by change Module.finrank K (Fin 6 → K) = 2 * 3 + 0; rw [Module.finrank_fin_fun])
    C hC
  let R : Submodule K V := aSpan (⇑w) 3
  let E : Fin 3 → V := fun i => w (.inl i)
  let F : Fin 3 → V := fun i => w (.inr (.inr i))
  have hUR : U ≤ R := by
    rw [← hCU, hspan (Module.finrank K U) le_rfl]
    exact aSpan_mono (⇑w) hk3
  have hE_li : LinearIndependent K E := by
    have h := w.linearIndependent.comp (fun i : Fin 3 => (Sum.inl i : HypIndex 3 0)) (by
      intro i j hij
      simpa using hij)
    simpa [E, Function.comp_def] using h
  have hR_eq : R = Submodule.span K (Set.range E) := by
    simp [R, E, aSpan]
  have hE_mem : ∀ i : Fin 3, E i ∈ R := by
    intro i
    rw [hR_eq]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hR_iso : ∀ x ∈ R, ∀ y ∈ R, B x y = 0 := by
    intro x hx y hy
    rw [hR_eq] at hx hy
    refine Submodule.span_induction₂ (p := fun x y _ _ => B x y = 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro x y hx hy
      obtain ⟨i, hi⟩ := Set.mem_range.mp hx
      obtain ⟨j, hj⟩ := Set.mem_range.mp hy
      rw [← hi, ← hj]
      have h := hw (.inl i) (.inl j)
      simpa [E, hypGram_inl_inl] using h
    · intro y hy
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz ihx ihy
      simp [map_add, ihx, ihy]
    · intro x y z hx hy hz ihy ihz
      simp [map_add, ihy, ihz]
    · intro r x y hx hy ih
      simp [ih]
    · intro r x y hx hy ih
      simp [ih]
  have hNR : ∀ (a : A) (x : V), x ∈ R → N a x = 0 := by
    intro a x hx
    refine stdHermForm_separatingLeft h 6 (N a x) ?_
    intro z
    rw [hself a x z]
    exact hR_iso x hx (N a z) (hUR (hU_mem a z))
  have hFE : ∀ i j : Fin 3, B (F i) (E j) = if i = j then 1 else 0 := by
    intro i j
    have h := hw (.inr (.inr i)) (.inl j)
    simpa [F, E, hypGram_inr_inr_inl] using h
  have hcoord : ∀ x ∈ R, x = ∑ i, B (F i) x • E i := by
    intro x hx
    rw [hR_eq] at hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [hFE]
    · intro j _ hj
      have hji : i ≠ j := fun h => hj h.symm
      rw [hFE, if_neg hji, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hNF : ∀ (a : A) (j : Fin 3),
      N a (F j) = ∑ i, B (F i) (N a (F j)) • E i := by
    intro a j
    exact hcoord (N a (F j)) (hUR (hU_mem a (F j)))
  let M : A → Matrix (Fin 3) (Fin 3) K := fun a i j => B (F i) (N a (F j))
  have hMherm : ∀ (a : A) (i j : Fin 3), (M a i j) ^ (2 ^ f) = M a j i := by
    intro a i j
    have hsym := (stdHermForm_isSymm h 6).eq (F i) (N a (F j))
    have hself' : B (N a (F j)) (F i) = B (F j) (N a (F i)) := hself a (F j) (F i)
    have hbar : h.bar (M a i j) = M a j i := by
      rw [hsym, hself']
    simpa [M, h.bar_apply] using hbar
  have hT_apply : ∀ (a : A) (x : V), T a x = x + N a x := by
    intro a x
    simp only [N, LinearMap.sub_apply, Module.End.one_apply]
    abel
  have hexp : ∀ (N' : Module.End K V) (u v w : V),
      wedge3 (K := K) (u + N' u) (v + N' v) w =
        wedge3 (K := K) u v w + wedge3 (K := K) (N' u) v w +
          wedge3 (K := K) u (N' v) w + wedge3 (K := K) (N' u) (N' v) w := by
    intro N' u v w
    rw [wedge3_add_first, wedge3_add_second, wedge3_add_second]
    abel
  have hdd : ∀ (a b : A) (i j k : Fin 3), i ≠ j →
      ((exteriorPower.map 3 (T a) - 1) * (exteriorPower.map 3 (T b) - 1))
        (wedge3 (K := K) (F i) (F j) (E k)) =
      wedge3 (K := K) (N a (F i)) (N b (F j)) (E k) +
        wedge3 (K := K) (N b (F i)) (N a (F j)) (E k) := by
    intro a b i j k hij
    set x := F i with hx
    set y := F j with hy
    set z := E k with hz
    set p := N b x with hp
    set q := N b y with hq
    set s := N a x with hs
    set t := N a y with ht
    have hbz : N b z = 0 := hNR b z (hE_mem k)
    have haz : N a z = 0 := hNR a z (hE_mem k)
    have hap : N a p = 0 := by
      have h := congrArg (fun f : Module.End K V => f x) (hN_mul a b)
      simpa [hp, Module.End.mul_apply] using h
    have haq : N a q = 0 := by
      have h := congrArg (fun f : Module.End K V => f y) (hN_mul a b)
      simpa [hq, Module.End.mul_apply] using h
    have hb1 : (exteriorPower.map 3 (T b) - 1) (wedge3 (K := K) x y z) =
        wedge3 (K := K) p y z + wedge3 (K := K) x q z + wedge3 (K := K) p q z := by
      rw [LinearMap.sub_apply, Module.End.one_apply, wedge3_map]
      rw [hT_apply b x, hT_apply b y, hT_apply b z, hbz, add_zero]
      rw [hexp (N b) x y z]
      abel
    have ha1 : (exteriorPower.map 3 (T a) - 1) (wedge3 (K := K) p y z) =
        wedge3 (K := K) p t z := by
      rw [LinearMap.sub_apply, Module.End.one_apply, wedge3_map]
      rw [hT_apply a p, hT_apply a y, hT_apply a z, hap, haz]
      simp only [add_zero]
      rw [wedge3_add_second]
      abel
    have ha2 : (exteriorPower.map 3 (T a) - 1) (wedge3 (K := K) x q z) =
        wedge3 (K := K) s q z := by
      rw [LinearMap.sub_apply, Module.End.one_apply, wedge3_map]
      rw [hT_apply a x, hT_apply a q, hT_apply a z, haq, haz]
      simp only [add_zero]
      rw [wedge3_add_first]
      abel
    have ha3 : (exteriorPower.map 3 (T a) - 1) (wedge3 (K := K) p q z) = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, wedge3_map]
      rw [hT_apply a p, hT_apply a q, hT_apply a z, hap, haq, haz]
      simp only [add_zero]
      abel
    calc ((exteriorPower.map 3 (T a) - 1) * (exteriorPower.map 3 (T b) - 1))
          (wedge3 (K := K) x y z)
        = (exteriorPower.map 3 (T a) - 1)
            ((exteriorPower.map 3 (T b) - 1) (wedge3 (K := K) x y z)) := by
          rw [Module.End.mul_apply]
      _ = (exteriorPower.map 3 (T a) - 1)
            (wedge3 (K := K) p y z + wedge3 (K := K) x q z +
              wedge3 (K := K) p q z) := by
          rw [hb1]
      _ = (exteriorPower.map 3 (T a) - 1) (wedge3 (K := K) p y z) +
            (exteriorPower.map 3 (T a) - 1) (wedge3 (K := K) x q z) +
            (exteriorPower.map 3 (T a) - 1) (wedge3 (K := K) p q z) := by
          rw [map_add, map_add]
      _ = wedge3 (K := K) p t z + wedge3 (K := K) s q z + 0 := by
          rw [ha1, ha2, ha3]
      _ = wedge3 (K := K) (N a (F i)) (N b (F j)) (E k) +
            wedge3 (K := K) (N b (F i)) (N a (F j)) (E k) := by
          rw [hp, hq, hs, ht, hx, hy, hz]
          abel
  have hwedge_zero : ∀ (a b : A) (i j k : Fin 3), i ≠ j →
      wedge3 (K := K) (N a (F i)) (N b (F j)) (E k) +
        wedge3 (K := K) (N b (F i)) (N a (F j)) (E k) = 0 := by
    intro a b i j k hij
    have hz : ((exteriorPower.map 3 (T a) - 1) * (exteriorPower.map 3 (T b) - 1))
        (wedge3 (K := K) (F i) (F j) (E k)) = 0 := by
      have h := congrArg (fun f : Module.End K (⋀[K]^3 V) =>
        f (wedge3 (K := K) (F i) (F j) (E k)))
        (hq (a : GL (Fin 6) K) a.2 (b : GL (Fin 6) K) b.2)
      simpa using h
    rw [← hdd a b i j k hij]
    exact hz
  let ω : ⋀[K]^3 V := wedge3 (K := K) (E 0) (E 1) (E 2)
  have hwedge_coord : ∀ (u v : Fin 3 → K) (k : Fin 3),
      wedge3 (K := K) (∑ l, u l • E l) (∑ m, v m • E m) (E k) =
        (crossProduct u v k) • ω := by
    intro u v k
    have hzE : ∀ {i j l : Fin 3}, i = j ∨ i = l ∨ j = l →
        wedge3 (K := K) (E i) (E j) (E l) = 0 := by
      rintro i j l (h | h | h)
      · exact wedge3_eq_zero_of_eq (Or.inl (by rw [h]))
      · exact wedge3_eq_zero_of_eq (Or.inr (Or.inl (by rw [h])))
      · exact wedge3_eq_zero_of_eq (Or.inr (Or.inr (by rw [h])))
    have h120 : wedge3 (K := K) (E 1) (E 2) (E 0) = ω := by
      rw [wedge3_swap_first (a := E 2) (b := E 1) (d := E 0),
        wedge3_swap_first_third (a := E 0) (b := E 1) (d := E 2), neg_neg]
    have h210 : wedge3 (K := K) (E 2) (E 1) (E 0) = -ω := by
      rw [wedge3_swap_first_third (a := E 0) (b := E 1) (d := E 2)]
    have h021 : wedge3 (K := K) (E 0) (E 2) (E 1) = -ω := by
      rw [wedge3_swap_second (a := E 0) (b := E 1) (d := E 2)]
    have h201 : wedge3 (K := K) (E 2) (E 0) (E 1) = ω := by
      rw [wedge3_swap_first (a := E 0) (b := E 2) (d := E 1), h021, neg_neg]
    have h102 : wedge3 (K := K) (E 1) (E 0) (E 2) = -ω := by
      rw [wedge3_swap_first (a := E 0) (b := E 1) (d := E 2)]
    have h012 : wedge3 (K := K) (E 0) (E 1) (E 2) = ω := rfl
    rw [wedge3_sum_first]
    simp only [wedge3_sum_second, Finset.smul_sum, smul_smul]
    fin_cases k <;>
      simp only [Fin.sum_univ_three] <;>
      simp [hzE, h120, h210, h021, h201, h102, h012, cross_apply, add_smul,
        CharTwo.sub_eq_add] <;>
      try rw [← neg_smul, CharTwo.neg_eq] <;>
      try abel
  let col : A → Fin 3 → (Fin 3 → K) := fun a i l => M a l i
  have hcol_eq : ∀ (a : A) (i : Fin 3), N a (F i) = ∑ l, col a i l • E l := by
    intro a i
    rw [hNF a i]
  have hcross : ∀ (a b : A) (i j : Fin 3), i ≠ j →
      crossProduct (col a i) (col b j) + crossProduct (col b i) (col a j) = 0 := by
    intro a b i j hij
    funext k
    have h0 := hwedge_zero a b i j k hij
    rw [hcol_eq a i, hcol_eq b j, hcol_eq b i, hcol_eq a j] at h0
    rw [hwedge_coord (col a i) (col b j) k, hwedge_coord (col b i) (col a j) k] at h0
    rw [← add_smul] at h0
    have hE_li3 : LinearIndependent K ![E 0, E 1, E 2] := by
      convert hE_li using 2
      funext i
      fin_cases i <;> rfl
    have hω : ω ≠ 0 := by
      simpa [ω] using wedge3_ne_zero_of_linearIndependent hE_li3
    exact (smul_eq_zero.mp h0).resolve_right hω
  have hcol_single : ∀ (a : A) (i : Fin 3),
      M a *ᵥ (Pi.single i (1 : K) : Fin 3 → K) = col a i := by
    intro a i
    ext l
    simp [Matrix.mulVec, dotProduct, col, Pi.single_apply]
  have hsplit : ∀ (a : A) (α : Fin 3 → K),
      M a *ᵥ α = ∑ i, α i • col a i := by
    intro a α
    have hα : α = ∑ i, α i • (Pi.single i (1 : K) : Fin 3 → K) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hα]
    calc M a *ᵥ (∑ i, α i • (Pi.single i (1 : K) : Fin 3 → K))
        = ∑ i, M a *ᵥ (α i • (Pi.single i (1 : K) : Fin 3 → K)) := by
          rw [← Matrix.mulVecLin_apply, map_sum]
          simp only [Matrix.mulVecLin_apply]
      _ = ∑ i, α i • (M a *ᵥ (Pi.single i (1 : K) : Fin 3 → K)) := by
          simp only [Matrix.mulVec_smul]
      _ = ∑ i, α i • col a i := by
          simp only [hcol_single]
  have hpol_base : ∀ (a b : A) (i j : Fin 3),
      crossProduct (col a i) (col b j) + crossProduct (col b i) (col a j) = 0 := by
    intro a b i j
    by_cases hij : i = j
    · subst hij
      exact cross_anticomm' (col a i) (col b i)
    · exact hcross a b i j hij
  have hpol : ∀ (a b : A) (α β : Fin 3 → K),
      crossProduct (M a *ᵥ α) (M b *ᵥ β) +
        crossProduct (M b *ᵥ α) (M a *ᵥ β) = 0 := by
    intro a b α β
    rw [hsplit a α, hsplit b β, hsplit b α, hsplit a β]
    rw [crossProduct_sum_sum, crossProduct_sum_sum]
    have h1 : (∑ i, ∑ j, (α i * β j) • crossProduct (col a i) (col b j)) +
        (∑ i, ∑ j, (α i * β j) • crossProduct (col b i) (col a j)) =
        ∑ i, ∑ j, (α i * β j) • (crossProduct (col a i) (col b j) +
          crossProduct (col b i) (col a j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_add]
    rw [h1]
    simp [hpol_base a b]
  have hS_bound : Nat.card (Set.range M) ≤ (2 ^ f) ^ 2 := by
    refine card_le_sq_of_hermitian_polarized_cross hK (Set.range M) ?_ ?_
    · rintro B ⟨a, rfl⟩
      ext i j
      simp only [Matrix.map_apply, Matrix.transpose_apply]
      exact hMherm a j i
    · rintro B ⟨a, rfl⟩ D ⟨b, rfl⟩ α β
      exact hpol a b α β
  have hM_inj : Function.Injective M := by
    intro a b hab
    have hN_eq : N a = N b := by
      refine w.ext ?_
      intro l
      rcases l with i | l
      · rw [hNR a (E i) (hE_mem i), hNR b (E i) (hE_mem i)]
      rcases l with l | i
      · exact Fin.elim0 l
      · rw [hNF a i, hNF b i]
        change ∑ l, M a l i • E l = ∑ l, M b l i • E l
        rw [hab]
    have hT_eq : T a = T b := by
      calc T a = N a + 1 := by simp [N]
        _ = N b + 1 := by rw [hN_eq]
        _ = T b := by simp [N]
    have hmat : ((a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((b : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
      Matrix.toLin'.injective (by simpa [T] using hT_eq)
    exact Subtype.ext (Units.ext hmat)
  have hcard : Nat.card A ≤ Nat.card (Set.range M) := by
    have hinj : Function.Injective (fun a : A => (⟨M a, Set.mem_range_self a⟩ : Set.range M)) := by
      intro a b hab
      exact hM_inj (congrArg Subtype.val hab)
    exact Nat.card_le_card_of_injective
      (fun a : A => (⟨M a, Set.mem_range_self a⟩ : Set.range M)) hinj
  calc Nat.card A ≤ Nat.card (Set.range M) := hcard
    _ ≤ (2 ^ f) ^ 2 := hS_bound

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
