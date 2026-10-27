module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup

structure SigRel {M : Type*} [Group M] (T y c k : M) : Prop where
  comm_Ty : T * y = y * T
  y3 : orderOf y = 3
  c3 : orderOf c = 3
  kk : k * k = 1
  k1 : k ≠ 1
  yc : y * c = c * y
  ycp : y * (T * c * T⁻¹) = (T * c * T⁻¹) * y
  ccp : c * (T * c * T⁻¹) = (T * c * T⁻¹) * c
  yk : y * k = k * y
  card27 : Nat.card ↥(closure ({y, c, T * c * T⁻¹} : Set M)) = 27
  kc : k * c * k⁻¹ = c⁻¹
  kcp : k * (T * c * T⁻¹) = (T * c * T⁻¹) * k
  kkp : k * (T * k * T⁻¹) = (T * k * T⁻¹) * k

theorem SigRel.map {M M' : Type*} [Group M] [Group M'] (f : M →* M') (hf : Function.Injective f)
    {T y c k : M} (h : SigRel T y c k) : SigRel (f T) (f y) (f c) (f k) := by
  have hcl : closure ({f y, f c, f T * f c * (f T)⁻¹} : Set M') =
      (closure ({y, c, T * c * T⁻¹} : Set M)).map f := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h.comm_Ty]
  · rw [orderOf_injective f hf, h.y3]
  · rw [orderOf_injective f hf, h.c3]
  · rw [← map_mul, h.kk, map_one]
  · intro h1
    exact h.k1 (hf (by rw [h1, map_one]))
  · rw [← map_mul, ← map_mul, h.yc]
  · have := congrArg f h.ycp
    simpa only [map_mul, map_inv] using this
  · have := congrArg f h.ccp
    simpa only [map_mul, map_inv] using this
  · rw [← map_mul, ← map_mul, h.yk]
  · rw [hcl, Subgroup.card_map_of_injective hf, h.card27]
  · have := congrArg f h.kc
    simpa only [map_mul, map_inv] using this
  · have := congrArg f h.kcp
    simpa only [map_mul, map_inv] using this
  · have := congrArg f h.kkp
    simpa only [map_mul, map_inv] using this

theorem SigRel.conj {M : Type*} [Group M] (a : M) {T y c k : M} (h : SigRel T y c k) :
    SigRel (a * T * a⁻¹) (a * y * a⁻¹) (a * c * a⁻¹) (a * k * a⁻¹) :=
  h.map (MulAut.conj a).toMonoidHom (MulAut.conj a).injective

theorem inf_centralizer_conj_set {M : Type*} [Group M] (G : Subgroup M) {a : M} (ha : a ∈ G)
    (S : Set M) :
    G ⊓ centralizer ((fun x => a * x * a⁻¹) '' S) =
      (G ⊓ centralizer S).map (MulAut.conj a).toMonoidHom := by
  ext z
  simp only [mem_inf, mem_centralizer_iff, Set.forall_mem_image, mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨a⁻¹ * z * a, ⟨G.mul_mem (G.mul_mem (G.inv_mem ha) hz) ha, fun s hs => ?_⟩, by group⟩
    have := hc hs
    calc s * (a⁻¹ * z * a) = a⁻¹ * ((a * s * a⁻¹) * z) * a := by group
      _ = a⁻¹ * (z * (a * s * a⁻¹)) * a := by rw [this]
      _ = a⁻¹ * z * a * s := by group
  · rintro ⟨w, ⟨hw, hc⟩, rfl⟩
    refine ⟨G.mul_mem (G.mul_mem ha hw) (G.inv_mem ha), fun s hs => ?_⟩
    have := hc s hs
    calc a * s * a⁻¹ * (a * w * a⁻¹) = a * (s * w) * a⁻¹ := by group
      _ = a * (w * s) * a⁻¹ := by rw [this]
      _ = a * w * a⁻¹ * (a * s * a⁻¹) := by group

theorem card_inf_centralizer_conj_set {M : Type*} [Group M] (G : Subgroup M) {a : M} (ha : a ∈ G)
    (S : Set M) :
    Nat.card ↥(G ⊓ centralizer ((fun x => a * x * a⁻¹) '' S)) = Nat.card ↥(G ⊓ centralizer S) := by
  rw [inf_centralizer_conj_set G ha S]
  exact Subgroup.card_map_of_injective (MulAut.conj a).injective

theorem card_closure_pair_le_nine {M : Type*} [Group M] [Finite M] {u v : M} (hu : u ^ 3 = 1)
    (hv : v ^ 3 = 1) (huv : Commute u v) : Nat.card ↥(closure ({u, v} : Set M)) ≤ 9 := by
  classical
  set W : Set M := (fun p : Fin 3 × Fin 3 => u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ)) '' Set.univ with hW
  have hmod : ∀ (x : M) (n : ℕ), x ^ 3 = 1 → x ^ n = x ^ (n % 3) := by
    intro x n hx
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]
  have hWmem : ∀ i j : ℕ, u ^ i * v ^ j ∈ W := by
    intro i j
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩),
      Set.mem_univ _, ?_⟩
    simp only [hmod u i hu, hmod v j hv]
  let K : Subgroup M :=
    { carrier := {x | ∃ i j : ℕ, x = u ^ i * v ^ j}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        refine ⟨i + i', j + j', ?_⟩
        have h1 : Commute (v ^ j) (u ^ i') := (huv.symm.pow_pow j i')
        calc u ^ i * v ^ j * (u ^ i' * v ^ j') = u ^ i * (v ^ j * u ^ i') * v ^ j' := by group
          _ = u ^ i * (u ^ i' * v ^ j) * v ^ j' := by rw [h1.eq]
          _ = u ^ (i + i') * v ^ (j + j') := by rw [pow_add, pow_add]; group
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨2 * i, 2 * j, ?_⟩
        have h1 : Commute (u ^ i) (v ^ j) := huv.pow_pow i j
        have hui : (u ^ i)⁻¹ = u ^ (2 * i) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hu,
            one_pow]
        have hvj : (v ^ j)⁻¹ = v ^ (2 * j) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hv,
            one_pow]
        rw [mul_inv_rev, hui, hvj]
        exact (Commute.pow_pow (huv.symm) (2 * j) (2 * i)).eq }
  have hle : closure ({u, v} : Set M) ≤ K := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
  have hsub : (K : Set M) ⊆ W := by
    rintro _ ⟨i, j, rfl⟩
    exact hWmem i j
  have hWcard : W.ncard ≤ 9 := by
    have := Set.ncard_image_le (f := fun p : Fin 3 × Fin 3 => u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ))
      (s := (Set.univ : Set (Fin 3 × Fin 3))) (Set.toFinite _)
    rw [Set.ncard_univ] at this
    rw [hW]
    simpa [Nat.card_eq_fintype_card] using this
  calc Nat.card ↥(closure ({u, v} : Set M)) ≤ Nat.card ↥K := Subgroup.card_le_of_le hle
    _ = (K : Set M).ncard := Nat.card_coe_set_eq _
    _ ≤ W.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 9 := hWcard

theorem closure_insert_eq_of_mem {M : Type*} [Group M] {x : M} {S : Set M}
    (hx : x ∈ closure S) : closure (insert x S) = closure S :=
  le_antisymm ((closure_le _).2 (Set.insert_subset_iff.2 ⟨hx, subset_closure⟩))
    (closure_mono (Set.subset_insert _ _))

theorem relFree_of_card_27 {M : Type*} [Group M] [Finite M] {y c c' : M} (hy : y ^ 3 = 1)
    (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1) (hyc : Commute y c) (hyc' : Commute y c')
    (hcc' : Commute c c') (h27 : Nat.card ↥(closure ({y, c, c'} : Set M)) = 27) :
    ∀ a b d : ℕ, a < 3 → b < 3 → d < 3 → y ^ a * c ^ b * c' ^ d = 1 →
      a = 0 ∧ b = 0 ∧ d = 0 := by
  intro a b d ha hb hd h
  have hsq : ∀ (x : M), x ^ 3 = 1 → ∀ n : ℕ, 0 < n → n < 3 → (x ^ n) ^ n = x := by
    intro x hx n hn0 hn3
    interval_cases n
    · simp
    · rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
  have hmem : ∀ (x : M) (S : Set M), x ∈ S → ∀ n : ℕ, x ^ n ∈ closure S :=
    fun x S hx n => pow_mem (subset_closure hx) n
  have h9 : ∀ {S : Set M} {x u v : M}, S = insert x {u, v} → x ∈ closure ({u, v} : Set M) →
      x ^ 3 = 1 → u ^ 3 = 1 → v ^ 3 = 1 → Commute u v → Nat.card ↥(closure S) ≤ 9 := by
    intro S x u v hS hx _ hu hv huv
    rw [hS, closure_insert_eq_of_mem hx]
    exact card_closure_pair_le_nine hu hv huv
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · by_cases hd0 : d = 0
      · exact ⟨ha0, hb0, hd0⟩
      · exfalso
        subst ha0 hb0
        have h1 : c' ^ d = 1 := by simpa using h
        have hc'1 : c' ∈ closure ({y, c} : Set M) := by
          rw [← hsq c' hc' d (Nat.pos_of_ne_zero hd0) hd, h1, one_pow]
          exact one_mem _
        have := h9 (S := {y, c, c'}) (x := c') (u := y) (v := c)
          (by ext z; simp; tauto) hc'1 hc' hy hc hyc
        omega
    · exfalso
      subst ha0
      have h' : c ^ b * c' ^ d = 1 := by simpa using h
      have h1 : c ^ b = (c' ^ d)⁻¹ := eq_inv_of_mul_eq_one_left h'
      have hcm : c ∈ closure ({y, c'} : Set M) := by
        rw [← hsq c hc b (Nat.pos_of_ne_zero hb0) hb, h1]
        exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (hmem c' {y, c'} (by simp) d)) b
      have := h9 (S := {y, c, c'}) (x := c) (u := y) (v := c')
        (by ext z; simp; tauto) hcm hc hy hc' hyc'
      omega
  · exfalso
    have h' : y ^ a * (c ^ b * c' ^ d) = 1 := by rw [← mul_assoc]; exact h
    have h1 : y ^ a = (c ^ b * c' ^ d)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hym : y ∈ closure ({c, c'} : Set M) := by
      rw [← hsq y hy a (Nat.pos_of_ne_zero ha0) ha, h1]
      exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
        (hmem c {c, c'} (by simp) b) (hmem c' {c, c'} (by simp) d))) a
    have := h9 (S := {y, c, c'}) (x := y) (u := c) (v := c') rfl hym hy hc hc' hcc'
    omega

end CFSG.EvenSporadicStandard.HSStd.U43
