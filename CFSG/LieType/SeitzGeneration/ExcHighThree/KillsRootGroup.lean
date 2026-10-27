module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootComb
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsLeaf
public import CFSG.RankThree.PartOne.KE.E7FourHI

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint

section KillsRoot


variable {τ : Tag}

theorem exists_sign_family {L : Type} [Field L] (w : WeylGroup τ) :
    ∃ s : (Fin τ.rank → ℤ) → L, ∀ α, IsRoot τ α → s α * s α = 1 ∧ ∀ c : L,
      canonicalRep (coxeterSystem τ) L w * pinnedX τ L α c *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L (w • α) (s α * c) := by
  have h : ∀ α : Fin τ.rank → ℤ, ∃ e : L, IsRoot τ α → e * e = 1 ∧ ∀ c : L,
      canonicalRep (coxeterSystem τ) L w * pinnedX τ L α c *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L (w • α) (e * c) := by
    intro α
    by_cases hα : IsRoot τ α
    · obtain ⟨ε, h1, h2⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hα
      exact ⟨ε, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h' => absurd h' hα⟩
  choose s hs using h
  exact ⟨s, fun α hα => hs α hα⟩

def cycSeq {L : Type} [Field L] (s : ℕ → L) (q : ℕ) (t₀ : L) : ℕ → L
  | 0 => t₀
  | k + 1 => s k * (cycSeq s q t₀ k) ^ q

theorem cycSeq_affine {L : Type} [Field L] (s : ℕ → L) (hs : ∀ k, s k * s k = 1) (q : ℕ) :
    ∀ n : ℕ, ∃ S : L, S * S = 1 ∧ ∀ t₀ : L, cycSeq s q t₀ n = S * t₀ ^ (q ^ n)
  | 0 => ⟨1, by simp, fun t₀ => by simp [cycSeq]⟩
  | n + 1 => by
    obtain ⟨S, hS, hf⟩ := cycSeq_affine s hs q n
    refine ⟨s n * S ^ q, ?_, fun t₀ => ?_⟩
    · calc (s n * S ^ q) * (s n * S ^ q) = (s n * s n) * (S * S) ^ q := by rw [mul_pow]; ring
        _ = 1 := by rw [hs n, hS, one_pow, mul_one]
    · simp only [cycSeq]
      rw [hf, mul_pow, ← pow_mul, pow_succ]
      ring

theorem exists_cycSeq_fixed {L : Type} [Field L] [IsAlgClosed L] (s : ℕ → L)
    (hs : ∀ k, s k * s k = 1) {q n : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    ∃ t₀ : L, t₀ ≠ 0 ∧ cycSeq s q t₀ n = t₀ := by
  obtain ⟨S, hS, hf⟩ := cycSeq_affine s hs q n
  have hqn : 2 ≤ q ^ n := le_trans hq (Nat.le_self_pow hn.ne' q)
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_pow_nat_eq S (show 0 < q ^ n - 1 by omega)
  have hS0 : S ≠ 0 := fun h => by rw [h, zero_mul] at hS; exact zero_ne_one hS
  have ht0 : t₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht₀
    exact hS0 ht₀.symm
  refine ⟨t₀, ht0, ?_⟩
  rw [hf, show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, ht₀, ← mul_assoc, hS, one_mul]

theorem cycSeq_periodic {L : Type} [Field L] (s : ℕ → L) (q n : ℕ) (hper : ∀ k, s (k + n) = s k)
    (t₀ : L) (hfix : cycSeq s q t₀ n = t₀) : ∀ k, cycSeq s q t₀ (k + n) = cycSeq s q t₀ k
  | 0 => by simpa [cycSeq] using hfix
  | k + 1 => by
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [cycSeq]
    rw [hper k, cycSeq_periodic s q n hper t₀ hfix k]

theorem pinnedX_pow_char {L : Type} [Field L] (p : ℕ) [CharP L p] (α : Fin τ.rank → ℤ) (c : L) :
    pinnedX τ L α c ^ p = 1 := by
  have key : ∀ m : ℕ, pinnedX τ L α c ^ m = pinnedX τ L α ((m : L) * c) := by
    intro m
    induction m with
    | zero => simp [pinnedX_zero τ L α]
    | succ m ih =>
      rw [pow_succ, ih, ← pinnedX_add τ L α]
      congr 1
      push_cast
      ring
  rw [key, CharP.cast_eq_zero, zero_mul, pinnedX_zero τ L α]

theorem pow_prod_range_eq_one {M : Type} [Monoid M] (r : ℕ) (f : ℕ → M) :
    ∀ n : ℕ, (∀ i j, i < n → j < n → i ≠ j → Commute (f i) (f j)) → (∀ i < n, f i ^ r = 1) →
      ((List.range n).map f).prod ^ r = 1
  | 0, _, _ => by simp
  | n + 1, hc, hr => by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    have hcomm : Commute (f 0) (((List.range n).map (f ∘ Nat.succ)).prod) := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      have hk' : k < n := List.mem_range.1 hk
      exact hc 0 (k + 1) (by omega) (by omega) (by omega)
    have hrest : (((List.range n).map (f ∘ Nat.succ)).prod) ^ r = 1 := by
      refine pow_prod_range_eq_one r (f ∘ Nat.succ) n
        (fun i j hi hj hij => hc (i + 1) (j + 1) (by omega) (by omega) (by omega)) ?_
      intro i hi
      exact hr (i + 1) (by omega)
    rw [hcomm.mul_pow, hr 0 (by omega), one_mul, hrest]

theorem conj_list_prod {L : Type} [Field L] {n : ℕ} (g : ModGL τ L) (f : Fin n → ModGL τ L) :
    g * (List.ofFn f).prod * g⁻¹ = (List.ofFn fun i => g * f i * g⁻¹).prod := by
  have h := map_list_prod (MulAut.conj g).toMonoidHom (List.ofFn f)
  rw [List.map_ofFn] at h
  simpa [Function.comp_def, MulAut.conj_apply] using h

theorem exists_flip_conj {L : Type} [Field L] {n : ℕ} (γ : Fin n → Fin τ.rank → ℤ) (c : Fin n → L)
    (hroot : ∀ i, IsRoot τ (γ i)) (horth : ∀ i k, i ≠ k → iform (γ i) (γ k) = 0) (j : Fin n)
    (hj : height (γ j) < 0) :
    ∃ (g : ModGL τ L) (c' : Fin n → L), (∀ i, c' i ≠ 0 ↔ c i ≠ 0) ∧
      (∀ i, i ≠ j → rootReflection (γ j) • γ i = γ i) ∧ 0 < height (rootReflection (γ j) • γ j) ∧
      g * (List.ofFn fun i => pinnedX τ L (γ i) (c i)).prod * g⁻¹ =
        (List.ofFn fun i => pinnedX τ L (rootReflection (γ j) • γ i) (c' i)).prod := by
  obtain ⟨s, hs⟩ := exists_sign_family (L := L) (τ := τ) (rootReflection (γ j))
  refine ⟨canonicalRep (coxeterSystem τ) L (rootReflection (γ j)), fun i => s (γ i) * c i,
    ?_, ?_, ?_, ?_⟩
  · intro i
    have hs0 : s (γ i) ≠ 0 := fun h => by
      have h1 := (hs (γ i) (hroot i)).1
      rw [h, zero_mul] at h1
      exact zero_ne_one h1
    exact ⟨fun h hc => h (by show s (γ i) * c i = 0; rw [hc, mul_zero]),
      fun h hc => h ((mul_eq_zero.1 hc).resolve_left hs0)⟩
  · intro i hi
    exact rootReflection_smul_of_iform_eq_zero (hroot j) (horth j i (Ne.symm hi))
  · rw [rootReflection_smul_self (hroot j), height_neg]
    exact neg_pos.2 hj
  · rw [conj_list_prod]
    congr 2
    funext i
    exact (hs (γ i) (hroot i)).2 (c i)

theorem prod_ne_one_of_pos {L : Type} [Field L] {n : ℕ} (γ : Fin n → Fin τ.rank → ℤ) (c : Fin n → L)
    (i0 : Fin n) (hpos : ∀ i, IsRoot τ (γ i) ∧ 0 < height (γ i)) (hinj : Function.Injective γ)
    (hc : c i0 ≠ 0) : (List.ofFn fun i => pinnedX τ L (γ i) (c i)).prod ≠ 1 := by
  intro h1
  have hinj2 := (positive_root_product_injectivity τ L (m := n) γ hinj hpos).2
  have h0 : (List.ofFn fun i => pinnedX τ L (γ i) ((fun _ : Fin n => (0 : L)) i)).prod = 1 := by
    simp [pinnedX_zero τ L]
  have hc0 : c = fun _ => 0 :=
    hinj2 (show (fun c : Fin n → L => (List.ofFn fun i => pinnedX τ L (γ i) (c i)).prod) c =
      (fun c : Fin n → L => (List.ofFn fun i => pinnedX τ L (γ i) (c i)).prod) (fun _ => 0) from
        h1.trans h0.symm)
  exact hc (congrFun hc0 i0)

theorem prod_ne_one_aux {L : Type} [Field L] (m : ℕ) : ∀ (n : ℕ) (γ : Fin n → Fin τ.rank → ℤ)
    (c : Fin n → L) (i0 : Fin n), (∀ i, IsRoot τ (γ i)) → Function.Injective γ →
    (∀ i k, i ≠ k → iform (γ i) (γ k) = 0) →
    (Finset.univ.filter fun i => height (γ i) < 0).card ≤ m → c i0 ≠ 0 →
    (List.ofFn fun i => pinnedX τ L (γ i) (c i)).prod ≠ 1 := by
  induction m with
  | zero =>
    intro n γ c i0 hroot hinj _ hcard hc
    refine prod_ne_one_of_pos γ c i0 (fun i => ⟨hroot i, ?_⟩) hinj hc
    have hnn : ¬ height (γ i) < 0 := fun hneg => by
      have hmem : i ∈ Finset.univ.filter (fun i => height (γ i) < 0) := by simp [hneg]
      have := Finset.card_pos.2 ⟨i, hmem⟩
      omega
    exact (IsRoot.height_pos_or_neg (hroot i)).resolve_right hnn
  | succ m ih =>
    intro n γ c i0 hroot hinj horth hcard hc
    by_cases hneg : ∃ j, height (γ j) < 0
    · obtain ⟨j, hj⟩ := hneg
      obtain ⟨g, c', hc', hfix, hposj, hconj⟩ := exists_flip_conj γ c hroot horth j hj
      have hmemj : j ∈ Finset.univ.filter (fun i => height (γ i) < 0) := by simp [hj]
      have hsub : Finset.univ.filter (fun i => height (rootReflection (γ j) • γ i) < 0) ⊆
          (Finset.univ.filter (fun i => height (γ i) < 0)).erase j := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Finset.mem_erase]
        by_cases hij : i = j
        · subst hij
          exact absurd hi (not_lt.2 hposj.le)
        · rw [hfix i hij] at hi
          exact ⟨hij, by simpa using hi⟩
      have hcard' := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hmemj] at hcard'
      have hcard'' : (Finset.univ.filter fun i =>
          height (rootReflection (γ j) • γ i) < 0).card ≤ m := by
        omega
      have hroot' : ∀ i, IsRoot τ (rootReflection (γ j) • γ i) := fun i =>
        CFSG.LieType.Chevalley.IsRoot.smul (hroot i) (rootReflection (γ j))
      have hinj' : Function.Injective (fun i => rootReflection (γ j) • γ i) :=
        (MulAction.injective (rootReflection (γ j))).comp hinj
      have horth' : ∀ i k, i ≠ k → iform (rootReflection (γ j) • γ i)
          (rootReflection (γ j) • γ k) = 0 := by
        intro i k hik
        rw [CFSG.LieType.Chevalley.iform_smul]
        exact horth i k hik
      have hc'0 : c' i0 ≠ 0 := (hc' i0).2 hc
      have hnew := ih n (fun i => rootReflection (γ j) • γ i) c' i0 hroot' hinj' horth' hcard'' hc'0
      intro h1
      apply hnew
      rw [← hconj, h1, mul_one, mul_inv_cancel]
    · have hneg' : ∀ i, ¬ height (γ i) < 0 := fun i h => hneg ⟨i, h⟩
      exact prod_ne_one_of_pos γ c i0
        (fun i => ⟨hroot i, (IsRoot.height_pos_or_neg (hroot i)).resolve_right (hneg' i)⟩)
        hinj hc

theorem exists_cycle_element {L : Type} [Field L] [IsAlgClosed L] (p e : ℕ) [Fact p.Prime]
    [CharP L p] (he : 1 ≤ e) (g : WeylGroup τ) (n : ℕ) (hn : 0 < n) (β : ℕ → Fin τ.rank → ℤ)
    (hper : ∀ k, β (k + n) = β k) (hroot : ∀ k, IsRoot τ (β k))
    (horth : ∀ k l, k < n → l < n → k ≠ l →
      iform (β k) (β l) = 0 ∧ β k ≠ β l ∧ ¬ IsRoot τ (β k + β l))
    (hgβ : ∀ k, g • β k = β (k + 1)) (S : Set (Fin τ.rank → ℤ)) (hS : ∀ k, β k ∈ S) :
    ∃ v : ModGL τ L, v ∈ rootSpan τ L S ∧
      frobTwistGL τ L p e (canonicalRep (coxeterSystem τ) L g) v = v ∧ v ≠ 1 ∧ v ^ p = 1 := by
  obtain ⟨s0, hs0⟩ := exists_sign_family (L := L) (τ := τ) g
  obtain ⟨Q, hQ⟩ : ∃ Q : ModGL τ L, Q = canonicalRep (coxeterSystem τ) L g := ⟨_, rfl⟩
  rw [← hQ]
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ e := le_trans hp2 (Nat.le_self_pow (by omega) p)
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → L, ∀ k, s k = s0 (β k) := ⟨fun k => s0 (β k), fun k => rfl⟩
  have hs : ∀ k, s k * s k = 1 := fun k => by rw [hsdef k]; exact (hs0 (β k) (hroot k)).1
  obtain ⟨t₀, ht₀, hfix⟩ := exists_cycSeq_fixed s hs hq2 hn
  obtain ⟨t, ht⟩ : ∃ t : ℕ → L, t = cycSeq s (p ^ e) t₀ := ⟨_, rfl⟩
  have ht0 : t 0 = t₀ := by rw [ht]; rfl
  have htsucc : ∀ k, t (k + 1) = s k * (t k) ^ (p ^ e) := fun k => by rw [ht]; rfl
  have htn : t n = t₀ := by rw [ht]; exact hfix
  have htper : ∀ k, t (k + n) = t k := by
    intro k
    rw [ht]
    exact cycSeq_periodic s (p ^ e) n (fun k => by rw [hsdef, hsdef, hper k]) t₀ hfix k
  obtain ⟨f, hf⟩ : ∃ f : ℕ → (Module.End L (RootModule τ L))ˣ,
      ∀ k, f k = pinnedX τ L (β k) (t k) := ⟨_, fun k => rfl⟩
  have hG : ∀ k, frobTwistGL τ L p e Q (f k) = f (k + 1) := by
    intro k
    rw [frobTwistGL_apply, hf, entrywiseFrobGL_pinnedX p e (β k) (t k), iterateFrobenius_def, hQ,
      (hs0 (β k) (hroot k)).2 (t k ^ (p ^ e)), hgβ k, hf, htsucc k, hsdef k]
  have hGv : frobTwistGL τ L p e Q (((List.range n).map f).prod) =
      ((List.range n).map (fun k => f (k + 1))).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hG k
  have hcomm : ∀ i j, i < n → j < n → i ≠ j → Commute (f i) (f j) := by
    intro i j hi hj hij
    rw [hf, hf]
    exact pinnedX_commute_of_iform_eq_zero L (hroot i) (hroot j) (horth i j hi hj hij).1
      (horth i j hi hj hij).2.2 (t i) (t j)
  have hcomm0 : ∀ k, k < n → Commute (f 0) (f k) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      exact Commute.refl _
    · exact hcomm 0 k (by omega) hk (Ne.symm hk0)
  have hPcomm : Commute (f 0) ((List.range n).map f).prod := by
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hcomm0 k (List.mem_range.1 hk)
  have hL1 : ((List.range (n + 1)).map f).prod =
      f 0 * ((List.range n).map (fun k => f (k + 1))).prod := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    rfl
  have hL2 : ((List.range (n + 1)).map f).prod = ((List.range n).map f).prod * f n := by
    rw [List.range_succ, List.map_append, List.prod_append]
    simp
  have hfn : f n = f 0 := by
    rw [hf, hf]
    have hβn : β n = β 0 := by simpa using hper 0
    have htn' : t n = t 0 := by rw [htn, ht0]
    rw [hβn, htn']
  have hP' : ((List.range n).map (fun k => f (k + 1))).prod = ((List.range n).map f).prod := by
    have key : f 0 * ((List.range n).map (fun k => f (k + 1))).prod =
        f 0 * ((List.range n).map f).prod := by
      rw [← hL1, hL2, hfn, hPcomm.eq]
    exact mul_left_cancel key
  have hmem : ((List.range n).map f).prod ∈ rootSpan τ L S := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [hf]
    have hle : rootSubgroup τ L (β k) ≤ rootSpan τ L S :=
      le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup τ L α) (β k) (hS k) le_rfl
    exact hle (Subgroup.subset_closure ⟨t k, rfl⟩)
  have hconv : ∀ g' : ℕ → (Module.End L (RootModule τ L))ˣ,
      (List.range n).map g' = List.ofFn (fun i : Fin n => g' i.val) := by
    intro g'
    apply List.ext_getElem <;> simp
  have hv_eq : ((List.range n).map f).prod =
      (List.ofFn fun i : Fin n => pinnedX τ L (β i.val) (t i.val)).prod := by
    rw [hconv f]
    simp only [hf]
  have hv_ne : ((List.range n).map f).prod ≠ 1 := by
    intro hv1
    have hcard : (Finset.univ.filter fun i : Fin n => height (β i.val) < 0).card ≤ n :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    have hinj : Function.Injective (fun i : Fin n => β i.val) := by
      intro i j hij
      by_contra hne
      exact (horth i.val j.val i.2 j.2 (fun h => hne (Fin.ext h))).2.1 hij
    have hne := prod_ne_one_aux n n (fun i : Fin n => β i.val) (fun i : Fin n => t i.val) ⟨0, hn⟩
      (fun i => hroot i.val) hinj
      (fun i k hik => (horth i.val k.val i.2 k.2 (fun h => hik (Fin.ext h))).1) hcard
      (show t 0 ≠ 0 by rw [ht0]; exact ht₀)
    have hP : (List.ofFn fun i : Fin n => pinnedX τ L (β i.val) (t i.val)).prod = 1 := by
      rw [← hv_eq]
      exact hv1
    exact hne hP
  have hvp : ((List.range n).map f).prod ^ p = 1 :=
    pow_prod_range_eq_one p f n hcomm (fun i _ => by rw [hf]; exact pinnedX_pow_char p _ _)
  refine ⟨((List.range n).map f).prod, hmem, ?_, hv_ne, hvp⟩
  rw [hGv, hP']

theorem reflection_mem_stab {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hχ : ∀ i, rootChar (a i) γ = 1) (i : ι) :
    rootReflection γ ∈ rootCharStabilizerSubgroup (a i) := by
  rw [mem_rootCharStabilizerSubgroup]
  intro v
  rw [rootReflection_smul hγ v, rootChar_sub, rootChar_zsmul, hχ i]
  simp

theorem closure_refl_stab {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (S : Set (Fin τ.rank → ℤ)) (hS : ∀ γ ∈ S, IsRoot τ γ ∧ ∀ i, rootChar (a i) γ = 1)
    {x : WeylGroup τ} (hx : x ∈ Subgroup.closure (rootReflection '' S))
    (i : ι) : x ∈ rootCharStabilizerSubgroup (a i) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    exact reflection_mem_stab a (hS γ hγ).1 (hS γ hγ).2 i
  | one => exact one_mem _
  | mul x y _ _ hx hy => exact mul_mem hx hy
  | inv x _ hx => exact inv_mem hx

theorem neg_mem_familyKernel {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ familyKernel a) : -γ ∈ familyKernel a := by
  refine ⟨CFSG.LieType.Chevalley.IsRoot.neg hγ.1, fun i => ?_⟩
  rw [show -γ = (-1 : ℤ) • γ by simp, rootChar_zsmul, hγ.2 i, one_zpow]

theorem add_mem_familyKernel {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {β γ : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) (hγ : γ ∈ familyKernel a)
    (hp : IsRoot τ (β + γ)) : β + γ ∈ familyKernel a :=
  ⟨hp, fun i => by rw [rootChar_add, hβ.2 i, hγ.2 i, one_mul]⟩

theorem stab_mem_familyKernel {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {x : WeylGroup τ} (hx : ∀ i, x ∈ rootCharStabilizerSubgroup (a i))
    {β : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) : x • β ∈ familyKernel a :=
  ⟨CFSG.LieType.Chevalley.IsRoot.smul hβ.1 x, fun i => by
    have hxa : ∀ v, rootChar (a i) (x • v) = rootChar (a i) v :=
      fun v => mem_rootCharStabilizerSubgroup.1 (hx i) v
    rw [hxa β]
    exact hβ.2 i⟩

theorem units_eq_one_of_pow_char {L : Type} [Field L] {p e : ℕ} [Fact p.Prime] [CharP L p]
    (x : Lˣ) (h : x ^ (p ^ e) = 1) : x = 1 := by
  have h' : ((x : L) - 1) ^ (p ^ e) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  have hne : p ^ e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff hne).1 h'))

theorem family_w_stab {L : Type} [Field L] {p e : ℕ} [Fact p.Prime] [CharP L p] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {w : WeylGroup τ}
    (hrel : ∀ i v, rootChar (a i) (w • v) = rootChar (a i) v ^ (p ^ e))
    {β : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) :
    w • β ∈ familyKernel a ∧ w⁻¹ • β ∈ familyKernel a := by
  refine ⟨⟨CFSG.LieType.Chevalley.IsRoot.smul hβ.1 w, fun i => ?_⟩,
    ⟨CFSG.LieType.Chevalley.IsRoot.smul hβ.1 w⁻¹, fun i => ?_⟩⟩
  · rw [hrel i β, hβ.2 i, one_pow]
  · have h := hrel i (w⁻¹ • β)
    rw [smul_inv_smul, hβ.2 i] at h
    exact units_eq_one_of_pow_char _ h.symm

theorem image_eq_of_mem_stab (S : Set (Fin τ.rank → ℤ)) (g : WeylGroup τ)
    (h1 : ∀ β ∈ S, g • β ∈ S) (h2 : ∀ β ∈ S, g⁻¹ • β ∈ S) : (fun α => g • α) '' S = S := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact h1 α hα
  · intro hβ
    exact ⟨g⁻¹ • β, h2 β hβ, smul_inv_smul g β⟩

theorem rootSpan_mono' {L : Type} [Field L] {S T : Set (Fin τ.rank → ℤ)} (h : S ⊆ T) :
    rootSpan τ L S ≤ rootSpan τ L T := by
  unfold rootSpan
  exact iSup₂_le fun α hα =>
    le_iSup₂_of_le (f := fun β (_ : β ∈ T) => rootSubgroup τ L β) α (h hα) le_rfl

theorem rootSpan_le_adjoint' {L : Type} [Field L] (S : Set (Fin τ.rank → ℤ)) :
    rootSpan τ L S ≤ adjointGroup τ L := by
  unfold rootSpan
  refine iSup₂_le fun α _ => ?_
  unfold rootSubgroup
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact pinnedX_mem_adjointGroup α c

theorem familyGroup_le_adjoint {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    familyGroup (K := L) a ≤ adjointGroup τ L := by
  unfold familyGroup
  exact sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' (rootSpan_le_adjoint' _)

theorem rootDiagUnit_mul_rootDiagUnit {L : Type} [Field L] (a b : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a * rootDiagUnit τ b = rootDiagUnit τ (a * b) :=
  Units.ext (rootDiag_mul_rootDiag a b)

theorem familyGroup_comm {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) (i : ι)
    {m : ModGL τ L} (hm : m ∈ familyGroup (K := L) a) :
    m * rootDiagUnit τ (a i) = rootDiagUnit τ (a i) * m := by
  have hcent : familyGroup (K := L) a ≤
      Subgroup.centralizer ({rootDiagUnit τ (a i)} : Set (ModGL τ L)) := by
    unfold familyGroup
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh, rootDiagUnit_mul_rootDiagUnit, rootDiagUnit_mul_rootDiagUnit,
        mul_comm]
    · unfold rootSpan
      refine iSup₂_le fun α hα => ?_
      unfold rootSubgroup
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      have hX := rootDiagUnit_conj_pinnedX (K := L) (τ := τ) (a i) hα.1 c
      rw [hα.2 i, Units.val_one, one_mul] at hX
      have h2 : pinnedX τ L α c * rootDiagUnit τ (a i) =
          rootDiagUnit τ (a i) * pinnedX τ L α c := by
        have e1 : pinnedX τ L α c =
            rootDiagUnit τ (a i) * pinnedX τ L α c * (rootDiagUnit τ (a i))⁻¹ := hX.symm
        calc pinnedX τ L α c * rootDiagUnit τ (a i)
            = (rootDiagUnit τ (a i) * pinnedX τ L α c * (rootDiagUnit τ (a i))⁻¹) *
                rootDiagUnit τ (a i) := by rw [← e1]
          _ = rootDiagUnit τ (a i) * pinnedX τ L α c := by group
      exact h2.symm
  exact ((Subgroup.mem_centralizer_iff.1 (hcent hm)) _ (Set.mem_singleton _)).symm

theorem canonicalRep_closure_mem_familyGroup {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {x : WeylGroup τ}
    (hx : x ∈ Subgroup.closure (rootReflection '' familyKernel a)) :
    canonicalRep (coxeterSystem τ) L x ∈ familyGroup (K := L) a := by
  have hTM : torusGroup τ L ≤ familyGroup (K := L) a := by
    unfold familyGroup
    exact le_sup_left
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    have hsub : ({γ, -γ} : Set (Fin τ.rank → ℤ)) ⊆ familyKernel a := by
      intro β hβ
      rcases hβ with rfl | rfl
      · exact hγ
      · exact neg_mem_familyKernel a hγ
    have hle : torusGroup τ L ⊔ rootSpan τ L {γ, -γ} ≤ familyGroup (K := L) a := by
      unfold familyGroup
      exact sup_le_sup_left (rootSpan_mono' hsub) _ |>.trans (by rfl)
    exact hle (CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.canonicalRep_rootReflection_mem (k := L) hγ.1)
  | one =>
    rw [canonicalRep_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk, hkxy⟩ := canonicalRep_mul_mem (R := L) x y
    have hQ : canonicalRep (coxeterSystem τ) L (x * y) =
        k⁻¹ * (canonicalRep (coxeterSystem τ) L x * canonicalRep (coxeterSystem τ) L y) := by
      rw [hkxy]
      group
    rw [hQ]
    exact mul_mem (inv_mem (hTM hk)) (mul_mem hx hy)
  | inv x _ hx =>
    obtain ⟨k, hk, hkx⟩ := canonicalRep_inv_eq (K := L) x
    have hQ : canonicalRep (coxeterSystem τ) L x⁻¹ = k⁻¹ * (canonicalRep (coxeterSystem τ) L x)⁻¹ := by
      rw [hkx]
      group
    rw [hQ]
    exact mul_mem (inv_mem (hTM hk)) (inv_mem hx)

theorem card_eq_pow_ringChar (K : Type) [Field K] [Finite K] :
    ∃ e : ℕ, 1 ≤ e ∧ Nat.card K = ringChar K ^ e := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  exact ⟨(n : ℕ), n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem rootChar_frob_of_conj {L : Type} [Field L] [IsAlgClosed L] {p e : ℕ} [Fact p.Prime]
    [CharP L p] (b : Fin τ.rank → Lˣ) (w : WeylGroup τ)
    (h : rootDiagUnit τ b = canonicalRep (coxeterSystem τ) L w *
      entrywiseFrobGL τ L p e (rootDiagUnit τ b) * (canonicalRep (coxeterSystem τ) L w)⁻¹)
    (v : Fin τ.rank → ℤ) : rootChar b (w • v) = rootChar b v ^ (p ^ e) := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_pow] at h
  rw [(rootDiagUnit_eq_conj_canonicalRep_iff b (b ^ (p ^ e)) w).1 h v, rootChar_pow']

theorem torus_le_familyGroup {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    torusGroup τ L ≤ familyGroup (K := L) a := by
  unfold familyGroup
  exact le_sup_left

theorem rootSpan_le_familyGroup {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    rootSpan τ L (familyKernel a) ≤ familyGroup (K := L) a := by
  unfold familyGroup
  exact le_sup_right

theorem kill_cycle_periodic {L : Type} [Field L] {ι : Type}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (a : ι → Fin τ.rank → Lˣ) (w : WeylGroup τ)
    (hw : (fun α => w • α) '' familyKernel a = familyKernel a)
    {α : Fin τ.rank → ℤ} (hα : α ∈ familyKernel a) :
    ∃ x ∈ Subgroup.closure (rootReflection '' familyKernel a), ∃ (n : ℕ) (β : ℕ → Fin τ.rank → ℤ),
      0 < n ∧ (∀ k, β (k + n) = β k) ∧ (∀ k, β k ∈ familyKernel a) ∧
      (∀ k l, k < n → l < n → k ≠ l →
        iform (β k) (β l) = 0 ∧ β k ≠ β l ∧ ¬ IsRoot τ (β k + β l)) ∧
      ∀ k, (x * w) • β k = β (k + 1) := by
  have hw' : (fun α => w • α) '' kernelRoots (familyChar a) = kernelRoots (familyChar a) := by
    rw [kernelRoots_familyChar]
    exact hw
  have hα' : α ∈ kernelRoots (familyChar a) := by
    rw [kernelRoots_familyChar]
    exact hα
  obtain ⟨x, hx, n, hn, β, -, hβS, horth, hgβ⟩ :=
    exists_kill_root_cycle hτ (familyChar a) w hw' hα'
  rw [kernelRoots_familyChar] at hx hβS
  refine ⟨x, hx, n, fun k => β ⟨k % n, Nat.mod_lt _ hn⟩, hn, ?_, ?_, ?_, ?_⟩
  · intro k
    show β ⟨(k + n) % n, Nat.mod_lt _ hn⟩ = β ⟨k % n, Nat.mod_lt _ hn⟩
    congr 1
    exact Fin.ext (Nat.add_mod_right k n)
  · intro k
    exact hβS _
  · intro k l hk hl hkl
    have hkl' : (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n) ≠ ⟨l % n, Nat.mod_lt _ hn⟩ := by
      intro h
      apply hkl
      have h' := congrArg Fin.val h
      simp only [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] at h'
      exact h'
    have h := horth ⟨k % n, Nat.mod_lt _ hn⟩ ⟨l % n, Nat.mod_lt _ hn⟩ hkl'
    refine ⟨h.1, h.2.1, ?_⟩
    have h11 := h.2.2.2 1 1 one_pos one_pos
    simpa using h11
  · intro k
    show (x * w) • β ⟨k % n, Nat.mod_lt _ hn⟩ = β ⟨(k + 1) % n, Nat.mod_lt _ hn⟩
    refine (hgβ ⟨k % n, Nat.mod_lt _ hn⟩).trans ?_
    congr 1
    exact Fin.ext (Nat.mod_add_mod k n 1)

theorem kill_core (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] (A : Subgroup (adjointGroup τ K)) (D : LangPlaneData τ K A)
    (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) (hk : D.Kills α) :
    ∃ uL : ModGL τ (AlgebraicClosure K), uL ∈ adjointGroup τ (AlgebraicClosure K) ∧ uL ≠ 1 ∧
      uL ^ ringChar K = 1 ∧ Units.map (entrywiseHom D.Fr) uL = uL ∧
      ∀ y ∈ A, uL * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * uL := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hFrEq : D.Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL τ (AlgebraicClosure K),
      Units.map (entrywiseHom D.Fr) g = entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e g := by
    intro g
    rw [hFrEq]
  have hg0F : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e D.g0 =
      D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by
    rw [← hFrob]
    exact D.hg0
  have hBF : ∀ z : ModGL τ K, entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) z := by
    intro z
    rw [← hFrob]
    exact CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed D.Fr D.hFr z
  have hk' : ∀ y : A, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * (y : adjointGroup τ K) * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 ∧
        rootChar a α = 1 := fun y => hk y.1 y.2
  choose a ha using hk'
  have hconj : ∀ y : A, rootDiagUnit τ (a y) =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (rootDiagUnit τ (a y)) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ := by
    intro y
    have hF : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (rootDiagUnit τ (a y)) =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ * rootDiagUnit τ (a y) *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by
      rw [(ha y).1, map_mul, map_mul, map_inv, hg0F, hBF]
      group
    rw [hF]
    group
  have hrel : ∀ y : A, ∀ v, rootChar (a y) (D.w • v) = rootChar (a y) v ^ (ringChar K ^ e) :=
    fun y v => rootChar_frob_of_conj (a y) D.w (hconj y) v
  have hαS : α ∈ familyKernel a := ⟨hα, fun y => (ha y).2⟩
  have hSw : ∀ β ∈ familyKernel a, D.w • β ∈ familyKernel a ∧ D.w⁻¹ • β ∈ familyKernel a :=
    fun β hβ => family_w_stab a (fun i v => hrel i v) hβ
  have hwS : (fun β => D.w • β) '' familyKernel a = familyKernel a :=
    image_eq_of_mem_stab _ D.w (fun β hβ => (hSw β hβ).1) (fun β hβ => (hSw β hβ).2)
  obtain ⟨x, hx, n, β, hn, hper, hβS, horth, hgβ⟩ := kill_cycle_periodic hτ a D.w hwS hαS
  have hxstab : ∀ i, x ∈ rootCharStabilizerSubgroup (a i) :=
    fun i => closure_refl_stab a (familyKernel a) (fun γ hγ => hγ) hx i
  have hxM : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x ∈
      familyGroup (K := AlgebraicClosure K) a :=
    canonicalRep_closure_mem_familyGroup a hx
  have hxw_img : (fun γ => (x * D.w) • γ) '' familyKernel a = familyKernel a := by
    apply image_eq_of_mem_stab
    · intro γ hγ
      rw [mul_smul]
      exact stab_mem_familyKernel a hxstab (hSw γ hγ).1
    · intro γ hγ
      rw [mul_inv_rev, mul_smul]
      exact (hSw _ (stab_mem_familyKernel a (fun i => inv_mem (hxstab i)) hγ)).2
  have hQnorm : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) ∈
      Subgroup.normalizer (familyGroup (K := AlgebraicClosure K) a :
        Set (ModGL τ (AlgebraicClosure K))) :=
    canonicalRep_mem_normalizer_of_image hxw_img
  obtain ⟨k, hk, hkxw⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) x D.w
  have hQk : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) =
      k⁻¹ * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w) := by
    rw [hkxw]
    group
  have hm_mem : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ ∈
        familyGroup (K := AlgebraicClosure K) a := by
    have hm : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x)⁻¹ * k := by
      rw [hQk]
      group
    rw [hm]
    exact mul_mem (inv_mem hxM) (torus_le_familyGroup a hk)
  have hn_lang : D.g0⁻¹ * entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e D.g0 =
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹) *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    rw [hg0F]
    group
  have hLang := lang_familyGroup (ringChar K) a e he _ hQnorm
  obtain ⟨ζ, hζ, hζQ⟩ := exists_mem_lang_conj (entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e)
    hm_mem hn_lang hLang
  have hg1F : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (D.g0 * ζ) =
      (D.g0 * ζ) * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    rw [← hζQ, mul_inv_cancel_left]
  obtain ⟨v, hvM, hvF, hv1, hvp⟩ := exists_cycle_element (L := AlgebraicClosure K) (ringChar K) e he
    (x * D.w) n hn β hper (fun k => (hβS k).1) horth hgβ (familyKernel a) hβS
  have hvM' : v ∈ familyGroup (K := AlgebraicClosure K) a := rootSpan_le_familyGroup a hvM
  have hFvQ : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) *
      entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v *
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ = v := by
    rw [frobTwistGL_apply] at hvF
    exact hvF
  have hFv : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v =
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ * v *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    calc entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v
        = (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) *
              entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹) *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by group
      _ = _ := by rw [hFvQ]
  have hζadj : ζ ∈ adjointGroup τ (AlgebraicClosure K) := familyGroup_le_adjoint a hζ
  have hvadj : v ∈ adjointGroup τ (AlgebraicClosure K) := familyGroup_le_adjoint a hvM'
  refine ⟨(D.g0 * ζ) * v * (D.g0 * ζ)⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem D.hg0C hζadj) hvadj) (inv_mem (mul_mem D.hg0C hζadj))
  · intro h
    apply hv1
    calc v = (D.g0 * ζ)⁻¹ * ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) * (D.g0 * ζ) := by group
      _ = 1 := by rw [h]; group
  · rw [conj_pow, hvp]
    group
  · rw [hFrob, map_mul, map_mul, map_inv, hg1F, hFv]
    group
  · intro y hy
    obtain ⟨d, hd⟩ : ∃ d, rootDiagUnit τ (a ⟨y, hy⟩) = d := ⟨_, rfl⟩
    have hdy : d = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 := by
      rw [← hd]
      exact (ha ⟨y, hy⟩).1
    have hζd : ζ * d = d * ζ := by
      rw [← hd]
      exact familyGroup_comm a ⟨y, hy⟩ hζ
    have hvd : v * d = d * v := by
      rw [← hd]
      exact familyGroup_comm a ⟨y, hy⟩ hvM'
    have hbz : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) =
        (D.g0 * ζ) * d * (D.g0 * ζ)⁻¹ := by
      have hζd' : ζ * d * ζ⁻¹ = d := by
        rw [hζd]
        group
      calc baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K)
          = D.g0 * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0) * D.g0⁻¹ := by group
        _ = D.g0 * d * D.g0⁻¹ := by rw [← hdy]
        _ = (D.g0 * ζ) * d * (D.g0 * ζ)⁻¹ := by
          rw [show D.g0 * ζ * d * (D.g0 * ζ)⁻¹ = D.g0 * (ζ * d * ζ⁻¹) * D.g0⁻¹ by group, hζd']
    rw [hbz]
    calc ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) * ((D.g0 * ζ) * d * (D.g0 * ζ)⁻¹)
        = (D.g0 * ζ) * (v * d) * (D.g0 * ζ)⁻¹ := by group
      _ = (D.g0 * ζ) * (d * v) * (D.g0 * ζ)⁻¹ := by rw [hvd]
      _ = ((D.g0 * ζ) * d * (D.g0 * ζ)⁻¹) * ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) := by group

theorem finish_of_descent (K : Type) [Field K] [Finite K] (A : Subgroup (adjointGroup τ K))
    (c : adjointGroup τ K) (u' : ModGL τ K) (hu'mem : u' ∈ adjointGroup τ K)
    (uL : ModGL τ (AlgebraicClosure K))
    (hu' : baseChangeGL (algebraMap K (AlgebraicClosure K)) u' = uL)
    (hL1 : uL ≠ 1) (hLp : uL ^ ringChar K = 1)
    (hLc : ∀ y ∈ A, uL * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((c * y * c⁻¹ : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((c * y * c⁻¹ : adjointGroup τ K) : ModGL τ K) * uL) :
    ∃ u : adjointGroup τ K, u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      ∀ x ∈ A, Commute u x := by
  have hinj := baseChangeGL_injective (τ := τ) (algebraMap K (AlgebraicClosure K))
  have hcomm : ∀ y ∈ A, u' * ((c * y * c⁻¹ : adjointGroup τ K) : ModGL τ K) =
      ((c * y * c⁻¹ : adjointGroup τ K) : ModGL τ K) * u' := by
    intro y hy
    apply hinj
    rw [map_mul, map_mul, hu']
    exact hLc y hy
  obtain ⟨U, hUval⟩ : ∃ U : adjointGroup τ K, (U : ModGL τ K) = u' := ⟨⟨u', hu'mem⟩, rfl⟩
  have hU1 : U ≠ 1 := by
    intro h
    apply hL1
    rw [← hu', ← hUval, h, Subgroup.coe_one, map_one]
  have hUp : U ^ ringChar K = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hUval, Subgroup.coe_one]
    apply hinj
    rw [map_pow, hu', hLp, map_one]
  refine ⟨c⁻¹ * U * c, ?_, ?_, ?_⟩
  · intro h
    apply hU1
    calc U = c * (c⁻¹ * U * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  · refine ⟨1, ?_⟩
    rw [pow_one]
    rw [show c⁻¹ * U * c = c⁻¹ * U * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hUp]
    group
  · intro x hx
    have hcomm' : U * (c * x * c⁻¹) = (c * x * c⁻¹) * U :=
      Subtype.ext (by simpa [hUval] using hcomm x hx)
    show c⁻¹ * U * c * x = x * (c⁻¹ * U * c)
    calc c⁻¹ * U * c * x = c⁻¹ * (U * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * U) * c := by rw [hcomm']
      _ = x * (c⁻¹ * U * c) := by group

theorem langPlaneKillsRoot_E7 : LangPlaneKillsRoot Tag.E7 := by
  intro K _ _ A D α hα hk
  obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ :=
    kill_core (τ := Tag.E7) (Or.inr (Or.inr (Or.inl rfl))) K A D α hα hk
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hodd : Odd (Nat.card K) → Odd (orderOf uL) := by
    intro hK
    rw [orderOf_eq_prime huLp huL1]
    rw [hcard] at hK
    exact Odd.of_dvd_nat hK (dvd_pow_self _ (by omega))
  obtain ⟨u', hu'mem, hu'eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E7 D.Fr D.hFr huLad huLF hodd)
  exact finish_of_descent K A D.c u' hu'mem uL hu'eq huL1 huLp huLc

theorem langPlaneKillsRoot_E8 : LangPlaneKillsRoot Tag.E8 := by
  intro K _ _ A D α hα hk
  obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ :=
    kill_core (τ := Tag.E8) (Or.inr (Or.inr (Or.inr rfl))) K A D α hα hk
  obtain ⟨u', hu'mem, hu'eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E8 D.Fr D.hFr huLad huLF)
  exact finish_of_descent K A D.c u' hu'mem uL hu'eq huL1 huLp huLc

end KillsRoot

end CFSG.LieType.SeitzGeneration.ExcHighThree
