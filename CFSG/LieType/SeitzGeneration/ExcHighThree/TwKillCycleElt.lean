module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree


open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def twCycSeq {L : Type} [Field L] (s : ℕ → L) (q : ℕ) (t₀ : L) : ℕ → L
  | 0 => t₀
  | k + 1 => s k * (twCycSeq s q t₀ k) ^ q

theorem twCycSeq_affine {L : Type} [Field L] (s : ℕ → L) (hs : ∀ k, s k * s k = 1) (q : ℕ) :
    ∀ n : ℕ, ∃ S : L, S * S = 1 ∧ ∀ t₀ : L, twCycSeq s q t₀ n = S * t₀ ^ (q ^ n)
  | 0 => ⟨1, by simp, fun t₀ => by simp [twCycSeq]⟩
  | n + 1 => by
    obtain ⟨S, hS, hf⟩ := twCycSeq_affine s hs q n
    refine ⟨s n * S ^ q, ?_, fun t₀ => ?_⟩
    · calc (s n * S ^ q) * (s n * S ^ q) = (s n * s n) * (S * S) ^ q := by rw [mul_pow]; ring
        _ = 1 := by rw [hs n, hS, one_pow, mul_one]
    · simp only [twCycSeq]
      rw [hf, mul_pow, ← pow_mul, pow_succ]
      ring

theorem exists_twCycSeq_fixed {L : Type} [Field L] [IsAlgClosed L] (s : ℕ → L)
    (hs : ∀ k, s k * s k = 1) {q n : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    ∃ t₀ : L, t₀ ≠ 0 ∧ twCycSeq s q t₀ n = t₀ := by
  obtain ⟨S, hS, hf⟩ := twCycSeq_affine s hs q n
  have hqn : 2 ≤ q ^ n := le_trans hq (Nat.le_self_pow hn.ne' q)
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_pow_nat_eq S (show 0 < q ^ n - 1 by omega)
  have hS0 : S ≠ 0 := fun h => by rw [h, zero_mul] at hS; exact zero_ne_one hS
  have ht0 : t₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht₀
    exact hS0 ht₀.symm
  refine ⟨t₀, ht0, ?_⟩
  rw [hf, show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, ht₀, ← mul_assoc, hS, one_mul]

theorem twCycSeq_periodic {L : Type} [Field L] (s : ℕ → L) (q n : ℕ) (hper : ∀ k, s (k + n) = s k)
    (t₀ : L) (hfix : twCycSeq s q t₀ n = t₀) : ∀ k, twCycSeq s q t₀ (k + n) = twCycSeq s q t₀ k
  | 0 => by simpa [twCycSeq] using hfix
  | k + 1 => by
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [twCycSeq]
    rw [hper k, twCycSeq_periodic s q n hper t₀ hfix k]

section TwCycle

theorem twistHom_pinnedX_sign {L : Type} [Field L] (Fr : L →+* L) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) :
    ∃ ε : L, ε * ε = 1 ∧ ∀ c : L, twistHom TwistTag.E6 L Fr (pinnedX TwistTag.E6.tag L γ c) =
      pinnedX TwistTag.E6.tag L (permLattice TwistTag.E6.perm γ) (ε * Fr c) := by
  obtain ⟨ε, he, hε⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hγ
  refine ⟨ε, he, fun c => ?_⟩
  have h1 : twistHom TwistTag.E6 L Fr (pinnedX TwistTag.E6.tag L γ c) =
      diagramMap TwistTag.E6 L * Units.map (entrywiseHom Fr) (pinnedX TwistTag.E6.tag L γ c) *
        (diagramMap TwistTag.E6 L)⁻¹ := rfl
  rw [h1, show Units.map (entrywiseHom Fr) (pinnedX TwistTag.E6.tag L γ c) =
    pinnedX TwistTag.E6.tag L γ (Fr c) from Units.ext (entrywise_pinnedX Fr γ c), hε]

theorem twisted_cycle_element {L : Type} [Field L] [IsAlgClosed L] (p e : ℕ) [Fact p.Prime]
    [CharP L p] (he : 1 ≤ e) (g : WeylGroup TwistTag.E6.tag) (n : ℕ) (hn : 0 < n)
    (β : ℕ → Fin TwistTag.E6.tag.rank → ℤ)
    (hper : ∀ k, β (k + n) = β k) (hroot : ∀ k, IsRoot TwistTag.E6.tag (β k))
    (horth : ∀ k l, k < n → l < n → k ≠ l →
      iform (β k) (β l) = 0 ∧ β k ≠ β l ∧ ¬ IsRoot TwistTag.E6.tag (β k + β l))
    (hgβ : ∀ k, g • permLattice TwistTag.E6.perm (β k) = β (k + 1))
    (S : Set (Fin TwistTag.E6.tag.rank → ℤ)) (hS : ∀ k, β k ∈ S) :
    ∃ v : ModGL TwistTag.E6.tag L, v ∈ rootSpan TwistTag.E6.tag L S ∧
      twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L g)
        (iterateFrobenius L p e) v = v ∧ v ≠ 1 ∧ v ^ p = 1 := by
  obtain ⟨s0, hs0⟩ := exists_sign_family (L := L) (τ := TwistTag.E6.tag) g
  have hpi : ∀ k, IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm (β k)) := fun k =>
    (hroot k).permLattice TwistTag.E6.cartan_perm
  have hsign : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, ∃ ε : L, IsRoot TwistTag.E6.tag γ →
      (ε * ε = 1 ∧ ∀ c : L, twistHom TwistTag.E6 L (iterateFrobenius L p e)
        (pinnedX TwistTag.E6.tag L γ c) =
          pinnedX TwistTag.E6.tag L (permLattice TwistTag.E6.perm γ) (ε * iterateFrobenius L p e c)) := by
    intro γ
    by_cases hγ : IsRoot TwistTag.E6.tag γ
    · obtain ⟨ε, h1, h2⟩ := twistHom_pinnedX_sign (iterateFrobenius L p e) hγ
      exact ⟨ε, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hγ⟩
  choose ε hε using hsign
  have hεc : ∀ k c, twistHom TwistTag.E6 L (iterateFrobenius L p e)
      (pinnedX TwistTag.E6.tag L (β k) c) =
        pinnedX TwistTag.E6.tag L (permLattice TwistTag.E6.perm (β k)) (ε (β k) * iterateFrobenius L p e c) :=
    fun k c => ((hε (β k)) (hroot k)).2 c
  have hs_sign : ∀ k, (s0 (permLattice TwistTag.E6.perm (β k)) * ε (β k)) *
      (s0 (permLattice TwistTag.E6.perm (β k)) * ε (β k)) = 1 := by
    intro k
    rw [mul_mul_mul_comm, (hs0 _ (hpi k)).1, ((hε (β k)) (hroot k)).1, mul_one]
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → L, ∀ k, s k = s0 (permLattice TwistTag.E6.perm (β k)) * ε (β k) :=
    ⟨fun k => s0 (permLattice TwistTag.E6.perm (β k)) * ε (β k), fun k => rfl⟩
  have hs : ∀ k, s k * s k = 1 := fun k => by rw [hsdef k]; exact hs_sign k
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ e := le_trans hp2 (Nat.le_self_pow (by omega) p)
  obtain ⟨t₀, ht₀, hfix⟩ := exists_twCycSeq_fixed s hs hq2 hn
  obtain ⟨t, ht⟩ : ∃ t : ℕ → L, t = twCycSeq s (p ^ e) t₀ := ⟨_, rfl⟩
  have ht0 : t 0 = t₀ := by rw [ht]; simp only [twCycSeq]
  have htsucc : ∀ k, t (k + 1) = s k * (t k) ^ (p ^ e) := fun k => by rw [ht]; simp only [twCycSeq]
  have htn : t n = t₀ := by rw [ht]; exact hfix
  have htper : ∀ k, t (k + n) = t k := by
    intro k
    rw [ht]
    exact twCycSeq_periodic s (p ^ e) n (fun k => by rw [hsdef, hsdef, hper k]) t₀ hfix k
  obtain ⟨f, hf⟩ : ∃ f : ℕ → (Module.End L (RootModule TwistTag.E6.tag L))ˣ,
      ∀ k, f k = pinnedX TwistTag.E6.tag L (β k) (t k) := ⟨_, fun k => rfl⟩
  have hG : ∀ k, twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L g)
      (iterateFrobenius L p e) (f k) = f (k + 1) := by
    intro k
    rw [twFrob_apply, hf k, hεc k (t k), iterateFrobenius_def,
      (hs0 _ (hpi k)).2 (ε (β k) * t k ^ (p ^ e)), hgβ k, hf (k + 1), htsucc k, hsdef k, mul_assoc]
  have hGv : twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L g)
      (iterateFrobenius L p e) (((List.range n).map f).prod) =
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
  have hmem : ((List.range n).map f).prod ∈ rootSpan TwistTag.E6.tag L S := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [hf]
    have hle : rootSubgroup TwistTag.E6.tag L (β k) ≤ rootSpan TwistTag.E6.tag L S :=
      le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup TwistTag.E6.tag L α) (β k) (hS k)
        le_rfl
    exact hle (Subgroup.subset_closure ⟨t k, rfl⟩)
  have hconv : ∀ g' : ℕ → (Module.End L (RootModule TwistTag.E6.tag L))ˣ,
      (List.range n).map g' = List.ofFn (fun i : Fin n => g' i.val) := by
    intro g'
    apply List.ext_getElem <;> simp
  have hv_eq : ((List.range n).map f).prod =
      (List.ofFn fun i : Fin n => pinnedX TwistTag.E6.tag L (β i.val) (t i.val)).prod := by
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
    have hP : (List.ofFn fun i : Fin n => pinnedX TwistTag.E6.tag L (β i.val) (t i.val)).prod = 1 := by
      rw [← hv_eq]
      exact hv1
    exact hne hP
  have hvp : ((List.range n).map f).prod ^ p = 1 :=
    pow_prod_range_eq_one p f n hcomm (fun i _ => by rw [hf]; exact pinnedX_pow_char p _ _)
  refine ⟨((List.range n).map f).prod, hmem, ?_, hv_ne, hvp⟩
  rw [hGv, hP']

end TwCycle

end CFSG.LieType.SeitzGeneration.ExcHighThree
