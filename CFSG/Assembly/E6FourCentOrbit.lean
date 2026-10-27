module

public import CFSG.Assembly.E6FourCentRows

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.E6FourCentChk
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix


private theorem rho_e6RootVec
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {k : ℕ} (hk : k < 72) :
    ρ (e6RootVec k) = e6RootVec (permAt permLit k) := by
  rw [hρ _ (isRoot_e6RootVec hk)]
  exact (permAt_permLit hk).2.symm

private theorem wordMat_e6Two_mulVec_mulVec (v : Fin Tag.E6.rank → ℤ) :
    (wordMat Tag.E6 e6TwoWord) *ᵥ ((wordMat Tag.E6 e6TwoWord) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← pow_two, e6Two_pow, Matrix.one_mulVec]

private theorem rho_rho_e6RootVec
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {k : ℕ} (hk : k < 72) :
    ρ (ρ (e6RootVec k)) = e6RootVec k := by
  have hj72 : permAt permLit k < 72 := (permAt_permLit hk).1
  rw [rho_e6RootVec ρ hρ hk, rho_e6RootVec ρ hρ hj72, (permAt_permLit hj72).2,
    (permAt_permLit hk).2, wordMat_e6Two_mulVec_mulVec]

private theorem e6MaskRoots_or (c m : ℕ) :
    e6MaskRoots (c ||| m) = e6MaskRoots c ∪ e6MaskRoots m := by
  ext γ
  simp only [e6MaskRoots, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨k, hk, hbit, rfl⟩
    rw [Nat.testBit_or, Bool.or_eq_true] at hbit
    rcases hbit with hbit | hbit
    · exact Or.inl ⟨k, hk, hbit, rfl⟩
    · exact Or.inr ⟨k, hk, hbit, rfl⟩
  · rintro (⟨k, hk, hbit, rfl⟩ | ⟨k, hk, hbit, rfl⟩)
    · exact ⟨k, hk, by rw [Nat.testBit_or, Bool.or_eq_true]; exact Or.inl hbit, rfl⟩
    · exact ⟨k, hk, by rw [Nat.testBit_or, Bool.or_eq_true]; exact Or.inr hbit, rfl⟩

theorem rho_image_e6MaskRoots
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {c : ℕ} (hc : c < 2 ^ 72) :
    ρ '' e6MaskRoots c = e6MaskRoots (mapMaskP permLit 72 c 0) := by
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    obtain ⟨k, hk, hbit, rfl⟩ := hδ
    refine ⟨permAt permLit k, (permAt_permLit hk).1, ?_, ?_⟩
    · rw [testBit_mapMaskP permLit 72 c 0 (permAt permLit k) hc, Nat.zero_testBit]
      exact Or.inr ⟨k, hk, hbit, rfl⟩
    · exact (rho_e6RootVec ρ hρ hk).symm
  · rintro ⟨j, hj, hbit, rfl⟩
    rw [testBit_mapMaskP permLit 72 c 0 j hc, Nat.zero_testBit] at hbit
    rcases hbit with hbit | ⟨i, hi, hci, hji⟩
    · exact absurd hbit (by decide)
    · refine ⟨e6RootVec i, ⟨i, hi, hci, rfl⟩, ?_⟩
      rw [rho_e6RootVec ρ hρ hi, hji]

private theorem rho_image_e6MaskRoots'
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {c : ℕ} (hc : c < 2 ^ 72) :
    ρ '' e6MaskRoots (mapMaskP permLit 72 c 0) = e6MaskRoots c := by
  rw [← rho_image_e6MaskRoots ρ hρ hc]
  ext γ
  constructor
  · rintro ⟨δ, ⟨ε, hε, rfl⟩, rfl⟩
    obtain ⟨k, hk, hbit, rfl⟩ := hε
    rw [rho_rho_e6RootVec ρ hρ hk]
    exact ⟨k, hk, hbit, rfl⟩
  · intro hγ
    obtain ⟨k, hk, hbit, rfl⟩ := hγ
    exact ⟨ρ (e6RootVec k), ⟨e6RootVec k, ⟨k, hk, hbit, rfl⟩, rfl⟩,
      rho_rho_e6RootVec ρ hρ hk⟩

private theorem mapMaskP_permLit_lt {c : ℕ} (hc : c < 2 ^ 72) :
    mapMaskP permLit 72 c 0 < 2 ^ 72 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  by_contra hne
  have htrue : (mapMaskP permLit 72 c 0).testBit j = true := by
    cases hbit : (mapMaskP permLit 72 c 0).testBit j
    · exact absurd hbit hne
    · rfl
  rw [testBit_mapMaskP permLit 72 c 0 j hc] at htrue
  rcases htrue with h0 | ⟨i, hi, hci, hji⟩
  · exact absurd h0 (by simp [Nat.zero_testBit])
  · have := (permAt_permLit hi).1
    omega

theorem e6Four_rationalRoots {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ} (i : KernelComponent χ) {c : ℕ}
    (hc : c < 2 ^ 72) (hi : componentRoots χ i = e6MaskRoots c) :
    rationalRoots ρ χ i = e6MaskRoots (Nat.lor c (mapMaskP permLit 72 c 0)) := by
  classical
  let m : ℕ := mapMaskP permLit 72 c 0
  change rationalRoots ρ χ i = e6MaskRoots (c ||| m)
  have himg : ρ '' e6MaskRoots c = e6MaskRoots m := rho_image_e6MaskRoots ρ hρ hc
  have himgB : ρ '' e6MaskRoots m = e6MaskRoots c := rho_image_e6MaskRoots' ρ hρ hc
  have hor : e6MaskRoots (c ||| m) = e6MaskRoots c ∪ e6MaskRoots m := e6MaskRoots_or c m
  have hstab : ρ '' e6MaskRoots (c ||| m) ⊆ e6MaskRoots (c ||| m) := by
    rw [hor, Set.image_union, himg, himgB]
    exact Set.union_subset Set.subset_union_right Set.subset_union_left
  have hiter : ∀ k, (ρ^[k]) '' e6MaskRoots c ⊆ e6MaskRoots (c ||| m) := by
    intro k
    induction k with
    | zero =>
      rw [Function.iterate_zero, Set.image_id, hor]
      exact Set.subset_union_left
    | succ k ih =>
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := hγ
      rw [Function.iterate_succ_apply']
      apply hstab
      exact ⟨(ρ^[k]) δ, ih ⟨δ, hδ, rfl⟩, rfl⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro γ ⟨k, δ, hδ, hγ⟩
    rw [hi] at hδ
    rw [hγ]
    exact hiter k ⟨δ, hδ, rfl⟩
  · rintro γ hγ
    rw [hor] at hγ
    rcases hγ with hγ | hγ
    · exact ⟨0, γ, by rw [hi]; exact hγ, by simp⟩
    · rw [← himg] at hγ
      obtain ⟨δ, hδ, rfl⟩ := hγ
      exact ⟨1, δ, by rw [hi]; exact hδ, by simp [Function.iterate_one]⟩

theorem e6Four_hasFive_card {R : ℕ} (hR : R < 2 ^ 72) (h : hasFive R sigsLit 0 = true) :
    6 ≤ Nat.card {w : Fin Tag.E6.rank → ZMod 5 //
      E6FourIsSol w ∧ ∀ γ ∈ e6MaskRoots R, e6Pair w γ = 0} := by
  classical
  let S := {w : Fin Tag.E6.rank → ZMod 5 //
      E6FourIsSol w ∧ ∀ γ ∈ e6MaskRoots R, e6Pair w γ = 0}
  let l : List ℕ := (List.range' 1 624).filter
    (fun n => Nat.land R (e6SolMask (e6SolVec n)) == R)
  have hlen : 5 ≤ l.length := by
    have h5 : 5 ≤ (sigsLit.filter fun m => Nat.land R m == R).length := by
      have := (hasFive_iff R sigsLit 0).1 h
      simpa using this
    rw [sigsLit_eq, List.filter_map, List.length_map] at h5
    change 5 ≤ ((List.range' 1 624).filter
      (fun n => Nat.land R (e6SolMask (e6SolVec n)) == R)).length at h5
    simpa [l] using h5
  have hmem : ∀ n ∈ l, E6FourIsSol (e6SolVec n) ∧
      ∀ γ ∈ e6MaskRoots R, e6Pair (e6SolVec n) γ = 0 := by
    intro n hn
    have hn' : n ∈ (List.range' 1 624).filter
        (fun n => Nat.land R (e6SolMask (e6SolVec n)) == R) := by
      simpa [l] using hn
    obtain ⟨hnr, hp⟩ := List.mem_filter.mp hn'
    obtain ⟨k, hk, hnk⟩ := List.mem_range'.mp hnr
    have hn1 : 1 ≤ n := by omega
    have hn624 : n ≤ 624 := by omega
    refine ⟨e6SolVec_isSol n, ?_⟩
    intro γ hγ
    obtain ⟨j, hj, hjR, rfl⟩ := hγ
    have hland : R &&& e6SolMask (e6SolVec n) = R := Nat.eq_of_beq_eq_true hp
    have hbit : (R &&& e6SolMask (e6SolVec n)).testBit j = true := by
      rw [hland]; exact hjR
    rw [Nat.testBit_and, Bool.and_eq_true] at hbit
    exact (testBit_e6SolMask (e6SolVec n) hj).1 hbit.2
  have hzero : E6FourIsSol (0 : Fin Tag.E6.rank → ZMod 5) ∧
      ∀ γ ∈ e6MaskRoots R, e6Pair 0 γ = 0 := by
    refine ⟨?_, ?_⟩
    · intro j
      simp [E6FourIsSol]
    · intro γ _
      simp [e6Pair]
  let z : S := ⟨0, hzero.1, hzero.2⟩
  have hl_nodup : l.Nodup := by
    have hbase : (List.range' 1 624).Nodup := by
      rw [List.range'_eq_map_range]
      exact (List.nodup_range (n := 624)).map (fun a b hab => by omega)
    exact (List.filter_sublist (p := fun n => Nat.land R (e6SolMask (e6SolVec n)) == R)).nodup hbase
  let T : Finset ℕ := l.toFinset
  have hTcard : 5 ≤ T.card := by
    change 5 ≤ l.toFinset.card
    rw [List.toFinset_card_of_nodup hl_nodup]
    exact hlen
  let f : ℕ → S := fun n =>
    dite (n ∈ l) (fun hn => ⟨e6SolVec n, (hmem n hn).1, (hmem n hn).2⟩) (fun _ => z)
  have hf_inj : Set.InjOn f ↑T := by
    intro a ha b hb hab
    have ha' : a ∈ l := by simpa [T] using ha
    have hb' : b ∈ l := by simpa [T] using hb
    have hfa : f a = ⟨e6SolVec a, (hmem a ha').1, (hmem a ha').2⟩ := dif_pos ha'
    have hfb : f b = ⟨e6SolVec b, (hmem b hb').1, (hmem b hb').2⟩ := dif_pos hb'
    rw [hfa, hfb] at hab
    have heq : e6SolVec a = e6SolVec b := congrArg Subtype.val hab
    have ha625 : a < 625 := by
      obtain ⟨k, hk, hnk⟩ := List.mem_range'.mp (List.mem_filter.mp ha').1
      omega
    have hb625 : b < 625 := by
      obtain ⟨k, hk, hnk⟩ := List.mem_range'.mp (List.mem_filter.mp hb').1
      omega
    exact e6SolVec_injOn ha625 hb625 heq
  have hcard_image : (T.image f).card = T.card := Finset.card_image_of_injOn hf_inj
  have hz_notin : z ∉ T.image f := by
    intro hz
    obtain ⟨n, hnT, hnf⟩ := Finset.mem_image.mp hz
    have hn' : n ∈ l := by simpa [T] using hnT
    have hfn : f n = ⟨e6SolVec n, (hmem n hn').1, (hmem n hn').2⟩ := dif_pos hn'
    rw [hfn] at hnf
    have hz0 : e6SolVec n = 0 := by
      have := congrArg Subtype.val hnf
      simpa [z] using this
    obtain ⟨k, hk, hnk⟩ := List.mem_range'.mp (List.mem_filter.mp hn').1
    have hn1 : 1 ≤ n := by omega
    have hn624 : n ≤ 624 := by omega
    exact absurd hz0 (e6SolVec_ne_zero hn1 hn624)
  let U : Finset S := insert z (T.image f)
  have hUcard : 6 ≤ U.card := by
    change 6 ≤ (insert z (T.image f)).card
    rw [Finset.card_insert_of_notMem hz_notin, hcard_image]
    omega
  have hUle : U.card ≤ Nat.card S := by
    have hle' := Finset.card_le_card (Finset.subset_univ U)
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle'
  exact hUcard.trans hUle

theorem e6Four_typed_row {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    {v : Fin Tag.E6.rank → ZMod 5} (hv : E6FourIsSol v) (hv0 : v ≠ 0)
    (i : KernelComponent (rootCharHom (fun j => ζ ^ (v j).val)))
    (hle : Nat.card {w : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol w ∧
      ∀ γ ∈ rationalRoots ρ (rootCharHom (fun j => ζ ^ (v j).val)) i, e6Pair w γ = 0} ≤ 5) :
    ∃ c : ℕ, c < 2 ^ 72 ∧
      componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i = e6MaskRoots c ∧
        typedOK c c = true ∧
        componentOrbitLength ρ (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i) = 1 := by
  classical
  obtain ⟨c, hc, hci, hrow⟩ := e6Four_component_row ζ hζ hv hv0 i
  have hrow' : hasFive (Nat.lor c (mapMaskP permLit 72 c 0)) sigsLit 0 = true ∨
      typedOK c (mapMaskP permLit 72 c 0) = true := by
    have this := hrow
    simp only [rowOK, Bool.and_eq_true, Bool.or_eq_true] at this
    exact this.2
  rcases hrow' with hfive | htyped
  · exfalso
    have hR : Nat.lor c (mapMaskP permLit 72 c 0) < 2 ^ 72 :=
      Nat.or_lt_two_pow hc (mapMaskP_permLit_lt hc)
    have hrr : rationalRoots ρ (rootCharHom (fun j => ζ ^ (v j).val)) i =
        e6MaskRoots (Nat.lor c (mapMaskP permLit 72 c 0)) :=
      e6Four_rationalRoots (L := L) ρ hρ (i := i) (c := c) hc hci
    rw [hrr] at hle
    have h6 := e6Four_hasFive_card (R := Nat.lor c (mapMaskP permLit 72 c 0)) hR hfive
    omega
  · have hmc : mapMaskP permLit 72 c 0 = c := by
      have h1 : Nat.beq (mapMaskP permLit 72 c 0) c = true := by
        have this := htyped
        simp only [typedOK, Bool.and_eq_true] at this
        exact this.1
      exact Nat.eq_of_beq_eq_true h1
    have htyped_cc : typedOK c c = true := by
      rw [hmc] at htyped
      exact htyped
    refine ⟨c, hc, hci, htyped_cc, ?_⟩
    rw [hci]
    have himg : ρ '' e6MaskRoots c = e6MaskRoots c := by
      rw [rho_image_e6MaskRoots ρ hρ hc, hmc]
    unfold componentOrbitLength
    refine le_antisymm ?_ ?_
    · apply Nat.sInf_le
      exact ⟨Nat.one_pos, by rw [Function.iterate_one]; exact himg⟩
    · have hmem : 1 ∈ {s : ℕ | 0 < s ∧
          (ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' e6MaskRoots c = e6MaskRoots c} :=
        ⟨Nat.one_pos, by rw [Function.iterate_one]; exact himg⟩
      exact (Nat.sInf_mem ⟨1, hmem⟩).1

end CFSG.Assembly

end
