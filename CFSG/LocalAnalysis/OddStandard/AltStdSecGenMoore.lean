module

public import CFSG.Sporadic.SchreierLemmas.MoorePresentation
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup CFSG.Sporadic.SchreierLemmas

@[expose] def mooreFrb (i : ℕ) : Finset ℕ := {0, 1, 2, i, i + 1}

theorem moorePerm_apply_of_notMem {n i : ℕ} {s : Fin n} (hs : s.val ∉ mooreFrb i) :
    moorePerm n i s = s := by
  simp only [mooreFrb, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  obtain ⟨h0, h1, h2, hi1, hi2⟩ := hs
  unfold moorePerm
  split_ifs with h h'
  · simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff]
  · simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff]
  · rfl

theorem exists_root_avoiding {n : ℕ} (T : Finset ℕ) (hT : T.card + 3 ≤ n) :
    ∃ S : Finset (Fin n), S.card = 3 ∧ ∀ s ∈ S, s.val ∉ T := by
  classical
  set U : Finset (Fin n) := Finset.univ.filter (fun s => s.val ∉ T) with hU
  have hbad : (Finset.univ.filter (fun s : Fin n => s.val ∈ T)).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn Fin.val (fun s hs => ?_) (fun a _ b _ h => Fin.ext h)
    simpa using hs
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun s : Fin n => s.val ∈ T)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hU3 : 3 ≤ U.card := by
    have : U.card = (Finset.univ.filter (fun s : Fin n => ¬ s.val ∈ T)).card := rfl
    omega
  obtain ⟨S, hSU, hS⟩ := Finset.exists_subset_card_eq hU3
  exact ⟨S, hS, fun s hs => by simpa [hU] using hSU hs⟩

section Rel

variable {n : ℕ}

theorem moorePerm_cube_one (h3 : 3 ≤ n) : moorePerm n 1 ^ 3 = 1 := by
  have := congrArg Subtype.val (isMooreFamily_mooreCycle h3).cube_one
  simpa [coe_mooreCycle] using this

theorem moorePerm_sq (h3 : 3 ≤ n) {j : ℕ} (h2 : 2 ≤ j) (hj : j ≤ n - 2) :
    moorePerm n j ^ 2 = 1 := by
  have := congrArg Subtype.val ((isMooreFamily_mooreCycle h3).sq_eq_one j h2 hj)
  simpa [coe_mooreCycle] using this

theorem moorePerm_cube_adjacent (h3 : 3 ≤ n) {j : ℕ} (h2 : 2 ≤ j) (hj : j ≤ n - 2) :
    (moorePerm n (j - 1) * moorePerm n j) ^ 3 = 1 := by
  have := congrArg Subtype.val ((isMooreFamily_mooreCycle h3).cube_adjacent j h2 hj)
  simpa [coe_mooreCycle] using this

theorem moorePerm_sq_distant (h3 : 3 ≤ n) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j)
    (hj : j ≤ n - 2) : (moorePerm n i * moorePerm n j) ^ 2 = 1 := by
  have := congrArg Subtype.val ((isMooreFamily_mooreCycle h3).sq_distant i j hi hij hj)
  simpa [coe_mooreCycle] using this

theorem moorePerm_mem_altSub {S : Finset (Fin n)} {i : ℕ} (h : ∀ s ∈ S, s.val ∉ mooreFrb i) :
    moorePerm n i ∈ altSub Sᶜ :=
  mem_altSub.2 ⟨sign_moorePerm i, fun j hj => moorePerm_apply_of_notMem
    (h j (by simpa using hj))⟩

end Rel

section Family

variable {G : Type*} [Group G] {n : ℕ}

abbrev RootFamily (G : Type*) [Group G] (n : ℕ) : Type _ :=
  (S : Finset (Fin n)) → S.card = 3 → ↥(altSub Sᶜ) →* G

@[expose] def RootFamily.Agree (ψ : RootFamily G n) : Prop :=
  ∀ (S : Finset (Fin n)) (hS : S.card = 3) (S' : Finset (Fin n)) (hS' : S'.card = 3)
    (x : Perm (Fin n)) (hx : x ∈ altSub Sᶜ) (hx' : x ∈ altSub S'ᶜ),
    ψ S hS ⟨x, hx⟩ = ψ S' hS' ⟨x, hx'⟩

theorem card_mooreFrb_union_le (i j : ℕ) : (mooreFrb i ∪ mooreFrb j).card ≤ 7 := by
  refine (Finset.card_le_card (t := [0, 1, 2, i, i + 1, j, j + 1].toFinset) ?_).trans
    (List.toFinset_card_le _)
  intro x hx
  simp only [mooreFrb, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem exists_root_avoiding_two (hn : 10 ≤ n) (i j : ℕ) :
    ∃ S : Finset (Fin n), S.card = 3 ∧ (∀ s ∈ S, s.val ∉ mooreFrb i) ∧
      ∀ s ∈ S, s.val ∉ mooreFrb j := by
  obtain ⟨S, hS, hSa⟩ := exists_root_avoiding (n := n) (mooreFrb i ∪ mooreFrb j) (by
    have := card_mooreFrb_union_le i j
    omega)
  exact ⟨S, hS, fun s hs => fun h => hSa s hs (Finset.mem_union_left _ h),
    fun s hs => fun h => hSa s hs (Finset.mem_union_right _ h)⟩

@[expose] noncomputable def mooreVal (hn : 10 ≤ n) (ψ : RootFamily G n) (i : ℕ) : G :=
  let h := exists_root_avoiding_two hn i i
  ψ (Classical.choose h) (Classical.choose_spec h).1
    ⟨moorePerm n i, moorePerm_mem_altSub (Classical.choose_spec h).2.1⟩

theorem mooreVal_eq (hn : 10 ≤ n) {ψ : RootFamily G n} (hψ : ψ.Agree) {i : ℕ}
    {S : Finset (Fin n)} (hS : S.card = 3) (hSi : ∀ s ∈ S, s.val ∉ mooreFrb i) :
    mooreVal hn ψ i = ψ S hS ⟨moorePerm n i, moorePerm_mem_altSub hSi⟩ := by
  unfold mooreVal
  exact hψ _ _ _ _ _ _ _

end Family

section Glue

variable {G : Type*} [Group G] {n : ℕ}

theorem isMooreFamily_mooreVal (hn : 10 ≤ n) {ψ : RootFamily G n} (hψ : ψ.Agree) :
    IsMooreFamily (n - 2) (mooreVal hn ψ) := by
  have h3 : 3 ≤ n := by omega
  refine ⟨?_, fun j h2 hj => ?_, fun j h2 hj => ?_, fun i j hi hij hj => ?_⟩
  · obtain ⟨S, hS, hS1, -⟩ := exists_root_avoiding_two hn 1 1
    rw [mooreVal_eq hn hψ hS hS1, ← map_pow]
    have : (⟨moorePerm n 1, moorePerm_mem_altSub hS1⟩ : ↥(altSub Sᶜ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using moorePerm_cube_one h3)
    rw [this, map_one]
  · obtain ⟨S, hS, hSj, -⟩ := exists_root_avoiding_two hn j j
    rw [mooreVal_eq hn hψ hS hSj, ← map_pow]
    have : (⟨moorePerm n j, moorePerm_mem_altSub hSj⟩ : ↥(altSub Sᶜ)) ^ 2 = 1 :=
      Subtype.ext (by simpa using moorePerm_sq h3 h2 hj)
    rw [this, map_one]
  · obtain ⟨S, hS, hS1, hS2⟩ := exists_root_avoiding_two hn (j - 1) j
    rw [mooreVal_eq hn hψ hS hS1, mooreVal_eq hn hψ hS hS2, ← map_mul, ← map_pow]
    have : (⟨moorePerm n (j - 1), moorePerm_mem_altSub hS1⟩ * ⟨moorePerm n j,
        moorePerm_mem_altSub hS2⟩ : ↥(altSub Sᶜ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using moorePerm_cube_adjacent h3 h2 hj)
    rw [this, map_one]
  · obtain ⟨S, hS, hS1, hS2⟩ := exists_root_avoiding_two hn i j
    rw [mooreVal_eq hn hψ hS hS1, mooreVal_eq hn hψ hS hS2, ← map_mul, ← map_pow]
    have : (⟨moorePerm n i, moorePerm_mem_altSub hS1⟩ * ⟨moorePerm n j,
        moorePerm_mem_altSub hS2⟩ : ↥(altSub Sᶜ)) ^ 2 = 1 :=
      Subtype.ext (by simpa using moorePerm_sq_distant h3 hi hij hj)
    rw [this, map_one]

theorem exists_hom_of_rootFamily (hn : 10 ≤ n) {ψ : RootFamily G n} (hψ : ψ.Agree) :
    ∃ Ψ : alternatingGroup (Fin n) →* G, ∀ i ∈ Set.Icc 1 (n - 2),
      ∀ (S : Finset (Fin n)) (hS : S.card = 3) (hSi : ∀ s ∈ S, s.val ∉ mooreFrb i),
        Ψ (mooreCycle n i) = ψ S hS ⟨moorePerm n i, moorePerm_mem_altSub hSi⟩ := by
  obtain ⟨Ψ, hΨ⟩ := exists_hom_mooreCycle (show 3 ≤ n by omega) (mooreVal hn ψ)
    (isMooreFamily_mooreVal hn hψ)
  exact ⟨Ψ, fun i hi S hS hSi => by rw [hΨ i hi, mooreVal_eq hn hψ hS hSi]⟩

end Glue

end CFSG.OddStandard.AltStdSec
