module

import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHsyl

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped commutatorElement

variable {K : Type} [Field K]

section Roots

variable {m : ℕ}

theorem commutatorElement_leviTv_leviTv {i k j : Fin m} (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j)
    (c d : K) : ⁅leviTv K hik c, leviTv K hkj d⁆ = leviTv K hij (c * d) := by
  rw [leviTv, leviTv, leviTv, ← map_commutatorElement,
    TauCeti.commutatorElement_transvectionUnit hik hkj hij]

theorem isSupp_leviTv {i j : Fin m} (hij : i ≠ j) (c : K) {S : Set (Fin m ⊕ Fin m)}
    (hi : coords i ⊆ S) (hj : coords j ⊆ S) : IsSupp S (mat m K (leviTv K hij c)) := by
  intro r t hrt
  rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
  rcases r with x | x <;> rcases t with y | y
  · have h : ¬ (i = x ∧ j = y) := by
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨hi (inl_mem_coords _), hj (inl_mem_coords _)⟩
    simp only [fromBlocks_apply₁₁, transvection, Matrix.add_apply, Matrix.single_apply, h,
      ite_false, add_zero, Matrix.one_apply, Sum.inl.injEq]
  · simp
  · simp
  · have h : ¬ (j = x ∧ i = y) := by
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨hj (inr_mem_coords _), hi (inr_mem_coords _)⟩
    simp only [fromBlocks_apply₂₂, Matrix.add_apply, Matrix.single_apply, h, ite_false, add_zero,
      Matrix.one_apply, Sum.inr.injEq]

theorem isSupp_siegPair (i j : Fin m) (c : K) {S : Set (Fin m ⊕ Fin m)} (hi : coords i ⊆ S)
    (hj : coords j ⊆ S) : IsSupp S (mat m K (siegPair K i j c)) := by
  intro r t hrt
  rw [mat_siegPair]
  rcases r with x | x <;> rcases t with y | y
  · simp [Matrix.one_apply]
  · have h1 : ¬ (i = x ∧ j = y) := by
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨hi (inl_mem_coords _), hj (inr_mem_coords _)⟩
    have h2 : ¬ (j = x ∧ i = y) := by
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨hj (inl_mem_coords _), hi (inr_mem_coords _)⟩
    simp only [fromBlocks_apply₁₂, Matrix.add_apply, Matrix.single_apply, h1, h2, ite_false,
      add_zero, Matrix.one_apply_ne Sum.inl_ne_inr]
  · simp
  · simp [Matrix.one_apply]

theorem leviTv_mem_complSp {i j p : Fin m} (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p) (c : K) :
    leviTv K hij c ∈ complSp K p :=
  isSupp_leviTv hij c (coords_subset_compl_coords hip) (coords_subset_compl_coords hjp)

theorem siegPair_mem_complSp {i j p : Fin m} (hip : i ≠ p) (hjp : j ≠ p) (c : K) :
    siegPair K i j c ∈ complSp K p :=
  isSupp_siegPair i j c (coords_subset_compl_coords hip) (coords_subset_compl_coords hjp)

variable {n : ℕ}

theorem coords_subset_offPQ {i : Fin (n + 3)} (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    coords i ⊆ {t : Fin (n + 3) ⊕ Fin (n + 3) | OffPQ 1 2 t} :=
  fun _ ht => ⟨coords_subset_compl_coords hi1 ht, coords_subset_compl_coords hi2 ht⟩

theorem leviTv_mem_spCompl12 {i j : Fin (n + 3)} (hij : i ≠ j) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (hj1 : j ≠ 1) (hj2 : j ≠ 2) (c : K) : leviTv K hij c ∈ spCompl12 K n := by
  rw [spCompl12_eq_suppGroup]
  exact isSupp_leviTv hij c (coords_subset_offPQ hi1 hi2) (coords_subset_offPQ hj1 hj2)

theorem siegPair_mem_spCompl12 {i j : Fin (n + 3)} (hi1 : i ≠ 1) (hi2 : i ≠ 2) (hj1 : j ≠ 1)
    (hj2 : j ≠ 2) (c : K) : siegPair K i j c ∈ spCompl12 K n := by
  rw [spCompl12_eq_suppGroup]
  exact isSupp_siegPair i j c (coords_subset_offPQ hi1 hi2) (coords_subset_offPQ hj1 hj2)

end Roots

theorem exists_fin_ne_ne_of_three_le {m : ℕ} (hm : 3 ≤ m) (a b : Fin m) :
    ∃ k : Fin m, k ≠ a ∧ k ≠ b := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin m)) ⊆ {a, b} := fun k _ => by
    by_cases hka : k = a
    · simp [hka]
    · simp [h k hka]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h2 := Finset.card_le_two (a := a) (b := b)
  omega

theorem exists_fin_ne_one_two {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 3)) :
    ∃ k : Fin (n + 3), k ≠ 1 ∧ k ≠ 2 ∧ k ≠ j := by
  have h0 : (0 : Fin (n + 3)) ≠ 1 := by simp
  have h02 : (0 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_two] at h'
    omega
  set k3 : Fin (n + 3) := ⟨3, by omega⟩ with hk3
  have h31 : k3 ≠ 1 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_one] at h'
    simp [hk3] at h'
  have h32 : k3 ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_two] at h'
    simp [hk3] at h'
  by_cases hj : j = 0
  · refine ⟨k3, h31, h32, ?_⟩
    rw [hj]
    intro h
    have h' := congrArg Fin.val h
    simp [hk3] at h'
  · exact ⟨0, h0, h02, Ne.symm hj⟩

section B1

variable [CharP K 2] {m : ℕ}

theorem commutator_centralizer_siegDiag_of_perfect (hm : 3 ≤ m) {p : Fin m}
    (hM : ⁅complSp K p, complSp K p⁆ = complSp K p) :
    ⁅centralizer ({siegDiag K p 1} : Set (StatedSp m K)),
      centralizer ({siegDiag K p 1} : Set (StatedSp m K))⁆ =
      centralizer ({siegDiag K p 1} : Set (StatedSp m K)) := by
  set C := centralizer ({siegDiag K p 1} : Set (StatedSp m K)) with hC
  have hMC : complSp K p ≤ C := complSp_le_centralizer_siegDiag
  have hQC : transvRadical K p ≤ C := transvRadical_le_centralizer
  have hMCC : complSp K p ≤ ⁅C, C⁆ := by
    rw [← hM]
    exact commutator_mono hMC hMC
  have hS : ∀ j : Fin m, p ≠ j → ∀ c : K, siegPair K p j c ∈ ⁅C, C⁆ := by
    intro j hpj c
    obtain ⟨k, hkp, hkj⟩ := exists_fin_ne_ne_of_three_le hm p j
    have e := commutatorElement_leviTv_siegPair (Ne.symm hkp) (Ne.symm hkj) (1 : K) c
    rw [one_mul] at e
    rw [← e]
    exact commutator_mem_commutator (hQC (leviTv_mem_transvRadical (Ne.symm hkp) 1))
      (hMC (siegPair_mem_complSp hkp (Ne.symm hpj) c))
  have hL : ∀ (j : Fin m) (hpj : p ≠ j) (c : K), leviTv K hpj c ∈ ⁅C, C⁆ := by
    intro j hpj c
    obtain ⟨k, hkp, hkj⟩ := exists_fin_ne_ne_of_three_le hm p j
    have e := commutatorElement_leviTv_leviTv (Ne.symm hkp) hkj hpj c (1 : K)
    rw [mul_one] at e
    rw [← e]
    exact commutator_mem_commutator (hQC (leviTv_mem_transvRadical (Ne.symm hkp) c))
      (hMC (leviTv_mem_complSp hkj hkp (Ne.symm hpj) 1))
  obtain ⟨j, hjp, -⟩ := exists_fin_ne_ne_of_three_le hm p p
  have hpj : p ≠ j := Ne.symm hjp
  have hD : ∀ c : K, siegDiag K p c ∈ ⁅C, C⁆ := by
    intro c
    have e := commutatorElement_leviTv_siegDiag hpj 1 c
    rw [one_mul, one_mul, one_mul] at e
    have h1 : ⁅leviTv K hpj 1, siegDiag K j c⁆ ∈ ⁅C, C⁆ :=
      commutator_mem_commutator (hQC (leviTv_mem_transvRadical hpj 1))
        (hMC (longRootSp2_le_complSp hpj (siegDiag_mem_longRootSp2 j c)))
    rw [e] at h1
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS j hpj c)) h1
    rwa [inv_mul_cancel_left] at h2
  have hQ : transvRadical K p ≤ ⁅C, C⁆ := transvRadical_le_of_forall_mem hD hL hS
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  calc C = transvRadical K p ⊔ complSp K p := centralizer_siegDiag_eq_sup
    _ ≤ ⁅C, C⁆ := sup_le hQ hMCC

omit [CharP K 2] in
theorem commutator_complSp_two (hK : Nat.card K = 2) (hm : 3 ≤ m) (p : Fin (m + 1)) :
    ⁅complSp K p, complSp K p⁆ = complSp K p := by
  have : Group.IsPerfect (StatedSp m K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp m K (Or.inr (Or.inr ⟨hK, hm⟩))
  rw [complSp_eq_range_spEmbed, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]

theorem commutator_centralizer_siegDiag_two (hK : Nat.card K = 2) (hm : 3 ≤ m)
    (p : Fin (m + 1)) :
    ⁅centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
      centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))⁆ =
      centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) :=
  commutator_centralizer_siegDiag_of_perfect (by omega) (commutator_complSp_two hK hm p)

theorem perfectCore_centralizer_spRep_b1_two (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) :
    perfectCore (centralizer ({spRep n .b1} : Set (StatedSp (n + 3) K))) =
      transvRadical K (1 : Fin (n + 3)) ⊔ complSp K (1 : Fin (n + 3)) := by
  rw [spRep_b1_eq_siegDiag, CFSG.Quasithin.perfectCore_eq_self_of_perfect
    (commutator_centralizer_siegDiag_two hK (m := n + 2) (by omega) 1),
    centralizer_siegDiag_eq_sup]

end B1

section W

variable {n : ℕ}

theorem commutator_wRadical_sup_spCompl12_of_perfect (hn : 1 ≤ n)
    (hS : ⁅spCompl12 K n, spCompl12 K n⁆ = spCompl12 K n) :
    ⁅wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n,
      wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n⁆ =
      wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  set P := wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n with hP
  have h12 : (1 : Fin (n + 3)) ≠ 2 := one_ne_two_fin
  have hQP : wRadical K (1 : Fin (n + 3)) 2 ≤ P := le_sup_left
  have hMP : spCompl12 K n ≤ P := le_sup_right
  have hM : spCompl12 K n ≤ ⁅P, P⁆ := by
    rw [← hS]
    exact commutator_mono hMP hMP
  have hik : ∀ {i k : Fin (n + 3)}, (i = 1 ∨ i = 2) → k ≠ 1 → k ≠ 2 → i ≠ k := by
    rintro i k (rfl | rfl) hk1 hk2 <;> [exact Ne.symm hk1; exact Ne.symm hk2]
  have hSm : ∀ (i j : Fin (n + 3)), (i = 1 ∨ i = 2) → j ≠ 1 → j ≠ 2 → ∀ c : K,
      siegPair K i j c ∈ ⁅P, P⁆ := by
    intro i j hi hj1 hj2 c
    obtain ⟨k, hk1, hk2, hkj⟩ := exists_fin_ne_one_two hn j
    have e := commutatorElement_leviTv_siegPair (hik hi hk1 hk2) (Ne.symm hkj) (1 : K) c
    rw [one_mul] at e
    rw [← e]
    exact commutator_mem_commutator
      (hQP (leviTv_mem_wRadical h12 (hik hi hk1 hk2) hi hk1 hk2 1))
      (hMP (siegPair_mem_spCompl12 hk1 hk2 hj1 hj2 c))
  have hL : ∀ (i j : Fin (n + 3)) (hij : i ≠ j), (i = 1 ∨ i = 2) → j ≠ 1 → j ≠ 2 → ∀ c : K,
      leviTv K hij c ∈ ⁅P, P⁆ := by
    intro i j hij hi hj1 hj2 c
    obtain ⟨k, hk1, hk2, hkj⟩ := exists_fin_ne_one_two hn j
    have e := commutatorElement_leviTv_leviTv (hik hi hk1 hk2) hkj hij c (1 : K)
    rw [mul_one] at e
    rw [← e]
    exact commutator_mem_commutator
      (hQP (leviTv_mem_wRadical h12 (hik hi hk1 hk2) hi hk1 hk2 c))
      (hMP (leviTv_mem_spCompl12 hkj hk1 hk2 hj1 hj2 1))
  have h0 : (0 : Fin (n + 3)) ≠ 1 := by simp
  have h0' : (0 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_two] at h'
    omega
  have hD : ∀ (i : Fin (n + 3)), (i = 1 ∨ i = 2) → ∀ c : K, siegDiag K i c ∈ ⁅P, P⁆ := by
    intro i hi c
    have hi0 : i ≠ 0 := hik hi h0 h0'
    have e := commutatorElement_leviTv_siegDiag hi0 1 c
    rw [one_mul, one_mul, one_mul] at e
    have h1 : ⁅leviTv K hi0 1, siegDiag K 0 c⁆ ∈ ⁅P, P⁆ :=
      commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 hi0 hi h0 h0' 1))
        (hMP (longRootSp2_le_spCompl12_of_ne h0 h0' (siegDiag_mem_longRootSp2 0 c)))
    rw [e] at h1
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hSm i 0 hi h0 h0' c)) h1
    rwa [inv_mul_cancel_left] at h2
  have hP12 : ∀ c : K, siegPair K (1 : Fin (n + 3)) 2 c ∈ ⁅P, P⁆ := by
    intro c
    have h10 : (1 : Fin (n + 3)) ≠ 0 := Ne.symm h0
    have e := commutatorElement_leviTv_siegPair h10 (Ne.symm h0') 1 c
    rw [one_mul] at e
    rw [← e]
    refine commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 h10 (Or.inl rfl) h0 h0' 1))
      (hQP ?_)
    rw [siegPair_comm]
    exact siegPair_mem_wRadical (Or.inr rfl) _
  have hQ : wRadical K (1 : Fin (n + 3)) 2 ≤ ⁅P, P⁆ :=
    wRadical_le_of_forall_mem h12 (hD 1 (Or.inl rfl)) (hD 2 (Or.inr rfl)) hP12
      (fun i j hij hi hj1 hj2 c => hL i j hij hi hj1 hj2 c)
      (fun i j hi hj1 hj2 c => hSm i j hi hj1 hj2 c)
  exact le_antisymm (Subgroup.commutator_le_self _) (sup_le hQ hM)

theorem commutator_spCompl12_two (hK : Nat.card K = 2) (hn : 2 ≤ n) :
    ⁅spCompl12 K n, spCompl12 K n⁆ = spCompl12 K n := by
  have : Group.IsPerfect (StatedSp (n + 1) K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (n + 1) K
      (Or.inr (Or.inr ⟨hK, by omega⟩))
  rw [spCompl12, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem commutator_wRadical_sup_spCompl12_two (hK : Nat.card K = 2) (hn : 2 ≤ n) :
    ⁅wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n,
      wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n⁆ =
      wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n :=
  commutator_wRadical_sup_spCompl12_of_perfect (by omega) (commutator_spCompl12_two hK hn)

end W

section Upper

theorem perfectCore_le_map_ker_of_isSolvable {G S : Type*} [Group G] [Group S] [Finite G]
    [Finite S] [Group.IsSolvable S] (C : Subgroup G) (f : C →* S) :
    perfectCore C ≤ f.ker.map C.subtype := by
  have h1 : (perfectCore (⊤ : Subgroup C)).map C.subtype = perfectCore C := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : (perfectCore (⊤ : Subgroup C)).map f = ⊥ := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map]
    exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).1 inferInstance
  rw [← h1]
  refine map_mono fun x hx => ?_
  rw [MonoidHom.mem_ker]
  have h3 : f x ∈ (perfectCore (⊤ : Subgroup C)).map f := mem_map_of_mem f hx
  rwa [h2, mem_bot] at h3

variable {n : ℕ} [CharP K 2]

theorem mem_wRadical_sup_spCompl12_of_c2Coord_eq_one
    (g : centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} : Set (StatedSp (n + 3) K)))
    (hg1 : c2Coord g = 1) :
    (g : StatedSp (n + 3) K) ∈ wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  have h12 : (1 : Fin (n + 3)) ≠ 2 := one_ne_two_fin
  have hy : mat (n + 3) K g (Sum.inl 1) (Sum.inl 2) = 0 := by
    have := congrArg Multiplicative.toAdd hg1
    simpa [c2Coord] using this
  have hg := (commute_twoCentralElt_iff (1 : K) 1).1 (mem_centralizer_singleton_iff.1 g.2)
  obtain ⟨a1, a2, a3, d1, d2, d3, d4⟩ := c2_blocks h12 hg
  rw [hy] at d4
  set m' : centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} : Set (StatedSp (n + 3) K)) :=
    ⟨leviHom h12 1 one_ne_zero g, leviHom_mem_centralizer h12 one_ne_zero g⟩
  have hq : ((g * m'⁻¹ : centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} :
      Set (StatedSp (n + 3) K))) : StatedSp (n + 3) K) ∈ wRadical K (1 : Fin (n + 3)) 2 := by
    rw [mem_wRadical_iff_leviHom_eq_one h12 one_ne_zero, map_mul, map_inv, leviHom_leviHom,
      mul_inv_cancel]
  have hm : leviHom h12 1 one_ne_zero g ∈ spCompl12 K n := by
    rw [spCompl12_eq_suppGroup]
    intro r t hrt
    rw [mat_leviHom, leviPart_apply]
    have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    have h21 : (2 : Fin (n + 3)) ≠ 1 := Ne.symm h12
    split_ifs with hb
    · have hnot : blk 1 2 r ≠ 2 := fun h2 => hrt ⟨blk_eq_two_iff.1 h2,
        blk_eq_two_iff.1 (hb ▸ h2)⟩
      rcases h3 (blk 1 2 r) with h0 | h1 | h2
      · rcases blk_eq_zero_iff.1 h0 with rfl | rfl <;>
          rcases blk_eq_zero_iff.1 (hb ▸ h0) with h' | h' <;> subst h' <;>
          simp_all
      · rcases blk_eq_one_iff.1 h1 with rfl | rfl <;>
          rcases blk_eq_one_iff.1 (hb ▸ h1) with h' | h' <;> subst h' <;>
          simp_all
      · exact absurd h2 hnot
    · rw [Matrix.one_apply_ne (by rintro rfl; exact hb rfl)]
  have e : (g : StatedSp (n + 3) K) =
      ((g * m'⁻¹ : centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} :
        Set (StatedSp (n + 3) K))) : StatedSp (n + 3) K) * leviHom h12 1 one_ne_zero g := by
    simp [m']
  rw [e]
  exact Subgroup.mul_mem _ (mem_sup_left hq) (mem_sup_right hm)

theorem perfectCore_centralizer_c2_le :
    perfectCore (centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} :
      Set (StatedSp (n + 3) K))) ≤ wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  set C := centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} : Set (StatedSp (n + 3) K))
  calc perfectCore C ≤ ⁅C, C⁆ := CFSG.Quasithin.perfectCore_le_derivedSeriesOf C 1
    _ ≤ wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hc : ⁅(⟨g₁, hg₁⟩ : C), ⟨g₂, hg₂⟩⁆ = (⟨⁅g₁, g₂⁆, Subgroup.commutator_mem_commutator
          hg₁ hg₂ |> fun h => (Subgroup.commutator_le_self C) h⟩ : C) := rfl
      have h1 : c2Coord ⁅(⟨g₁, hg₁⟩ : C), ⟨g₂, hg₂⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
      rw [hc] at h1
      exact mem_wRadical_sup_spCompl12_of_c2Coord_eq_one _ h1

theorem mem_wRadical_sup_spCompl12_of_a2Coord_eq_one
    (g : centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)))
    (hg1 : a2Coord one_ne_two_fin (one_ne_zero (α := K)) g = 1) :
    (g : StatedSp (n + 3) K) ∈ wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  have h12 := one_ne_two_fin (n := n)
  have hW : wBlock 1 2 (mat (n + 3) K g) = 1 := congrArg Subtype.val hg1
  have hcomm := (commute_twoCentralElt_iff (0 : K) 1).1 (mem_centralizer_singleton_iff.1 g.2)
  obtain ⟨-, d1, d2, d3, d4⟩ := a2_blocks h12 one_ne_zero hcomm
  have hW' : ∀ i j : Fin 2,
      wBlock 1 2 (mat (n + 3) K g) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by rw [hW]
  have a11 := hW' 0 0
  have a12 := hW' 0 1
  have a21 := hW' 1 0
  have a22 := hW' 1 1
  simp only [wBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply_eq] at a11 a12 a21 a22
  simp only [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at a12 a21
  have hA : ∀ x y : Fin (n + 3), (x = 1 ∨ x = 2) → (y = 1 ∨ y = 2) →
      mat (n + 3) K g (Sum.inl x) (Sum.inl y) =
        (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) x y := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp [a11, a12, a21, a22, h12, Ne.symm h12]
  have hD : ∀ x y : Fin (n + 3), (x = 1 ∨ x = 2) → (y = 1 ∨ y = 2) →
      mat (n + 3) K g (Sum.inr x) (Sum.inr y) =
        (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) x y := by
    rintro x y (rfl | rfl) (rfl | rfl) <;>
      simp [d1, d2, d3, d4, a11, a12, a21, a22, h12, Ne.symm h12]
  have hm := leviHom_mem_spCompl12 (one_ne_zero (α := K)) g hA hD
  set m' : centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)) :=
    ⟨leviHom h12 0 one_ne_zero g, leviHom_mem_centralizer h12 one_ne_zero g⟩
  have hq : ((g * m'⁻¹ : centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} :
      Set (StatedSp (n + 3) K))) : StatedSp (n + 3) K) ∈ wRadical K (1 : Fin (n + 3)) 2 := by
    rw [mem_wRadical_iff_leviHom_eq_one h12 one_ne_zero, map_mul, map_inv, leviHom_leviHom,
      mul_inv_cancel]
  have e : (g : StatedSp (n + 3) K) =
      ((g * m'⁻¹ : centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} :
        Set (StatedSp (n + 3) K))) : StatedSp (n + 3) K) * leviHom h12 0 one_ne_zero g := by
    simp [m']
  rw [e]
  exact Subgroup.mul_mem _ (mem_sup_left hq) (mem_sup_right hm)

theorem isSolvable_SL2_of_natCard_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (Or.inl hF)
  exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective

theorem perfectCore_centralizer_a2_le_two [Finite K] (hK : Nat.card K = 2) :
    perfectCore (centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} :
      Set (StatedSp (n + 3) K))) ≤ wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  have := isSolvable_SL2_of_natCard_two hK
  refine (perfectCore_le_map_ker_of_isSolvable _
    (a2Coord one_ne_two_fin (one_ne_zero (α := K)))).trans ?_
  rintro _ ⟨g, hg, rfl⟩
  exact mem_wRadical_sup_spCompl12_of_a2Coord_eq_one g hg

end Upper

section CoresW

variable {n : ℕ} [Finite K] [CharP K 2]

theorem perfectCore_centralizer_twoCentralElt_two (hK : Nat.card K = 2) (hn : 2 ≤ n) {a : K}
    (ha : a = 0 ∨ a = 1) :
    perfectCore (centralizer ({twoCentralElt (n + 3) 1 2 a 1} : Set (StatedSp (n + 3) K))) =
      wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect
    (sup_le (wRadical_le_centralizer_twoCentralElt a 1)
      (spCompl12_le_centralizer_twoCentralElt n a 1))
    (commutator_wRadical_sup_spCompl12_two hK hn))
  rcases ha with rfl | rfl
  · exact perfectCore_centralizer_a2_le_two hK
  · exact perfectCore_centralizer_c2_le

end CoresW

end CFSG.SeitzReduction.SymplecticPilot
