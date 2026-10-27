module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Facts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupA7
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5A7

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7 D8 sD tD card_D8 sq_eq_one_of_commute_D8)

@[expose] noncomputable def autPerm : MulAut A7 ≃* Perm (Fin 7) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))).symm

theorem autPerm_symm_apply (π : Perm (Fin 7)) (x : A7) :
    ((autPerm.symm π x : A7) : Perm (Fin 7)) = π * x * π⁻¹ := rfl

theorem coe_apply (α : MulAut A7) (x : A7) :
    ((α x : A7) : Perm (Fin 7)) = autPerm α * x * (autPerm α)⁻¹ := by
  rw [← autPerm_symm_apply, MulEquiv.symm_apply_apply]

theorem autPerm_conj (s : A7) : autPerm (MulAut.conj s) = s := by
  apply autPerm.symm.injective
  rw [MulEquiv.symm_apply_apply]
  ext x
  rw [autPerm_symm_apply, MulAut.conj_apply]
  rfl

theorem mem_innAut5_iff (α : MulAut A7) :
    α ∈ innAut5 A7 ↔ Perm.sign (autPerm α) = 1 := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [autPerm_conj]
    exact mem_alternatingGroup.mp s.2
  · intro h
    refine ⟨⟨autPerm α, h⟩, autPerm.injective ?_⟩
    rw [autPerm_conj]

theorem conj_injective : Function.Injective (MulAut.conj : A7 →* MulAut A7) := fun s t h =>
  Subtype.ext (by rw [← autPerm_conj s, ← autPerm_conj t, h])

theorem autPerm_sign_of_not_mem {β : MulAut A7} (hβ : β ∉ innAut5 A7) :
    Perm.sign (autPerm β) = -1 := by
  rw [mem_innAut5_iff] at hβ
  rcases Int.units_eq_one_or (Perm.sign (autPerm β)) with h | h
  · exact absurd h hβ
  · exact h

theorem mem_sylow_of_commute {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Sylow p G) {s : G} {k : ℕ} (hs : s ^ p ^ k = 1)
    (hsR : ∀ r ∈ (R : Subgroup G), s * r = r * s) : s ∈ (R : Subgroup G) := by
  have hsp : IsPGroup p (zpowers s) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hs)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hconj : ∀ r ∈ (R : Subgroup G), s * r * s⁻¹ = r := fun r hr => by
    rw [hsR r hr, mul_inv_cancel_right]
  have hle : zpowers s ≤ normalizer ((R : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      rw [hconj r hr]
      exact hr
    · intro hr
      have h1 : r = s⁻¹ * (s * r * s⁻¹) * s := by group
      have h2 : s⁻¹ * (s * r * s⁻¹) * s = s * r * s⁻¹ := by
        have h3 := hsR _ hr
        calc s⁻¹ * (s * r * s⁻¹) * s = s⁻¹ * ((s * r * s⁻¹) * s) := by group
          _ = s⁻¹ * (s * (s * r * s⁻¹)) := by rw [h3]
          _ = s * r * s⁻¹ := by group
      rw [h1, h2]
      exact hr
  have hsup := IsPGroup.to_sup_of_normal_right' hsp R.isPGroup' hle
  have heq := R.3 hsup le_sup_right
  rw [← heq]
  exact mem_sup_left (mem_zpowers s)

theorem d8_index_odd : ¬ 2 ∣ D8.index := by
  have h1 := D8.card_mul_index
  rw [card_D8, show Nat.card A7 = 2520 from AutL2Facts.card_alternatingGroup_seven] at h1
  omega

theorem d8_isPGroup : IsPGroup 2 D8 := IsPGroup.of_card (n := 3) (by rw [card_D8]; norm_num)

@[expose] noncomputable def d8Sylow : Sylow 2 A7 :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  d8_isPGroup.toSylow d8_index_odd

theorem coe_d8Sylow : (d8Sylow : Subgroup A7) = D8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.toSylow_coe d8_isPGroup d8_index_odd

theorem exists_conj_d8 (R : Sylow 2 A7) :
    ∃ h : A7, ∀ r : A7, r ∈ (R : Subgroup A7) ↔ h⁻¹ * r * h ∈ D8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq A7 d8Sylow R
  refine ⟨h, fun r => ?_⟩
  rw [← hh, AutL2Facts.mem_smul_sylow_iff_conj, coe_d8Sylow]

theorem commute_d8_of_gens {t : Perm (Fin 7)}
    (hs : (sD : Perm (Fin 7)) * t = t * (sD : Perm (Fin 7)))
    (ht : (tD : Perm (Fin 7)) * t = t * (tD : Perm (Fin 7))) :
    ∀ d ∈ D8, (d : Perm (Fin 7)) * t = t * (d : Perm (Fin 7)) := by
  have hle : D8 ≤ (centralizer ({t} : Set (Perm (Fin 7)))).comap
      (alternatingGroup (Fin 7)).subtype := by
    refine closure_le _ |>.mpr ?_
    rintro x (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr hs
    · exact mem_centralizer_singleton_iff.mpr ht
  intro d hd
  exact mem_centralizer_singleton_iff.mp (hle hd)

theorem swap45_commute_d8 :
    ∀ d ∈ D8, (d : Perm (Fin 7)) * swap 4 5 = swap 4 5 * (d : Perm (Fin 7)) :=
  commute_d8_of_gens (by decide) (by decide)

theorem triple_commute_d8 : ∀ d ∈ D8,
    (d : Perm (Fin 7)) * (swap 0 2 * swap 1 3 * swap 4 5) =
      (swap 0 2 * swap 1 3 * swap 4 5) * (d : Perm (Fin 7)) :=
  commute_d8_of_gens (by decide) (by decide)

theorem mul_self_of_commute_sylow (R : Sylow 2 A7)
    {σ : Perm (Fin 7)}
    (hσ : ∀ r ∈ (R : Subgroup A7), (r : Perm (Fin 7)) * σ = σ * (r : Perm (Fin 7))) :
    σ * σ = 1 := by
  obtain ⟨h, hh⟩ := exists_conj_d8 R
  set H : Perm (Fin 7) := (h : Perm (Fin 7)) with hH
  have h1 : (H⁻¹ * σ * H) * (H⁻¹ * σ * H) = 1 := by
    apply sq_eq_one_of_commute_D8
    intro d hd
    have hr : h * d * h⁻¹ ∈ (R : Subgroup A7) := by
      rw [hh, show h⁻¹ * (h * d * h⁻¹) * h = d by group]
      exact hd
    have h2 := hσ _ hr
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hH] at h2
    calc (d : Perm (Fin 7)) * (H⁻¹ * σ * H) = H⁻¹ * (H * d * H⁻¹ * σ) * H := by group
      _ = H⁻¹ * (σ * (H * d * H⁻¹)) * H := by rw [h2]
      _ = H⁻¹ * σ * H * d := by group
  calc σ * σ = H * ((H⁻¹ * σ * H) * (H⁻¹ * σ * H)) * H⁻¹ := by group
    _ = 1 := by rw [h1, mul_one, mul_inv_cancel]

theorem exists_odd_central (R : Sylow 2 A7) :
    ∃ t : Perm (Fin 7), Perm.sign t = -1 ∧ t * t = 1 ∧
      ∀ r ∈ (R : Subgroup A7), (r : Perm (Fin 7)) * t = t * (r : Perm (Fin 7)) := by
  obtain ⟨h, hh⟩ := exists_conj_d8 R
  set H : Perm (Fin 7) := (h : Perm (Fin 7)) with hH
  refine ⟨H * swap 4 5 * H⁻¹, ?_, ?_, fun r hr => ?_⟩
  · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, Perm.sign_swap (by decide)]
    simp [mul_comm]
  · calc H * swap 4 5 * H⁻¹ * (H * swap 4 5 * H⁻¹) = H * (swap 4 5 * swap 4 5) * H⁻¹ := by group
      _ = 1 := by rw [swap_mul_self, mul_one, mul_inv_cancel]
  · have h1 := swap45_commute_d8 _ ((hh r).mp hr)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hH] at h1
    calc (r : Perm (Fin 7)) * (H * swap 4 5 * H⁻¹)
        = H * (H⁻¹ * (r : Perm (Fin 7)) * H * swap 4 5) * H⁻¹ := by group
      _ = H * (swap 4 5 * (H⁻¹ * (r : Perm (Fin 7)) * H)) * H⁻¹ := by rw [h1]
      _ = H * swap 4 5 * H⁻¹ * (r : Perm (Fin 7)) := by group

theorem cycleType_of_odd_involution {π : Perm (Fin 7)} (h2 : π * π = 1)
    (hodd : Perm.sign π = -1) : π.cycleType = {2} ∨ π.cycleType = {2, 2, 2} := by
  have hpow : π ^ 2 = 1 := by rw [sq]; exact h2
  have htypes : ∀ n, n ∈ cycleType π → n = 2 := pow_prime_eq_one_iff.mp hpow
  rw [← Multiset.eq_replicate_card] at htypes
  have hsupport := π.support.card_le_univ
  rw [← sum_cycleType, htypes, Multiset.sum_replicate, smul_eq_mul] at hsupport
  norm_num at hsupport
  have hcard : Multiset.card π.cycleType ≤ 3 := by omega
  rw [sign_of_cycleType, htypes] at hodd
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate] at hodd
  interval_cases h : Multiset.card π.cycleType
  · exact absurd hodd (by decide)
  · left
    rw [htypes]
    rfl
  · exact absurd hodd (by decide)
  · right
    rw [htypes]
    rfl

theorem cycleType_swap45 : (swap (4 : Fin 7) 5).cycleType = {2} := by
  rw [(isCycle_swap (by decide)).cycleType, card_support_swap (by decide)]

theorem cycleType_triple : (swap (0 : Fin 7) 2 * swap 1 3 * swap 4 5).cycleType = {2, 2, 2} := by
  have h1 : Perm.Disjoint (swap (0 : Fin 7) 2) (swap 1 3) := by
    intro x
    fin_cases x <;> decide
  have h2 : Perm.Disjoint (swap (0 : Fin 7) 2 * swap 1 3) (swap 4 5) := by
    intro x
    fin_cases x <;> decide
  rw [Perm.Disjoint.cycleType_mul h2, Perm.Disjoint.cycleType_mul h1,
    (isCycle_swap (by decide)).cycleType, (isCycle_swap (by decide)).cycleType,
    (isCycle_swap (by decide)).cycleType, card_support_swap (by decide),
    card_support_swap (by decide), card_support_swap (by decide)]
  rfl

theorem exists_conj_central (R : Sylow 2 A7) {π : Perm (Fin 7)} (h2 : π * π = 1)
    (hodd : Perm.sign π = -1) :
    ∃ g : A7, ∀ r ∈ (R : Subgroup A7),
      (r : Perm (Fin 7)) * ((g : Perm (Fin 7)) * π * (g : Perm (Fin 7))⁻¹) =
        ((g : Perm (Fin 7)) * π * (g : Perm (Fin 7))⁻¹) * r := by
  obtain ⟨t, hπt, htD, ht45⟩ : ∃ t : Perm (Fin 7), IsConj π t ∧
      (∀ d ∈ D8, (d : Perm (Fin 7)) * t = t * (d : Perm (Fin 7))) ∧
        swap 4 5 * t = t * swap 4 5 := by
    rcases cycleType_of_odd_involution h2 hodd with h | h
    · exact ⟨swap 4 5, isConj_iff_cycleType_eq.mpr (h.trans cycleType_swap45.symm),
        swap45_commute_d8, rfl⟩
    · exact ⟨swap 0 2 * swap 1 3 * swap 4 5,
        isConj_iff_cycleType_eq.mpr (h.trans cycleType_triple.symm), triple_commute_d8,
        by decide⟩
  obtain ⟨σ, hσ⟩ := isConj_iff.mp hπt
  obtain ⟨g₀, hg₀, hg₀π⟩ : ∃ g₀ : Perm (Fin 7), Perm.sign g₀ = 1 ∧ g₀ * π * g₀⁻¹ = t := by
    rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
    · exact ⟨σ, hs, hσ⟩
    · refine ⟨swap 4 5 * σ, ?_, ?_⟩
      · rw [Perm.sign_mul, hs, Perm.sign_swap (by decide)]
        rfl
      · have h1 : swap 4 5 * σ * π * (swap 4 5 * σ)⁻¹ =
            swap 4 5 * (σ * π * σ⁻¹) * (swap (4 : Fin 7) 5)⁻¹ := by group
        rw [h1, hσ, swap_inv, ht45, mul_assoc, swap_mul_self, mul_one]
  obtain ⟨h, hh⟩ := exists_conj_d8 R
  set H : Perm (Fin 7) := (h : Perm (Fin 7)) with hH
  refine ⟨h * ⟨g₀, hg₀⟩, fun r hr => ?_⟩
  have h1 := htD _ ((hh r).mp hr)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hH] at h1 ⊢
  calc (r : Perm (Fin 7)) * (H * g₀ * π * (H * g₀)⁻¹)
      = H * ((H⁻¹ * r * H) * (g₀ * π * g₀⁻¹)) * H⁻¹ := by group
    _ = H * ((g₀ * π * g₀⁻¹) * (H⁻¹ * r * H)) * H⁻¹ := by rw [hg₀π, h1]
    _ = H * g₀ * π * (H * g₀)⁻¹ * r := by group

end CFSG.ComponentClassification.FooteLit.Aut5A7
