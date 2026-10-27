module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open SymplecticHigher (flagStabilizer)

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

noncomputable def spFlagLeviBlockZeroEquiv (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)}
    (hj0 : (j : ℕ) = 0) :
    spFlagLeviBlock (K := K) hI t j ≃* commutator (StatedSp (r - t) K) :=
  (MulEquiv.subgroupCongr (spFlagLeviBlock_of_eq_zero hI hj0)).trans
    ((commutator _).equivMapOfInjective _ (spFlagResEmb_injective t)).symm

noncomputable def spFlagLeviBlockMemEquiv (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)}
    (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I) :
    spFlagLeviBlock (K := K) hI t j ≃* SpecialLinearGroup (Fin (j - spFlagPrev I j)) K :=
  (MulEquiv.subgroupCongr (spFlagLeviBlock_of_mem hI hj0 hj)).trans
    (MonoidHom.ofInjective (f := (spFlagCutEmb (spFlagPrev I j) j (hI j hj)).comp
      Matrix.SpecialLinearGroup.toGL) fun _ _ h =>
        Matrix.SpecialLinearGroup.toGL_injective (spFlagCutEmb_injective _ _ _ h)).symm

theorem spFlag_not_isSolvable {G : Type} [Group G] (hG : CFSG.Open.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hs
  obtain ⟨a, b, hab⟩ := exists_noncomm_centerQuotient hG
  have : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim x y])
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)).ne hG.1

theorem spFlag_card_center_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (map_center_mulEquiv e)).toEquiv

theorem spFlag_res_cases (m : ℕ) (K : Type) [Field K] :
    (m = 0 ∨ (m = 1 ∧ Nat.card K = 2)) ∨ (m = 2 ∧ Nat.card K = 2) ∨
      (1 ≤ m ∧ (4 ≤ Nat.card K ∨ 3 ≤ m)) ∨ Nat.card K ≠ 2 ∧ Nat.card K < 4 := by
  omega

theorem spFlagLeviBlock_cases [Finite K] [CharP K 2] (hI : ∀ i ∈ I, i ≤ r) (t : ℕ)
    (j : Fin (r + 1)) :
    CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j) ∨
      Group.IsSolvable (spFlagLeviBlock (K := K) hI t j) := by
  have hK := spFlag_card_eq_two_or_four_le (K := K)
  by_cases hj0 : (j : ℕ) = 0
  · let e := spFlagLeviBlockZeroEquiv (K := K) hI t hj0
    rcases spFlag_res_cases (r - t) K with hs | h2 | hq | hbad
    · right
      have := spFlag_isSolvable_Sp (K := K) hs
      have : Group.IsSolvable (commutator (StatedSp (r - t) K)) :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · left
      obtain ⟨hm, hK2⟩ := h2
      have h := (spFlag_spFour_comm (K := K) hK2).1
      rw [← hm] at h
      exact isQuasisimple_of_mulEquiv e.symm h
    · left
      have hq' := spFlag_isQuasisimple_Sp (K := K) hq.1 hq.2
      exact isQuasisimple_of_mulEquiv (e.trans ((MulEquiv.subgroupCongr hq'.1).trans
        Subgroup.topEquiv)).symm hq'
    · omega
  by_cases hj : (j : ℕ) ∈ I
  · let e := spFlagLeviBlockMemEquiv (K := K) hI t hj0 hj
    by_cases hs : j - spFlagPrev I j ≤ 1 ∨ (j - spFlagPrev I j = 2 ∧ Nat.card K = 2)
    · right
      have := spFlag_isSolvable_SL (K := K) hs
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · left
      exact isQuasisimple_of_mulEquiv e.symm (spFlag_isQuasisimple_SL (by omega) (by omega))
  · right
    rw [spFlagLeviBlock_of_not_mem hI hj0 hj]
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _

theorem card_spFlagLeviBlock_zero [Finite K] [CharP K 2] (hI : ∀ i ∈ I, i ≤ r) (t : ℕ)
    {j : Fin (r + 1)} (hj0 : (j : ℕ) = 0)
    (hq : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j)) :
    Nat.card (spFlagLeviBlock (K := K) hI t j ⧸ Subgroup.center (spFlagLeviBlock hI t j)) =
        ordBC (r - t) (Nat.card K) ∨
      (r - t = 2 ∧ Nat.card K = 2 ∧
        Nat.card (spFlagLeviBlock (K := K) hI t j ⧸ Subgroup.center (spFlagLeviBlock hI t j)) =
          360) := by
  have hK := spFlag_card_eq_two_or_four_le (K := K)
  let e := spFlagLeviBlockZeroEquiv (K := K) hI t hj0
  rw [spFlag_card_center_congr e]
  rcases spFlag_res_cases (r - t) K with hs | h2 | hq' | hbad
  · exfalso
    have := spFlag_isSolvable_Sp (K := K) hs
    have : Group.IsSolvable (commutator (StatedSp (r - t) K)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    exact spFlag_not_isSolvable (isQuasisimple_of_mulEquiv e hq) this
  · right
    obtain ⟨hm, hK2⟩ := h2
    refine ⟨hm, hK2, ?_⟩
    have h := (spFlag_spFour_comm (K := K) hK2).2
    revert h
    rw [← hm]
    exact id
  · left
    have hq'' := spFlag_isQuasisimple_Sp (K := K) hq'.1 hq'.2
    rw [spFlag_card_center_congr ((MulEquiv.subgroupCongr hq''.1).trans Subgroup.topEquiv),
      spFlag_card_Sp_center]
  · omega

theorem card_spFlagLeviBlock_mem [Finite K] (hI : ∀ i ∈ I, i ≤ r) (t : ℕ)
    {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I) :
    Nat.card (spFlagLeviBlock (K := K) hI t j ⧸ Subgroup.center (spFlagLeviBlock hI t j)) =
      ordA (j - spFlagPrev I j - 1) (Nat.card K) := by
  let e := spFlagLeviBlockMemEquiv (K := K) hI t hj0 hj
  have hprev := spFlagPrev_le I j
  rw [spFlag_card_center_congr e, spFlag_card_SL_center (by omega)]

theorem spFlagLeviBlock_sixty [Finite K] [CharP K 2] (hI : ∀ i ∈ I, i ≤ r) (t : ℕ)
    {j : Fin (r + 1)} (hq : CFSG.Open.IsQuasisimple (spFlagLeviBlock (K := K) hI t j))
    (h60 : Nat.card (spFlagLeviBlock (K := K) hI t j ⧸
      Subgroup.center (spFlagLeviBlock hI t j)) = 60) :
    Nat.card K = 4 ∧ Nat.card (spFlagLeviBlock (K := K) hI t j) = 60 ∧
      (((j : ℕ) = 0 ∧ r - t = 1) ∨ ((j : ℕ) ≠ 0 ∧ (j : ℕ) ∈ I ∧ j - spFlagPrev I j = 2)) := by
  obtain ⟨f, hf, hqf⟩ := spFlag_card_eq_two_pow (K := K)
  by_cases hj0 : (j : ℕ) = 0
  · rcases card_spFlagLeviBlock_zero hI t hj0 hq with h | ⟨-, -, h⟩
    · rw [h60] at h
      obtain ⟨hm, hK4⟩ := (ordBC_eq_sixty_iff hqf).mp h.symm
      refine ⟨hK4, ?_, Or.inl ⟨hj0, hm⟩⟩
      let e := spFlagLeviBlockZeroEquiv (K := K) hI t hj0
      have hq'' := spFlag_isQuasisimple_Sp (K := K) (m := r - t) (by omega) (Or.inl hK4.ge)
      rw [Nat.card_congr (e.trans ((MulEquiv.subgroupCongr hq''.1).trans
        Subgroup.topEquiv)).toEquiv, SymplecticFlag.card_statedSp, hm, hK4]
      decide
    · omega
  by_cases hj : (j : ℕ) ∈ I
  · rw [card_spFlagLeviBlock_mem hI t hj0 hj] at h60
    obtain ⟨hn, hK4⟩ := (ordA_eq_sixty_iff hqf).mp h60
    have hprev := spFlagPrev_le I j
    have hℓ : j - spFlagPrev I j = 2 := by omega
    refine ⟨hK4, ?_, Or.inr ⟨hj0, hj, hℓ⟩⟩
    let e := spFlagLeviBlockMemEquiv (K := K) hI t hj0 hj
    rw [Nat.card_congr e.toEquiv, LinearFlag.card_SL_eq (by omega), hℓ, hK4]
    decide
  · exfalso
    rw [spFlagLeviBlock_of_not_mem hI hj0 hj] at hq
    exact spFlag_not_isSolvable hq (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)

@[expose] def spBlockOrders (q : ℕ) : Set ℕ :=
  {n | (∃ k, n = ordA k q) ∨ (∃ m, n = ordBC m q) ∨ n = 360}

theorem u38_not_mem_spBlockOrders {q f : ℕ} (hq : q = 2 ^ f) : 5515776 ∉ spBlockOrders q := by
  rintro (⟨k, hk⟩ | ⟨m, hm⟩ | h)
  · exact ordA_ne_u38 hq hk.symm
  · exact ordBC_ne_u38 hq hm.symm
  · norm_num at h

theorem u42_not_mem_spBlockOrders {q f : ℕ} (hq : q = 2 ^ f) : 25920 ∉ spBlockOrders q := by
  rintro (⟨k, hk⟩ | ⟨m, hm⟩ | h)
  · exact ordA_ne_u42 hq hk.symm
  · exact ordBC_ne_u42 hq hm.symm
  · norm_num at h

theorem hasLeviBlocks_spFlag [Finite K] [CharP K 2] (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ}
    (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t) :
    HasLeviBlocks (flagStabilizer r K I) (spBlockOrders (Nat.card K)) := by
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  refine ⟨r + 1, fun _ => StatedSp r K, fun _ => inferInstance, fun _ => inferInstance,
    spFlagLeviBlock hI' t, spFlagLeviHom hI' htI,
    isPGroup_ker_spFlagLeviHom hI' htI fun i hi => (hI i hi).1,
    pi_le_range_spFlagLeviHom hI' htI hmax, commutator_range_spFlagLeviHom_le hI' htI,
    spFlagLeviBlock_cases hI' t, fun j hq => ?_⟩
  by_cases hj0 : (j : ℕ) = 0
  · rcases card_spFlagLeviBlock_zero hI' t hj0 hq with h | ⟨-, -, h⟩
    · exact Or.inr (Or.inl ⟨_, h⟩)
    · exact Or.inr (Or.inr h)
  by_cases hj : (j : ℕ) ∈ I
  · exact Or.inl ⟨_, card_spFlagLeviBlock_mem hI' t hj0 hj⟩
  · exfalso
    rw [spFlagLeviBlock_of_not_mem hI' hj0 hj] at hq
    exact spFlag_not_isSolvable hq (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)

end CFSG.AGLEmbedding.LeviBlock
