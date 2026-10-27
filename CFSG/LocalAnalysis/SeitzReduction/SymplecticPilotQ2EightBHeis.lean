module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignTwist

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.CurtisTits (rankOne)

section Matrix

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

theorem heisenbergMatrix_mul_heisenbergMatrix (hσ : ∀ c, σ (σ c) = c) {i p k : Fin n}
    (hi : i ≠ Fin.rev i) (hp : p ≠ Fin.rev p) (hip : i ≠ Fin.rev p) (hk : Fin.rev k = k)
    (a b a' b' : F) :
    heisenbergMatrix σ i k a b * heisenbergMatrix σ p k a' b' =
      rootMatrix σ i (Fin.rev p) (-(a * σ a')) *
        (heisenbergMatrix σ p k a' b' * heisenbergMatrix σ i k a b) := by
  have hkp : k ≠ p := fun h => hp (by rw [← h, hk])
  have hki : k ≠ i := fun h => hi (by rw [← h, hk])
  have hi'p : Fin.rev i ≠ p := fun h => hip (by rw [← h, Fin.rev_rev])
  have hi'k : Fin.rev i ≠ k := fun h => hi (by
    rw [h]
    have h' := congrArg Fin.rev h
    rwa [Fin.rev_rev, hk] at h')
  have hp'i : Fin.rev p ≠ i := fun h => hip h.symm
  have hp'k : Fin.rev p ≠ k := fun h => hp (by
    rw [h]
    have h' := congrArg Fin.rev h
    rwa [Fin.rev_rev, hk] at h')
  have hp'p : Fin.rev p ≠ p := fun h => hp h.symm
  have hi'i : Fin.rev i ≠ i := fun h => hi h.symm
  have hc : σ (-(a * σ a')) = -(a' * σ a) := by rw [map_neg, map_mul, hσ, mul_comm]
  rw [rootMatrix, hc, Fin.rev_rev, heisenbergMatrix, heisenbergMatrix]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hkp,
    single_mul_single_of_ne _ _ _ _ hki, single_mul_single_of_ne _ _ _ _ hi'p,
    single_mul_single_of_ne _ _ _ _ hi'k, single_mul_single_of_ne _ _ _ _ hp'i,
    single_mul_single_of_ne _ _ _ _ hp'k, single_mul_single_of_ne _ _ _ _ hp'p,
    single_mul_single_of_ne _ _ _ _ hi'i, ← single_neg, Matrix.neg_mul, add_zero, sub_zero,
    neg_zero]
  abel

end Matrix

section Group

variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem exists_mem_heisenbergSubgroup {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) {a b : F} (hab : b + σ b + σ a * a = 0) :
    ∃ g ∈ heisenbergSubgroup σ hσ hi hik hk,
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = heisenbergMatrix σ i k a b := by
  have h1 : heisenbergMatrix σ i k a b * heisenbergMatrix σ i k (-a) (-b - a * σ a) = 1 := by
    rw [heisenbergMatrix_mul σ hi hik hk, add_neg_cancel,
      show b + (-b - a * σ a) - a * σ (-a) = 0 by rw [map_neg]; ring, heisenbergMatrix_zero]
  have h2 : heisenbergMatrix σ i k (-a) (-b - a * σ a) * heisenbergMatrix σ i k a b = 1 := by
    rw [heisenbergMatrix_mul σ hi hik hk, neg_add_cancel,
      show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]
  exact ⟨⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a), h1, h2⟩,
    det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩,
    ⟨a, b, hab, rfl⟩, rfl⟩

theorem rootHom_mem_sup_heisenbergSubgroup (htr : ∀ x, σ x = x → ∃ c, c + σ c = x)
    {i j p k : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j)
    (hpj : Fin.rev p = j) (hk : Fin.rev k = k) (hik : i ≠ k)
    (hp : p ≠ Fin.rev p) (hpk : p ≠ k) (c : Multiplicative F) :
    rootHom σ hσ hij hi hj c ∈
      heisenbergSubgroup σ hσ hi hik hk ⊔ heisenbergSubgroup σ hσ hp hpk hk := by
  subst hpj
  set a : F := -c.toAdd with ha
  obtain ⟨b, hb⟩ := htr (-(σ a * a)) (by rw [map_neg, map_mul, hσ, mul_comm])
  obtain ⟨b', hb'⟩ := htr (-1) (by rw [map_neg, map_one])
  obtain ⟨g₁, hg₁, hm₁⟩ := exists_mem_heisenbergSubgroup σ hσ hi hik hk
    (a := a) (b := b) (by rw [hb]; ring)
  obtain ⟨g₂, hg₂, hm₂⟩ := exists_mem_heisenbergSubgroup σ hσ hp hpk hk
    (a := 1) (b := b') (by rw [hb', map_one]; ring)
  have hkey : g₁ * g₂ = rootHom σ hσ hij hi hj c * (g₂ * g₁) := by
    apply Subtype.ext
    apply Units.ext
    change ((g₁ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((g₂ : GL (Fin n) F) : Matrix _ _ F)
      = ((rootHom σ hσ hij hi hj c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (((g₂ : GL (Fin n) F) : Matrix _ _ F) * ((g₁ : GL (Fin n) F) : Matrix _ _ F))
    rw [hm₁, hm₂, coe_rootHom, heisenbergMatrix_mul_heisenbergMatrix σ hσ hi hp hij hk,
      map_one, mul_one, ha, neg_neg]
  have hx : rootHom σ hσ hij hi hj c = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
    rw [hkey]
    group
  rw [hx]
  exact mul_mem (mul_mem (mul_mem (mem_sup_left hg₁) (mem_sup_right hg₂))
    (inv_mem (mem_sup_left hg₁))) (inv_mem (mem_sup_right hg₂))

end Group

section RankOne

variable {F : Type*} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {n : ℕ}

theorem rankOne_short_le_of_heisenberg (htr : ∀ x, σ x = x → ∃ c, c + σ c = x)
    {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) {m : Fin n} (hm : Fin.rev m = m)
    {H : Subgroup (SU σ n)}
    (hH : ∀ (i : Fin n) (hi : i ≠ Fin.rev i) (him : i ≠ m),
      (i = lowIdx k ∨ i = lowIdx ⟨k.val + 1, hk⟩ ∨ i = Fin.rev (lowIdx k) ∨
        i = Fin.rev (lowIdx ⟨k.val + 1, hk⟩)) → heisenbergSubgroup σ hσ hi him hm ≤ H) :
    rankOne (rootGroup σ hσ n) k ≤ H := by
  obtain ⟨h1, h2, h3, h4⟩ := short_facts (n := n) hk
  have h5 : lowIdx (n := n) k ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := lowIdx_ne_rev _ _
  have hne : ∀ {i : Fin n}, i ≠ Fin.rev i → i ≠ m := fun {i} hi h => hi (by rw [h, hm])
  have hroot : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
      ((i = lowIdx k ∧ j = lowIdx ⟨k.val + 1, hk⟩) ∨
        (i = Fin.rev (lowIdx ⟨k.val + 1, hk⟩) ∧ j = Fin.rev (lowIdx k)) ∨
        (i = lowIdx ⟨k.val + 1, hk⟩ ∧ j = lowIdx k) ∨
        (i = Fin.rev (lowIdx k) ∧ j = Fin.rev (lowIdx ⟨k.val + 1, hk⟩))) →
      (rootHom σ hσ hij hi hj).range ≤ H := by
    intro i j hij hi hj hcase
    have hj' : Fin.rev j ≠ Fin.rev (Fin.rev j) := by
      rw [Fin.rev_rev]
      exact fun h => hj h.symm
    rintro _ ⟨c, rfl⟩
    have hmem := rootHom_mem_sup_heisenbergSubgroup σ hσ htr hij hi hj (p := Fin.rev j)
      (Fin.rev_rev j) hm (hne hi) hj' (hne hj') c
    refine (sup_le (hH i hi (hne hi) ?_) (hH (Fin.rev j) hj' (hne hj') ?_)) hmem
    · rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    · rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hX : ∀ γ : Fin (n / 2) → ℤ,
      (toStd n γ = weight n (lowIdx k) - weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) ∨
        toStd n γ = weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) - weight n (lowIdx k)) →
      rootGroup σ hσ n γ ≤ H := by
    intro γ hγ
    unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun _ => iSup_le fun hw => ?_
      apply hroot i j hij hi hj
      rcases hγ with hγ | hγ <;> rw [hγ] at hw
      · rcases eq_of_weight_sub_eq_sub h1 h2 h3 h4 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases eq_of_weight_sub_eq_sub h1.symm h3 h2 h5 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · refine iSup_le fun i => iSup_le fun _ => iSup_le fun hw => ?_
      exfalso
      have hkk := congrFun hw k
      have hlt : 2 * (k.val + 1) < n := by omega
      rcases hγ with hγ | hγ <;> rw [hγ] at hkk <;>
        simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.sub_apply, weight_apply',
          val_lowIdx] at hkk <;>
        split_ifs at hkk <;> omega
    · refine iSup_le fun i => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun _ => iSup_le fun hw => ?_
      exfalso
      rcases hγ with hγ | hγ <;> rw [hγ] at hw
      · exact weight_ne_weight_sub h1 h2 h3 h4 hw
      · exact weight_ne_weight_sub h1.symm h3 h2 h5 hw
  exact sup_le (hX _ (Or.inl (toStd_short hk))) (hX _ (Or.inr (toStd_short_neg hk)))

end RankOne

section Blocks

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {N : ℕ}

theorem heisenbergSubgroup_le_ctuBlock {R : Finset (Fin N)} {i k : Fin (2 * N + 1)}
    (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) (hiR : i ∉ ctuPlanes 1 R)
    (hkR : k ∉ ctuPlanes 1 R) : heisenbergSubgroup σ hσ hi hik hk ≤ ctuBlock σ 1 R := by
  rintro g ⟨a, b, -, hg⟩
  rw [mem_ctuBlock]
  intro c d hcd
  have hirR : Fin.rev i ∉ ctuPlanes 1 R := by rwa [rev_mem_ctuPlanes_iff le_rfl]
  rw [hg, heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply,
    ctua_apply_of_plane hcd hiR hkR, ctua_apply_of_plane hcd hkR hirR,
    ctua_apply_of_plane hcd hiR hirR, add_zero, sub_zero, add_zero]

end Blocks

end CFSG.SeitzReduction.SymplecticPilot
