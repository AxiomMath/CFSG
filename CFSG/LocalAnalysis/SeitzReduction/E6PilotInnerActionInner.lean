module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def e6CentList : Fin 3 → List (Fin Tag.E6.rank → ℤ) :=
  ![[![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 0],
      ![0, 0, 1, 1, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1],
      ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0], ![1, 0, 1, 1, 0, 0],
      ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 0],
      ![1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0],
      ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1],
      ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]],
    [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1],
      ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1],
      ![0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 1],
      ![0, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 1],
      ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 1],
      ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1],
      ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]],
    [![0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 1, 0, 0],
      ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1],
      ![1, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0],
      ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1],
      ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]]

@[expose] def zDiagA : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 1, 1, 1]

@[expose] def zDiagB : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 1, 1, 0]

@[expose] def zDiagD : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 1, 0, 0]

@[expose] def zFrameG : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 2, 2, 1]

@[expose] def zFrameD : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 1, 1]

@[expose] def zFrameE : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 2, 1, 0]

@[expose] def e6R : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def zFullList : List (Fin Tag.E6.rank → ℤ) := zDiagA :: zDiagB :: zDiagD :: e6CentList 2

theorem e6CentList_check (κ : Fin 3) :
    (e6CentList κ).Nodup ∧ (∀ γ ∈ e6CentList κ, oddDerivIsRootB .E6 γ = true ∧ 0 < height γ) ∧
      ∀ γ ∈ e6CentList κ, ∀ σ ∈ e6ASFrame κ,
        γ = σ ∨ (γ ≠ -σ ∧ oddDerivNotRootB .E6 (γ + σ) = true) := by
  revert κ
  decide +kernel

theorem zFullList_check : zFullList.Nodup ∧
    ∀ γ ∈ zFullList, oddDerivIsRootB .E6 γ = true ∧ 0 < height γ := by
  decide +kernel

theorem zDiag_check :
    oddDerivE6ZFrame = [zFrameG, zFrameD, zFrameE] ∧
    (∀ v ∈ [zDiagA, zDiagB, zDiagD, zFrameG, zFrameD, zFrameE, e6R],
      oddDerivIsRootB .E6 v = true) ∧
    zFrameE + zDiagA = e6R ∧ zFrameD + zDiagB = e6R ∧ zFrameG + zDiagD = e6R ∧
    zFrameE ≠ zDiagA ∧ zFrameE ≠ -zDiagA ∧ zFrameD ≠ zDiagB ∧ zFrameD ≠ -zDiagB ∧
    zFrameG ≠ zDiagD ∧ zFrameG ≠ -zDiagD := by
  decide +kernel

theorem conj_eq_of_commute {M : Type*} [Group M] {x y : M} (h : Commute x y) :
    MulAut.conj x y = y := by
  rw [MulAut.conj_apply, h.eq, mul_inv_cancel_right]



section General

variable {τ : Tag} {K : Type} [Field K]

theorem pow_dvd_card_centralizer_of_injective [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (w : adjointGroup τ K) {X : Type*} [Finite X] {a : ℕ}
    (hX : Nat.card X = p ^ a) (ψ : X → ModGL τ K) (hψ : Function.Injective ψ)
    (hψU : ∀ x, ψ x ∈ posUnipotent τ K) (hψw : ∀ x, Commute (ψ x) (w : ModGL τ K)) :
    p ^ a ∣ Nat.card (centralizer ({w} : Set (adjointGroup τ K))) := by
  classical
  set H : Subgroup (ModGL τ K) :=
    centralizer ({(w : ModGL τ K)} : Set (ModGL τ K)) ⊓ posUnipotent τ K with hHdef
  have hU : Nat.card (posUnipotent τ K) =
      p ^ (f * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) := by
    rw [card_posUnipotent, hK, ← pow_mul]
  have hHU : Nat.card H ∣ Nat.card (posUnipotent τ K) := card_dvd_of_le inf_le_right
  rw [hU] at hHU
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hHU
  have hUfin : Finite (posUnipotent τ K) :=
    Nat.finite_of_card_ne_zero (by rw [hU]; exact pow_ne_zero _ hp.ne_zero)
  have hHfin : Finite H :=
    Finite.of_injective (Subgroup.inclusion (inf_le_right : H ≤ posUnipotent τ K))
      (Subgroup.inclusion_injective _)
  have hmem : ∀ x, ψ x ∈ H := fun x =>
    mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (hψw x).eq, hψU x⟩
  have hXH : Nat.card X ≤ Nat.card H :=
    Nat.card_le_card_of_injective (fun x => (⟨ψ x, hmem x⟩ : H))
      fun x y h => hψ (congrArg Subtype.val h)
  rw [hX, hk] at hXH
  have hak : a ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 hXH
  have h1 : p ^ a ∣ Nat.card H := hk ▸ pow_dvd_pow p hak
  have h2 : Nat.card H ∣ Nat.card (centralizer ({w} : Set (adjointGroup τ K))) := by
    rw [← card_map_of_injective (adjointGroup τ K).subtype_injective]
    refine card_dvd_of_le fun y hy => ?_
    obtain ⟨hyc, hyU⟩ := mem_inf.1 hy
    refine ⟨⟨y, posUnipotent_le_adjointGroup hyU⟩, ?_, rfl⟩
    exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 hyc))
  exact h1.trans h2

theorem commute_pinnedX_of_eq_or_not_isRoot (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ σ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hσ : IsRoot τ σ)
    (h : γ = σ ∨ (γ ≠ -σ ∧ ¬ IsRoot τ (γ + σ))) (c d : K) :
    Commute (pinnedX τ K γ c) (pinnedX τ K σ d) := by
  rcases h with rfl | ⟨hne', hnot⟩
  · change pinnedX τ K γ c * pinnedX τ K γ d = pinnedX τ K γ d * pinnedX τ K γ c
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · by_cases hne : γ = σ
    · subst hne
      change pinnedX τ K γ c * pinnedX τ K γ d = pinnedX τ K γ d * pinnedX τ K γ c
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · exact (simply_laced_root_commutator_unit τ hτ hγ hσ hne hne').2 hnot K _
        (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

end General

theorem commute_pinnedX_of_checkB {K : Type} [Field K] {ρ σ : Fin Tag.E6.rank → ℤ}
    (h : oddDerivIsRootB .E6 ρ = true ∧ oddDerivIsRootB .E6 σ = true ∧ ρ ≠ -σ ∧
      oddDerivNotRootB .E6 (ρ + σ) = true) (c d : K) :
    Commute (pinnedX .E6 K ρ c) (pinnedX .E6 K σ d) :=
  commute_pinnedX_of_eq_or_not_isRoot (Or.inr (Or.inl rfl)) (isRoot_of_oddDerivIsRootB h.1)
    (isRoot_of_oddDerivIsRootB h.2.1) (Or.inr ⟨h.2.2.1, not_isRoot_of_oddDerivNotRootB h.2.2.2⟩)
    c d

section Commutation

variable {K : Type} [Field K]

theorem commute_pinnedX_e6ASFrame (κ : Fin 3) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ e6CentList κ) (c : K) :
    Commute (pinnedX .E6 K γ c) (((e6ASFrame κ).map fun σ => pinnedX .E6 K σ 1).prod) := by
  obtain ⟨-, hroot, hcomm⟩ := e6CentList_check κ
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
  have hσr : IsRoot .E6 σ := e6ASFrame_isRoot κ σ hσ
  refine commute_pinnedX_of_eq_or_not_isRoot (Or.inr (Or.inl rfl))
    (isRoot_of_oddDerivIsRootB (hroot γ hγ).1) hσr ?_ c 1
  rcases hcomm γ hγ σ hσ with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, not_isRoot_of_oddDerivNotRootB h2⟩

theorem conj_pinnedX_eq_mul_of_charTwo [CharP K 2] {σ ρ μ : Fin Tag.E6.rank → ℤ}
    (hσ : IsRoot .E6 σ) (hρ : IsRoot .E6 ρ) (hne : σ ≠ ρ) (hne' : σ ≠ -ρ) (hμ : σ + ρ = μ)
    (hμr : IsRoot .E6 μ) (c : K) (hρμ : Commute (pinnedX .E6 K ρ c) (pinnedX .E6 K μ c)) :
    pinnedX .E6 K σ 1 * pinnedX .E6 K ρ c * (pinnedX .E6 K σ 1)⁻¹ =
      pinnedX .E6 K ρ c * pinnedX .E6 K μ c := by
  obtain ⟨hN, hcomm⟩ := (simply_laced_root_commutator_unit .E6 (Or.inr (Or.inl rfl)) hσ hρ hne
    hne').1 (hμ ▸ hμr)
  have h := hcomm K 1 c
  have hN' : ((commConst .E6 σ ρ (1, 1) : ℤ) : K) = 1 := by
    rcases hN with h1 | h1
    · rw [h1, Int.cast_one]
    · rw [h1, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  rw [hN', one_mul, one_mul, hμ, commutatorElement_def] at h
  calc pinnedX .E6 K σ 1 * pinnedX .E6 K ρ c * (pinnedX .E6 K σ 1)⁻¹ =
        (pinnedX .E6 K σ 1 * pinnedX .E6 K ρ c * (pinnedX .E6 K σ 1)⁻¹ *
          (pinnedX .E6 K ρ c)⁻¹) * pinnedX .E6 K ρ c := by group
    _ = pinnedX .E6 K μ c * pinnedX .E6 K ρ c := by rw [h]
    _ = pinnedX .E6 K ρ c * pinnedX .E6 K μ c := hρμ.eq.symm

theorem commute_zDiag_zRep [CharP K 2] (s u : K) :
    Commute (pinnedX .E6 K zDiagA s * (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K zDiagD u))
      ((oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod) := by
  obtain ⟨hF, hroots, hεa, hδb, hγd, hεa1, hεa2, hδb1, hδb2, hγd1, hγd2⟩ := zDiag_check
  have hr : ∀ v ∈ [zDiagA, zDiagB, zDiagD, zFrameG, zFrameD, zFrameE, e6R], IsRoot .E6 v :=
    fun v hv => isRoot_of_oddDerivIsRootB (hroots v hv)
  have hA := hr zDiagA (by simp)
  have hB := hr zDiagB (by simp)
  have hD := hr zDiagD (by simp)
  have hγ := hr zFrameG (by simp)
  have hδ := hr zFrameD (by simp)
  have hε := hr zFrameE (by simp)
  have hrr := hr e6R (by simp)
  have cεB := commute_pinnedX_of_checkB (K := K) (ρ := zFrameE) (σ := zDiagB) (by decide +kernel)
  have cεD := commute_pinnedX_of_checkB (K := K) (ρ := zFrameE) (σ := zDiagD) (by decide +kernel)
  have cδA := commute_pinnedX_of_checkB (K := K) (ρ := zFrameD) (σ := zDiagA) (by decide +kernel)
  have cδD := commute_pinnedX_of_checkB (K := K) (ρ := zFrameD) (σ := zDiagD) (by decide +kernel)
  have cδr := commute_pinnedX_of_checkB (K := K) (ρ := zFrameD) (σ := e6R) (by decide +kernel)
  have cγA := commute_pinnedX_of_checkB (K := K) (ρ := zFrameG) (σ := zDiagA) (by decide +kernel)
  have cγB := commute_pinnedX_of_checkB (K := K) (ρ := zFrameG) (σ := zDiagB) (by decide +kernel)
  have cγr := commute_pinnedX_of_checkB (K := K) (ρ := zFrameG) (σ := e6R) (by decide +kernel)
  have cAr := commute_pinnedX_of_checkB (K := K) (ρ := zDiagA) (σ := e6R) (by decide +kernel)
  have cBr := commute_pinnedX_of_checkB (K := K) (ρ := zDiagB) (σ := e6R) (by decide +kernel)
  have cDr := commute_pinnedX_of_checkB (K := K) (ρ := zDiagD) (σ := e6R) (by decide +kernel)
  have sεA : MulAut.conj (pinnedX .E6 K zFrameE 1) (pinnedX .E6 K zDiagA s) =
      pinnedX .E6 K zDiagA s * pinnedX .E6 K e6R s :=
    conj_pinnedX_eq_mul_of_charTwo hε hA hεa1 hεa2 hεa hrr s (cAr s s)
  have sδB : MulAut.conj (pinnedX .E6 K zFrameD 1) (pinnedX .E6 K zDiagB (s + u)) =
      pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K e6R (s + u) :=
    conj_pinnedX_eq_mul_of_charTwo hδ hB hδb1 hδb2 hδb hrr (s + u) (cBr (s + u) (s + u))
  have sγD : MulAut.conj (pinnedX .E6 K zFrameG 1) (pinnedX .E6 K zDiagD u) =
      pinnedX .E6 K zDiagD u * pinnedX .E6 K e6R u :=
    conj_pinnedX_eq_mul_of_charTwo hγ hD hγd1 hγd2 hγd hrr u (cDr u u)
  have hz : (oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod =
      pinnedX .E6 K zFrameG 1 * (pinnedX .E6 K zFrameD 1 * pinnedX .E6 K zFrameE 1) := by
    rw [hF]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have h2 : s + (s + u + u) = 0 := by
    have h20 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (s + u) * h20
  have st1 : MulAut.conj (pinnedX .E6 K zFrameE 1)
      (pinnedX .E6 K zDiagA s * (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K zDiagD u)) =
      pinnedX .E6 K zDiagA s * pinnedX .E6 K e6R s *
        (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K zDiagD u) := by
    simp only [map_mul]
    rw [sεA, conj_eq_of_commute (cεB 1 (s + u)),
      conj_eq_of_commute (cεD 1 u)]
  have st2 : MulAut.conj (pinnedX .E6 K zFrameD 1)
      (pinnedX .E6 K zDiagA s * pinnedX .E6 K e6R s *
        (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K zDiagD u)) =
      pinnedX .E6 K zDiagA s * pinnedX .E6 K e6R s *
        (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K e6R (s + u) * pinnedX .E6 K zDiagD u) := by
    simp only [map_mul]
    rw [conj_eq_of_commute (cδA 1 s),
      conj_eq_of_commute (cδr 1 s), sδB, conj_eq_of_commute (cδD 1 u)]
  have st3 : MulAut.conj (pinnedX .E6 K zFrameG 1)
      (pinnedX .E6 K zDiagA s * pinnedX .E6 K e6R s *
        (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K e6R (s + u) * pinnedX .E6 K zDiagD u)) =
      pinnedX .E6 K zDiagA s * pinnedX .E6 K e6R s *
        (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K e6R (s + u) *
          (pinnedX .E6 K zDiagD u * pinnedX .E6 K e6R u)) := by
    simp only [map_mul]
    rw [conj_eq_of_commute (cγA 1 s),
      conj_eq_of_commute (cγr 1 s), conj_eq_of_commute (cγB 1 (s + u)),
      conj_eq_of_commute (cγr 1 (s + u)), sγD]
  rw [hz]
  refine (Commute.symm ?_)
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  change MulAut.conj (pinnedX .E6 K zFrameG 1 * (pinnedX .E6 K zFrameD 1 * pinnedX .E6 K zFrameE 1))
    (pinnedX .E6 K zDiagA s * (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K zDiagD u)) = _
  rw [(MulAut.conj : ModGL .E6 K →* MulAut (ModGL .E6 K)).map_mul,
    (MulAut.conj : ModGL .E6 K →* MulAut (ModGL .E6 K)).map_mul, MulAut.mul_apply,
    MulAut.mul_apply, st1, st2, st3]
  have e1 : pinnedX .E6 K e6R s * (pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K e6R (s + u) *
      (pinnedX .E6 K zDiagD u * pinnedX .E6 K e6R u)) =
      pinnedX .E6 K zDiagB (s + u) * pinnedX .E6 K zDiagD u := by
    rw [mul_assoc (pinnedX .E6 K zDiagB (s + u)), (cBr (s + u) s).symm.left_comm,
      (cDr u (s + u)).symm.left_comm, (cDr u s).symm.left_comm, ← pinnedX_add, ← pinnedX_add,
      h2, pinnedX_zero, mul_one]
  rw [mul_assoc, e1]

end Commutation

section Bounds

variable {K : Type} [Field K] [Finite K]

theorem pow_dvd_card_centralizer_e6ASRep {f : ℕ} (hK : Nat.card K = 2 ^ f) (κ : Fin 3) :
    2 ^ (f * (e6CentList κ).length) ∣
      Nat.card (centralizer ({e6ASRep K κ} : Set (adjointGroup .E6 K))) := by
  obtain ⟨hnodup, hroot, -⟩ := e6CentList_check κ
  have hinj : Function.Injective (e6CentList κ).get := List.nodup_iff_injective_get.1 hnodup
  have hpos : ∀ i, IsRoot .E6 ((e6CentList κ).get i) ∧ 0 < height ((e6CentList κ).get i) :=
    fun i => ⟨isRoot_of_oddDerivIsRootB (hroot _ (List.get_mem _ _)).1,
      (hroot _ (List.get_mem _ _)).2⟩
  obtain ⟨hU, hψ⟩ := positive_root_product_injectivity .E6 K _ hinj hpos
  refine pow_dvd_card_centralizer_of_injective Nat.prime_two hK (e6ASRep K κ)
    (X := Fin (e6CentList κ).length → K) ?_ _ hψ hU fun c => ?_
  · rw [Nat.card_fun, Nat.card_fin, hK, ← pow_mul]
  · refine Commute.list_prod_left _ _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact commute_pinnedX_e6ASFrame κ (List.get_mem _ _) (c i)

theorem pow_dvd_card_centralizer_e6ASRep_two [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    2 ^ (f * 26) ∣ Nat.card (centralizer ({e6ASRep K 2} : Set (adjointGroup .E6 K))) := by
  obtain ⟨hnodup, hroot⟩ := zFullList_check
  have hinj : Function.Injective zFullList.get := List.nodup_iff_injective_get.1 hnodup
  have hpos : ∀ i, IsRoot .E6 (zFullList.get i) ∧ 0 < height (zFullList.get i) :=
    fun i => ⟨isRoot_of_oddDerivIsRootB (hroot _ (List.get_mem _ _)).1,
      (hroot _ (List.get_mem _ _)).2⟩
  obtain ⟨hU, hψ⟩ := positive_root_product_injectivity .E6 K _ hinj hpos
  let ι : K × K × (Fin (e6CentList 2).length → K) → Fin zFullList.length → K :=
    fun x => Fin.cons x.1 (Fin.cons (x.1 + x.2.1) (Fin.cons x.2.1 x.2.2))
  have hι : Function.Injective ι := by
    rintro ⟨s, u, c⟩ ⟨s', u', c'⟩ h
    obtain ⟨hs, h1⟩ := Fin.cons_inj.1 h
    obtain ⟨-, h2⟩ := Fin.cons_inj.1 h1
    obtain ⟨hu, hc⟩ := Fin.cons_inj.1 h2
    simp only at hs hu hc
    subst hs hu hc
    rfl
  have hprod : ∀ x : K × K × (Fin (e6CentList 2).length → K),
      (List.ofFn fun i => pinnedX .E6 K (zFullList.get i) (ι x i)).prod =
        (pinnedX .E6 K zDiagA x.1 * (pinnedX .E6 K zDiagB (x.1 + x.2.1) *
          pinnedX .E6 K zDiagD x.2.1)) *
        (List.ofFn fun i => pinnedX .E6 K ((e6CentList 2).get i) (x.2.2 i)).prod := by
    intro x
    simp only [ι, zFullList, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ,
      List.get_cons_zero, mul_assoc]
    rfl
  refine pow_dvd_card_centralizer_of_injective Nat.prime_two hK (e6ASRep K 2)
    (X := K × K × (Fin (e6CentList 2).length → K))
    (ψ := fun x => (List.ofFn fun i => pinnedX .E6 K (zFullList.get i) (ι x i)).prod) ?_
    (hψ.comp hι) (fun x => hU _) fun x => ?_
  · rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin, hK, ← pow_mul, ← pow_add,
      ← pow_add]
    have : (e6CentList 2).length = 24 := by decide +kernel
    rw [this]
    ring_nf
  · rw [hprod]
    refine Commute.mul_left ?_ ?_
    · exact commute_zDiag_zRep x.1 x.2.1
    · refine Commute.list_prod_left _ _ fun y hy => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact commute_pinnedX_e6ASFrame 2 (List.get_mem _ _) (x.2.2 i)

theorem two_pow_dvd_card_centralizer_E6 {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {w : adjointGroup .E6 K} (hw : orderOf w = 2) :
    2 ^ (26 * f) ∣ Nat.card (centralizer ({w} : Set (adjointGroup .E6 K))) := by
  have : CharP K 2 := by
    have hf : f ≠ 0 := by
      rintro rfl
      have h1 : Nat.card K = 1 := by rw [hK, pow_zero]
      have : Subsingleton K := (Nat.card_eq_one_iff_unique.1 h1).1
      exact zero_ne_one (Subsingleton.elim (0 : K) 1)
    exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (Nat.one_le_iff_ne_zero.2 hf) hK
  have hw2 : w ^ 2 = 1 := hw ▸ pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE6 hw2 hw1
  obtain ⟨κ, hκ⟩ := mem_innerRepsE6_iff.1 hg
  have hcard : Nat.card (centralizer ({w} : Set (adjointGroup .E6 K))) =
      Nat.card (centralizer ({e6ASRep K κ} : Set (adjointGroup .E6 K))) := by
    have hmap : (centralizer ({w} : Set (adjointGroup .E6 K))).map (MulAut.conj g).toMonoidHom =
        centralizer ({e6ASRep K κ} : Set (adjointGroup .E6 K)) := by
      rw [← hκ]
      ext x
      simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
          _ = g * (w * y) * g⁻¹ := by rw [hy]
          _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by group⟩
        calc g⁻¹ * x * g * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [hx]
          _ = w * (g⁻¹ * x * g) := by group
    rw [← hmap, card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  rw [hcard]
  fin_cases κ
  · have h := pow_dvd_card_centralizer_e6ASRep hK 0
    have hl : (e6CentList 0).length = 36 := by decide +kernel
    rw [hl] at h
    exact (pow_dvd_pow 2 (by omega)).trans h
  · have h := pow_dvd_card_centralizer_e6ASRep hK 1
    have hl : (e6CentList 1).length = 30 := by decide +kernel
    rw [hl] at h
    exact (pow_dvd_pow 2 (by omega)).trans h
  · have h := pow_dvd_card_centralizer_e6ASRep_two hK
    exact (pow_dvd_pow 2 (by omega)).trans h

end Bounds

end CFSG.SeitzReduction.E6Pilot
