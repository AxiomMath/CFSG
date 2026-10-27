module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinOIdx
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthWitness

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem commute_of_preserve {M F : Submodule K V} (hMF : IsCompl M F) {A g : V ≃ₗ[K] V} {s : K}
    (hAM : ∀ m ∈ M, A m = s • m) (hAF : ∀ f ∈ F, A f = -s • f)
    (hgM : ∀ m ∈ M, g m ∈ M) (hgF : ∀ f ∈ F, g f ∈ F) : g * A = A * g := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ M ⊔ F := by rw [hMF.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨m, hm, f, hf, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [LinearEquiv.mul_apply, map_add, map_smul, hAM m hm, hAF f hf, hAM _ (hgM m hm),
    hAF _ (hgF f hf)]

theorem reflect_preserve {M F : Submodule K V} {Q : QuadraticForm K V}
    (horth : ∀ x ∈ M, ∀ y ∈ F, polar Q x y = 0) {w : V} (hw : w ∈ M) :
    (∀ m ∈ M, reflect Q w m ∈ M) ∧ ∀ f ∈ F, reflect Q w f = f := by
  refine ⟨fun m hm => ?_, fun f hf => reflect_apply_of_polar_eq_zero (horth w hw f hf)⟩
  by_cases hQ : Q w = 0
  · rw [reflect_of_map_eq_zero hQ]
    exact hm
  · rw [reflect_apply hQ]
    exact M.sub_mem hm (M.smul_mem _ hw)

theorem reflect_self_eq {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0) : reflect Q w w = -w := by
  rw [reflect_apply hw, OddClassSelector.polar_self_eq, mul_div_assoc, div_self hw, mul_one,
    two_smul, sub_add_cancel_left]

theorem exists_orthogonal_family [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {Q : QuadraticForm K V} {M F : Submodule K V}
    (horth : ∀ x ∈ M, ∀ y ∈ F, polar Q x y = 0)
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate)
    (hFnd : (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate) :
    ∃ w : Fin (finrank K M) ⊕ Fin (finrank K F) → V,
      (∀ i, w i ∈ M ∨ w i ∈ F) ∧ (∀ i, Q (w i) ≠ 0) ∧
        ∀ i j, i ≠ j → polar Q (w i) (w j) = 0 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hsymm : ∀ W : Submodule K V, (LinearMap.BilinForm.restrict Q.polarBilin W).IsSymm :=
    fun W => ⟨fun x y => by
      change Q.polarBilin x y = Q.polarBilin y x
      rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]⟩
  obtain ⟨bM, hbM⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp (hsymm M))
  obtain ⟨bF, hbF⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp (hsymm F))
  have hQ : ∀ (W : Submodule K V) (x : W),
      LinearMap.BilinForm.restrict Q.polarBilin W x x ≠ 0 → Q x ≠ 0 := by
    intro W x hx h
    apply hx
    change polar Q x x = 0
    rw [OddClassSelector.polar_self_eq, h, mul_zero]
  refine ⟨Sum.elim (fun j => (bM j : V)) (fun j => (bF j : V)), ?_, ?_, ?_⟩
  · rintro (j | j)
    · exact Or.inl (bM j).2
    · exact Or.inr (bF j).2
  · rintro (j | j)
    · exact hQ M _ (LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate hbM
        hMnd j)
    · exact hQ F _ (LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate hbF
        hFnd j)
  · rintro (i | i) (j | j) hij
    · exact hbM (fun h => hij (by rw [h]))
    · exact horth _ (bM i).2 _ (bF j).2
    · rw [polar_comm]
      exact horth _ (bM j).2 _ (bF i).2
    · exact hbF (fun h => hij (by rw [h]))

theorem exists_elemTwo_split [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hP : ThreePairs Q)
    (hd : 7 ≤ finrank K V) {M F : Submodule K V} (hMF : IsCompl M F)
    (horth : ∀ x ∈ M, ∀ y ∈ F, polar Q x y = 0)
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate)
    (hFnd : (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate)
    {A : V ≃ₗ[K] V} {s : K} (hAM : ∀ m ∈ M, A m = s • m) (hAF : ∀ f ∈ F, A f = -s • f) :
    ∃ E : Subgroup (V ≃ₗ[K] V),
      E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      ElemTwo E ∧ 16 ≤ Nat.card E ∧ (∀ g ∈ E, g * A = A * g) ∧
      ∀ g ∈ E, ∀ c : K, (∀ v, g v = c • v) → g = 1 := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  obtain ⟨w, hwMF, hwQ, hworth⟩ := exists_orthogonal_family h2 horth hMnd hFnd
  have hw0 : ∀ i, w i ≠ 0 := fun i h => hwQ i (by rw [h, QuadraticMap.map_zero])
  have hcardι : 7 ≤ Fintype.card (Fin (finrank K M) ⊕ Fin (finrank K F)) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      Submodule.finrank_add_eq_of_isCompl hMF]
    exact hd
  obtain ⟨i₀⟩ : Nonempty (Fin (finrank K M) ⊕ Fin (finrank K F)) :=
    Fintype.card_pos_iff.mp (by omega)
  have hcard6 : 6 ≤ (Finset.univ.erase i₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨S, hS, hS6⟩ := Finset.exists_subset_card_eq hcard6
  have hi₀ : i₀ ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
  set x := fun i => reflect Q (w i) with hx
  obtain ⟨hH2, hHcard, hHfix⟩ := card_closure_dual h2 x w
    (fun i j => by
      by_cases hij : i = j
      · rw [hij]
      · exact OddClassSelector.reflect_comm_of_polar_eq_zero (hworth i j hij))
    (fun i => reflect_mul_self Q (w i)) (fun i => reflect_self_eq (hwQ i))
    (fun i j hij => reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact hworth i j hij))
    hw0 S
  set H := closure (x '' ↑S) with hHdef
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hHdef, closure_le]
    rintro _ ⟨i, -, rfl⟩
    exact reflect_mem_orthogonalGroup Q (w i)
  have hHA : H ≤ centralizer {A} := by
    rw [hHdef, closure_le]
    rintro _ ⟨i, -, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hwMF i with hi | hi
    · obtain ⟨hM, hF⟩ := reflect_preserve horth hi
      exact commute_of_preserve hMF hAM hAF hM (fun f hf => by rw [hF f hf]; exact hf)
    · have horth' : ∀ y ∈ F, ∀ x ∈ M, polar Q y x = 0 := fun y hy x hx => by
        rw [polar_comm]; exact horth x hx y hy
      obtain ⟨hF, hM⟩ := reflect_preserve horth' hi
      exact commute_of_preserve hMF hAM hAF (fun m hm => by rw [hM m hm]; exact hm) hF
  have h4 := card_le_four_mul_card_inf h2 hQ hP hHO
  rw [hS6] at hHcard
  refine ⟨H ⊓ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
    inf_le_right, ⟨fun a ha b hb => hH2.1 a ha.1 b hb.1, fun a ha => hH2.2 a ha.1⟩,
    by omega, fun g hg => mem_centralizer_singleton_iff.mp (hHA hg.1), ?_⟩
  intro g hg c hc
  have hfix := hHfix i₀ hi₀ hg.1
  rw [mem_fixVec, hc] at hfix
  have hc1 : c = 1 := by
    have h0 : (c - 1) • w i₀ = 0 := by rw [sub_smul, hfix, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right (hw0 i₀))
  refine LinearEquiv.ext fun v => ?_
  rw [hc, hc1, one_smul]
  rfl

end CFSG.ComponentClassification.HarrisLit.Hin
