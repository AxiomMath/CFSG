module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONormA

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix CFSG.Open
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  coe_quadMinus)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

abbrev idx0 : Fin (3 - 1) := ⟨0, by norm_num⟩

abbrev idx1 : Fin (3 - 1) := ⟨1, by norm_num⟩

theorem comm_eichler (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (f : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) →+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hf : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      f ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
        (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          f x)
    (u w x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    f (eichler (quadMinus 3 F b c) u w x) = eichler (quadMinus 3 F b c) u w (f x) := by
  obtain ⟨A, hA, hAx⟩ := eichler_mem_statedOmega hirr u w
  have h1 := hf A hA x
  rwa [hAx x, hAx (f x)] at h1

theorem polar_e_right (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (i : Fin (3 - 1)) :
    polar (quadMinus 3 F b c) x (Pi.single (Sum.inl i) 1) = x (Sum.inr (Sum.inl i)) := by
  rw [polar_comm, polar_single_inl_quadMinus]

theorem polar_f_right (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (i : Fin (3 - 1)) :
    polar (quadMinus 3 F b c) x (Pi.single (Sum.inr (Sum.inl i)) 1) = x (Sum.inl i) := by
  rw [polar_comm, polar_single_inr_quadMinus]

theorem comm_e0 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (f : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) →+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hf : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      f ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
        (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          f x) :
    ∃ a : F, f (Pi.single (Sum.inl idx0) 1) = a • Pi.single (Sum.inl idx0) 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hneg : ∀ y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F, -y = y := fun y => CharTwo.neg_eq y
  set Q := quadMinus 3 F b c with hQdef
  set e₀ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inl idx0) 1 with he₀
  set e₁ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inl idx1) 1 with he₁
  set f₁ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inr (Sum.inl idx1)) 1 with hf₁
  have hQe₀ : Q e₀ = 0 := quadMinus_single_inl idx0
  have hQe₁ : Q e₁ = 0 := quadMinus_single_inl idx1
  have hQf₁ : Q f₁ = 0 := quadMinus_single_inr idx1
  have hpe : polar Q e₁ e₀ = 0 := by
    rw [he₁, polar_single_inl_quadMinus]; simp [he₀, Pi.single_apply]
  have hne01 : idx0 ≠ idx1 := by decide
  have hL : eichler Q e₁ e₀ f₁ = f₁ + e₀ := by
    rw [eichler_apply hQe₁ hpe, polar_e_right, polar_e_right, hQe₀]
    simp [hf₁, he₀, he₁, Pi.single_apply, hne01]
  have hE1 : f e₀ = (f f₁ (Sum.inr (Sum.inl idx1))) • e₀ - (f f₁ (Sum.inr (Sum.inl idx0))) • e₁ := by
    have h := comm_eichler hirr f hf e₁ e₀ f₁
    rw [hL, map_add, eichler_apply hQe₁ hpe, polar_e_right, polar_e_right, hQe₀, zero_mul,
      add_zero] at h
    have h' : f f₁ + f e₀ = f f₁ + ((f f₁ (Sum.inr (Sum.inl idx1))) • e₀ -
        (f f₁ (Sum.inr (Sum.inl idx0))) • e₁) := by rw [h]; abel
    exact add_left_cancel h'
  have hpf : polar Q f₁ e₀ = 0 := by
    rw [hf₁, polar_single_inr_quadMinus]; simp [he₀, Pi.single_apply]
  have hL2 : eichler Q f₁ e₀ e₁ = e₁ + e₀ := by
    rw [eichler_apply hQf₁ hpf, polar_f_right, polar_e_right, hQe₀]
    simp [he₀, he₁, Pi.single_apply, hne01]
  have hE2 : f e₀ = (f e₁ (Sum.inl idx1)) • e₀ - (f e₁ (Sum.inr (Sum.inl idx0))) • f₁ := by
    have h := comm_eichler hirr f hf f₁ e₀ e₁
    rw [hL2, map_add, eichler_apply hQf₁ hpf, polar_f_right, polar_e_right, hQe₀, zero_mul,
      add_zero] at h
    have h' : f e₁ + f e₀ = f e₁ + ((f e₁ (Sum.inl idx1)) • e₀ -
        (f e₁ (Sum.inr (Sum.inl idx0))) • f₁) := by rw [h]; abel
    exact add_left_cancel h'
  have hb : f f₁ (Sum.inr (Sum.inl idx0)) = 0 := by
    have h1 := congrFun hE1 (Sum.inl idx1)
    have h2 := congrFun hE2 (Sum.inl idx1)
    rw [h1] at h2
    simpa [he₀, he₁, hf₁, Pi.single_apply, hne01] using h2
  exact ⟨f f₁ (Sum.inr (Sum.inl idx1)), by rw [hE1, hb, zero_smul, sub_zero]⟩

theorem single_eq_smul_single {ι : Type*} [DecidableEq ι] (k : ι) (t : F) :
    (Pi.single k t : ι → F) = t • (Pi.single k 1 : ι → F) := by
  ext j
  by_cases h : j = k
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem eichler_e1_e0_f1 :
    eichler (quadMinus 3 F b c) (Pi.single (Sum.inl idx1) 1) (Pi.single (Sum.inl idx0) 1)
        (Pi.single (Sum.inr (Sum.inl idx1)) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) =
      Pi.single (Sum.inr (Sum.inl idx1)) 1 + Pi.single (Sum.inl idx0) 1 := by
  have hne01 : idx0 ≠ idx1 := by decide
  have hpe : polar (quadMinus 3 F b c) (Pi.single (Sum.inl idx1) 1)
      (Pi.single (Sum.inl idx0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) = 0 := by
    rw [polar_single_inl_quadMinus]; simp [Pi.single_apply]
  rw [eichler_apply (quadMinus_single_inl idx1) hpe, polar_e_right, polar_e_right,
    quadMinus_single_inl]
  simp [Pi.single_apply, hne01]

theorem exists_statedOmega_apply_e0 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {s : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F} (hs : quadMinus 3 F b c s = 0) (hs0 : s ≠ 0) :
    ∃ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        (Pi.single (Sum.inl idx0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) = s := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hne01 : idx0 ≠ idx1 := by decide
  have he₀ne : (Pi.single (Sum.inl idx0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl idx0)
    simp at this
  obtain ⟨g, hgE, hge⟩ := exists_mem_elementaryGroup_apply_eq hQ
    (minusPair_orth (K := F) (b := b) (c := c) (n := 3) hne01)
    (x := (Pi.single (Sum.inl idx0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) (y := s)
    he₀ne hs0 (by rw [quadMinus_single_inl, hs])
  have hgΩ : g ∈ ⁅orthogonalGroup (quadMinus 3 F b c), orthogonalGroup (quadMinus 3 F b c)⁆ :=
    elementaryGroup_le_of_eichler_mem
      (H := ⁅orthogonalGroup (quadMinus 3 F b c), orthogonalGroup (quadMinus 3 F b c)⁆)
      (fun u w _ _ => eichler_mem_commutator hirr u w) hgE
  refine ⟨(toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g, ?_, ?_⟩
  · rw [mem_statedOmega_iff, MulEquiv.apply_symm_apply]
    exact hgΩ
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    exact hge

theorem mem_of_forall_singular_mem (S : AddSubgroup (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hS : ∀ s, quadMinus 3 F b c s = 0 → s ∈ S) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    x ∈ S := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set Q := quadMinus 3 F b c with hQdef
  set e₀ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inl idx0) 1 with he₀
  set f₀ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inr (Sum.inl idx0)) 1 with hf₀
  have hQe₀ : Q e₀ = 0 := quadMinus_single_inl idx0
  have hQf₀ : Q f₀ = 0 := quadMinus_single_inr idx0
  have h4 : ∀ y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F, y + y = 0 := fun y => by
    rw [← two_smul F y, h2, zero_smul]
  have hsingle : ∀ (k : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (t : F), Pi.single k t ∈ S := by
    intro k t
    rcases k with i | k
    · apply hS
      rw [single_eq_smul_single, map_smul_eq_sq, quadMinus_single_inl, mul_zero]
    rcases k with i | j
    · apply hS
      rw [single_eq_smul_single, map_smul_eq_sq, quadMinus_single_inr, mul_zero]
    · set z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inr (Sum.inr j)) t with hz
      obtain ⟨t', ht'⟩ : ∃ t' : F, t' = Q z := ⟨_, rfl⟩
      have hsf : Q (t' • f₀) = 0 := by rw [map_smul_eq_sq, hQf₀, mul_zero]
      have hpe : polar Q e₀ (t' • f₀) = t' := by
        rw [polar_smul_right_eq, he₀, hf₀, polar_single_inl_quadMinus]
        simp
      have hzf : polar Q z f₀ = 0 := by
        rw [hf₀, polar_f_right]; simp [hz, Pi.single_apply]
      have hze : polar Q z e₀ = 0 := by
        rw [he₀, polar_e_right]; simp [hz, Pi.single_apply]
      have hQz' : Q (z + e₀ + t' • f₀) = 0 := by
        have hs1 : polar Q z (e₀ + t' • f₀) = 0 := by
          rw [polar_add_right, polar_smul_right_eq, hze, hzf, mul_zero, add_zero]
        have hs2 : Q (e₀ + t' • f₀) = t' := by
          rw [QuadraticMap.map_add Q e₀ (t' • f₀), hQe₀, hsf, hpe]; ring
        rw [add_assoc, QuadraticMap.map_add Q z (e₀ + t' • f₀), hs1, hs2, ← ht']
        linear_combination t' * h2
      have hz' : z + e₀ + t' • f₀ + e₀ + t' • f₀ = z := by
        calc z + e₀ + t' • f₀ + e₀ + t' • f₀ = z + (e₀ + e₀) + (t' • f₀ + t' • f₀) := by abel
          _ = z := by rw [h4, h4, add_zero, add_zero]
      rw [← hz']
      exact S.add_mem (S.add_mem (hS _ hQz') (hS _ hQe₀)) (hS _ hsf)
  rw [← Finset.univ_sum_single x]
  exact AddSubgroup.sum_mem S fun k _ => hsingle k (x k)

theorem omega_commutant (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (f : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) →+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hf : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      f ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
        (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          f x) :
    ∃ μ : F, ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F, f x = μ • x := by
  obtain ⟨a, ha⟩ := comm_e0 hirr f hf
  have hsing : ∀ s, quadMinus 3 F b c s = 0 → f s = a • s := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0, map_zero, smul_zero]
    obtain ⟨g, hgΩ, hge⟩ := exists_statedOmega_apply_e0 hirr hs hs0
    have h1 := hf g hgΩ (Pi.single (Sum.inl idx0) 1)
    rw [hge, ha] at h1
    rw [h1, Matrix.mulVec_smul, hge]
  refine ⟨a, fun x => ?_⟩
  let S : AddSubgroup (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :=
    { carrier := {x | f x = a • x}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add, hx, hy, smul_add]
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_neg, hx, smul_neg] }
  exact mem_of_forall_singular_mem S hsing x

end CFSG.LocalAnalysis.RankThreeUC
