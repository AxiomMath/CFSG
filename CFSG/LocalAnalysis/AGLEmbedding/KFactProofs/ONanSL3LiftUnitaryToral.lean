module

public import CFSG.RankThree.PartOne.CTP.SeitzUToral

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP

section Elementary

variable {K : Type} [Field K]

theorem cube_dichotomy {u v : K} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    u = 1 ∨ v = 1 ∨ u * v = 1 ∨ u * v ^ 2 = 1 := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  by_cases hv1 : v = 1
  · exact Or.inr (Or.inl hv1)
  have hu2 : u ^ 2 + u + 1 = 0 := by
    have : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination hu
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hu1)
  have hv2 : v ^ 2 + v + 1 = 0 := by
    have : (v - 1) * (v ^ 2 + v + 1) = 0 := by linear_combination hv
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hv1)
  by_cases huv : u = v
  · subst huv
    exact Or.inr (Or.inr (Or.inr (by linear_combination hu)))
  · have h1 : (u - v) * (u + v + 1) = 0 := by linear_combination hu2 - hv2
    have h2 : u + v + 1 = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 huv)
    exact Or.inr (Or.inr (Or.inl (by linear_combination u * h2 - hu2)))

theorem exists_eq_entries {ι : Type*} {u w : ι → K} (hu : ∀ c, u c ^ 3 = 1)
    (hw : ∀ c, w c ^ 3 = 1) (a b : ι) :
    u a = u b ∨ w a = w b ∨ u a * w a = u b * w b ∨ u a * w a * w a = u b * w b * w b := by
  have hu0 : ∀ c, u c ≠ 0 := fun c h0 => by simpa [h0] using hu c
  have hw0 : ∀ c, w c ≠ 0 := fun c h0 => by simpa [h0] using hw c
  have hr : (u a / u b) ^ 3 = 1 := by
    rw [div_pow, hu, hu, div_one]
  have ht : (w a / w b) ^ 3 = 1 := by
    rw [div_pow, hw, hw, div_one]
  rcases cube_dichotomy hr ht with h | h | h | h
  · exact Or.inl ((div_eq_one_iff_eq (hu0 b)).1 h)
  · exact Or.inr (Or.inl ((div_eq_one_iff_eq (hw0 b)).1 h))
  · refine Or.inr (Or.inr (Or.inl ?_))
    have := hu0 b
    have := hw0 b
    field_simp at h
    linear_combination h
  · refine Or.inr (Or.inr (Or.inr ?_))
    have := hu0 b
    have := hw0 b
    field_simp at h
    linear_combination h

end Elementary

section Toral

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem closure_centralizers_unitarySU_pair (h : UnitaryFieldData ℓ f K) (hpq : 3 ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) {s g : GL (Fin (n + 1)) K}
    (hs : s ∈ primeFormUnitary h (idGram K (n + 1)))
    (hg : g ∈ primeFormUnitary h (idGram K (n + 1))) (hsg : s * g = g * s) (hs3 : s ^ 3 = 1)
    (hg3 : g ^ 3 = 1) :
    Subgroup.closure {t : unitarySU ℓ f K (n + 1) |
      ∃ x ∈ ({s, g, s * g, s * g ^ 2} : Set (GL (Fin (n + 1)) K)),
        (t : GL (Fin (n + 1)) K) * x = x * (t : GL (Fin (n + 1)) K)} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  let s' : primeFormUnitary h (idGram K (n + 1)) := ⟨s, hs⟩
  let g' : primeFormUnitary h (idGram K (n + 1)) := ⟨g, hg⟩
  let G : Subgroup (primeFormUnitary h (idGram K (n + 1))) := Subgroup.closure {s', g'}
  have hss : Commute s' g' := Subtype.ext hsg
  have hs'3 : s' ^ 3 = 1 := Subtype.ext (by simpa using hs3)
  have hg'3 : g' ^ 3 = 1 := Subtype.ext (by simpa using hg3)
  have hc1 : ∀ x ∈ G, ∀ y ∈ ({s', g'} : Set (primeFormUnitary h (idGram K (n + 1)))),
      Commute x y := by
    intro x hx y hy
    refine Subgroup.closure_induction (p := fun x _ => Commute x y) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact hss
      · exact hss.symm
      · exact Commute.refl _
    · exact Commute.one_left y
    · intro x₁ x₂ _ _ h₁ h₂
      exact h₁.mul_left h₂
    · intro x _ hx
      exact hx.inv_left
  have hcomm : ∀ x ∈ G, ∀ y ∈ G, Commute x y := by
    intro x hx y hy
    refine Subgroup.closure_induction (p := fun y _ => Commute x y) ?_ ?_ ?_ ?_ hy
    · intro y hy
      exact hc1 x hx y hy
    · exact Commute.one_right x
    · intro y₁ y₂ _ _ h₁ h₂
      exact h₁.mul_right h₂
    · intro y _ hy
      exact hy.inv_right
  have hexp : ∀ x ∈ G, x ^ 3 = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with rfl | rfl
      · exact hs'3
      · exact hg'3
    · exact one_pow 3
    · intro x₁ x₂ hx₁ hx₂ h₁ h₂
      rw [(hcomm x₁ hx₁ x₂ hx₂).mul_pow, h₁, h₂, one_mul]
    · intro x _ hx
      rw [inv_pow, hx, inv_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three hpq G
    (fun x hx y hy => hcomm x hx y hy) hexp
  set Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K) with hPg
  have hDs : ((Pg⁻¹ * s * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    hP s' (Subgroup.subset_closure (by simp))
  have hDg : ((Pg⁻¹ * g * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    hP g' (Subgroup.subset_closure (by simp))
  set u : Fin (n + 1) → K := fun c =>
    ((Pg⁻¹ * s * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c with hu
  set w : Fin (n + 1) → K := fun c =>
    ((Pg⁻¹ * g * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c with hw
  have hDs_eq : ((Pg⁻¹ * s * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      diagonal u := hDs.diagonal_diag.symm
  have hDg_eq : ((Pg⁻¹ * g * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      diagonal w := hDg.diagonal_diag.symm
  have hnz : ∀ M : GL (Fin (n + 1)) K, ((M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)).IsDiag →
      ∀ c, (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro M hM c
    have h1 : ((M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        ((M⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag hM] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hu0 : ∀ c, u c ≠ 0 := hnz _ hDs
  have hw0 : ∀ c, w c ≠ 0 := hnz _ hDg
  have hcube : ∀ (x : GL (Fin (n + 1)) K) (d : Fin (n + 1) → K), x ^ 3 = 1 →
      ((Pg⁻¹ * x * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        diagonal d → ∀ c, d c ^ 3 = 1 := by
    intro x d hx hd c
    have h1 : (Pg⁻¹ * x * Pg) * (Pg⁻¹ * x * Pg) * (Pg⁻¹ * x * Pg) = 1 := by
      have h2 : (Pg⁻¹ * x * Pg) * (Pg⁻¹ * x * Pg) * (Pg⁻¹ * x * Pg) =
          Pg⁻¹ * (x * x * x) * Pg := by group
      rw [h2, ← pow_three', hx]
      group
    have h3 := congrArg (fun M : GL (Fin (n + 1)) K => (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K))
      h1
    simp only [Units.val_mul, Units.val_one, hd, diagonal_mul_diagonal] at h3
    have h4 := congrFun (congrFun h3 c) c
    simpa [pow_three'] using h4
  have hu3 : ∀ c, u c ^ 3 = 1 := hcube s u hs3 hDs_eq
  have hw3 : ∀ c, w c ^ 3 = 1 := hcube g w hg3 hDg_eq
  have hcommblock : ∀ i : Fin n, ∃ x ∈ ({s, g, s * g, s * g ^ 2} : Set (GL (Fin (n + 1)) K)),
      ∀ A : Matrix (Fin 2) (Fin 2) K, blockMat (n + 1) i A *
          ((Pg⁻¹ * x * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        ((Pg⁻¹ * x * Pg : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          blockMat (n + 1) i A := by
    intro i
    rcases exists_eq_entries hu3 hw3 i.castSucc i.succ with e | e | e | e
    · refine ⟨s, by simp, fun A => ?_⟩
      rw [hDs_eq]
      exact blockMat_mul_diagonal_comm (by omega) u hu0 i.castSucc i.succ (by simp) (by simp) e A
    · refine ⟨g, by simp, fun A => ?_⟩
      rw [hDg_eq]
      exact blockMat_mul_diagonal_comm (by omega) w hw0 i.castSucc i.succ (by simp) (by simp) e A
    · refine ⟨s * g, by simp, fun A => ?_⟩
      have hx : ((Pg⁻¹ * (s * g) * Pg : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) = diagonal (fun c => u c * w c) := by
        rw [show Pg⁻¹ * (s * g) * Pg = (Pg⁻¹ * s * Pg) * (Pg⁻¹ * g * Pg) by group,
          Units.val_mul, hDs_eq, hDg_eq, diagonal_mul_diagonal]
      rw [hx]
      exact blockMat_mul_diagonal_comm (by omega) _ (fun c => mul_ne_zero (hu0 c) (hw0 c))
        i.castSucc i.succ (by simp) (by simp) e A
    · refine ⟨s * g ^ 2, by simp, fun A => ?_⟩
      have hx : ((Pg⁻¹ * (s * g ^ 2) * Pg : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) = diagonal (fun c => u c * w c * w c) := by
        rw [show Pg⁻¹ * (s * g ^ 2) * Pg =
          (Pg⁻¹ * s * Pg) * (Pg⁻¹ * g * Pg) * (Pg⁻¹ * g * Pg) by rw [pow_two]; group,
          Units.val_mul, Units.val_mul, hDs_eq, hDg_eq, diagonal_mul_diagonal,
          diagonal_mul_diagonal]
      rw [hx]
      exact blockMat_mul_diagonal_comm (by omega) _
        (fun c => mul_ne_zero (mul_ne_zero (hu0 c) (hw0 c)) (hw0 c))
        i.castSucc i.succ (by simp) (by simp) e A
  let φ := conjSU h P
  set S := Subgroup.closure {t : unitarySU ℓ f K (n + 1) |
      ∃ x ∈ ({s, g, s * g, s * g ^ 2} : Set (GL (Fin (n + 1)) K)),
        (t : GL (Fin (n + 1)) K) * x = x * (t : GL (Fin (n + 1)) K)} with hS
  have hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1)) (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → φ y ∈ S := by
    intro i y A hA
    obtain ⟨x, hxl, hxc⟩ := hcommblock i
    refine Subgroup.subset_closure ⟨x, hxl, ?_⟩
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * (Pg⁻¹ * x * Pg) =
        (Pg⁻¹ * x * Pg) * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      exact hxc A
    change Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ * x =
      x * (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
    have hxeq : x = Pg * (Pg⁻¹ * x * Pg) * Pg⁻¹ := by group
    calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ * x
        = Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * (Pg⁻¹ * x * Pg) * Pg⁻¹) := by rw [← hxeq]
      _ = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * (Pg⁻¹ * x * Pg)) *
          Pg⁻¹ := by group
      _ = Pg * ((Pg⁻¹ * x * Pg) * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) *
          Pg⁻¹ := by rw [hYD]
      _ = (Pg * (Pg⁻¹ * x * Pg) * Pg⁻¹) *
          (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by group
      _ = x * (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by
        rw [← hxeq]
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hle' : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle'
  exact top_unique hle'

end Toral

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
