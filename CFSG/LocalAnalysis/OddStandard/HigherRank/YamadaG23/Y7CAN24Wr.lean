module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Blk
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Abs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Struct

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

@[expose] def n24Stab2 : Subgroup (GL (Fin 6) (ZMod 2)) where
  carrier := {g | img g T₁ = T₁ ∧ img g T₂ = T₂}
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂⟩ ⟨hh₁, hh₂⟩
    exact ⟨by rw [img_mul, hh₁, hg₁], by rw [img_mul, hh₂, hg₂]⟩
  one_mem' := ⟨img_one _, img_one _⟩
  inv_mem' := by
    rintro g ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · calc img g⁻¹ T₁ = img g⁻¹ (img g T₁) := by rw [h₁]
        _ = T₁ := img_inv_img g T₁
    · calc img g⁻¹ T₂ = img g⁻¹ (img g T₂) := by rw [h₂]
        _ = T₂ := img_inv_img g T₂

private def n24B₁ (g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).submatrix (Fin.castAdd 3) (Fin.castAdd 3)

private def n24B₂ (g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).submatrix (Fin.castAdd 3) (Fin.natAdd 3)

private def n24B₃ (g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).submatrix (Fin.natAdd 3) (Fin.castAdd 3)

private def n24B₄ (g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).submatrix (Fin.natAdd 3) (Fin.natAdd 3)

private theorem n24B_eq (g : GL (Fin 6) (ZMod 2)) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      n24Blk (n24B₁ g) (n24B₂ g) (n24B₃ g) (n24B₄ g) := by
  ext i j
  refine Fin.addCases (m := 3) (n := 3) (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (m := 3) (n := 3) (fun b => ?_) (fun b => ?_) j
  · rw [n24Blk_ll]; rfl
  · rw [n24Blk_lr]; rfl
  · rw [n24Blk_rl]; rfl
  · rw [n24Blk_rr]; rfl

private theorem n24Blk_mulVec_append (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (v w : Fin 3 → ZMod 2) :
    n24Blk P Q R S *ᵥ Fin.append v w =
      Fin.append (P *ᵥ v + Q *ᵥ w) (R *ᵥ v + S *ᵥ w) := by
  have h := Matrix.submatrix_mulVec_equiv (Matrix.fromBlocks P Q R S) (Fin.append v w)
    (n24Eq.symm : Fin 6 → Fin 3 ⊕ Fin 3) n24Eq.symm
  unfold n24Blk
  rw [h, Matrix.fromBlocks_mulVec, Equiv.symm_symm]
  have hx : (Fin.append v w ∘ ⇑n24Eq) = Sum.elim v w := by
    funext j
    rcases j with a | a
    · show Fin.append v w (n24Eq (Sum.inl a)) = v a
      rw [show n24Eq (Sum.inl a) = Fin.castAdd 3 a from rfl]
      simp only [Fin.append_left]
    · show Fin.append v w (n24Eq (Sum.inr a)) = w a
      rw [show n24Eq (Sum.inr a) = Fin.natAdd 3 a from rfl]
      simp only [Fin.append_right]
  rw [hx]
  have hx' : (Sum.elim (P *ᵥ v + Q *ᵥ w) (R *ᵥ v + S *ᵥ w)) ∘ ⇑n24Eq.symm =
      Fin.append (P *ᵥ v + Q *ᵥ w) (R *ᵥ v + S *ᵥ w) := by
    funext i
    obtain ⟨j, rfl⟩ := n24Eq.surjective i
    rcases j with a | a
    · show Sum.elim (P *ᵥ v + Q *ᵥ w) (R *ᵥ v + S *ᵥ w) (n24Eq.symm (n24Eq (Sum.inl a))) =
        Fin.append (P *ᵥ v + Q *ᵥ w) (R *ᵥ v + S *ᵥ w) (n24Eq (Sum.inl a))
      rw [show n24Eq (Sum.inl a) = Fin.castAdd 3 a from rfl]
      simp only [Equiv.symm_apply_apply, n24Eq_symm_castAdd, Sum.elim_inl, Fin.append_left]
    · show Sum.elim (P *ᵥ v + Q *ᵥ w) (R *ᵥ v + S *ᵥ w) (n24Eq.symm (n24Eq (Sum.inr a))) =
        Fin.append (P *ᵥ v + Q *ᵥ w) (R *ᵥ v + S *ᵥ w) (n24Eq (Sum.inr a))
      rw [show n24Eq (Sum.inr a) = Fin.natAdd 3 a from rfl]
      simp only [Equiv.symm_apply_apply, n24Eq_symm_natAdd, Sum.elim_inr, Fin.append_right]
  exact hx'

private theorem n24B₂_eq_zero {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₂ g = 0 := by
  obtain ⟨hg₁, -⟩ := hg
  ext i j
  have hv : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
      Fin.append (0 : Fin 3 → ZMod 2) (Pi.single j 1) ∈ T₁ := by
    have hmem : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
        Fin.append (0 : Fin 3 → ZMod 2) (Pi.single j 1) ∈ img g T₁ :=
      ⟨_, ⟨Pi.single j 1, rfl⟩, rfl⟩
    rwa [hg₁] at hmem
  rw [n24B_eq g, n24Blk_mulVec_append] at hv
  simp only [Matrix.mulVec_zero, zero_add] at hv
  obtain ⟨w, hw⟩ := hv
  have hcoord := congrFun hw (Fin.castAdd 3 i)
  simp only [Fin.append_left] at hcoord
  rw [Matrix.mulVec_single_one] at hcoord
  exact hcoord.symm

private theorem n24B₁_eq {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₁ g = n24B₃ g + n24B₄ g := by
  have hb : n24B₂ g = 0 := n24B₂_eq_zero hg
  have hg₂ : img g T₂ = T₂ := hg.2
  ext i j
  have hv : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
      Fin.append (Pi.single j 1) (Pi.single j 1) ∈ T₂ := by
    have hmem : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
        Fin.append (Pi.single j 1) (Pi.single j 1) ∈ img g T₂ :=
      ⟨_, ⟨Pi.single j 1, rfl⟩, rfl⟩
    rwa [hg₂] at hmem
  rw [n24B_eq g, n24Blk_mulVec_append, hb] at hv
  simp only [Matrix.zero_mulVec, add_zero] at hv
  obtain ⟨w, hw⟩ := hv
  have h1 := congrFun hw (Fin.castAdd 3 i)
  have h2 := congrFun hw (Fin.natAdd 3 i)
  simp only [Fin.append_left, Fin.append_right] at h1 h2
  have e1 : n24B₁ g i j = w i := by simpa using h1.symm
  have e2 : n24B₃ g i j + n24B₄ g i j = w i := by
    simpa [Matrix.add_apply] using h2.symm
  rw [Matrix.add_apply, e1, e2]

private theorem n24B₃_eq {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₃ g = n24B₁ g + n24B₄ g := by
  have h := n24B₁_eq hg
  have : n24B₁ g + n24B₄ g = n24B₃ g := by
    rw [h, add_assoc, n24_add_self, add_zero]
  exact this.symm

private theorem n24B₄_mul {g h : GL (Fin 6) (ZMod 2)} (hh : h ∈ n24Stab2) :
    n24B₄ (g * h) = n24B₄ g * n24B₄ h := by
  have hb : n24B₂ h = 0 := n24B₂_eq_zero hh
  have hmat : ((g * h : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      n24Blk (n24B₁ g * n24B₁ h + n24B₂ g * n24B₃ h)
        (n24B₁ g * n24B₂ h + n24B₂ g * n24B₄ h)
        (n24B₃ g * n24B₁ h + n24B₄ g * n24B₃ h)
        (n24B₃ g * n24B₂ h + n24B₄ g * n24B₄ h) := by
    rw [Units.val_mul, n24B_eq g, n24B_eq h, n24Blk_mul]
  rw [n24B_eq (g * h)] at hmat
  obtain ⟨-, -, -, h4⟩ := n24Blk_inj hmat
  simpa [hb] using h4

private theorem n24B₁_mul {g h : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₁ (g * h) = n24B₁ g * n24B₁ h := by
  have hb : n24B₂ g = 0 := n24B₂_eq_zero hg
  have hmat : ((g * h : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      n24Blk (n24B₁ g * n24B₁ h + n24B₂ g * n24B₃ h)
        (n24B₁ g * n24B₂ h + n24B₂ g * n24B₄ h)
        (n24B₃ g * n24B₁ h + n24B₄ g * n24B₃ h)
        (n24B₃ g * n24B₂ h + n24B₄ g * n24B₄ h) := by
    rw [Units.val_mul, n24B_eq g, n24B_eq h, n24Blk_mul]
  rw [n24B_eq (g * h)] at hmat
  obtain ⟨h1, -, -, -⟩ := n24Blk_inj hmat
  simpa [hb] using h1

private theorem n24B₄_mul_inv {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₄ g * n24B₄ g⁻¹ = 1 := by
  have hb : n24B₂ g⁻¹ = 0 := n24B₂_eq_zero (n24Stab2.inv_mem hg)
  have hmat : ((g * g⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [mul_inv_cancel]; rfl
  rw [Units.val_mul, n24B_eq g, n24B_eq g⁻¹, n24Blk_mul, ← n24Blk_one] at hmat
  obtain ⟨-, -, -, h4⟩ := n24Blk_inj hmat
  simpa [hb] using h4

private theorem n24B₄_inv_mul {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₄ g⁻¹ * n24B₄ g = 1 := by
  have hb : n24B₂ g = 0 := n24B₂_eq_zero hg
  have hmat : ((g⁻¹ * g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [inv_mul_cancel]; rfl
  rw [Units.val_mul, n24B_eq g⁻¹, n24B_eq g, n24Blk_mul, ← n24Blk_one] at hmat
  obtain ⟨-, -, -, h4⟩ := n24Blk_inj hmat
  simpa [hb] using h4

private theorem n24B₁_mul_inv {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₁ g * n24B₁ g⁻¹ = 1 := by
  have hb : n24B₂ g = 0 := n24B₂_eq_zero hg
  have hmat : ((g * g⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [mul_inv_cancel]; rfl
  rw [Units.val_mul, n24B_eq g, n24B_eq g⁻¹, n24Blk_mul, ← n24Blk_one] at hmat
  obtain ⟨h1, -, -, -⟩ := n24Blk_inj hmat
  simpa [hb] using h1

private theorem n24B₁_inv_mul {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ n24Stab2) :
    n24B₁ g⁻¹ * n24B₁ g = 1 := by
  have hb : n24B₂ g⁻¹ = 0 := n24B₂_eq_zero (n24Stab2.inv_mem hg)
  have hmat : ((g⁻¹ * g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [inv_mul_cancel]; rfl
  rw [Units.val_mul, n24B_eq g⁻¹, n24B_eq g, n24Blk_mul, ← n24Blk_one] at hmat
  obtain ⟨h1, -, -, -⟩ := n24Blk_inj hmat
  simpa [hb] using h1

private def n24Stab2Rho₁ : ↥n24Stab2 →* GL (Fin 3) (ZMod 2) :=
  MonoidHom.mk' (fun x => ⟨n24B₄ x.1, n24B₄ x.1⁻¹,
      n24B₄_mul_inv x.2, n24B₄_inv_mul x.2⟩)
    (fun x y => by
      refine Units.ext ?_
      rw [Units.val_mul]
      simpa using n24B₄_mul y.2)

private def n24Stab2Rho₂ : ↥n24Stab2 →* GL (Fin 3) (ZMod 2) :=
  MonoidHom.mk' (fun x => ⟨n24B₁ x.1, n24B₁ x.1⁻¹,
      n24B₁_mul_inv x.2, n24B₁_inv_mul x.2⟩)
    (fun x y => by
      refine Units.ext ?_
      rw [Units.val_mul]
      simpa using n24B₁_mul x.2)

private theorem n24Stab2Rho₁_coe (x : ↥n24Stab2) :
    (n24Stab2Rho₁ x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = n24B₄ x.1 := rfl

private theorem n24Stab2Rho₂_coe (x : ↥n24Stab2) :
    (n24Stab2Rho₂ x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = n24B₁ x.1 := rfl

theorem n24_homs_of_stab2 (H : Subgroup (GL (Fin 6) (ZMod 2))) (hH : H ≤ n24Stab2) :
    ∃ ρ₁ ρ₂ : ↥H →* GL (Fin 3) (ZMod 2), ∀ x : ↥H, ρ₁ x = 1 → ρ₂ x = 1 → x = 1 := by
  refine ⟨n24Stab2Rho₁.comp (Subgroup.inclusion hH),
    n24Stab2Rho₂.comp (Subgroup.inclusion hH), fun x h1 h2 => ?_⟩
  have h4 : n24B₄ x.1 = 1 := by
    have h := congrArg (fun u : GL (Fin 3) (ZMod 2) =>
      (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
    simpa [n24Stab2Rho₁_coe] using h
  have h1' : n24B₁ x.1 = 1 := by
    have h := congrArg (fun u : GL (Fin 3) (ZMod 2) =>
      (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) h2
    simpa [n24Stab2Rho₂_coe] using h
  have hb : n24B₂ x.1 = 0 := n24B₂_eq_zero (hH x.2)
  have hc : n24B₃ x.1 = 0 := by
    rw [n24B₃_eq (hH x.2), h1', h4, n24_add_self]
  refine Subtype.ext (Units.ext ?_)
  rw [n24B_eq x.1, h1', hb, hc, h4, n24Blk_one]
  rfl

theorem n24_MW_card_dvd (H : Subgroup (GL (Fin 6) (ZMod 2))) (hH : H ≤ MW)
    (hs : IsSimpleGroup ↥H) (hnc : ¬ ∀ x y : ↥H, x * y = y * x) : Nat.card ↥H ∣ 168 := by
  have hstab : H ≤ n24Stab2 := by
    apply n24_index_two H n24Stab2 hs hnc
    intro x hxH y hyH hx hy
    have hxswap : img x T₁ = T₂ ∧ img x T₂ = T₁ := by
      rcases MW_le_pairStab (hH hxH) with h | h
      · exact absurd h hx
      · exact h
    have hyswap : img y T₁ = T₂ ∧ img y T₂ = T₁ := by
      rcases MW_le_pairStab (hH hyH) with h | h
      · exact absurd h hy
      · exact h
    exact ⟨by rw [img_mul, hyswap.1, hxswap.2], by rw [img_mul, hyswap.2, hxswap.1]⟩
  obtain ⟨ρ₁, ρ₂, htriv⟩ := n24_homs_of_stab2 H hstab
  exact n24_two_homs H hs ρ₁ ρ₂ htriv

end CFSG.OddStandard.HigherRank.YamadaG23
