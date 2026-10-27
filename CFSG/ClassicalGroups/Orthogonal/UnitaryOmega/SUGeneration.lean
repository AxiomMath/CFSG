module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapGen

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open Matrix CFSG.GH74.Generic.S1.SymBlocksUni
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

private theorem coe_suEquiv_apply (h : UnitaryFieldData 2 f K) (n : ℕ)
    (g : SUid (unitaryInvolution K 2 f) n) :
    (((suEquiv h n g : unitarySU 2 f K n) : GL (Fin n) K)) = (g : GL (Fin n) K) :=
  MulEquiv.subgroupCongr_apply _ g

private theorem coe_suEquiv_symm (h : UnitaryFieldData 2 f K) (n : ℕ)
    (g : unitarySU 2 f K n) :
    (((suEquiv h n).symm g : SUid (unitaryInvolution K 2 f) n) : GL (Fin n) K) =
      (g : GL (Fin n) K) :=
  MulEquiv.subgroupCongr_symm_apply _ g

private theorem coe_uniCast (h : UnitaryFieldData 2 f K) (m : ℕ)
    (g : unitarySU 2 f K m) :
    (((uniCast h m g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      blkMat (Fin.castSucc : Fin m → Fin (m + 1))
        (((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  unfold uniCast
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [coe_suEquiv_apply, coe_coe_blkEmb, coe_suEquiv_symm]

private theorem blkMat_castSucc_eq_of_mem_unitaryBlock (h : UnitaryFieldData 2 f K) (m : ℕ)
    {A : unitarySU 2 f K (m + 1)}
    (hA : A ∈ unitaryBlock h (Finset.univ.map Fin.castSuccEmb)) :
    blkMat (Fin.castSucc : Fin m → Fin (m + 1))
      (fun i j => (((A : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K)) (Fin.castSucc i) (Fin.castSucc j)) =
      ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
  classical
  set B : Matrix (Fin m) (Fin m) K := fun i j =>
    (((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
      (Fin.castSucc i) (Fin.castSucc j) with hB
  rw [mem_unitaryBlock] at hA
  have hlast_not_mem : Fin.last m ∉
      (Finset.univ.map Fin.castSuccEmb : Finset (Fin (m + 1))) := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hmem
    exact Fin.castSucc_ne_last i hi
  ext i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
  · rw [blkMat_apply_ι (ι := Fin.castSucc) (A := B) (Fin.castSucc_injective m)]
  · rw [blkMat_apply_of_not_mem_right B (Fin.castSucc a) (j := Fin.last m)
      (fun y => (Fin.castSucc_ne_last y).symm)]
    exact (hA (Fin.castSucc a) (Fin.last m) (Or.inr hlast_not_mem)).symm
  · rw [blkMat_apply_of_not_mem_left B (i := Fin.last m)
      (fun y => (Fin.castSucc_ne_last y).symm) (Fin.castSucc b)]
    exact (hA (Fin.last m) (Fin.castSucc b) (Or.inl hlast_not_mem)).symm
  · rw [blkMat_apply_of_not_mem_left B (i := Fin.last m)
      (fun y => (Fin.castSucc_ne_last y).symm) (Fin.last m)]
    exact (hA (Fin.last m) (Fin.last m) (Or.inl hlast_not_mem)).symm

private theorem exists_uniCast_eq_of_mem_unitaryBlock (h : UnitaryFieldData 2 f K) (m : ℕ)
    {A : unitarySU 2 f K (m + 1)}
    (hA : A ∈ unitaryBlock h (Finset.univ.map Fin.castSuccEmb)) :
    ∃ g : unitarySU 2 f K m, uniCast h m g = A := by
  classical
  set Am : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hAm
  set B : Matrix (Fin m) (Fin m) K := fun i j => Am (Fin.castSucc i) (Fin.castSucc j) with hB
  have hBA : blkMat (Fin.castSucc : Fin m → Fin (m + 1)) B = Am := by
    simpa only [hB, hAm] using blkMat_castSucc_eq_of_mem_unitaryBlock h m hA
  have hAunitary : (Am.map h.bar)ᵀ * Am = 1 := by
    simpa only [hAm] using ((mem_unitarySU_iff h).1 A.2).2
  have hAdet : Am.det = 1 := by
    simpa only [hAm] using ((mem_unitarySU_iff h).1 A.2).1
  have hbar_eq : (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar := by
    funext c
    rw [unitaryInvolution_apply, h.bar_apply]
  have hAunitary' : (Am.map (unitaryInvolution K 2 f))ᵀ * Am = 1 := by
    simpa only [hbar_eq] using hAunitary
  have hBunit : (B.map h.bar)ᵀ * B = 1 := by
    have hBunit' : (B.map (unitaryInvolution K 2 f))ᵀ * B = 1 := by
      apply blkMat_injective (Fin.castSucc_injective m)
      change blkMat (Fin.castSucc : Fin m → Fin (m + 1))
        (conjTr (unitaryInvolution K 2 f) B * B) =
        blkMat (Fin.castSucc : Fin m → Fin (m + 1)) (1 : Matrix (Fin m) (Fin m) K)
      rw [blkMat_mul (Fin.castSucc_injective m),
        ← conjTr_blkMat (unitaryInvolution K 2 f) B, hBA, blkMat_one]
      exact hAunitary'
    simpa only [hbar_eq] using hBunit'
  have hBdet : B.det = 1 := by
    rw [← det_blkMat (Fin.castSucc_injective m) B, hBA, hAdet]
  let BS : Matrix.SpecialLinearGroup (Fin m) K := ⟨B, hBdet⟩
  refine ⟨ofSL h BS hBunit, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_uniCast, coe_ofSL, ← hAm]
  change blkMat (Fin.castSucc : Fin m → Fin (m + 1)) B = Am
  exact hBA

theorem unitaryBlock_castSucc_le_range_uniCast (h : UnitaryFieldData 2 f K) (m : ℕ) :
    unitaryBlock h (Finset.univ.map Fin.castSuccEmb) ≤ (uniCast h m).range := by
  rintro A hA
  obtain ⟨g, rfl⟩ := exists_uniCast_eq_of_mem_unitaryBlock h m hA
  exact ⟨g, rfl⟩

theorem eq_of_eqOn_uniCast_permSUHom (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 4 ≤ m)
    {M : Type*} [Monoid M] {φ₁ φ₂ : unitarySU 2 f K (m + 1) →* M}
    (hcast : ∀ g, φ₁ (uniCast h m g) = φ₂ (uniCast h m g))
    (hperm : ∀ σ, φ₁ (permSUHom h σ) = φ₂ (permSUHom h σ)) : φ₁ = φ₂ := by
  classical
  set L : Subgroup (unitarySU 2 f K (m + 1)) := φ₁.eqLocus φ₂ with hL
  have hpermL : ∀ σ : Equiv.Perm (Fin (m + 1)), permSU h σ ∈ L := by
    intro σ
    have hσ : permSU h σ = permSUHom h σ⁻¹ := by
      rw [permSUHom_apply, inv_inv]
    rw [hL]
    change φ₁ (permSU h σ) = φ₂ (permSU h σ)
    rw [hσ]
    exact hperm σ⁻¹
  set I₀ : Finset (Fin (m + 1)) :=
    (Finset.univ : Finset (Fin 4)).map (Fin.castLEEmb (by omega : 4 ≤ m + 1)) with hI₀
  have hI₀card : I₀.card = 4 := by
    rw [hI₀, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hI₀sub : I₀ ⊆ Finset.univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
    intro j hj
    rw [hI₀] at hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
    rw [Fin.castLEEmb_apply]
    refine Finset.mem_map.mpr ⟨⟨(i : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    rw [Fin.castSuccEmb_apply]
    apply Fin.ext
    rfl
  have hblockI₀ : unitaryBlock h I₀ ≤ L := by
    calc
      unitaryBlock h I₀ ≤ unitaryBlock h (Finset.univ.map Fin.castSuccEmb) :=
        unitaryBlock_mono h hI₀sub
      _ ≤ (uniCast h m).range := unitaryBlock_castSucc_le_range_uniCast h m
      _ ≤ L := by
        rintro _ ⟨g, rfl⟩
        rw [hL]
        change φ₁ (uniCast h m g) = φ₂ (uniCast h m g)
        exact hcast g
  refine eq_of_eqOn_unitaryBlock (h := h) (m := 4) (n := m + 1)
    (by norm_num) (by omega) ?_
  intro I hI x hx
  have hIle : unitaryBlock h I ≤ L :=
    unitaryBlock_le_of_permSU_mem (h := h) (H := L) hpermL
      (hI₀card.trans hI.symm) hblockI₀
  have hxL := hIle hx
  rw [hL] at hxL
  change φ₁ x = φ₂ x at hxL
  exact hxL

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
