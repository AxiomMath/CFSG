module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Mat
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41R

open Subgroup Matrix CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Std

variable {F : Type} [Field F]

@[expose] def tz (F : Type) [Field F] : SpecialLinearGroup (Fin 3) F :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

theorem coe_tz : ((tz F : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl

theorem tz_mul_tz : tz F * tz F = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_tz, Matrix.mul_apply, Fin.sum_univ_three]

theorem tz_inv : (tz F)⁻¹ = tz F := inv_eq_of_mul_eq_one_right tz_mul_tz

theorem tz_ne_one (h2 : (2 : F) ≠ 0) : tz F ≠ 1 := by
  intro h
  have := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [coe_tz] at this
  apply h2
  linear_combination -this

@[expose] def X₀ (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 3) F) :=
  (Subgroup.center (Heis F)).map heisSL

theorem mem_X₀ {A : SpecialLinearGroup (Fin 3) F} :
    A ∈ X₀ F ↔ ∃ c : F, heisSL (⟨0, 0, c⟩ : Heis F) = A := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨ha, hb⟩ := Heis.mem_center.mp hh
    refine ⟨h.c, ?_⟩
    have : h = ⟨0, 0, h.c⟩ := by ext <;> simp [ha, hb]
    rw [← this]
  · rintro ⟨c, rfl⟩
    exact ⟨_, Heis.mem_center.mpr ⟨rfl, rfl⟩, rfl⟩

theorem heisSL_mem_X₀ (c : F) : heisSL (⟨0, 0, c⟩ : Heis F) ∈ X₀ F := mem_X₀.mpr ⟨c, rfl⟩

theorem X₀_le_unitriangular : X₀ F ≤ unitriangular 3 F := by
  rintro _ ⟨h, -, rfl⟩
  exact heisSL_mem_unitriangular h

theorem tz_conj_heis (x : Heis F) :
    tz F * heisSL x * (tz F)⁻¹ * heisSL x = heisSL (⟨0, 0, 2 * x.c - x.a * x.b⟩ : Heis F) := by
  rw [tz_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_tz, coe_heisSL, heisMat, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem X₀_le_centralizer_tz :
    X₀ F ≤ centralizer ({tz F} : Set (SpecialLinearGroup (Fin 3) F)) := by
  intro A hA
  obtain ⟨c, rfl⟩ := mem_X₀.mp hA
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_tz, coe_heisSL, heisMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem unitriangular_eq_map : unitriangular 3 F = (⊤ : Subgroup (Heis F)).map heisSL := by
  ext A
  constructor
  · intro hA
    obtain ⟨x, hx⟩ := exists_heisSL_of_mem_unitriangular hA
    exact ⟨x, Subgroup.mem_top _, hx⟩
  · rintro ⟨x, -, rfl⟩
    exact heisSL_mem_unitriangular x

theorem commutator_unitriangular : ⁅unitriangular 3 F, unitriangular 3 F⁆ = X₀ F := by
  rw [unitriangular_eq_map, ← Subgroup.map_commutator, Heis.commutator_eq_center]
  rfl

theorem unitriangular_le_centralizer :
    unitriangular 3 F ≤ centralizer ((X₀ F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) := by
  intro u hu
  rw [mem_centralizer_iff]
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨y, rfl⟩ := exists_heisSL_of_mem_unitriangular hu
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hh y]

theorem centralizer_le_upperTriangular :
    centralizer ((X₀ F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) ≤ upperTriangular 3 F := by
  intro g hg
  have h := mem_centralizer_iff.mp hg _ (heisSL_mem_X₀ (1 : F))
  have hmat : (g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 0, 1⟩ : Heis F) =
      heisMat (⟨0, 0, 1⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h
    simpa [coe_heisSL] using this.symm
  obtain ⟨h10, h20, h21⟩ := lower_entries_zero g 1 hmat
  exact mem_upperTriangular_of_lower_entries h10 h20 h21

theorem centralizer_le_normalizer :
    centralizer ((X₀ F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) ≤
      normalizer ((unitriangular 3 F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
        Set (SpecialLinearGroup (Fin 3) F)) :=
  centralizer_le_upperTriangular.trans normalizer_unitriangular.ge

theorem rgood_std [Finite F] {p n : ℕ} (hp : p.Prime) [CharP F p] (hF : Nat.card F = p ^ n) :
    RGood p n (tz F) (X₀ F) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) p (n := 3) (by norm_num)
  have hRp : IsPGroup p (unitriangular 3 F) := by
    rw [← hP]
    exact P.isPGroup'
  refine ⟨unitriangular 3 F, ?_, hRp, X₀_le_unitriangular, unitriangular_le_centralizer, ?_,
    ?_, commutator_unitriangular.ge, ?_, ?_⟩
  · apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p unitriangular_le_centralizer
        centralizer_le_normalizer hRp
    · have hQ := CFSG.LieType.BorelTits.pCoreOf_isPGroup p
        (centralizer ((X₀ F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
          Set (SpecialLinearGroup (Fin 3) F)))
      have hQC := CFSG.LieType.BorelTits.pCoreOf_le p
        (centralizer ((X₀ F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
          Set (SpecialLinearGroup (Fin 3) F)))
      have hQN : CFSG.Open.pCoreOf p (centralizer ((X₀ F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
          Set (SpecialLinearGroup (Fin 3) F))) ≤
          normalizer (P : Set (SpecialLinearGroup (Fin 3) F)) := by
        have hPset : (P : Set (SpecialLinearGroup (Fin 3) F)) =
            (unitriangular 3 F : Set (SpecialLinearGroup (Fin 3) F)) :=
          congrArg (fun T : Subgroup (SpecialLinearGroup (Fin 3) F) =>
            (T : Set (SpecialLinearGroup (Fin 3) F))) hP
        rw [hPset]
        exact hQC.trans centralizer_le_normalizer
      have := hQ.inf_normalizer_sylow P
      rw [inf_eq_left.mpr hQN] at this
      exact this.le.trans (inf_le_right.trans hP.le)
  · rw [card_unitriangular, hF]
  · intro r hr hc
    obtain ⟨y, rfl⟩ := exists_heisSL_of_mem_unitriangular hr
    refine ⟨y, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    have := hc (heisSL g) (heisSL_mem_unitriangular g)
    rw [← map_mul, ← map_mul] at this
    exact (heisSL_injective this).symm
  · intro r hr s hs
    rw [← commutator_unitriangular]
    exact Subgroup.commutator_mem_commutator hr hs
  · intro r hr
    obtain ⟨y, rfl⟩ := exists_heisSL_of_mem_unitriangular hr
    rw [tz_conj_heis]
    exact heisSL_mem_X₀ _

end Std

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41R
