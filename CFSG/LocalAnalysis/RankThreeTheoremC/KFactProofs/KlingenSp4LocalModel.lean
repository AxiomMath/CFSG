module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalLevi
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.AGLEmbedding.KlingenSpFour
  CFSG.Quasithin CFSG.Open

section Matrix

variable {F : Type} [Field F]

theorem sp_conj_xEl_of_coe_eq {h : StatedSp 2 F} {A B D : Matrix (Fin 2) (Fin 2) F}
    (hh : ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks A B 0 D) (hAD : Aᵀ * D = 1) (a b c : F) :
    h * xEl a b c * h⁻¹ = xEl ((A * S2 a b c * Aᵀ) 0 0) ((A * S2 a b c * Aᵀ) 0 1)
      ((A * S2 a b c * Aᵀ) 1 1) := by
  have hsymm : (A * S2 a b c * Aᵀ)ᵀ = A * S2 a b c * Aᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, S2_symm, Matrix.mul_assoc]
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_xEl, coe_xEl, hh,
    ← eq_S2_of_transpose_eq hsymm]
  exact fromBlocks_mul_siegel hAD _

theorem eq_A2_of_isUnitriangular {A : Matrix (Fin 2) (Fin 2) F} (hA : IsUnitriangular A) :
    A = A2 (A 0 1) := by
  have h10 : A 1 0 = 0 := hA.1 (show (0 : Fin 2) < 1 by decide)
  have h00 : A 0 0 = 1 := hA.2 0
  have h11 : A 1 1 = 1 := hA.2 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A2, h10, h00, h11]

theorem unipotent_conj_xEl {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) :
    ∃ s : F, ∀ a b c : F,
      g * xEl a b c * g⁻¹ = xEl (a + 2 * s * b + s ^ 2 * c) (b + s * c) c := by
  obtain ⟨A, C, hA, hC, hgA⟩ := mem_unipotent.mp hg
  obtain ⟨s, rfl⟩ : ∃ s, A = A2 s := ⟨_, eq_A2_of_isUnitriangular hA⟩
  have hdet : IsUnit (A2 s).det := hA.isUnit_det
  have hAD : (A2 s)ᵀ * (A2 s)⁻¹ᵀ = 1 := by
    rw [← transpose_mul, nonsing_inv_mul _ hdet, transpose_one]
  refine ⟨s, fun a b c => ?_⟩
  rw [sp_conj_xEl_of_coe_eq (A := A2 s) (B := A2 s * C) (D := (A2 s)⁻¹ᵀ) hgA hAD,
    A2_mul_S2_mul_transpose]
  simp [S2]

theorem eEl_conj_xEl (s t u a b c : F) :
    eEl s t u * xEl a b c * (eEl s t u)⁻¹ =
      xEl (a + 2 * s * b + s ^ 2 * c) (b + s * c) c := by
  have hAD : (A2 s)ᵀ * (A2 s)⁻¹ᵀ = 1 := by
    rw [← transpose_mul, nonsing_inv_mul _ (A2_isUnit s), transpose_one]
  rw [sp_conj_xEl_of_coe_eq (A := A2 s) (B := A2 s * C2 u t) (D := (A2 s)⁻¹ᵀ)
    (coe_eEl s t u) hAD, A2_mul_S2_mul_transpose]
  simp [S2]

theorem unipotent_eq_xEl {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F)
    (h2 : (2 : F) ≠ 0)
    (hs : ∀ a b c : F, g * xEl a b c * g⁻¹ = xEl a b c) :
    ∃ a b c : F, g = xEl a b c := by
  obtain ⟨A, C, hA, hC, hgA⟩ := mem_unipotent.mp hg
  obtain ⟨s, rfl⟩ : ∃ s, A = A2 s := ⟨_, eq_A2_of_isUnitriangular hA⟩
  have hdet : IsUnit (A2 s).det := hA.isUnit_det
  have hAD : (A2 s)ᵀ * (A2 s)⁻¹ᵀ = 1 := by
    rw [← transpose_mul, nonsing_inv_mul _ hdet, transpose_one]
  have h1 := hs 0 1 0
  rw [sp_conj_xEl_of_coe_eq (A := A2 s) (B := A2 s * C) (D := (A2 s)⁻¹ᵀ) hgA hAD,
    A2_mul_S2_mul_transpose] at h1
  have h3 : (0 : F) + 2 * s * 1 + s ^ 2 * 0 = 0 := (xEl_inj h1).1
  have h4 : s = 0 := by
    have : (2 : F) * s = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left h2
  refine ⟨C 0 0, C 0 1, C 1 1, Subtype.ext (Units.ext ?_)⟩
  rw [hgA, coe_xEl, ← eq_S2_of_transpose_eq hC, h4, A2_zero]
  simp [blockMat]

end Matrix

section Center

variable (p : ℕ) [Fact p.Prime]

@[expose] noncomputable def zS : Subgroup (PSp4 p) where
  carrier := {g | ∃ a : ZMod p, g = (xS p).x a 0 0}
  one_mem' := ⟨0, (xS p).x_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
    exact ⟨a + a', by rw [(xS p).x_mul]; exact (xS p).x_congr rfl (by ring) (by ring)⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [(xS p).x_inv]; exact (xS p).x_congr rfl (by ring) (by ring)⟩

theorem card_zS : Nat.card (zS p) = p := by
  have hinj : Function.Injective (fun a : ZMod p => (xS p).x a 0 0) := fun a a' h =>
    ((xS p).x_inj _ _ _ _ _ _ h).1
  rw [CFSG.AGLEmbedding.KlingenSpFour.card_eq_of_mem_iff_range (zS p) _ hinj
    (fun g => Iff.rfl), Nat.card_zmod]

variable {p} in
theorem xS_mem_projUnipotent (a b c : ZMod p) :
    (xS p).x a b c ∈ projUnipotent 2 (ZMod p) :=
  Subgroup.mem_map.mpr ⟨xEl a b c, xEl_mem_unipotent a b c, rfl⟩

variable {p} in
theorem U_le_projUnipotent : (xS p).U ≤ projUnipotent 2 (ZMod p) := by
  rintro _ ⟨a, b, c, rfl⟩
  exact xS_mem_projUnipotent a b c

theorem centerOf_projUnipotent (hp2 : p ≠ 2) :
    centerOf (projUnipotent 2 (ZMod p)) = zS p := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h2)
  ext z
  constructor
  · rintro ⟨hzT, hzC⟩
    have hzC := Subgroup.mem_centralizer_iff.mp hzC
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hzT
    have hcomm : ∀ a b c : ZMod p, u * xEl a b c * u⁻¹ = xEl a b c := by
      intro a b c
      have h := hzC _ (xS_mem_projUnipotent a b c)
      refine proj_injOn_unipotent (r := 2) (by norm_num)
        ((unipotent 2 (ZMod p)).mul_mem ((unipotent 2 (ZMod p)).mul_mem hu
          (xEl_mem_unipotent a b c)) ((unipotent 2 (ZMod p)).inv_mem hu))
        (xEl_mem_unipotent a b c) ?_
      rw [map_mul, map_mul, map_inv]
      have h' : proj 2 (ZMod p) (xEl a b c) * proj 2 (ZMod p) u =
          proj 2 (ZMod p) u * proj 2 (ZMod p) (xEl a b c) := h
      rw [← h', mul_inv_cancel_right]
    obtain ⟨a, b, c, rfl⟩ := unipotent_eq_xEl hu h2 hcomm
    have he : proj 2 (ZMod p) (eEl 1 0 0) ∈ projUnipotent 2 (ZMod p) :=
      Subgroup.mem_map.mpr ⟨eEl 1 0 0, eEl_mem_unipotent 1 0 0, rfl⟩
    have h := hzC _ he
    have h' : proj 2 (ZMod p) (eEl 1 0 0) * proj 2 (ZMod p) (xEl a b c) =
        proj 2 (ZMod p) (xEl a b c) * proj 2 (ZMod p) (eEl 1 0 0) := h
    have h3 : eEl 1 0 0 * xEl a b c * (eEl 1 0 0)⁻¹ = xEl a b c := by
      refine proj_injOn_unipotent (r := 2) (by norm_num)
        ((unipotent 2 (ZMod p)).mul_mem ((unipotent 2 (ZMod p)).mul_mem (eEl_mem_unipotent 1 0 0)
          (xEl_mem_unipotent a b c)) ((unipotent 2 (ZMod p)).inv_mem (eEl_mem_unipotent 1 0 0)))
        (xEl_mem_unipotent a b c) ?_
      rw [map_mul, map_mul, map_inv, h', mul_inv_cancel_right]
    rw [eEl_conj_xEl] at h3
    obtain ⟨h4, h5, -⟩ := xEl_inj h3
    have hc : c = 0 := by
      have : (1 : ZMod p) * c = 0 := by linear_combination h5
      simpa using this
    have hb : b = 0 := by
      have : (2 : ZMod p) * b = 0 := by
        subst hc
        linear_combination h4
      exact (mul_eq_zero.mp this).resolve_left h2
    exact ⟨a, by rw [hb, hc]; rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨xS_mem_projUnipotent a 0 0, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨s, hs⟩ := unipotent_conj_xEl hu
    have h1 := hs a 0 0
    have h2' : u * xEl a 0 0 * u⁻¹ = xEl a 0 0 := by
      rw [h1]; congr 1 <;> ring
    rw [xS_x, ← map_mul, ← map_mul]
    congr 1
    rw [← mul_inv_eq_iff_eq_mul.mp h2']

theorem card_projUnipotent_zmod : Nat.card (projUnipotent 2 (ZMod p)) = p ^ 4 := by
  rw [card_projUnipotent (by norm_num), Nat.card_zmod]
  norm_num

theorem card_centerOf_projUnipotent (hp2 : p ≠ 2) :
    Nat.card (centerOf (projUnipotent 2 (ZMod p))) = p := by
  rw [centerOf_projUnipotent p hp2, card_zS]

theorem eq_xS_of_isElemAbelian (hp2 : p ≠ 2) {B : Subgroup (PSp4 p)}
    (hBT : B ≤ projUnipotent 2 (ZMod p)) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 3) :
    B = (xS p).U :=
  eq_of_abelian_of_card_center (card_projUnipotent_zmod p) (card_centerOf_projUnipotent p hp2)
    U_le_projUnipotent hBT (xS p).card_U hBc
    (fun _ ha _ hb => (xS p).isElemAbelian_U.comm ha hb) (fun _ ha _ hb => hB.comm ha hb)

end Center

section Parabolic

variable (p : ℕ) [Fact p.Prime]

theorem projStabilizer_le_normalizer_xS :
    projStabilizer 2 (ZMod p) (flag 2 (ZMod p) 2) ≤
      Subgroup.normalizer ((xS p).U : Set (PSp4 p)) := by
  have hfwd : ∀ y ∈ projStabilizer 2 (ZMod p) (flag 2 (ZMod p) 2), ∀ n ∈ (xS p).U,
      y * n * y⁻¹ ∈ (xS p).U := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨a, b, c, rfl⟩
    obtain ⟨a', b', c', hab⟩ := stabilizer_conj_xEl hh a b c
    refine ⟨a', b', c', ?_⟩
    show _ = proj 2 (ZMod p) (xEl a' b' c')
    rw [← hab]
    simp only [map_mul, map_inv]
    rfl
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hfwd y hy n hn, fun hn => ?_⟩
  have := hfwd y⁻¹ (Subgroup.inv_mem _ hy) _ hn
  simpa [mul_assoc] using this

theorem normalizer_xS (hp2 : p ≠ 2) :
    Subgroup.normalizer ((xS p).U : Set (PSp4 p)) =
      projStabilizer 2 (ZMod p) (flag 2 (ZMod p) 2) := by
  have hcoatom : IsCoatom (projStabilizer 2 (ZMod p) (flag 2 (ZMod p) 2)) :=
    isCoatom_projStabilizer_flag (r := 2) (d := 2) (by norm_num) le_rfl
  rcases hcoatom.le_iff.mp (projStabilizer_le_normalizer_xS p) with h | h
  swap
  · exact h
  · exfalso
    have hnormal : (xS p).U.Normal := Subgroup.normalizer_eq_top_iff.mp h
    have hp : p.Prime := Fact.out
    have hsimple : IsSimpleGroup (PSp4 p) := by
      refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod p) 2
        (by norm_num) ?_
      rw [Nat.card_zmod]
      rcases Nat.lt_or_ge p 4 with h4 | h4
      · have hp3 : p = 3 := by
          have := hp.two_le
          omega
        exact Or.inr (Or.inl ⟨hp3, le_rfl⟩)
      · exact Or.inl (Or.inr h4)
    rcases hsimple.eq_bot_or_eq_top_of_normal (xS p).U with hU | hU
    · have h1 : Nat.card (xS p).U = 1 := by rw [hU]; exact Subgroup.card_bot
      rw [(xS p).card_U] at h1
      have := Nat.one_lt_pow (by norm_num : (3 : ℕ) ≠ 0) hp.one_lt
      omega
    · have hT : projUnipotent 2 (ZMod p) = ⊤ := eq_top_iff.mpr (hU ▸ U_le_projUnipotent)
      have h1 := card_projUnipotent_zmod p
      rw [hT, Subgroup.card_top, ← (Subgroup.card_top (G := PSp4 p)), ← hU, (xS p).card_U] at h1
      have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 3 < 4)
      omega

theorem isCoatom_normalizer_xS (hp2 : p ≠ 2) :
    IsCoatom (Subgroup.normalizer ((xS p).U : Set (PSp4 p))) := by
  rw [normalizer_xS p hp2]
  exact isCoatom_projStabilizer_flag (r := 2) (d := 2) (by norm_num) le_rfl

end Parabolic

theorem siegelRadicalData_psp4 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    SiegelRadicalData p (⊤ : Subgroup (PSp4 p)) (projUnipotent 2 (ZMod p)) (xS p).U where
  T_le := le_top
  U_le := U_le_projUnipotent
  elem := (xS p).isElemAbelian_U
  card_U := (xS p).card_U
  card_T := card_projUnipotent_zmod p
  card_center := card_centerOf_projUnipotent p hp2
  unique := fun _ hBT hB hBc => eq_xS_of_isElemAbelian p hp2 hBT hB hBc
  coatom := fun M hM _ => by
    rw [inf_top_eq] at hM ⊢
    exact ((isCoatom_normalizer_xS p hp2).le_iff.mp hM).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
