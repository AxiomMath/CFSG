module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z4
public import CFSG.ClassicalInvolution.Asc77.AscCX9X3
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm kappa_longBlock0 kappa_longBlock1)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (blockMat_four_zero blockMat_four_two)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {F : Type} [Field F]

theorem blk0_mulVec {L : Type} [Field L] (B : Matrix (Fin 2) (Fin 2) L) (φ : L →+* K)
    {v : Fin 4 → K} (h0 : v 0 = 0) (h1 : v 1 = 0) : (blockMat 4 0 B).map φ *ᵥ v = v := by
  rw [blockMat_four_zero]
  funext a
  fin_cases a <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0, h1]

theorem blk2_mulVec {L : Type} [Field L] (B : Matrix (Fin 2) (Fin 2) L) (φ : L →+* K)
    {v : Fin 4 → K} (h2 : v 2 = 0) (h3 : v 3 = 0) : (blockMat 4 2 B).map φ *ᵥ v = v := by
  rw [blockMat_four_two]
  funext a
  fin_cases a <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h2, h3]

namespace DescData

variable (D : DescData (unitaryInvolution K p f) F)

theorem conj_blk0_single {L : Type} [Field L] (B : Matrix (Fin 2) (Fin 2) L) (φ : L →+* K)
    {l : Fin 4} (hl : l = 2 ∨ l = 3) :
    (descH (unitaryInvolution K p f) D.c D.t D.m D.n * (blockMat 4 0 B).map φ *
      descHInv (unitaryInvolution K p f) D.c D.t D.m D.n) *ᵥ (Pi.single l 1 : Fin 4 → K) =
      Pi.single l 1 := by
  have hv : (blockMat 4 0 B).map φ *ᵥ (descHInv (unitaryInvolution K p f) D.c D.t D.m D.n *ᵥ
      (Pi.single l 1 : Fin 4 → K)) =
      descHInv (unitaryInvolution K p f) D.c D.t D.m D.n *ᵥ (Pi.single l 1 : Fin 4 → K) := by
    apply blk0_mulVec
    · rcases hl with rfl | rfl <;> simp [descHInv]
    · rcases hl with rfl | rfl <;> simp [descHInv]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec,
    descH_mul_inv D.hc D.ht D.hm D.hn, Matrix.one_mulVec]

theorem conj_blk2_single {L : Type} [Field L] (B : Matrix (Fin 2) (Fin 2) L) (φ : L →+* K)
    {l : Fin 4} (hl : l = 0 ∨ l = 1) :
    (descH (unitaryInvolution K p f) D.c D.t D.m D.n * (blockMat 4 2 B).map φ *
      descHInv (unitaryInvolution K p f) D.c D.t D.m D.n) *ᵥ (Pi.single l 1 : Fin 4 → K) =
      Pi.single l 1 := by
  have hv : (blockMat 4 2 B).map φ *ᵥ (descHInv (unitaryInvolution K p f) D.c D.t D.m D.n *ᵥ
      (Pi.single l 1 : Fin 4 → K)) =
      descHInv (unitaryInvolution K p f) D.c D.t D.m D.n *ᵥ (Pi.single l 1 : Fin 4 → K) := by
    apply blk2_mulVec
    · rcases hl with rfl | rfl <;> simp [descHInv]
    · rcases hl with rfl | rfl <;> simp [descHInv]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec,
    descH_mul_inv D.hc D.ht D.hm D.hn, Matrix.one_mulVec]

theorem kU_longBlock0_mem (b : SL(2, F)) :
    D.kU (longBlock F 2 0 b) ∈ (blockEmb K p f 4 2 0 (by norm_num)).range := by
  refine mem_range_blockEmb_of_smul_single _ _ fun l hl => ?_
  have hl' : l = 2 ∨ l = 3 := by
    fin_cases l <;> simp_all
  rw [suMat_smul, D.suMat_kU, kap1, kappa_longBlock0]
  exact D.conj_blk0_single _ D.ι hl'

theorem kU_longBlock1_mem (b : SL(2, F)) :
    D.kU (longBlock F 2 1 b) ∈ (blockEmb K p f 4 2 2 (by norm_num)).range := by
  refine mem_range_blockEmb_of_smul_single _ _ fun l hl => ?_
  have hl' : l = 0 ∨ l = 1 := by
    fin_cases l <;> simp_all
  rw [suMat_smul, D.suMat_kU, kap1, kappa_longBlock1]
  exact D.conj_blk2_single _ D.ι hl'

@[expose] def iotaEquiv : F ≃+* fixedSubfield K p f :=
  RingEquiv.ofBijective
    (D.ι.codRestrict (fixedSubfield K p f) fun a => mem_fixedSubfield.mpr (D.fix a))
    ⟨fun a b h => D.ι.injective (congrArg Subtype.val h), fun b => by
      obtain ⟨a, ha⟩ := D.onto b.1 (mem_fixedSubfield.mp b.2)
      exact ⟨a, Subtype.ext ha⟩⟩

end DescData

theorem card_su2 (hK : Nat.card K = (p ^ f) ^ 2) (ε : F ≃+* fixedSubfield K p f) :
    Nat.card (Su K p f 2) = Nat.card SL(2, F) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
  rw [← Nat.card_congr e.toEquiv]
  exact (Nat.card_congr
    { toFun := Matrix.SpecialLinearGroup.map ε.toRingHom
      invFun := Matrix.SpecialLinearGroup.map ε.symm.toRingHom
      left_inv := fun x => Subtype.ext (by ext i j; simp)
      right_inv := fun x => Subtype.ext (by ext i j; simp) }).symm

theorem card_range_of_injective {G H : Type} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) : Nat.card φ.range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

theorem blockEmb_injective' {i : ℕ} (h : i + 2 ≤ 4) :
    Function.Injective (blockEmb K p f 4 2 i h) := by
  intro A B hAB
  apply suMat_injective
  have h1 : blockMat 4 i (suMat A) = blockMat 4 i (suMat B) := congrArg suMat hAB
  exact blockMat_injective h h1

namespace DescData

variable (D : DescData (unitaryInvolution K p f) F)

theorem map_kU_longRoot0 (hK : Nat.card K = (p ^ f) ^ 2) :
    (longRootSp2 F 2 0).map D.kU = (blockEmb K p f 4 2 0 (by norm_num)).range := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact D.kU_longBlock0_mem b
  · rw [Subgroup.card_map_of_injective D.kU_injective, longRootSp2,
      card_range_of_injective (longBlock_injective 0),
      card_range_of_injective (blockEmb_injective' _), card_su2 hK D.iotaEquiv]

theorem map_kU_longRoot1 (hK : Nat.card K = (p ^ f) ^ 2) :
    (longRootSp2 F 2 1).map D.kU = (blockEmb K p f 4 2 2 (by norm_num)).range := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact D.kU_longBlock1_mem b
  · rw [Subgroup.card_map_of_injective D.kU_injective, longRootSp2,
      card_range_of_injective (longBlock_injective 1),
      card_range_of_injective (blockEmb_injective' _), card_su2 hK D.iotaEquiv]

theorem spU_perfect [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅(spU (spForm D.m D.n) : Subgroup (Su K p f 4)),
      (spU (spForm D.m D.n) : Subgroup (Su K p f 4))⁆ =
      (spU (spForm D.m D.n) : Subgroup (Su K p f 4)) := by
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inl (Or.inr h4))).1
  rw [← D.range_kU, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact hperf.commutator_eq_top

theorem perfRes_fix_eq [Finite F] (h4 : 4 ≤ Nat.card F) (hK : Nat.card K = (p ^ f) ^ 2)
    {Y : Type} [Group Y] [Finite Y] (θ : Su K p f 4 →* Y) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (α : Su K p f 4 →* Su K p f 4)
    (hα : ∀ x, suMat (α x) =
      spForm D.m D.n * (suMat x).map (unitaryInvolution K p f) * spFormInv D.m D.n)
    (β : MulAut Y) (hβ : ∀ x, β (θ x) = θ (α x)) :
    Goldschmidt75.perfRes (fixSubgroup β) = (spU (spForm D.m D.n)).map θ := by
  apply le_antisymm
  · have hfix : fixSubgroup β ≤ (simU (spForm D.m D.n)).map θ := by
      intro y hy
      obtain ⟨x, rfl⟩ := hθ y
      have hy' : β (θ x) = θ x := hy
      rw [hβ] at hy'
      exact Subgroup.mem_map_of_mem θ (mem_simU_of_fix
        (isUnitaryInvolution_unitaryInvolution hK) θ hker α D.hm D.hn hα hy')
    calc Goldschmidt75.perfRes (fixSubgroup β)
        ≤ Goldschmidt75.perfRes ((simU (spForm D.m D.n)).map θ) :=
          Goldschmidt75.le_perfRes ((Goldschmidt75.perfRes_le _).trans hfix)
            (Goldschmidt75.commutator_perfRes _)
      _ = (Goldschmidt75.perfRes (simU (spForm D.m D.n))).map θ :=
          (Goldschmidt75.map_perfRes θ _).symm
      _ ≤ (spU (spForm D.m D.n)).map θ := by
          refine Subgroup.map_mono ?_
          calc Goldschmidt75.perfRes (simU (spForm D.m D.n))
              = ⁅Goldschmidt75.perfRes (simU (spForm D.m D.n)),
                  Goldschmidt75.perfRes (simU (spForm D.m D.n))⁆ :=
                (Goldschmidt75.commutator_perfRes _).symm
            _ ≤ ⁅simU (spForm D.m D.n), simU (spForm D.m D.n)⁆ :=
                Subgroup.commutator_mono (Goldschmidt75.perfRes_le _)
                  (Goldschmidt75.perfRes_le _)
            _ ≤ spU (spForm D.m D.n) := commutator_simU_le_spU _
  · refine Goldschmidt75.le_perfRes ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      show β (θ x) = θ x
      rw [hβ, lift_eq_of_mem_spU α D.hm D.hn hα hx]
    · rw [← Subgroup.map_commutator, D.spU_perfect h4]

end DescData

end CFSG.ClassicalInvolution.Asc77.CX.MF2U
