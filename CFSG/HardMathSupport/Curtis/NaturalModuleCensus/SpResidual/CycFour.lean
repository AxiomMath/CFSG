module

public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.CycFour

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)

def lam : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* StatedSp 4 (ZMod 2) :=
  leviSp.comp Matrix.SpecialLinearGroup.toGL

theorem lam_injective : Function.Injective lam := by
  intro g h hgh
  have h1 := congrArg (fun z : StatedSp 4 (ZMod 2) =>
    (((z : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)))) hgh
  simp only [lam, MonoidHom.comp_apply, coe_leviSp] at h1
  have h2 := congrArg Matrix.toBlocks₁₁ h1
  simp only [Matrix.toBlocks_fromBlocks₁₁] at h2
  exact Matrix.SpecialLinearGroup.toGL_injective (Units.ext h2)

theorem lam_mem_stabilizer (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    lam g ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer 4 (ZMod 2) {4} := by
  have key : ∀ A : GL (Fin 4) (ZMod 2), ∀ v ∈ SymplecticFlag.flag 4 (ZMod 2) 4,
      (((leviSp A : StatedSp 4 (ZMod 2)) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v ∈ SymplecticFlag.flag 4 (ZMod 2) 4 := by
    intro A v hv
    rw [SymplecticFlag.mem_flag_of_le le_rfl, SymplecticFlag.mem_isoFlag] at hv ⊢
    refine ⟨fun j => ?_, fun j hj => absurd j.2 (by omega)⟩
    rw [coe_leviSp, Matrix.fromBlocks_mulVec]
    have : (v ∘ Sum.inr) = 0 := funext hv.1
    simp [this]
  rw [SymplecticHigher.mem_flagStabilizer]
  intro i hi
  rw [Set.mem_singleton_iff.mp hi]
  refine SymplecticFlag.mem_stabilizer_of_mulVec_mem (key _) ?_
  have : (lam g)⁻¹ = lam g⁻¹ := (map_inv lam g).symm
  rw [this]
  exact key _

def x : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by
    rw [Matrix.det_succ_row_zero]; decide +kernel⟩

def y : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by
    rw [Matrix.det_succ_row_zero]; decide +kernel⟩

theorem x_pow : x ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two]
  show _ * _ * _ = (1 : Matrix _ _ _)
  decide +kernel

theorem y_pow : y ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two]
  show _ * _ * _ = (1 : Matrix _ _ _)
  decide +kernel

theorem xy_comm : x * y = y * x := by
  apply Subtype.ext
  show (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) * y = y * x
  decide +kernel

theorem x_ne_one : x ≠ 1 := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
    (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this; decide +kernel

theorem xx_ne_one : x * x ≠ 1 := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
    (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this; decide +kernel

theorem x_ne_xx : x ≠ x * x := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
    (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this; decide +kernel

theorem y_ne_one : y ≠ 1 := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
    (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this; decide +kernel

theorem y_ne_x : y ≠ x := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
    (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this; decide +kernel

theorem y_ne_xx : y ≠ x * x := fun h => by
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
    (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  revert this; decide +kernel

theorem false_of_cyc_lagrangian_four
    (hcyc : CFSG.AGLEmbedding.CycPerfect 3
      (SymplecticHigher.flagStabilizer 4 (ZMod 2) {4})) : False := by
  classical
  set P : Subgroup (StatedSp 4 (ZMod 2)) := lam.range with hP
  have hPJ : P ≤ SymplecticHigher.flagStabilizer 4 (ZMod 2) {4} := by
    rintro _ ⟨g, rfl⟩
    exact lam_mem_stabilizer g
  have hPperf : ⁅P, P⁆ = P := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
    have htop : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))), ⊤⁆ = ⊤ :=
      Group.IsPerfect.commutator_eq_top
    rw [hP, MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  set a : StatedSp 4 (ZMod 2) := lam x with ha
  set b : StatedSp 4 (ZMod 2) := lam y with hb
  clear_value a b
  have hcomm : Commute a b := by
    show a * b = b * a
    rw [ha, hb, ← map_mul, ← map_mul, xy_comm]
  have hapow : a ^ 3 = 1 := by rw [ha, ← map_pow, x_pow, map_one]
  have hbpow : b ^ 3 = 1 := by rw [hb, ← map_pow, y_pow, map_one]
  have hS : ({a, b} : Set (StatedSp 4 (ZMod 2))).Pairwise Commute := by
    intro u hu v hv huv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · exact hcomm
    · exact hcomm.symm
    · exact absurd rfl huv
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (StatedSp 4 (ZMod 2)), Q = Subgroup.closure {a, b} :=
    ⟨_, rfl⟩
  have hQ3 : ∀ g ∈ Q, g ^ 3 = 1 := fun g hg =>
    CFSG.AGLEmbedding.ParabHub.pow_eq_one_of_mem_closure hS
      (fun u hu => by rcases hu with rfl | rfl <;> assumption) (hQ ▸ hg)
  have haQ : a ∈ Q := hQ ▸ Subgroup.subset_closure (by simp)
  have hbQ : b ∈ Q := hQ ▸ Subgroup.subset_closure (by simp)
  have hQP : Q ≤ P := by
    rw [hQ]
    refine (Subgroup.closure_le _).2 ?_
    rintro u (rfl | rfl)
    · exact ⟨x, ha.symm⟩
    · exact ⟨y, hb.symm⟩
  have hpg : IsPGroup 3 Q := fun g => ⟨1, Subtype.ext (by simp [hQ3 g g.2])⟩
  have hcy : IsCyclic Q := hcyc P hPJ hPperf Q hQP hpg
  have : Finite Q := inferInstance
  have : Fintype Q := Fintype.ofFinite Q
  have hxxQ : a * a ∈ Q := Q.mul_mem haQ haQ
  have hle := IsCyclic.card_pow_eq_one_le (α := Q) (n := 3) (by norm_num)
  have hsub : ({1, ⟨a, haQ⟩, ⟨a * a, hxxQ⟩, ⟨b, hbQ⟩} : Finset Q) ⊆
      ({g : Q | g ^ 3 = 1} : Finset Q) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext (hQ3 g g.2)
  have hc := Finset.card_le_card hsub
  have hinj := lam_injective
  have n1 : ((1 : Q)) ≠ ⟨a, haQ⟩ := fun h => x_ne_one (hinj (by
    have := congrArg Subtype.val h; simpa [ha] using this.symm))
  have n2 : ((1 : Q)) ≠ ⟨a * a, hxxQ⟩ := fun h => xx_ne_one (hinj (by
    have := congrArg Subtype.val h; simpa [ha] using this.symm))
  have n3 : ((1 : Q)) ≠ ⟨b, hbQ⟩ := fun h => y_ne_one (hinj (by
    have := congrArg Subtype.val h; simpa [hb] using this.symm))
  have n4 : (⟨a, haQ⟩ : Q) ≠ ⟨a * a, hxxQ⟩ := fun h => x_ne_xx (hinj (by
    have := congrArg Subtype.val h; simpa [ha] using this))
  have n5 : (⟨a, haQ⟩ : Q) ≠ ⟨b, hbQ⟩ := fun h => y_ne_x (hinj (by
    have := congrArg Subtype.val h; simpa [ha, hb] using this.symm))
  have n6 : (⟨a * a, hxxQ⟩ : Q) ≠ ⟨b, hbQ⟩ := fun h => y_ne_xx (hinj (by
    have := congrArg Subtype.val h; simpa [ha, hb] using this.symm))
  rw [Finset.card_insert_of_notMem (by simp [n1, n2, n3]),
    Finset.card_insert_of_notMem (by simp [n4, n5]),
    Finset.card_insert_of_notMem (by simp [n6]), Finset.card_singleton] at hc
  omega

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.CycFour
