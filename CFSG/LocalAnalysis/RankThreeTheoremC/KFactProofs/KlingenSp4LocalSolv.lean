module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourMat
import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.AGLEmbedding.KlingenSpFour

section Lagrangian

variable {F : Type} [Field F]

private def sv_mat (h : stabilizer 2 F (flag 2 F 2)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  (((h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

private theorem sv_mat_mul (g h : stabilizer 2 F (flag 2 F 2)) :
    sv_mat (g * h) = sv_mat g * sv_mat h := rfl

private theorem sv_mat_one : sv_mat (1 : stabilizer 2 F (flag 2 F 2)) = 1 := rfl

private theorem sv_mat_injective : Function.Injective (sv_mat (F := F)) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Units.ext h))

private theorem sv_blocks (h : stabilizer 2 F (flag 2 F 2)) :
    ∃ A B D : Matrix (Fin 2) (Fin 2) F, sv_mat h = fromBlocks A B 0 D ∧ Aᵀ * D = 1 := by
  obtain ⟨A, B, D, hM⟩ :=
    exists_fromBlocks_of_entries_inr_inl (stabilizer_flag_entry_inr_inl h.2)
  refine ⟨A, B, D, hM, ?_⟩
  have hsymp := CFSG.LieType.BorelTits.transpose_mul_mul_of_mem_statedSp (h : StatedSp 2 F).2
  rw [hM] at hsymp
  exact transpose_mul_eq_one_of_symplectic hsymp

private noncomputable def sv_blockHom :
    stabilizer 2 F (flag 2 F 2) →* Matrix (Fin 2) (Fin 2) F where
  toFun h := (sv_mat h).toBlocks₁₁
  map_one' := by
    show (sv_mat 1).toBlocks₁₁ = 1
    rw [sv_mat_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]
  map_mul' g h := by
    show (sv_mat (g * h)).toBlocks₁₁ = (sv_mat g).toBlocks₁₁ * (sv_mat h).toBlocks₁₁
    obtain ⟨A, B, D, hg, -⟩ := sv_blocks g
    obtain ⟨A', B', D', hh, -⟩ := sv_blocks h
    rw [sv_mat_mul, hg, hh, fromBlocks_multiply]
    simp

private noncomputable def sv_rho : stabilizer 2 F (flag 2 F 2) →* GL (Fin 2) F :=
  (sv_blockHom (F := F)).toHomUnits

private theorem sv_rho_val (h : stabilizer 2 F (flag 2 F 2)) :
    ((sv_rho h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (sv_mat h).toBlocks₁₁ := rfl

private theorem sv_ker_blocks {h : stabilizer 2 F (flag 2 F 2)}
    (hh : h ∈ (sv_rho (F := F)).ker) :
    ∃ B : Matrix (Fin 2) (Fin 2) F, sv_mat h = fromBlocks 1 B 0 1 := by
  obtain ⟨A, B, D, hM, hAD⟩ := sv_blocks h
  have hA : A = 1 := by
    have h1 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F))
      (MonoidHom.mem_ker.mp hh)
    simpa [sv_rho_val, hM] using h1
  subst hA
  rw [transpose_one, Matrix.one_mul] at hAD
  subst hAD
  exact ⟨B, hM⟩

private theorem sv_ker_comm (g h : (sv_rho (F := F)).ker) : g * h = h * g := by
  obtain ⟨B, hB⟩ := sv_ker_blocks g.2
  obtain ⟨B', hB'⟩ := sv_ker_blocks h.2
  refine Subtype.ext (sv_mat_injective ?_)
  show sv_mat (g.1 * h.1) = sv_mat (h.1 * g.1)
  rw [sv_mat_mul, sv_mat_mul, hB, hB', fromBlocks_multiply, fromBlocks_multiply]
  simp [add_comm]

private theorem sv_isSolvable_stabilizer (hGL : Group.IsSolvable (GL (Fin 2) F)) :
    Group.IsSolvable (stabilizer 2 F (flag 2 F 2)) := by
  have hker : Group.IsSolvable (sv_rho (F := F)).ker := Group.isSolvable_of_comm sv_ker_comm
  exact Group.isSolvable_of_ker_le_range (sv_rho (F := F)).ker.subtype (sv_rho (F := F))
    (Subgroup.range_subtype _).ge

end Lagrangian

private theorem sv_isSolvable_GL_two_three : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := by
  have hcard : Nat.card (GL (Fin 2) (ZMod 3)) = 2 ^ 4 * 3 ^ 1 := by
    rw [Matrix.card_GL_field, ZMod.card]
    decide
  have : Fintype (GL (Fin 2) (ZMod 3)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

theorem isSolvable_projStabilizer_two_three :
    Group.IsSolvable (projStabilizer 2 (ZMod 3) (flag 2 (ZMod 3) 2)) := by
  have hQ := sv_isSolvable_stabilizer (F := ZMod 3) sv_isSolvable_GL_two_three
  exact Group.isSolvable_of_surjective
    (f := (proj 2 (ZMod 3)).subgroupMap (stabilizer 2 (ZMod 3) (flag 2 (ZMod 3) 2)))
    ((proj 2 (ZMod 3)).subgroupMap_surjective _)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
