module

public import CFSG.CGT.Harada80.OmegaReflect
public import Certificates.Certificate840012

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80.OmegaEight

open CFSG.CGT.Harada80
open CFSG.RankThree.PartTwo
open CFSG.Quasithin.SteinbergCB.G2Two
open CFSG.Quasithin.SteinbergCB.I16
open CFSG.Quasithin.JonesParshall
open Matrix

theorem nsCodes_lt : ∀ c ∈ nsCodes, c < 2 ^ 8 := by
  decide +kernel


noncomputable def gens (i : Fin 2) : ↥(omegaMinusTwo 3) :=
  ⟨commGL 3 (xyCodes.getD (2 * i) []) (xyCodes.getD (2 * i + 1) []), commGL_mem _ _ _⟩

theorem gens_vec (i : Fin 2) {x : ℕ} (hx : x < 2 ^ 8) :
    (((gens i : ↥(omegaMinusTwo 3)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ vec 3 x =
      vec 3 (mApp (sCols.getD i []) x) := by
  have hX : ∀ c ∈ xyCodes.getD (2 * i) [],
      CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0 := by
    intro c hc
    have hmem : c ∈ nsCodes := sChain_mem i c (by
      simp only [sChain]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc)))
    exact (nsCheck_spec (Certificates.certificate840012.1) (nsCodes_lt c hmem)).2 hmem
  have hY : ∀ c ∈ xyCodes.getD (2 * i + 1) [],
      CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0 := by
    intro c hc
    have hmem : c ∈ nsCodes := sChain_mem i c (by
      simp only [sChain]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hc)))
    exact (nsCheck_spec (Certificates.certificate840012.1) (nsCodes_lt c hmem)).2 hmem
  change ((commGL 3 (xyCodes.getD (2 * i) []) (xyCodes.getD (2 * i + 1) []) :
      GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ vec 3 x =
    vec 3 (mApp (sCols.getD i []) x)
  rw [commGL_vec hX hY x]
  congr 1
  exact (genCheck_spec (Certificates.certificate840012.2.1) i hx).symm

theorem closure_gens : Subgroup.closure (Set.range gens) = ⊤ := by
  have hv0lt : v0Code < 2 ^ 8 := by decide
  have hv0 : CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 v0Code) ≠ 0 :=
    (nsCheck_spec (Certificates.certificate840012.1) hv0lt).2 v0Code_mem
  have hword : ∀ u < 2 ^ 8,
      CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 u) ≠ 0 →
      ∃ w : List (Fin 2), ∀ x < 2 ^ 8,
        mApp (wordCols 8 sCols w) x = reflCode 3 u (reflCode 3 v0Code x) := by
    intro u hu hne
    exact wordCheck_spec (Certificates.certificate840012.2.2.2.1)
      ((nsCheck_spec (Certificates.certificate840012.1) hu).1 hne)
  have hle : omegaMinusTwo 3 ≤ Subgroup.closure (Set.range (fun i : Fin 2 =>
      ((gens i : ↥(omegaMinusTwo 3)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)))) :=
    omegaMinusTwo_le_closure (m := 3) (k := 2) (by norm_num) sCols_lt
      (fun i x hx => gens_vec i hx) hv0 hword
  apply Subgroup.map_injective (omegaMinusTwo 3).subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  have hG : ((⇑(omegaMinusTwo 3).subtype) '' Set.range gens) = Set.range (fun i : Fin 2 =>
      ((gens i : ↥(omegaMinusTwo 3)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2))) := by
    rw [← Set.range_comp]
    rfl
  rw [hG]
  refine le_antisymm ?_ hle
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact (gens i).2

theorem rels_eq : ∀ r ∈ rels,
    CFSG.Quasithin.JonesParshall.wordEval gens r = 1 := by
  intro r hr
  apply Subtype.ext
  rw [val_wordEval]
  apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
    (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)).injective
  refine LinearEquiv.ext fun y => ?_
  have hy : y = vec 3 (code y) := (vec_code y).symm
  rw [hy, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
    wordEval_vec sCols_lt (fun i x hx => gens_vec i hx) r (code_lt y),
    relCheck_spec (Certificates.certificate840012.2.2.1) hr,
    mApp_range_pow (code_lt y)]
  simp

theorem h1OmegaMinusEight_holds : CFSG.CGT.Foote82.H1OmegaMinusEight :=
  h1Natural_of_checks closure_gens sCols_lt (fun i x hx => gens_vec i hx) rels_eq
    (foxCheck_spec (Certificates.certificate840012.2.2.2.2))

end CFSG.CGT.Harada80.OmegaEight
