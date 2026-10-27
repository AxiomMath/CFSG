module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four2
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

@[expose] def d8Exponent : Fin 8 → Fin 8 → ℤ :=
  ![![1, 0, -1, -2, -3, -4, -3, -2], ![0, 0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0]]

theorem d8Exponent_form (i k : Fin 8) :
    (2 : ℤ) * Tag.E8.cartan i k =
      ∑ j, d8Exponent i j * iform (d8Simple j) (Pi.single k 1) := by
  revert i k
  decide +kernel

theorem d8Simple_norm (j : Fin 8) :
    iform (d8Simple j) (d8Simple j) = 2 := by
  revert j
  decide +kernel

section CharTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_sq_eq_unit (t : Kˣ) : ∃ s : Kˣ, s * s = t := by
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two hchar (t : K)
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : (t : K) = (0 : K) * 0 := hb
    rw [mul_zero] at h0
    exact Units.ne_zero t h0
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  simpa [Units.val_mk0] using hb.symm

end CharTwo

section Torus

theorem rootDiagUnit_list_prod {ι : Type*} {K : Type} [Field K] (l : List ι)
    (f : ι → Fin Tag.E8.rank → Kˣ) :
    (l.map fun j => rootDiagUnit Tag.E8 (f j)).prod =
      rootDiagUnit Tag.E8 (fun k => (l.map fun j => f j k).prod) := by
  induction l with
  | nil =>
    rw [show (fun k : Fin Tag.E8.rank => (List.map (fun j => f j k) ([] : List ι)).prod) =
      (1 : Fin Tag.E8.rank → Kˣ) from rfl]
    exact (rootDiagUnit_one (τ := Tag.E8) (K := K)).symm
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, ← rootDiagUnit_mul]
    congr 1

theorem zpow_list_sum {G : Type*} [CommGroup G] (s : G) (l : List ℤ) :
    s ^ l.sum = (l.map (s ^ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.sum_cons, zpow_add, List.map_cons, List.prod_cons, ih]

theorem torusElt_eq_prod_rootTorus {K : Type} [Field K]
    (i : Fin 8) (s : Kˣ) :
    torusElt Tag.E8 K i (s * s) =
      ((List.finRange 8).map fun j =>
        rootTorusSL2 Tag.E8 K (d8Simple j) (s ^ d8Exponent i j)).prod := by
  classical
  have hR : ((List.finRange 8).map fun j =>
      rootTorusSL2 Tag.E8 K (d8Simple j) (s ^ d8Exponent i j)).prod =
      rootDiagUnit Tag.E8
        (fun k => ((List.finRange 8).map fun j =>
          (s ^ d8Exponent i j) ^ iform (d8Simple j) (Pi.single k 1)).prod) := by
    have hstep : ((List.finRange 8).map fun j =>
        rootTorusSL2 Tag.E8 K (d8Simple j) (s ^ d8Exponent i j)).prod =
        ((List.finRange 8).map fun j =>
          rootDiagUnit Tag.E8 (fun k =>
            (s ^ d8Exponent i j) ^ iform (d8Simple j) (Pi.single k 1))).prod := by
      refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
      rw [rootTorusSL2_eq_rootDiagUnit_corootPair (d8Simple_isRoot j)]
      congr 1
      funext k
      rw [d8Simple_norm j, mul_comm (2 : ℤ) (iform (d8Simple j) (Pi.single k 1))]
      rw [show iform (d8Simple j) (Pi.single k 1) * 2 / 2 =
        iform (d8Simple j) (Pi.single k 1) from by omega]
    rw [hstep, rootDiagUnit_list_prod]
  calc torusElt Tag.E8 K i (s * s)
      = rootDiagUnit Tag.E8 (fun j => (s * s) ^ Tag.E8.cartan i j) :=
        torusElt_eq_rootDiagUnit (τ := Tag.E8) (K := K) i (s * s)
    _ = rootDiagUnit Tag.E8 (fun k => ((List.finRange 8).map fun j =>
          (s ^ d8Exponent i j) ^ iform (d8Simple j) (Pi.single k 1)).prod) := by
        congr 1
        funext k
        have hsum : (2 : ℤ) * Tag.E8.cartan i k =
            ((List.finRange 8).map
              (fun j => d8Exponent i j * iform (d8Simple j) (Pi.single k 1))).sum := by
          rw [← Fin.sum_univ_def]
          exact d8Exponent_form i k
        calc (s * s) ^ Tag.E8.cartan i k
            = s ^ (2 * Tag.E8.cartan i k) := by
              rw [mul_zpow, ← zpow_add]
              ring_nf
          _ = s ^ ((List.finRange 8).map
                (fun j => d8Exponent i j * iform (d8Simple j) (Pi.single k 1))).sum := by
              rw [hsum]
          _ = (List.map (fun e => s ^ e) ((List.finRange 8).map
                (fun j => d8Exponent i j * iform (d8Simple j) (Pi.single k 1)))).prod :=
              zpow_list_sum s _
          _ = ((List.finRange 8).map
                (fun j => s ^ (d8Exponent i j * iform (d8Simple j) (Pi.single k 1)))).prod := by
              rw [List.map_map]
              rfl
          _ = ((List.finRange 8).map
                (fun j => (s ^ d8Exponent i j) ^ iform (d8Simple j) (Pi.single k 1))).prod := by
              refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
              rw [← zpow_mul]
    _ = ((List.finRange 8).map fun j =>
          rootTorusSL2 Tag.E8 K (d8Simple j) (s ^ d8Exponent i j)).prod := hR.symm

theorem rootTorusSL2_mem_d8Target {K : Type} [Field K] (j : Fin 8) (c : Kˣ) :
    rootTorusSL2 Tag.E8 K (d8Simple j) c ∈ d8Target K := by
  have hmem : rootTorusSL2 Tag.E8 K (d8Simple j) c ∈ rootRankOneGroup Tag.E8 K (d8Simple j) :=
    ⟨HSL c, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport Tag.E8 K (d8Simple_isRoot j)).1] at hmem
  exact (rootSubgroup_d8Simple_pair_le j) hmem

theorem torusElt_mem_d8Target {K : Type} [Field K] [Finite K] [CharP K 2]
    (i : Fin 8) (t : Kˣ) :
    torusElt Tag.E8 K i t ∈ d8Target K := by
  obtain ⟨s, hs⟩ := exists_sq_eq_unit (K := K) t
  rw [← hs, torusElt_eq_prod_rootTorus i s]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact rootTorusSL2_mem_d8Target j _

end Torus

theorem torusGroup_le_d8Chain (K : Type) [Field K] [Finite K] [CharP K 2] :
    torusGroup Tag.E8 K ≤ (⨆ k, e8D8Chain K k).map (adjointGroup Tag.E8 K).subtype := by
  change Subgroup.closure (Set.range fun p : Fin Tag.E8.rank × Kˣ =>
    torusElt Tag.E8 K p.1 p.2) ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_d8Target i t

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
