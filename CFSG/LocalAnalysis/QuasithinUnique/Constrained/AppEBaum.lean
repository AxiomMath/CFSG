module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppERed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppELin2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppELoc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalMain

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Dbl

variable {n : ℕ} {t : G} (D : Dbl T M H S L n t)
include D

theorem naturalConcl : NaturalConcl (R1 S L) (H1 S L) L :=
  C56.natural_Lin2 D.isMinimalParabolic D.isChi0Block_H1
    ⟨n, by have := D.hn; omega, D.hlin⟩ D.thompson_R1 rfl R1_le_normalizer_L

theorem baumann_R1 : baum (R1 S L) ≤ normalizer (L : Set G) ∧
    IsSylowTwoOf (baum (R1 S L)) (L ⊔ baum (R1 S L)) :=
  C56.baumann_single D.isMinimalParabolic D.isChi0Block_H1
    (Or.inl ⟨n, by have := D.hn; omega, D.hlin⟩) D.thompson_R1 rfl R1_le_normalizer_L

theorem baumann_Lin2_R1 :
    IsSylowTwoOf (baum (R1 S L)) (L ⊔ baum (R1 S L)) ∧
      baum (R1 S L) ≤ (baum (R1 S L) ⊓ L) ⊔ pCoreOf 2 (L ⊔ baum (R1 S L)) :=
  C56.baumann_Lin2_single D.isMinimalParabolic D.isChi0Block_H1 (by have := D.hn; omega) D.hlin
    D.thompson_R1 rfl R1_le_normalizer_L

theorem exists_u : ∃ u ∈ blockU L, u ∉ blockZ L ∧ ∀ y ∈ baum (R1 S L), u * y = y * u := by
  obtain ⟨q, W, hq2, hWU, -, hidxW, hcent, -, hZ, -, -⟩ := D.naturalConcl
  have hW : ¬ W ≤ blockZ L := by
    intro hWZ
    have h1 := C5.relIndex_le_of_le_left hWZ (blockU L)
    have h2 : (blockZ L).relIndex (blockU L) = q ^ 2 := hZ
    rw [h2, hidxW] at h1
    nlinarith
  obtain ⟨u, huW, huZ⟩ := IsConcreteLE.not_le_iff_exists.mp hW
  refine ⟨u, hWU huW, huZ, fun y hy => ?_⟩
  by_cases hyQ : y ∈ baum (R1 S L) ⊓ centralizer (blockU L : Set G)
  · exact Subgroup.mem_centralizer_iff.1 hyQ.2 u (hWU huW)
  · exact (hcent y hy hyQ u (hWU huW)).1 huW

theorem baum_le_R1 : baum S ≤ R1 S L := by
  obtain ⟨u, huU, huZ, hucomm⟩ := D.exists_u
  have hu2 : u ^ 2 = 1 := C1.blockU_sq D.hL u huU
  have huS : u ∈ S := C56.pCoreOf_le_S D.hcs (C56.blockU_le_pCoreOf_general D.hcs huU)
  have hJ : thompsonJ S ≤ baum (R1 S L) := by
    rw [← D.thompsonJ_R1]; exact C5.thompsonJ_le_baum' _
  have huJ : ∀ j ∈ thompsonJ S, u * j = j * u := fun j hj => hucomm j (hJ hj)
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian S
  have huA₀ : u ∈ A₀ := C56.mem_of_isMaxElemAbelian_of_commute hA₀ huS
    (fun a ha => (huJ a (GammaExtra.le_thompsonJ hA₀ ha)).symm) hu2
  have huJS : u ∈ thompsonJ S := GammaExtra.le_thompsonJ hA₀ huA₀
  have huΩ : u ∈ omegaOneCenterOf (thompsonJ S) :=
    Subgroup.subset_closure ⟨show u ∈ thompsonJ S ⊓ centralizer ((thompsonJ S : Subgroup G) : Set G)
      from ⟨huJS, Subgroup.mem_centralizer_iff.mpr fun j hj => (huJ j hj).symm⟩, hu2⟩
  intro b hb
  by_contra hbR
  have hbS : b ∈ S := hb.1
  have hbu : u * b = b * u := Subgroup.mem_centralizer_iff.1 hb.2 u huΩ
  have hu₂ : u ∈ conjR L t := by
    rw [← D.conjR_eq_t_of_not_mem hbS hbR, C56.conjR_eq, mem_conjSubgroup_iff]
    have e : b * u * b⁻¹ = u := by rw [← hbu]; group
    rw [e]
    exact (C1.blockU_le_blockQ D.hL).trans (C1.blockQ_le L) huU |> fun h => by simpa using h
  have huC : u ∈ centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => D.comm_elem l hl u hu₂
  exact huZ ⟨huU, huC⟩

theorem baum_R1_eq : baum (R1 S L) = baum S := by
  rw [D.baum_R1]
  exact inf_eq_left.2 D.baum_le_R1

theorem baum_le_normalizer : baum S ≤ normalizer (L : Set G) :=
  D.baum_le_R1.trans R1_le_normalizer_L

theorem isSylowTwoOf_baum : IsSylowTwoOf (baum S) (L ⊔ baum S) := by
  have := D.baumann_R1.2
  rwa [D.baum_R1_eq] at this

theorem loc : ∃ (q : ℕ) (W : Subgroup G),
    Loc (baum S) L (blockU L) (baum S ⊓ centralizer (blockU L : Set G)) W q := by
  obtain ⟨q, W, hq2, hWU, hidxQ, hidxW, hcent, hcomm, hZ, hgen, -⟩ := D.naturalConcl
  rw [D.baum_R1_eq] at hidxQ hcent hcomm hgen
  have hLsh := D.hL
  have hB2 : IsPGroup 2 (baum S) := D.hcs.sylow.isPGroup.to_le inf_le_left
  have hBN := D.baum_le_normalizer
  have hBU : baum S ≤ normalizer (blockU L : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (hBN hg)
  have hsyl := D.isSylowTwoOf_baum
  have hQX : baum S ⊓ centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ baum S) :=
    C56.baum_inf_centralizer_eq hLsh hB2 hBN hsyl
  have hLX : L ≤ L ⊔ baum S := le_sup_left
  have hKQ : L ≤ normalizer ((baum S ⊓ centralizer (blockU L : Set G) : Subgroup G) : Set G) := by
    rw [hQX]
    exact hLX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hXU : L ⊔ baum S ≤ normalizer (blockU L : Set G) :=
    sup_le (C1.le_normalizer_blockU L) hBU
  have hUB : blockU L ≤ baum S :=
    hsyl.le_of_normalizes (hUL.trans hLX) hXU (C1.isPGroup_blockU hLsh)
  have hUQ : blockU L ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    le_inf hUB (fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (C1.elemAb2_blockU hLsh).1 v hv u hu)
  have hR1 : C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU L : Set G)) (blockU L) W q :=
    { U_le_Q := hUQ
      Q_le_B := inf_le_left
      B_le_normQ := fun _ hb => C5.mem_normalizer_inf (Subgroup.le_normalizer hb)
        (C5.mem_normalizer_centralizer (hBU hb))
      B_le_normU := hBU
      Q_eq := rfl
      W_le_U := hWU
      idx_Q := hidxQ
      idx_W := hidxW
      q_ne_zero := by omega
      cent_y := hcent
      comm_UB := hcomm
      U_comm := (C1.elemAb2_blockU hLsh).1 }
  have hXN : L ⊔ baum S ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hTsyl : IsSylowTwoOf (baum S ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hsyl hLX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN).isSubnormal
  have hBTQ : baum S ≤ (baum S ⊓ L) ⊔ (baum S ⊓ centralizer (blockU L : Set G)) := by
    have := D.baumann_Lin2_R1.2
    rw [D.baum_R1_eq, ← hQX] at this
    exact this
  refine ⟨q, W, ⟨hR1, hq2, hZ, hgen, hKQ, hUL, ?_⟩⟩
  exact lin2_B_commutator_inf_Z hLsh (by have := D.hn; omega) D.hlin hTsyl rfl hBTQ hKQ

end Dbl

end CFSG.QuasithinUnique.AppE
