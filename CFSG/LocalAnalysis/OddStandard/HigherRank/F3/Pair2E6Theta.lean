module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Sigma
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Fixed
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Double
public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
public import CFSG.ClassicalInvolution.RouteD.TypeEModel

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.RouteD (path6)
open scoped MatrixGroups

theorem rhoPerm_path6 (i : Fin 5) : rhoPerm (path6 i) = path6 (Fin.rev i) := by
  fin_cases i <;> rfl

private theorem path6_injective : Function.Injective path6 := by
  decide +kernel

section Theta

variable {k : Type} [Field k]

theorem exists_theta6 [Finite k] :
    ∃ Θ : SL(6, k) →* e6Data_valid.minGroup k,
      ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i) := by
  have hn01 : (path6 0 : Fin (Tag.rank .E6)) ≠ path6 1 := by decide
  have hc01 : Tag.cartan .E6 (path6 0) (path6 1) = -1 := by decide
  have hc10 : Tag.cartan .E6 (path6 1) (path6 0) = -1 := by decide
  have hn12 : (path6 1 : Fin (Tag.rank .E6)) ≠ path6 2 := by decide
  have hc12 : Tag.cartan .E6 (path6 1) (path6 2) = -1 := by decide
  have hc21 : Tag.cartan .E6 (path6 2) (path6 1) = -1 := by decide
  have hn23 : (path6 2 : Fin (Tag.rank .E6)) ≠ path6 3 := by decide
  have hc23 : Tag.cartan .E6 (path6 2) (path6 3) = -1 := by decide
  have hc32 : Tag.cartan .E6 (path6 3) (path6 2) = -1 := by decide
  have hn34 : (path6 3 : Fin (Tag.rank .E6)) ≠ path6 4 := by decide
  have hc34 : Tag.cartan .E6 (path6 3) (path6 4) = -1 := by decide
  have hc43 : Tag.cartan .E6 (path6 4) (path6 3) = -1 := by decide
  obtain ⟨Ψ₀, -, h00, h01⟩ := exists_e6Sl3 (k := k) (a := (path6 0 : Fin (Tag.rank .E6)))
    (b := (path6 1 : Fin (Tag.rank .E6))) hn01 hc01 hc10
  obtain ⟨Ψ₁, -, h10, h11⟩ := exists_e6Sl3 (k := k) (a := (path6 1 : Fin (Tag.rank .E6)))
    (b := (path6 2 : Fin (Tag.rank .E6))) hn12 hc12 hc21
  obtain ⟨Ψ₂, -, h20, h21⟩ := exists_e6Sl3 (k := k) (a := (path6 2 : Fin (Tag.rank .E6)))
    (b := (path6 3 : Fin (Tag.rank .E6))) hn23 hc23 hc32
  obtain ⟨Ψ₃, -, h30, h31⟩ := exists_e6Sl3 (k := k) (a := (path6 3 : Fin (Tag.rank .E6)))
    (b := (path6 4 : Fin (Tag.rank .E6))) hn34 hc34 hc43
  let F : CTFamily k (e6Data_valid.minGroup k) 5 :=
    { ι := fun i => e6Rank1 k (path6 i)
      θ := ![Ψ₀, Ψ₁, Ψ₂, Ψ₃, 1]
      left := fun i hi => by
        fin_cases i
        · exact h00
        · exact h10
        · exact h20
        · exact h30
        · exact absurd hi (by decide)
      right := fun i hi => by
        fin_cases i
        · exact h01
        · exact h11
        · exact h21
        · exact h31
        · exact absurd hi (by decide)
      comm := fun i j hij a b => by
        refine (commute_e6Rank1 (a := path6 i) (b := path6 j) ?_ ?_ a b).eq
        · intro h
          exact absurd (congrArg Fin.val (path6_injective h)) (by omega)
        · exact CFSG.ClassicalInvolution.RouteD.path6_comm i j hij }
  obtain ⟨Φ, hΦ, -⟩ := exists_hom_of_ctFamily F
  exact ⟨Φ, hΦ⟩

theorem sigma_comp_theta6 (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) :
    (sigma k θ).comp Θ = Θ.comp (sigmaA6 (involEquiv θ hθ)).toMonoidHom := by
  refine hom_ext_blockSL2 fun i => MonoidHom.ext fun A => ?_
  show sigma k θ (Θ (blockSL2 k 5 i A)) =
    Θ (sigmaA6 (involEquiv θ hθ) (blockSL2 k 5 i A))
  rw [show Θ (blockSL2 k 5 i A) = e6Rank1 k (path6 i) A from DFunLike.congr_fun (h i) A,
    sigmaA6_blockSL2,
    show Θ (blockSL2 k 5 (Fin.rev i) (fieldAutSL (involEquiv θ hθ) 2 A)) =
      e6Rank1 k (path6 (Fin.rev i)) (fieldAutSL (involEquiv θ hθ) 2 A) from
        DFunLike.congr_fun (h (Fin.rev i)) _,
    sigma_e6Rank1 (k := k) (θ := θ) (a := path6 i) (A := A), rhoPerm_path6]
  rfl

theorem map_blockSL2_range_theta6 {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) (i : Fin 5) :
    (blockSL2 k 5 i).range.map Θ = rankOne (e6Datum k).rootGroup (path6 i) := by
  rw [← MonoidHom.range_comp Θ (blockSL2 k 5 i), h i]
  exact (rankOne_eq_range_of_param (D := e6Datum k) (i := path6 i) (r := e6Rank1 k (path6 i))
    (fun c => by
      rw [e6Rank1_tv01 (k := k) (a := path6 i) c]
      exact e6Data_valid.xm_mem_rootGroup k _ c)
    (fun c => by
      rw [e6Rank1_tv10 (k := k) (a := path6 i) c]
      exact e6Data_valid.xm_mem_rootGroup k _ c)
    (fun g hg => by
      obtain ⟨c, hc⟩ := (e6Data_valid.mem_rootGroup k).1 hg
      exact ⟨c, by rw [e6Rank1_tv01 (k := k) (a := path6 i) c]; exact hc⟩)
    (fun g hg => by
      obtain ⟨c, hc⟩ := (e6Data_valid.mem_rootGroup k).1 hg
      exact ⟨c, by rw [e6Rank1_tv10 (k := k) (a := path6 i) c]; exact hc⟩)).symm

theorem range_theta6 {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) :
    Θ.range = ⨆ i : Fin 5, rankOne (e6Datum k).rootGroup (path6 i) := by
  rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := k) 5, Subgroup.map_iSup]
  exact iSup_congr fun i => map_blockSL2_range_theta6 h i

@[expose] noncomputable def thetaFixed (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (Θ : SL(6, k) →* e6Data_valid.minGroup k)
    (hσ : (sigma k θ).comp Θ = Θ.comp (sigmaA6 (involEquiv θ hθ)).toMonoidHom) :
    ↥(unitaryGroup6 θ hθ) →* ↥(fixedGroup k θ) :=
  fixedRestrict (sigma k θ) (sigmaA6 (involEquiv θ hθ)).toMonoidHom Θ hσ

theorem thetaFixed_injective (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (hσ : (sigma k θ).comp Θ = Θ.comp (sigmaA6 (involEquiv θ hθ)).toMonoidHom)
    (hinj : Function.Injective Θ) : Function.Injective (thetaFixed θ hθ Θ hσ) :=
  fixedRestrict_injective _ _ Θ hσ hinj

end Theta

end CFSG.OddStandard.HigherRank.F3
