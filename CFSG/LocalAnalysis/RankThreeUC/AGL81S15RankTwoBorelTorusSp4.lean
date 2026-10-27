module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBorelTorus
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.Assembly.QuasithinDefs
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial

private theorem unipotent_isSylowTwoOf_top {K : Type} [Field K] [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (SymplecticFlag.unipotent 2 K) ⊤ := by
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  have hPcoe : (P : Subgroup (StatedSp 2 K)) = SymplecticFlag.unipotent 2 K := hP
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hPcoe]
    exact P.isPGroup'
  · rw [show ((SymplecticFlag.unipotent 2 K).subgroupOf ⊤).index
        = (SymplecticFlag.unipotent 2 K).index from Subgroup.relIndex_top_right _,
      ← hPcoe]
    exact P.not_dvd_index

private theorem torus_mul_comm {r : ℕ} {K : Type} [Field K] {a b : StatedSp r K}
    (ha : a ∈ SymplecticTorusWeyl.torus r K) (hb : b ∈ SymplecticTorusWeyl.torus r K) :
    a * b = b * a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

private theorem exists_unipotent_mul_torus {r : ℕ} {K : Type} [Field K]
    {g : StatedSp r K} (hg : g ∈ SymplecticFlag.borelSubgroup r K) :
    ∃ u ∈ SymplecticFlag.unipotent r K, ∃ h ∈ SymplecticTorusWeyl.torus r K, g = u * h := by
  let t : Fin r → Kˣ := SymplecticFlag.diagHom r K ⟨g, hg⟩
  let h : StatedSp r K := SymplecticTorusWeyl.torusHom t
  have hhT : h ∈ SymplecticTorusWeyl.torus r K := SymplecticTorusWeyl.torusHom_mem_torus t
  have hhB : h ∈ SymplecticFlag.borelSubgroup r K := SymplecticFlag.torus_le_borelSubgroup hhT
  have hdiag : SymplecticFlag.diagHom r K ⟨h, hhB⟩ = t := by
    funext i
    apply Units.ext
    simp [h, t, SymplecticFlag.diagHom, SymplecticFlag.diagEntry,
      SymplecticTorusWeyl.coe_torusHom]
  have huB : g * h⁻¹ ∈ SymplecticFlag.borelSubgroup r K :=
    (SymplecticFlag.borelSubgroup r K).mul_mem hg ((SymplecticFlag.borelSubgroup r K).inv_mem hhB)
  refine ⟨g * h⁻¹, ?_, h, hhT, by group⟩
  have hker : (⟨g * h⁻¹, huB⟩ : SymplecticFlag.borelSubgroup r K) ∈
      (SymplecticFlag.diagHom r K).ker := by
    rw [MonoidHom.mem_ker]
    have hsub : (⟨g * h⁻¹, huB⟩ : SymplecticFlag.borelSubgroup r K) =
        (⟨g, hg⟩ : SymplecticFlag.borelSubgroup r K) *
          (⟨h, hhB⟩ : SymplecticFlag.borelSubgroup r K)⁻¹ := Subtype.ext rfl
    rw [hsub, map_mul, map_inv, hdiag, mul_inv_cancel]
  rw [SymplecticFlag.ker_diagHom] at hker
  exact hker

theorem hasBorelTorus_statedSp_two {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ}
    (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1)
    {U : Subgroup ↥(CFSG.Open.StatedSp 2 F)} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    HasBorelTorus ↥(CFSG.Open.StatedSp 2 F) q U := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hcardq : q ∣ Nat.card Fˣ := by
    rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' q hcardq
  let P : Subgroup (Fin 2 → Fˣ) :=
    Subgroup.pi Set.univ fun i : Fin 2 =>
      (if i ∈ (Finset.univ : Finset (Fin 2)) then Subgroup.zpowers ζ else ⊥)
  let E : Subgroup (StatedSp 2 F) := P.map (SymplecticTorusWeyl.torusHom (r := 2) (k := F))
  have hET : E ≤ SymplecticTorusWeyl.torus 2 F := by
    rintro _ ⟨t, -, rfl⟩
    exact SymplecticTorusWeyl.torusHom_mem_torus t
  haveI hPcomm : IsMulCommutative P := by
    refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    funext i
    exact mul_comm (a.1 i) (b.1 i)
  have hEcomm : IsMulCommutative E :=
    Subgroup.map_isMulCommutative P (SymplecticTorusWeyl.torusHom (r := 2) (k := F))
  have hcardP : Nat.card P = q ^ 2 := by
    have h := SymplecticTorusWeyl.card_pi_ite_zpowers (m := 2) (ζ := ζ) (s := Finset.univ)
    simpa [P, hζ] using h
  have hEcard : Nat.card E = q ^ 2 := by
    rw [Subgroup.card_map_of_injective
      (SymplecticTorusWeyl.torusHom_injective (r := 2) (k := F)), hcardP]
  refine HasBorelTorus.of_isSylowTwoOf (unipotent_isSylowTwoOf_top (K := F)) hU ?_
  refine ⟨E, isBorelTorus_of_le_torus (H := SymplecticTorusWeyl.torus 2 F)
    (U := SymplecticFlag.unipotent 2 F) ?_ ?_ ?_ hET ⟨hEcomm, ?_⟩ hEcard⟩
  · exact fun a ha b hb => torus_mul_comm ha hb
  · rw [SymplecticHigher.normalizer_unipotent]
    exact SymplecticFlag.torus_le_borelSubgroup
  · intro g hg
    rw [SymplecticHigher.normalizer_unipotent] at hg
    exact exists_unipotent_mul_torus hg
  · intro x hx
    exact SymplecticTorusWeyl.pow_eq_one_of_mem_map_pi_ite_zpowers (m := 2) hζ hx

end CFSG.LocalAnalysis.RankThreeUC.S15

end
