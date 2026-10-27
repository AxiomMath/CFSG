module

public import CFSG.Quasithin.Background.Basic
import CFSG.LocalAnalysis.ComponentInitial.OddCoreQuotient
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {X : Type} [Group X] [Finite X]

theorem nonempty_quotient_pCore_mulEquiv_of_map {n : ℕ} {L : Subgroup X} (hLn : L.Normal)
    (φ : X →* Equiv.Perm (Fin n)) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hL : L.map φ = alternatingGroup (Fin n)) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin n)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : ↥L →* Equiv.Perm (Fin n) := φ.comp L.subtype
  have hmem : ∀ x : ↥L, (x ∈ CFSG.pCore 2 ↥L ↔ (x : X) ∈ L ⊓ CFSG.pCore 2 X) := by
    intro x
    rw [← CFSG.LocalAnalysis.ComponentInitial.pCore_normal_intersection 2 hLn]
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  have hkerψ : ψ.ker = CFSG.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    show φ (x : X) = 1 ↔ x ∈ CFSG.pCore 2 ↥L
    rw [← MonoidHom.mem_ker, hker,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2, hmem]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : ψ.range = alternatingGroup (Fin n) := by
    rw [← hL]
    ext g
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : X), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem isSimpleGroup_quotient_pCore_of_map {n : ℕ} (hn : 5 ≤ n) {L : Subgroup X}
    (hLn : L.Normal) (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hL : L.map φ = alternatingGroup (Fin n)) : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := nonempty_quotient_pCore_mulEquiv_of_map hLn φ hker hL
  exact e.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simpa using hn))

theorem center_quotient_pCore_eq_bot_of_map {n : ℕ} (hn : 5 ≤ n) {L : Subgroup X}
    (hLn : L.Normal) (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hL : L.map φ = alternatingGroup (Fin n)) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  obtain ⟨e⟩ := nonempty_quotient_pCore_mulEquiv_of_map hLn φ hker hL
  have hA : Subgroup.center ↥(alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)
  have h := Subgroup.map_center_eq e
  rw [hA] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem exists_maxElemAbelian_offender_of_not_thompsonJ_le {R W : Subgroup X}
    (hW : CFSG.Open.IsElemAbelian 2 W) (hWR : W ≤ R)
    (hJ : ¬ CFSG.Quasithin.thompsonJ R ≤ Subgroup.centralizer (W : Set X)) :
    ∃ A : Subgroup X, CFSG.Quasithin.IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (W : Set X) ∧
      Nat.card W ≤ (Subgroup.centralizer (W : Set X)).relIndex A *
        Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set X)) := by
  classical
  obtain ⟨A, hA, hAW⟩ : ∃ A : Subgroup X, CFSG.Quasithin.IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (W : Set X) := by
    by_contra h
    apply hJ
    rw [CFSG.Quasithin.thompsonJ, iSup_le_iff]
    intro A
    rw [iSup_le_iff]
    intro hA
    by_contra hAW
    exact h ⟨A, hA, hAW⟩
  obtain ⟨hAR, hAel, hAmax⟩ := hA
  have hmax : ∀ B : Subgroup X, B ≤ R →
      Offender.IsElemAb2 B →
      Nat.card B ≤ Nat.card A :=
    fun B hBR hB => hAmax B hBR
      (isElemAbelian_of_isElemAb2 hB)
  have hres := Offender.card_le_relIndex_mul_of_max (isElemAb2_of_isElemAbelian hW) hWR
    (isElemAb2_of_isElemAbelian hAel) hAR hmax
  have hri : (R ⊓ Subgroup.centralizer (W : Set X)).relIndex A =
      (Subgroup.centralizer (W : Set X)).relIndex A := by
    have h1 := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (W : Set X)) R A
    rw [inf_eq_right.2 hAR, Subgroup.relIndex_eq_one.2 hAR, mul_one] at h1
    rw [inf_comm R (Subgroup.centralizer (W : Set X)), ← h1]
  exact ⟨A, ⟨hAR, hAel, hAmax⟩, hAW, by rwa [hri] at hres⟩

theorem exists_offender_of_not_thompsonJ_le {R W : Subgroup X} (hW : CFSG.Open.IsElemAbelian 2 W)
    (hWR : W ≤ R) (hJ : ¬ CFSG.Quasithin.thompsonJ R ≤ Subgroup.centralizer (W : Set X)) :
    ∃ A : Subgroup X, CFSG.Open.IsElemAbelian 2 A ∧ A ≤ R ∧
      ¬ A ≤ Subgroup.centralizer (W : Set X) ∧
      Nat.card W ≤ (Subgroup.centralizer (W : Set X)).relIndex A *
        Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set X)) := by
  obtain ⟨A, hA, hAW, hoff⟩ :=
    exists_maxElemAbelian_offender_of_not_thompsonJ_le hW hWR hJ
  exact ⟨A, hA.2.1, hA.1, hAW, hoff⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
