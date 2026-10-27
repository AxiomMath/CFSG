module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Norm

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18 (le_pCoreOf_of_normal)
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

@[expose] def PNormalizesLarge : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
      ¬ p ∣ Nat.card ↥K → ∀ d : X, d ^ p = 1 →
        pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X)

section Aux

variable {X : Type} [Group X] [Finite X]

theorem subgroupOf_pCoreOf_le {N : Subgroup X} {d : X} (hdN : d ∈ N) :
    (pCoreOf 2 (Subgroup.centralizer ({d} : Set X))).subgroupOf N ≤
      pCoreOf 2 (Subgroup.centralizer ({(⟨d, hdN⟩ : ↥N)} : Set ↥N)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_normal ?_ ?_ ?_
  · intro x hx
    have hx' : (x : X) ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) := hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.1
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx')
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext h1)
  · intro c hc x hx
    have hcX : (c : X) ∈ Subgroup.centralizer ({d} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
    have hx' : (x : X) ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) := hx
    have := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hcX) (x : X)).1 hx'
    exact this
  · exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer ({d} : Set X))).comap_of_injective
      N.subtype N.subtype_injective)

end Aux

theorem pCoreOf_le_normalizer_of_family (hB : PNormalizesLarge)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hCh : IsChevTwo (↥K ⧸ Subgroup.center ↥K)) {D : Subgroup X}
    {Sd : X → Subgroup X} (hfam : SignalizerFamily p D Sd) :
    ∀ d ∈ D, d ≠ 1 →
      pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  intro d hd hd1
  by_cases hdvd : p ∣ Nat.card ↥K
  · exact pCoreOf_centralizer_singleton_le_normalizer_of_dvd hp hp2 hK hdvd
      (hfam.elemAbelian.2 d hd)
  · exact hB X p hp hp2 K hK hCh hdvd d (hfam.elemAbelian.2 d hd)

theorem quotAutOfCentreHom_injective {X : Type} [Group X] {K : Subgroup X}
    (hK : IsComponentOf K ⊤) :
    Function.Injective (quotAutOfCentreHom : MulAut ↥K →* MulAut (Kbar K)) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  refine eq_one_of_forall_mk_eq_aut hK.2.2.1 φ fun x => ?_
  have := congrArg (fun ψ : MulAut (Kbar K) => ψ (QuotientGroup.mk x)) hφ
  simpa [quotAutOfCentreHom, quotAutOfCentre_mk] using this

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
