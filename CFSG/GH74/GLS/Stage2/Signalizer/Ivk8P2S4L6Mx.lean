module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L4Aux
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Act
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isL34_of_noncyclic (hKA : IVK_8_13_lift) {z : G} {k : Kind} {S M : Subgroup G}
    (hS2 : Stage2Ctx G z k S) (hMz : M = centralizer ({z} : Set G)) (hz2' : orderOf z = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H₀ I J : Subgroup G} (hH₀ : H₀ ≠ ⊤)
    (hI : IsCompIn H₀ I) (hIq : IsQuasisimple ↥I) (hJq : IsQuasisimple ↥J)
    (hzI : z ∈ normalizer (I : Set G)) (hIz : ⁅I, zpowers z⁆ = I) (hJI : J ≤ I)
    {Q : Subgroup G}
    (hQ : Q ≤ Op p M ⊓ H₀ ⊓ normalizer (I : Set G) ⊓ normalizer (J : Set G))
    (hQnc : ¬ IsCyclic ↥(Pbar J Q)) : IsL34Quotient ↥I := by
  have hperfI : Group.IsPerfect ↥I := hIq.1
  have hperfJ : Group.IsPerfect ↥J := hJq.1
  have hMc' : ∀ c : G, c * z = z * c → c ∈ M := fun c hc => by
    rw [hMz]
    exact Subgroup.mem_centralizer_singleton_iff.2 hc
  have hCJ : centralizer (I : Set G) ≤ centralizer (J : Set G) :=
    Subgroup.centralizer_le (fun x hx => hJI hx)
  have hQP : Q ≤ Op p M ⊓ H₀ ⊓ normalizer (I : Set G) := fun q hq => (hQ hq).1
  have hPnc : ¬ Op p M ⊓ H₀ ⊓ normalizer (I : Set G) ≤ centralizer (I : Set G) := by
    intro hle
    apply hQnc
    have hbot : Pbar J Q = ⊥ := by
      rw [eq_bot_iff]
      rintro e ⟨n, hn, rfl⟩
      have hnC : (n : G) ∈ centralizer (J : Set G) := hCJ (hle (hQP hn))
      rw [(YCfg.yAct_eq_one_iff J n).mpr hnC]
      exact Subgroup.one_mem _
    rw [hbot]
    infer_instance
  have hKA' := hKA G z k S hS2 H₀ I hH₀ hI hz2' hzI hIz p
    (Op p M ⊓ H₀ ⊓ normalizer (I : Set G)) hp hp2
    ((isPGroup_Op p hp M).to_le (inf_le_left.trans inf_le_left))
    (fun x hx => ⟨hx.1.2, hx.2⟩)
    (fun x hx => (Subgroup.mem_centralizer_singleton_iff.1
      (hMz ▸ Op_le p M hx.1.1 : x ∈ centralizer ({z} : Set G))).symm)
    (fun c hc hcz => P2S4.mem_normalizer_inf3 (le_normalizer_Op p M (hMc' c hcz))
      (Subgroup.le_normalizer hc.1) (Subgroup.le_normalizer hc.2))
    hPnc
  rcases hKA'.2 with ⟨x, hxP, hPx⟩ | ⟨hLie, -, -, -⟩
  · exfalso
    have h1 : IsCyclic ↥(Pbar I (Op p M ⊓ H₀ ⊓ normalizer (I : Set G))) :=
      P2S4.isCyclic_Pbar_of_le_sup hxP.2 hPx
    have h2 : Pbar I Q ≤ Pbar I (Op p M ⊓ H₀ ⊓ normalizer (I : Set G)) := by
      rintro e ⟨n, hn, rfl⟩
      exact ⟨n, hQP hn, rfl⟩
    have h3 : IsCyclic ↥(Pbar I Q) := P2S4.isCyclic_of_le h2
    obtain ⟨y, hyQ, hQy⟩ := K0.exists_gen_of_cyclic (J := I) (P := Q)
      (fun q hq => (hQ hq).1.2) h3
    have h4 : Q ≤ zpowers y ⊔ centralizer (J : Set G) := hQy.trans (sup_le_sup_left hCJ _)
    exact hQnc (P2S4.isCyclic_Pbar_of_le_sup (J := J) (hQ hyQ).2 h4)
  · exact hLie

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
