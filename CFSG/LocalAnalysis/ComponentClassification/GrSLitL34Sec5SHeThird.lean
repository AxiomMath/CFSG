module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMInvol
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMUEq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMCMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMCrit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Five
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
public import CFSG.Open.QuasithinDefs
public import Certificates.Certificate22705

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeNT

variable {X : Type} [Group X] [Finite X]

theorem commute_of_isComponent {C K K' : Subgroup X} (hKC : K ≤ C) (hK'C : K' ≤ C)
    (hKc : IsComponent (K.subgroupOf C)) (hK : IsPComponent 2 (K.subgroupOf C))
    (hK' : IsPComponent 2 (K'.subgroupOf C)) (hne : K ≠ K') :
    ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
  have hne' : K.subgroupOf C ≠ K'.subgroupOf C := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map C.subtype) h
    rwa [map_subgroupOf_eq_of_le hKC, map_subgroupOf_eq_of_le hK'C] at h1
  obtain ⟨-, h2⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
    _ _ hK hK'
  have hbot := (h2 hne').2.2.2 (Or.inl hKc.1)
  intro x hx y hy
  have hm := commutator_mem_commutator (show (⟨x, hKC hx⟩ : ↥C) ∈ K.subgroupOf C from hx)
    (show (⟨y, hK'C hy⟩ : ↥C) ∈ K'.subgroupOf C from hy)
  rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
  exact congrArg Subtype.val hm

theorem diag_data {L : Subgroup X} {a u : X} {M : Subgroup X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) :
    ∃ (hMN : ∀ x ∈ M, ∀ y ∈ conjugate M a, x * y = y * x)
      (haM : ∀ y ∈ M, a * y * a⁻¹ ∈ conjugate M a),
      gsFixedLayer L u = (HeDQ.delta hMN haM).range ∧ IsQuasisimple ↥M ∧
        IsComponent (M.subgroupOf (centralizer ({u} : Set X))) ∧
        IsComponent ((conjugate M a).subgroupOf (centralizer ({u} : Set X))) ∧
        conjugate M a ≤ centralizer ({u} : Set X) := by
  set Cu := centralizer ({u} : Set X) with hCu
  set N := conjugate M a with hN
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haCu : a ∈ Cu := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hLa hu.1)).symm
  have hMc : IsComponent (M.subgroupOf Cu) := HeUC.isComponent_of_central hMu hMp hc
  have hNc : IsComponent (N.subgroupOf Cu) := HeKP.isComponent_conjugate hMc haCu
  have hNu : N ≤ Cu := by
    intro x hx
    rw [hN, HeKP.mem_conjugate] at hx
    have h := mul_mem (mul_mem (inv_mem haCu) (hMu hx)) haCu
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h
  have hMN := HeKP.commute_of_components hMu hNu hMc hNc (Ne.symm hne)
  have hMq : IsQuasisimple ↥M :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMu) hMc.1
  have haM : ∀ y ∈ M, a * y * a⁻¹ ∈ N := fun y hy => by
    rw [hN, HeKP.mem_conjugate,
      show a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ by group, haa]
    simpa using hy
  have haN : ∀ x ∈ N, a * x * a⁻¹ ∈ M := fun x hx => HeKP.mem_conjugate.mp hx
  exact ⟨hMN, haM, hfix.symm.trans
    (HeDG.gsFixedLayer_eq_range haa hMN haM haN hMq (by rw [hfix]; exact hu.2.2)), hMq, hMc,
    hNc, hNu⟩

end HeNT

end CFSG.ComponentClassification.GrSLit
