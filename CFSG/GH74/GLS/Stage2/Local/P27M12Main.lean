module

public import CFSG.GH74.GLS.Stage2.Local.P27M12Basic
public import CFSG.GH74.GLS.Stage2.Local.Prop27Br
public import CFSG.GH74.GLS.Stage2.Local.Ctx0
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.GH74.GLS.Stage2.Local.P27Br CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem prop27WM12_of_detail {z x : G} (hzc : IsCentralInvolution z) (hxC : x ∈ Cen z)
    (hxnc : IsNonCentralInvolution x) (hM : M12NonCentral x) : Prop27WM12 z x := by
  classical
  obtain ⟨K, y, q, hKc, hKL2, hq8, hyC, hy2', hPGL, -, hRO, hout⟩ := hM
  have hx2 : orderOf x = 2 := hxnc.1
  have hz2 : orderOf z = 2 := hzc.1
  have hq : Odd q := Nat.odd_iff.2 (by omega)
  have hzN : z ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm
  have hzK : z ∈ K := by
    by_contra hzK
    exact hxnc.2 (isCentralInvolution_of_isConj_P34 hzc (hout z hzN hz2 hzK).symm)
  have hq5 : 5 ≤ q := by
    by_contra hlt
    obtain ⟨F₀, iF₀, fF₀, hF₀, ⟨e₀⟩⟩ := hKL2
    have h3 : Nat.card F₀ ≤ 3 := by
      have : q ≤ 4 := by omega
      omega
    have hsol : Group.IsSolvable (PSL2 F₀) := psl2_solvable_of_card_le_three h3
    have hsol' : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) :=
      Group.isSolvable_of_surjective (f := (e₀.trans (IVK.L2.equivPSL F₀)).symm.toMonoidHom)
        (e₀.trans (IVK.L2.equivPSL F₀)).symm.surjective
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
      (TwoThin.isQuasisimple_hat hKc) hsol'
  have hKy : ∀ k ∈ K, y * k * y⁻¹ ∈ K := normalizes_of_pgl hq hq5 hKL2 hPGL
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hx2' : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2', pow_two] at this
  have hJ : Jx x ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K :=
    Jx_le_sup hx2' hy2 hxy hKc.1 hyC hKy hRO
  have hKJ : K ≤ Jx x := le_sSup hKc
  have hL2J := isL2_Jx hKc hKJ hJ hKL2
  refine ⟨q, hq, hL2J, fun u hu hu2 => ?_⟩
  have hD : DihJ (HBar (Jx x)) := by
    obtain ⟨F, iF, fF, hF, e⟩ := hL2J
    exact Or.inl ⟨F, iF, fF, by rw [hF]; exact hq, e⟩
  obtain ⟨j, -, hju⟩ := exists_conj_of_involutions hD (hKJ hzK) hu hz2 hu2
  exact isConj_iff.2 ⟨j, hju⟩

theorem leaf_prop27WM12_of_ctx
    {Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop}
    (hdet : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx G z k S →
      Stage1Detail G z k S)
    (hcen : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx G z k S →
      IsCentralInvolution z) : Leaf_Prop27WM12 Ctx :=
  fun G _ _ z k S hctx hk x hxC hxnc =>
    prop27WM12_of_detail (hcen G z k S hctx) hxC hxnc
      ((hdet G z k S hctx).m12 hk x hxnc.1 (fun hc => hxnc.2 (isCentralInvolution_of_isConj_P34 (hcen G z k S hctx) hc)))

end CFSG.GH74.GLS.Stage2.Local.P27M12
