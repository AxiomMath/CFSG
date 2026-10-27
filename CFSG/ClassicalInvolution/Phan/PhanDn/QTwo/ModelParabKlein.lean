module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelKlein
public import CFSG.ClassicalInvolution.Phan.PhanDn.KleinDickson
public import CFSG.ClassicalInvolution.Phan.PhanDn.Chambers

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
open CFSG.StandardType.QTwo
open CFSG.RankThree.PartOne.K159

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem exists_kleinPsiHom_eq_of_mem_rulingGroup
    {g : (Fin 3 → K) ≃ₗ[F] (Fin 3 → K)} (hg : g ∈ rulingGroup E 3) :
    ∃ u : Su K 2 1 4, CFSG.StandardType.QTwo.kleinPsiHom E u = g.toLinearMap := by
  classical
  obtain ⟨hgO, hEven⟩ := (mem_rulingGroup E 3 g).mp hg
  let L : TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) :=
    ⟨bc E 3 g, (bc_mem_orthogonalGroup_iff E 3 g).mpr hgO⟩
  have hLdick : kleinDickson L = 1 := by
    refine (kleinDickson_eq_one_iff L).mpr ?_
    rw [inf_comm, bcLin_eq_coe_bc] at hEven
    simpa [L] using hEven
  obtain ⟨a, ha⟩ := exists_rho_eq L hLdick
  have hcomm : ∀ w : Fin 3 ⊕ Fin 3 → K,
      Klein.rho a (dFlip (unitaryInvolution K 2 1) w) =
        dFlip (unitaryInvolution K 2 1) (Klein.rho a w) := by
    intro w
    rw [ha]
    exact bc_dFlip E 3 g w
  obtain ⟨u, hu⟩ := exists_SUid_of_rho_comm (σ := unitaryInvolution K 2 1)
    E.isUnitary.invol a hcomm
  refine ⟨u, ?_⟩
  apply LinearMap.ext
  intro x
  funext i
  change kleinPsi E (((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) x i =
    g.toLinearMap x i
  rw [hu]
  change Klein.rho a (kleinJ E x) (Sum.inl i) = g x i
  rw [ha]
  change bc E 3 g (kleinJ E x) (Sum.inl i) = g x i
  have hJ : kleinJ E x = jEmb E 3 x := by
    ext s
    rcases s with j | j <;> rfl
  rw [hJ, bc_apply_jEmb, jEmb_apply_inl]

end CFSG.ClassicalInvolution.PhanDn.QTwo
