module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.Quasithin.Background.F918P4
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}

section Fact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]

omit [CFSG.GH74.QTGen4.Finite4 G] [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))] in

theorem V₁_le_DH_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) :
    fsuV1 T V ≤ F8.DH V (fsuV1 T V) H (g : G) := by
  have hF98 := hF.toHypF98
  obtain ⟨-, -, -, hV12, -⟩ := stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have hHC : ∀ y ∈ H, ∀ z ∈ fsuV1 T V, y * z = z * y := by
    intro y hy z hz
    have h1 := hF.H_le_normalizer_V₁ hy
    rw [normalizer_eq_centralizer_of_card_eq_two hV12] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm
  have hA₁H : F8.A₁ (fsuV1 T V) (g : G) ≤ H := (hF98.A₁_le_Uγ (g := g)).trans (hF98.Uγ_le_H s)
  intro z hz
  refine ⟨le_conjClosure V H ((inf_le_left : fsuV1 T V ≤ V) hz), ?_, fun u hu => ?_⟩
  · rw [normalizer_eq_centralizer_of_card_eq_two (hF98.card_A₁ (g := g)),
      Subgroup.mem_centralizer_iff]
    intro a ha
    exact hHC a (hA₁H ha) z hz
  · have h1 := hHC u (hF98.Uγ_le_H s hu) z hz
    have e : z * u * z⁻¹ * u⁻¹ = 1 := by
      rw [← h1]
      group
    rw [e]
    exact (F8.A₁ (fsuV1 T V) (g : G)).one_mem

end Fact

end CFSG.Quasithin.H13.L32A.C
