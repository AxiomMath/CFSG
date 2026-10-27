module

public import CFSG.Quasithin.H13.L32NItems144CTL7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144CTL5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem exists_cComp_F4 (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4)
    {σ h t : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g) (hσQ : σ ∉ pCoreOf 2 (l32nH T V))
    (hσ2 : σ * σ = 1) (hhH : h ∈ l32nH T V) (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V))
    (hσT : σ ∈ T) (htT : t ∈ T) (htZ : t ∈ Subgroup.centralizer (T : Set G)) (ht1 : t ≠ 1)
    (htL : L.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ K₀ ∈ cComp (Subgroup.centralizer ({t} : Set G)), L.map (MulAut.conj h).toMonoidHom ≤ K₀ := by
  have hTX : T ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htZ x hx)
  have hTS := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTX
  have htp : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    S.hyp.fsu.sylow.1.to_le (Subgroup.zpowers_le.mpr htT)
  have hO : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ := fun hb =>
    ht1 (by have := mem_pCoreOf_centralizer htp; rwa [hb, Subgroup.mem_bot] at this)
  exact lemma_1_2_5_exists S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian h37 h39 hO hTS
    (sup_le S.QT (Subgroup.zpowers_le.mpr hσT)) (relIndex_R_le_F4 S hRest hσT hσQ)
    (isLocal_R S hσW hσQ hσ2 hhH hσh hσT) htL

end Setup

end L1444CTL

end CFSG.Quasithin.H13
