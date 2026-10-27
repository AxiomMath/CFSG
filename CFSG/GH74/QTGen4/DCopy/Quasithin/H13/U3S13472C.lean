module

public import CFSG.Quasithin.H13.U3S13472C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS134Defs

public section

namespace CFSG.Quasithin.H13.U3.P2

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
variable {S : A6.Setting134 G T L V} {H₁ H₂ : Subgroup G}

theorem settingX_of_F4 (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h1345 : NQS134.Stmt13_4_5_F4)
    (D : Data2 S H₁ H₂) {X : Subgroup G} (hX : InH (H₁ ⊔ H₂) X)
    (hXZ : X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T) : SettingX D X := by
  have hTX : T ≤ X := D.hH₀.1.trans hX.1
  have hXT : InH T X := ⟨hTX, hX.2⟩
  have hsylX : IsSylowTwoOf T X := A5.isSylowTwoOf_of_le S.h13.sylow hTX
  have hXM : ¬ X ≤ normalizer (L : Set G) := fun h => D.hH₀M (hX.1.trans h)
  have hns : ¬ Group.IsSolvable ↥X := fun hs => s1347_not_solvable_of_cComp D.hK₀
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hX.1))
  obtain ⟨-, hall⟩ := h1345 G T L V S X hXT hXM hns
  have hKX : D.K₀ ≤ X := D.KH.trans hX.1
  have hKl : D.K₀ ∈ lFamily T := D.hmax.1.2.1
  obtain ⟨K, hK, hKK⟩ := lemma_1_2_4_exists S.h13.qtke S.h13.simple S.h13.nonabelian
    (a37ForSQTK_of_cat h37) (a39ForSQTK_of_cat h39) hX.2 hsylX hKX hKl
  obtain ⟨⟨hKmax, -⟩, hN, -⟩ := hall K hK
  have hKeq : K = D.K₀ := D.hmax.2 K hKmax.1 hKK
  subst hKeq
  exact ⟨hX, hXZ, hK, hN⟩

end CFSG.Quasithin.H13.U3.P2
