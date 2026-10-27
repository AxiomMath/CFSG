module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4315
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L43Steps

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem Setting4311.setting4315_F4 {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ}
    {F : Type} [Field F] [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)}
    {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)} {W' : Submodule F (Fin 3 → F)}
    {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
    (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y) (h314 : Step4314_F4)
    (hKZ : KZ ∈ cComp (Subgroup.normalizer (ZS : Set G)))
    (hGZ : Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G)) (hK₂ : K₂ ≤ KZ)
    (hKZC : KZ ≤ Subgroup.centralizer (ZS : Set G)) :
    Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ := by
  obtain ⟨h1, -, h3, h4⟩ := h314 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ s hKZ hGZ hK₂ hKZC
  exact ⟨s, hKZ, hGZ, hK₂, hKZC, h1, h3, h4⟩

end CFSG.Quasithin.H13.Ch4
