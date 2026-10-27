module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.Vol2.Ch3T326A

public section
namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open T325 (V₀_le_V V_le_VM T_le_NV M_le_NVM isSylowTwoOf_of_le)

variable {G : Type} [Group G]

theorem Ctx.of_F4 [CFSG.GH74.QTGen4.Finite4 G] (h331 : Stmt3_3_1_F4) (h3222 : Vol2.Ch10.TmpL6_3_2_2_two)
    (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight) {T L V₀ : Subgroup G} (hfsu : FSU G T L V₀)
    (hne : L ≠ conjClosure L T) : Ctx T L V₀ := by
  obtain ⟨⟨hmax, hLT, huniq⟩, -, hH, -⟩ :=
    (h331 G T hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow).2 L hfsu.maximal hfsu.quasisimple
  have h1 : IsTwoReducedIn (fsuM T L) (fsuVM T L V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 (h3222 G T L V₀ hfsu)
  obtain ⟨hVLT, hredV, hO⟩ := h3228 G T L V₀ hfsu
  have h2 : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hredV⟩
  exact ⟨hfsu, hne, hmax, ⟨⟨hmax, hLT⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩, hH, h1, h2, hO⟩

end CFSG.Quasithin.H13.T326
