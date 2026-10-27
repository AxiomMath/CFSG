module

public import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.GF2Type.Aschbacher1976Full.HSEmbed
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnsideLayer2
public import CFSG.GF2Type.Aschbacher1976Full.HSAut
public import CFSG.GF2Type.Aschbacher1976Full.HSOne

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

theorem gl3Stmt_holds : GL3Stmt := fun hV hcomm hsq =>
  ⟨card_mulAut_eq_168 hV hcomm hsq, fun X h => dvd_56_of_dvd_14 hV hcomm hsq X h⟩

theorem embedStmt_holds : EmbedStmt := fun hZ hz hF2 => hbar_embeds_perm_six hZ hz hF2

theorem burnsideStmt_holds : BurnsideStmt :=
  fun hset hti T hTH hE hW => hsV_of_wide hset hti T hTH hE hW

theorem autStmt_holds : AutStmt := fun hset hV =>
  ⟨hsAut_surj gl3Stmt_holds hset hV, hsAut_card gl3Stmt_holds hset hV,
    fun _ _ hv hv' hvz hv'z => hsAut_transitive gl3Stmt_holds hset hV hv hv' hvz hv'z⟩

theorem hs1Stmt_holds :
    ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSS5 z →
      CFSG.Quasithin.HSType.HSOne z := fun hset hS5 => hsOne_of_S5 hset hS5

end CFSG.GF2Type.Aschbacher1976Full.HS
