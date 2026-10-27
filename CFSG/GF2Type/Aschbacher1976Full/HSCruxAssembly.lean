module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxBasic
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxHyper
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxS0
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxFibre
public import CFSG.GF2Type.Aschbacher1976Full.HSDischarge
public import CFSG.GF2Type.Aschbacher1976Full.HSBadCrux
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCTwo

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC

theorem badCruxStmt_of_inputs (hSix : CruxSixStmt) (hNine : CruxNineStmt) (hPLocal : CruxPLocalStmt)
    (hFrattini : CruxFrattiniStmt) (hFinW : CruxFinWStmt) (hQuad : CruxQuadStmt)
    (hL5 : CruxL5Stmt) : BadCruxStmt := by
  intro G _ _ z hset hti T hTH hcard k hk
  have hbad : BadAt z T := ⟨hset, hti, hTH, hcard⟩
  have hfib : FibreProp z := cruxFibre_holds hbad
  obtain ⟨hne, hinv, hconj, hno⟩ := dtil_hyps hset hti hfib
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨ι, hι⟩ := exists_injective_iota embedStmt_holds hz hZ4 hF2
  obtain ⟨hord, hsmall | ⟨-, hcn⟩⟩ :=
    hSix ι hι (O2_quotient_trivial hF2) (Dtil z) hne hinv hconj hno
  · exfalso
    refine hsmall.2 (hFrattini hset hti hfib (hPLocal hset hti) ?_)
    refine transitive_of_odd (Dtil z) (fun d hd => (hinv d hd).1) fun d hd e he hde => ?_
    rcases hord d hd e he hde with h | h <;> rw [h] <;> decide
  · obtain ⟨hnf, htf⟩ := hNine ι hι (Dtil z) hconj hcn
    obtain ⟨θ, hθ⟩ := hQuad hFinW hset hti hnf
    obtain ⟨E, hE⟩ := exists_cruxE_of_quad hset hti hk hθ
    have hk5 := hL5 hbad hfib k hk E hE htf
    intro hmem
    refine hk5 (sup_le_sup_left ((Subgroup.closure_le E).mpr ?_) _ hmem)
    rintro u ⟨-, huc, huk⟩
    rcases cruxS0_holds hset k hk u huc huk with rfl | hu
    · exact hE.2.2.1
    · exact hE.2.2.2.2.2 hu

end CFSG.GF2Type.Aschbacher1976Full.HS
