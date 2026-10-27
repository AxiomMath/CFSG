module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCTwo

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup

theorem hsPartTrans_of_inputs (hEmb : EmbedStmt) (hStar : StarStmt) (hFin : FinStmt)
    (hY : YStructStmt) : HSPartTrans := by
  intro G _ _ z hset hti hcfg
  obtain ⟨T, hTH, hE, hW⟩ := hcfg
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨ι, hι⟩ := PartC.exists_injective_iota hEmb hz hZ4 hF2
  obtain ⟨v, y, hy, Y, hvE, hvz, hZv, hYc, hYsq, hYcard, haY, ha1, hYn⟩ :=
    hY hset hti T hTH hE hW
  obtain ⟨P', hP'2, haP', hP'n⟩ :=
    hFin ι hι (PartC.O2_quotient_trivial hF2) Y hYc hYsq hYcard _ haY ha1
  apply hP'n
  have hker : IsPGroup 2 ↥(qmk z).ker := by
    rw [ker_qmk]
    exact hF2.comap_subtype
  have hpre : IsPGroup 2 ↥(P'.comap (qmk z)) :=
    IsPGroup.comap_of_ker_isPGroup hP'2 (qmk z) hker
  have hP2 : IsPGroup 2 ↥((P'.comap (qmk z)).map (Hz z).subtype) := hpre.map _
  have hPH : (P'.comap (qmk z)).map (Hz z).subtype ≤ Hz z := by
    rintro x ⟨h, _, rfl⟩
    exact h.2
  have hyP : y ∈ (P'.comap (qmk z)).map (Hz z).subtype := ⟨⟨y, hy⟩, haP', rfl⟩
  have hPN := hStar hset hti T hTH hE hvE hvz hZv _ hPH hP2 hyP
  intro q hq
  obtain ⟨h, rfl⟩ := qmk_surjective z q
  have hhP : (h : G) ∈ (P'.comap (qmk z)).map (Hz z).subtype := ⟨h, hq, rfl⟩
  exact hYn (h : G) h.2 (hPN hhP)

end CFSG.GF2Type.Aschbacher1976Full.HS
