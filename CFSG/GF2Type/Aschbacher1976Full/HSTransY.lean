module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSTransYQuot
public import CFSG.GF2Type.Aschbacher1976Full.HSTransYW

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

theorem yStructStmt_holds : YStructStmt := by
  intro G _ _ z hset hti T hTH hcard hW
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  have c : BL.Ctx z 2 Z A T := ⟨hD, hz, hsymp.1, hTH⟩
  have hWH : BL.WZ Z (T : Subgroup G) ≤ Hz z := BL.WZ_le.trans hTH
  have hWcard : 128 ≤ Nat.card (BL.WZ Z (T : Subgroup G)) :=
    TransY.card_WZ_ge c hti hcard (by rw [← c.WT_eq]; exact hW)
  have hV := TransY.elemV c hti hcard
  obtain ⟨v, hvV, hvz⟩ := hV.exists_not_mem_zpowers hz
  have hv1 : v ≠ 1 := fun h => hvz (h ▸ Subgroup.one_mem _)
  have hvz' : v ≠ z := fun h => hvz (h ▸ Subgroup.mem_zpowers z)
  have hvS := ((c.mem_ET_iff hti).mp hvV).resolve_left hv1
  obtain ⟨y, hy⟩ := PartC.exists_gen hD hz hsymp.1 hvS.1
  have hyW : y ∈ BL.WZ Z (T : Subgroup G) := c.ZF_le_WZ hvS (hy ▸ Subgroup.mem_zpowers y)
  have hyH : y ∈ Hz z := hWH hyW
  have hDinv : v ∈ Dinv z := ⟨hvS.1, hvz', hvS.2.trans hTH⟩
  have hyF : y ∉ Fz z := (hti.2 v hDinv).2 y hy
  have hbound : Nat.card ↥(BL.WZ Z (T : Subgroup G) ⊓ Fz z) ≤ 16 := by
    refine le_trans (Subgroup.card_le_of_le (K := Fz z ⊓
      Subgroup.centralizer (ET (T : Subgroup G) z : Set G)) ?_) (hV.card_inf_centralizer_le hset')
    rintro x ⟨hxW, hxF⟩
    refine ⟨hxF, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    exact c.WZ_comm u (c.mem_WZ_of_mem_ET hti hu) x hxW
  refine ⟨v, y, hyH, TransY.imgW z (BL.WZ Z (T : Subgroup G)) hWH, hvV, hvz, hy,
    TransY.imgW_comm hWH c.WZ_comm,
    TransY.imgW_sq hWH fun a ha => hV.le_F (TransY.sq_mem_of_mem_WZ c ha), ?_,
    TransY.qmk_mem_imgW hWH (h := ⟨y, hyH⟩) hyW, ?_, ?_⟩
  · have h1 := TransY.card_le_imgW_mul hWH
    by_contra hlt
    push Not at hlt
    nlinarith
  · rw [Ne, qmk_eq_one_iff]
    exact hyF
  · intro n hn hnV
    exact TransY.qmk_mem_normalizer_imgW hWH hn
      (fun x hx => TransY.conj_mem_WZ c hti hnV hx)
      (fun x hx => by
        simpa using TransY.conj_mem_WZ c hti ((Subgroup.normalizer _).inv_mem hnV) hx)

end CFSG.GF2Type.Aschbacher1976Full.HS
