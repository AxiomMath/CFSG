module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransStarConj
public import CFSG.GF2Type.Aschbacher1976Full.HSTransInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCardSylow
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCardBound
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

namespace TransStar

variable {G : Type} [Group G] [Finite G]

theorem commute_of_twoBases (hNT : TwoBasesStmt) {z : G} (hset : HSSetting G z) (hti : HSTI z)
    {T T' : Sylow 2 G} (hTH : (T : Subgroup G) ≤ Hz z) (hT'H : (T' : Subgroup G) ≤ Hz z)
    {v : G} (hvT : v ∈ ET (T : Subgroup G) z) (hvT' : v ∈ ET (T' : Subgroup G) z)
    (hvz : v ∉ Subgroup.zpowers z) :
    ∀ u ∈ ET (T' : Subgroup G) z, ∀ w ∈ ET (T : Subgroup G) z, u * w = w * u := by
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  have c := BL.Ctx.mk hD hz hsymp.1 hTH
  have c' := BL.Ctx.mk hD hz hsymp.1 hT'H
  have hv1 : v ≠ 1 := fun h => hvz (by rw [h]; exact Subgroup.one_mem _)
  have hvVS := ((c.mem_ET_iff hti).mp hvT).resolve_left hv1
  have hvVS' := ((c'.mem_ET_iff hti).mp hvT').resolve_left hv1
  have hzv : z ≠ v := by
    rintro rfl
    exact hvz (Subgroup.mem_zpowers _)
  have hzE : z ∈ ET (T : Subgroup G) z :=
    (c.mem_ET_iff hti).mpr (Or.inr ⟨IsConj.refl z, by rw [c.ZF_self]; exact c.Z_le_T⟩)
  have hzE' : z ∈ ET (T' : Subgroup G) z :=
    (c'.mem_ET_iff hti).mpr (Or.inr ⟨IsConj.refl z, by rw [c'.ZF_self]; exact c'.Z_le_T⟩)
  intro u hu w hw
  rcases (c'.mem_ET_iff hti).mp hu with rfl | hu1
  · rw [one_mul, mul_one]
  rcases (c.mem_ET_iff hti).mp hw with rfl | hw1
  · rw [one_mul, mul_one]
  by_cases huzv : u = z ∨ u = v
  · have huE : u ∈ ET (T : Subgroup G) z := by
      rcases huzv with rfl | rfl
      exacts [hzE, hvT]
    exact ET_comm c hti huE hw
  by_cases hwzv : w = z ∨ w = v
  · have hwE' : w ∈ ET (T' : Subgroup G) z := by
      rcases hwzv with rfl | rfl
      exacts [hzE', hvT']
    exact ET_comm c' hti hu hwE'
  obtain ⟨huz, huv⟩ := not_or.mp huzv
  obtain ⟨hwz, hwv⟩ := not_or.mp hwzv
  refine hNT hset hti (IsConj.refl z) hvVS.1 hzv hu1.1 hw1.1 huz huv hwz hwv ?_ ?_ ?_ ?_
  · exact hu1.2.trans hT'H
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact c'.WZ_comm x (c'.ZF_le_WZ hu1 hx) v (c'.mem_WZ_of_mem_VS hvVS')
  · exact hw1.2.trans hTH
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact c.WZ_comm x (c.ZF_le_WZ hw1 hx) v (c.mem_WZ_of_mem_VS hvVS)

theorem ET_le_of_commute {z : G} {Z A : Subgroup G} {T T' : Sylow 2 G} (hD : Width.Z4Data z 2 Z A)
    (c : BL.Ctx z 2 Z A T) (c' : BL.Ctx z 2 Z A T') (hti : HSTI z)
    (hcard : Nat.card (ET (T : Subgroup G) z) = 8)
    (hcomm : ∀ u ∈ ET (T' : Subgroup G) z, ∀ w ∈ ET (T : Subgroup G) z, u * w = w * u) :
    ET (T' : Subgroup G) z ≤ ET (T : Subgroup G) z := by
  have hsup := CFSG.Open.IsElemAbelian.sup_of_commute (isElemAbelian_ET c' hti)
    (isElemAbelian_ET c hti) hcomm
  have hF : ET (T' : Subgroup G) z ⊔ ET (T : Subgroup G) z ≤ Fz z :=
    sup_le (ET_le_F c' hti) (ET_le_F c hti)
  have hle : Nat.card ↥(ET (T' : Subgroup G) z ⊔ ET (T : Subgroup G) z) ≤ 8 := by
    have := Card.card_elemAbelian_le hD c.hz hF hsup
    norm_num at this
    exact this
  have heq : ET (T : Subgroup G) z = ET (T' : Subgroup G) z ⊔ ET (T : Subgroup G) z :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcard]; exact hle)
  exact le_sup_left.trans heq.symm.le

end TransStar

theorem starStmt_of_twoBases (hNT : TwoBasesStmt) : StarStmt := by
  intro G _ _ z hset hti T hTH hcard v y hvE hvz hZv P hPH hP2 hyP
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  have hPF : IsPGroup 2 ↥(P ⊔ Fz z) :=
    hP2.to_sup_of_normal_right' hF2 (Card.le_normalizer_Fz hPH)
  obtain ⟨T', hPT', hT'H⟩ := Card.exists_sylow hD hz hF2 (K := P ⊔ Fz z) le_sup_right
    (sup_le hPH (Card.Fz_le_Hz z)) hPF
  have c := BL.Ctx.mk hD hz hF2 hTH
  have c' := BL.Ctx.mk hD hz hF2 hT'H
  have hv1 : v ≠ 1 := fun h => hvz (by rw [h]; exact Subgroup.one_mem _)
  have hvVS := ((c.mem_ET_iff hti).mp hvE).resolve_left hv1
  have hvT' : v ∈ ET (T' : Subgroup G) z := by
    refine (c'.mem_ET_iff hti).mpr (Or.inr ⟨hvVS.1, ?_⟩)
    rw [hZv]
    exact (Subgroup.zpowers_le.mpr hyP).trans (le_sup_left.trans hPT')
  have hcomm := TransStar.commute_of_twoBases hNT hset hti hTH hT'H hvE hvT' hvz
  have hle := TransStar.ET_le_of_commute hD c c' hti hcard hcomm
  have heq : ET (T' : Subgroup G) z = ET (T : Subgroup G) z :=
    Subgroup.eq_of_le_of_card_ge hle (TransStar.card_ET_eq z T T').ge
  have hPT : P ≤ (T' : Subgroup G) := le_sup_left.trans hPT'
  rw [← heq]
  exact hPT.trans (TransStar.le_normalizer_ET c' hti)

end CFSG.GF2Type.Aschbacher1976Full.HS
