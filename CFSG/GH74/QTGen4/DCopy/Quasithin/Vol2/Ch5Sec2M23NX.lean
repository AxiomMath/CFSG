module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23NX
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23MStr

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem isVFacts_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : IsVFacts M L := by
  obtain ⟨hbl, hLin, h16, hUQ, hL960⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hVsq := hbl.1.2.2.1
  rw [hUQ] at hVsq
  exact ⟨h16, fun v hv => by rw [← sq]; exact hVsq.2 v hv,
    fun v hv w hw => (Subgroup.mem_centralizer_iff.mp (hVsq.1 hw).2) v hv,
    fun W hW hWL => eq_bot_or_eq_of_le_pCoreOf_L hbl hLin h16 hUQ hW hWL,
    centralizer_le_pCoreOf_L_F4 h527 hyp h16, hyp.L_le, hyp.normal, hL960⟩

end CFSG.Quasithin.H13
