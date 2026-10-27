module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I163
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem eTable_of_bounds {lab : GLALabel} {c : Prop} {e : ℕ} (hE : Rk2ELowAt lab c e)
    (hU : Rk2EUpAt lab c e) : ETable lab c e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hn
    refine le_antisymm (hU.bd h hn) (hE.bcd_ge ?_ hn)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · intro h hn
    exact le_antisymm (hU.f4 h hn) (hE.f4 h hn)
  · intro h hn
    exact le_antisymm (hU.e7 h hn) (hE.e7 h hn)
  · intro h hn
    exact le_antisymm (hU.e8 h hn) (hE.e8 h hn)
  · intro h hc
    have hlow := hE.a_ge (by rw [h]) (by rw [h])
    rw [h] at hlow
    exact le_antisymm (hU.a5 h hc) hlow
  · intro h hc
    have hlow := hE.e6_two (by rw [h]) (by rw [h])
    exact le_antisymm (hU.e6_two h hc) hlow
  · intro h
    have hlow := hE.a_one (by rw [h]) (by rw [h])
    rw [h] at hlow
    exact le_antisymm (hU.a8 h) (by simpa using hlow)
  · intro h
    have hlow := hE.e6_one (by rw [h]) (by rw [h])
    exact le_antisymm (hU.e6_one h) hlow
  · intro ⟨ht, hr⟩ hn hc
    have hlow := hE.twa_one ht (by rw [hr]; exact rk2_not_dvd_six hn)
    rw [hr] at hlow
    exact le_antisymm (hU.twa5 ⟨ht, hr⟩ hn hc) hlow
  · intro ht hn hc
    exact le_antisymm (hU.twe6 ht hn hc) (hE.twe6 ht hn)
  · intro ⟨ht, hr⟩ hn
    have hlow := hE.a_ge ht hn
    rw [hr] at hlow
    exact hlow

theorem eTableAt_of_tables (hK : Rk2KRank) (hLow : Rk2Lower) (hUp : Rk2Upper) (G : Type) [Group G]
    [Finite G] : ETableAt G := by
  intro K lab hLab
  exact eTable_of_bounds (hLow ↥K lab hLab) (rk2_eUpAt_of_tables hK hUp hLab)

end CFSG.LocalAnalysis.GLTheoremA
