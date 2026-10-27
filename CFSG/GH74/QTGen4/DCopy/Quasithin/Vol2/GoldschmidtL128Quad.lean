module

public import CFSG.Quasithin.Vol2.GoldschmidtL128Quad
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneHat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem lemma12_8_8_two_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) : Lemma12_8_8_two_F4 := by
  intro G _ _ T L V n V₁ V₂ hs D
  have hA := hs.almostSpecial_F4 h1222 h12213
  refine ⟨L128A.HatU.B_isAlt D, L128A.HatU.B_nondegenerate D, ?_, ?_⟩
  · intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w
  · intro hΦ
    have hU2 : IsPGroup 2 ↥(u128 V V₁) := hs.hyp.hyp.sylow.1.to_le hA.G22_three.1
    have hZ : ∀ z ∈ zU128 V V₁, z ^ 2 = 1 := fun z hz =>
      L128A.HatU.sq_eq_one_of_frattiniOf_eq_bot (hU2.to_le inf_le_left) hΦ hz
    obtain ⟨q, hq1, hq2, hq3⟩ := L128A.HatU.exists_quadratic D (by simpa using hs.v1.2.1)
      (hs.le_centerOf_F4 h1222 h12213) (fun a ha b hb => hA.G22_commutator_mem ha hb)
      (fun a ha => hA.G22_sq_mem ha) hZ
    refine ⟨q, fun u hu => ?_, hq2, fun γ hγ v => ?_⟩
    · rw [hq1 u hu, L128A.HatU.eps_eq_zero_iff]
    · obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
      exact hq3 ⟨x, hxN⟩ v

end CFSG.Quasithin.H13
