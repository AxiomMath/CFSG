module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Str

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Quasithin.J4M2


theorem mem_Kgrp_iff_rho (hF : J4Facts) (g : J) (hg : g ∈ M2) :
    g ∈ Kgrp ↔ rho hF ⟨g, hg⟩ = 1 :=
  mem_Kgrp_iff hF ⟨g, hg⟩

theorem relIndex_Qgrp_Kgrp (hF : J4Facts) : Qgrp.relIndex Kgrp = 3 := by
  have h := Subgroup.relIndex_mul_card (H := Qgrp) (K := Kgrp)
  have e1 : Qgrp ⊓ Kgrp = Qgrp := inf_of_le_left Qgrp_le_Kgrp
  have h2 : Nat.card ↥Kgrp = 3 * 2 ^ 13 := card_Kgrp hF
  have h3 : Nat.card ↥Qgrp = 2 ^ 13 := card_Qgrp hF.mat
  rw [e1] at h
  rw [h2, h3] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 13) h

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
