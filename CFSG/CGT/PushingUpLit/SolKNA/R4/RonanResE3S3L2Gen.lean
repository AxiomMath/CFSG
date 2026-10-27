module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Sec
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Pkg

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

theorem l2GenR_holds (r : ℕ) : L2GenR r := by
  intro hr A _ _ T _ hT hC R S z hd hc s hzT hcomm hsz hconj
  obtain ⟨x, b, hxS, hbS, hxo, hbx, hbb⟩ := exists_quat_full_of_datum (by omega : 3 ≤ r) hc
  have hxR : x ∈ R := mem_sylowSet_le S hxS
  have hzx : x ^ 2 ^ (r - 2) = z := by
    apply hd.eq_of_orderOf_eq_two (Subgroup.pow_mem _ hxR _)
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (by rw [hxo]; exact pow_dvd_pow 2 (by omega)),
      hxo, show 2 ^ (r - 1) = 2 * 2 ^ (r - 2) by rw [← pow_succ']; congr 1; omega]
    exact Nat.mul_div_cancel 2 (by positivity)
  obtain ⟨-, ⟨p, f, K, _, _, hp, hp2, hKcard, h4, h13, ⟨e⟩⟩, -⟩ :=
    l2_package hr T hT hC hxo hbx hbb hzx
  exact E3C269G2.sup_centralizer_eq_top_of_normal hp hp2 hKcard h4 h13 e hzT hd.order hsz hconj

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
