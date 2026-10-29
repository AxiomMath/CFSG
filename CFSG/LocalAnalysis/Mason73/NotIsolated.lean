module

public import CFSG.LocalAnalysis.Mason73.Complement
public import CFSG.Adapters.Involutions

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem uT_mul_tT_ne (hn : 2 ≤ n) :
    uT (n := n) (by omega) * tT (by omega) ≠ tT (by omega) * uT (by omega) := by
  rw [uT, tT, el_hv_mul, el_hv_mul, Ne, el_hv_eq_el_hv_iff' hn]
  decide

theorem exists_conj_zT_ne [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) :
    ∃ g : G, g⁻¹ * ι (zT (by omega)) * g ∈ ι.range ∧
      g⁻¹ * ι (zT (by omega)) * g ≠ ι (zT (by omega)) := by
  by_contra hcon
  push Not at hcon
  set z := ι (zT (n := n) (by omega)) with hz
  have hzS : z ∈ (S : Subgroup G) := by
    rw [← hS]
    exact ⟨_, rfl⟩
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨y, hy⟩
    rw [← hS] at hy
    obtain ⟨t, rfl⟩ := hy
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hz, ← map_mul, ← map_mul,
      Subgroup.mem_center_iff.1 (zT_mem_center (n := n) (by omega)) t]
  have hzo' : orderOf z = 2 := by rw [hz, orderOf_injective ι hι, orderOf_zT (by omega)]
  have hzo : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 :=
    (Subgroup.orderOf_coe (⟨z, hzS⟩ : (S : Subgroup G))).symm.trans hzo'
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hzo
    (fun g hg => hcon g (by rw [hS]; exact hg))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCore G) with hK | hK
  · have hzc : ∀ g : G, g * z = z * g := by
      intro g
      have h := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hK,
        Subgroup.mem_bot] at h
      exact inv_mul_eq_one.1 h
    have hzcen : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 hzc
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzo'
      norm_num at hzo'
    have htop : Subgroup.center G = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · rw [h, Subgroup.mem_bot] at hzcen
        exact absurd hzcen hz1
      · exact h
    apply uT_mul_tT_ne (n := n) (by omega)
    apply hι
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top (ι (tT (by omega)))) (ι (uT _)))
  · exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hzo' (hK ▸ Subgroup.mem_top z)

end CFSG.LocalAnalysis.Mason73
