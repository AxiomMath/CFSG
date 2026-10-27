module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34V2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem521

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

namespace Setup521

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}
variable (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem mem_T_of_conj_eq_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) {z : G} (hz : z ∈ Z₁)
    (hz1 : z ≠ 1) {x : G} (hx : x ∈ conjClosure D₃ T ⊔ T) (hxz : x * z * x⁻¹ = z) : x ∈ T := by
  have hTL₂ : T ≤ Subgroup.normalizer (conjClosure D₃ T : Set G) := le_normalizer_conjClosure D₃ T
  have hset : ((conjClosure D₃ T ⊔ T : Subgroup G) : Set G) =
      (conjClosure D₃ T : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTL₂
  have hx' : x ∈ (conjClosure D₃ T : Set G) * (T : Set G) := by rw [← hset]; exact hx
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  have hset2 : ((T ⊓ L ⊔ D₃ : Subgroup G) : Set G) =
      ((T ⊓ L : Subgroup G) : Set G) * (D₃ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ s.D₃_le_normalizer_inf
  have hl' : l ∈ ((T ⊓ L : Subgroup G) : Set G) * (D₃ : Set G) := by
    rw [← hset2]; exact s.L₂_le hF hl
  obtain ⟨u, hu, e, he, rfl⟩ := Set.mem_mul.mp hl'
  have htz := s.conj_eq_of_mem_T ht hz
  have huz := s.conj_eq_of_mem_T hu.1 hz
  have hez : e * z * e⁻¹ = z := by
    have e1 : e * z * e⁻¹ = u⁻¹ * (u * e * t * z * (u * e * t)⁻¹) * u := by
      rw [show u * e * t * z * (u * e * t)⁻¹ = u * e * (t * z * t⁻¹) * e⁻¹ * u⁻¹ by group, htz]
      group
    rw [e1, hxz]
    have e2 : u⁻¹ * z * u = u⁻¹ * (u * z * u⁻¹) * u := by rw [huz]
    rw [e2]
    group
  have he1 : e = 1 := by
    by_contra he1
    exact s.hyp.conj_ne_F4 h5114 s.card_D₃ s.not_le (s.Z₁_le_Z hz) hz1 he he1 hez
  rw [he1, mul_one]
  exact T.mul_mem hu.1 ht

theorem inf_centralizer_le_T_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    (conjClosure D₃ T ⊔ T) ⊓ Subgroup.centralizer (Z₁ : Set G) ≤ T := by
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  rintro x ⟨hx, hxC⟩
  refine s.mem_T_of_conj_eq_F4 h5114 hF hz hz1 hx ?_
  rw [← Subgroup.mem_centralizer_iff.mp hxC z hz, mul_assoc, mul_inv_cancel, mul_one]

theorem inf_normalizer_le_T_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    conjClosure D₃ T ⊓ Subgroup.normalizer (Z₁ : Set G) ≤ T := by
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  rintro x ⟨hx, hxN⟩
  have hxz : x * z * x⁻¹ ∈ Z₁ := (Subgroup.mem_normalizer_iff.mp hxN z).mp hz
  refine s.mem_T_of_conj_eq_F4 h5114 hF hz hz1 (Subgroup.mem_sup_left hx) ?_
  rcases s.eq_one_or_eq hz hz1 hxz with h1 | h1
  · exfalso
    apply hz1
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h1]; group
  · exact h1

theorem inf_centralizer_V₂_le_T_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    (conjClosure D₃ T ⊔ T) ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤ T :=
  le_trans (inf_le_inf_left _ (Subgroup.centralizer_le (le_conjClosure Z₁ D₃)))
    (s.inf_centralizer_le_T_F4 h5114 hF)

section Elements

variable {z d : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hd : d ∈ D₃) (hd1 : d ≠ 1)
include hz hz1 hd hd1

omit hz1 in

theorem norm_eq_one_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    z * (d * z * d⁻¹) * (d ^ 2 * z * (d ^ 2)⁻¹) = 1 :=
  s.hyp.norm_eq_one_F4 h5114 hF s.le_D s.card_D₃ s.not_le (s.Z₁_le_Z hz) hd hd1

theorem b_props_F4 (h5114 : Stmt5_1_14_first_F4) :
    Commute z (d * z * d⁻¹) ∧ (d * z * d⁻¹) ^ 2 = 1 ∧ d * z * d⁻¹ ≠ 1 ∧ d * z * d⁻¹ ≠ z := by
  obtain ⟨hzP, -⟩ := s.conj_mem (D₃.one_mem) hz
  obtain ⟨hbP, hb2⟩ := s.conj_mem hd hz
  simp only [one_mul, inv_one, mul_one] at hzP
  refine ⟨Subgroup.mem_centralizer_iff.mp hbP.2 z hzP.1, hb2, ?_,
    s.hyp.conj_ne_F4 h5114 s.card_D₃ s.not_le (s.Z₁_le_Z hz) hz1 hd hd1⟩
  intro hb
  apply hz1
  have : z = d⁻¹ * (d * z * d⁻¹) * d := by group
  rw [this, hb]; group

theorem c_eq_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    d ^ 2 * z * (d ^ 2)⁻¹ = z * (d * z * d⁻¹) := by
  obtain ⟨hzb, hb2, -, -⟩ := s.b_props_F4 hz hz1 hd hd1 h5114
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hz)).2.2
  have e1 : d ^ 2 * z * (d ^ 2)⁻¹ = (z * (d * z * d⁻¹))⁻¹ :=
    eq_inv_of_mul_eq_one_right (s.norm_eq_one_F4 hz hd hd1 h5114 hF)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  have hbi : (d * z * d⁻¹)⁻¹ = d * z * d⁻¹ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
  rw [e1, mul_inv_rev, hzi, hbi]
  exact hzb.symm.eq

theorem V₂_le_sup_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    conjClosure Z₁ D₃ ≤ Z₁ ⊔ Subgroup.zpowers (d * z * d⁻¹) := by
  refine conjClosure_le fun g hg y hy => ?_
  rcases s.eq_one_or_eq hz hz1 hy with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  rcases eq_one_or_eq_or_eq_sq_of_card_three s.card_D₃ hd hd1 hg with rfl | rfl | rfl
  · rw [one_mul, inv_one, mul_one]; exact Subgroup.mem_sup_left hz
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · rw [s.c_eq_F4 hz hz1 hd hd1 h5114 hF]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem zpowers_le_normalizer_F4 (h5114 : Stmt5_1_14_first_F4) :
    Subgroup.zpowers (d * z * d⁻¹) ≤ Subgroup.normalizer (Z₁ : Set G) := by
  obtain ⟨hzb, -, -, -⟩ := s.b_props_F4 hz hz1 hd hd1 h5114
  rw [Subgroup.zpowers_le]
  apply mem_normalizer_of_forall_conj_mem'
  intro y hy
  rcases s.eq_one_or_eq hz hz1 hy with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Z₁.one_mem
  · rw [hzb.symm.eq, mul_assoc, mul_inv_cancel, mul_one]; exact hz

theorem mem_V₂_iff_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) {w : G}
    (hw : w ∈ conjClosure Z₁ D₃) :
    ∃ u ∈ Z₁, w = u ∨ w = u * (d * z * d⁻¹) := by
  have hset : ((Z₁ ⊔ Subgroup.zpowers (d * z * d⁻¹) : Subgroup G) : Set G) =
      (Z₁ : Set G) * (Subgroup.zpowers (d * z * d⁻¹) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (s.zpowers_le_normalizer_F4 hz hz1 hd hd1 h5114)
  have hmem : w ∈ (Z₁ : Set G) * (Subgroup.zpowers (d * z * d⁻¹) : Set G) := by
    rw [← hset]; exact s.V₂_le_sup_F4 hz hz1 hd hd1 h5114 hF hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hmem
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨-, hb2, hb1, -⟩ := s.b_props_F4 hz hz1 hd hd1 h5114
  have hord : orderOf (d * z * d⁻¹) = 2 := orderOf_eq_prime hb2 hb1
  refine ⟨u, hu, ?_⟩
  rcases Int.emod_two_eq_zero_or_one j with hj | hj
  · left
    rw [← zpow_mod_orderOf, hord]; push_cast; rw [hj, zpow_zero, mul_one]
  · right
    rw [← zpow_mod_orderOf, hord]; push_cast; rw [hj, zpow_one]

theorem Z₁_lt_V₂_F4 (h5114 : Stmt5_1_14_first_F4) : Z₁ < conjClosure Z₁ D₃ := by
  refine lt_of_le_of_ne (le_conjClosure Z₁ D₃) fun he => ?_
  obtain ⟨-, -, hb1, hbz⟩ := s.b_props_F4 hz hz1 hd hd1 h5114
  have hb' : d * z * d⁻¹ ∈ Z₁ := he ▸ mem_conjClosure hd hz
  rcases s.eq_one_or_eq hz hz1 hb' with h1 | h1
  · exact hb1 h1
  · exact hbz h1

theorem eq_or_eq_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) {W : Subgroup G} (hW1 : Z₁ ≤ W)
    (hW2 : W ≤ conjClosure Z₁ D₃) : W = Z₁ ∨ W = conjClosure Z₁ D₃ := by
  by_cases hbW : d * z * d⁻¹ ∈ W
  · right
    refine le_antisymm hW2 fun w hw => ?_
    obtain ⟨u, hu, rfl | rfl⟩ := s.mem_V₂_iff_F4 hz hz1 hd hd1 h5114 hF hw
    · exact hW1 hu
    · exact W.mul_mem (hW1 hu) hbW
  · left
    refine le_antisymm (fun w hw => ?_) hW1
    obtain ⟨u, hu, rfl | rfl⟩ := s.mem_V₂_iff_F4 hz hz1 hd hd1 h5114 hF (hW2 hw)
    · exact hu
    · exfalso
      apply hbW
      have : d * z * d⁻¹ = u⁻¹ * (u * (d * z * d⁻¹)) := by group
      rw [this]
      exact W.mul_mem (W.inv_mem (hW1 hu)) hw

theorem exists_conj_eq_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) {w : G}
    (hw : w ∈ conjClosure Z₁ D₃) (hw1 : w ≠ 1) : ∃ e ∈ D₃, e * w * e⁻¹ = z := by
  have hd3 := pow_three_of_mem_of_card_three s.card_D₃ hd
  obtain ⟨u, hu, rfl | rfl⟩ := s.mem_V₂_iff_F4 hz hz1 hd hd1 h5114 hF hw
  · rcases s.eq_one_or_eq hz hz1 hu with rfl | rfl
    · exact absurd rfl hw1
    · exact ⟨1, D₃.one_mem, by group⟩
  · rcases s.eq_one_or_eq hz hz1 hu with rfl | rfl
    · exact ⟨d⁻¹, D₃.inv_mem hd, by group⟩
    · refine ⟨d, hd, ?_⟩
      rw [← s.c_eq_F4 hz hz1 hd hd1 h5114 hF]
      have : d * (d ^ 2 * u * (d ^ 2)⁻¹) * d⁻¹ = d ^ 3 * u * (d ^ 3)⁻¹ := by group
      rw [this, hd3]
      group

theorem z_mem_L₂_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) : z ∈ conjClosure D₃ T := by
  have hzT : z ∈ T := quasithinOmegaOneCenter_le_self T (s.Z₁_le_Z hz)
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hz)).2.2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  have hdL₂ : d ∈ conjClosure D₃ T := le_conjClosure D₃ T hd
  have hc : z * (d * z * d⁻¹) ∈ conjClosure D₃ T := by
    have e1 : z * (d * z * d⁻¹) = (z * d * z⁻¹) * d⁻¹ := by rw [hzi]; group
    rw [e1]
    exact Subgroup.mul_mem _ (mem_conjClosure hzT hd) (Subgroup.inv_mem _ hdL₂)
  have hd3 := pow_three_of_mem_of_card_three s.card_D₃ hd
  have e2 : z = d * (z * (d * z * d⁻¹)) * d⁻¹ := by
    rw [← s.c_eq_F4 hz hz1 hd hd1 h5114 hF]
    have : d * (d ^ 2 * z * (d ^ 2)⁻¹) * d⁻¹ = d ^ 3 * z * (d ^ 3)⁻¹ := by group
    rw [this, hd3]
    group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hdL₂ hc) (Subgroup.inv_mem _ hdL₂)

end Elements

theorem V₂_le_L₂_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    conjClosure Z₁ D₃ ≤ conjClosure D₃ T := by
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hzL := s.z_mem_L₂_F4 hz hz1 hd hd1 h5114 hF
  refine conjClosure_le fun g hg y hy => ?_
  rcases s.eq_one_or_eq hz hz1 hy with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · have hgL : g ∈ conjClosure D₃ T := le_conjClosure D₃ T hg
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL hzL) (Subgroup.inv_mem _ hgL)

end Setup521

end CFSG.Quasithin.H13
