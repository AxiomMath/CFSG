module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFR
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private lemma yfn_comm_inv {l t : G} (h : l * t = t * l) : t * l⁻¹ = l⁻¹ * t := by
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h]
  group

private lemma yfn_conj_mul_eq {z t l : G} (h : l * t = t * l) :
    l * (z * t) * l⁻¹ = (l * z * l⁻¹) * t := by
  rw [show l * (z * t) * l⁻¹ = l * z * (t * l⁻¹) by group, yfn_comm_inv h]
  group

private lemma yfn_conj_mul (g a b : G) :
    (g * a) * b * (g * a)⁻¹ = g * (a * b * a⁻¹) * g⁻¹ := by
  group

theorem s3_inv_arg (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (h31 : s.Fact31)
    (hA : LFactsA s) (e : Setting3.Ext s) {X : Subgroup G} (hXL : X ≤ L)
    (hgen : closure (invols X) = X) {x : G} (hx : x ∈ e.T₁)
    (hXx : ∀ y ∈ X, x * y * x⁻¹ ∈ X ∨ ∃ a ∈ X, x * y * x⁻¹ = a * s.t) :
    ∀ y ∈ X, x * y * x⁻¹ ∈ X := by
  have ht2 : s.t * s.t = 1 := by
    have h := pow_orderOf_eq_one s.t
    rw [s.t_order] at h
    simpa [pow_two] using h
  have key : ∀ u ∈ X, orderOf u = 2 → x * u * x⁻¹ ∈ X := by
    intro u hu hu2
    rcases hXx u hu with h | ⟨a, ha, haeq⟩
    · exact h
    · by_cases hxT : x ∈ s.T
      ·
        have hxN : x ∈ normalizer (L : Set G) := s3_T_le_N s hS hxT
        have hxuL : x * u * x⁻¹ ∈ L :=
          (Subgroup.mem_set_normalizer_iff.mp hxN u).mp (hXL hu)
        have htL : s.t ∈ L := by
          have hst : s.t = a⁻¹ * (x * u * x⁻¹) := by rw [haeq]; group
          rw [hst]
          exact L.mul_mem (L.inv_mem (hXL ha)) hxuL
        exact absurd htL (s3_t_not_mem_L s h31)
      ·
        have hxt : x * s.t * x⁻¹ = s.fr.z * s.t := s3_T1_conj_t s hA h31 e hx hxT
        have huu : u * u = 1 := by
          have h := pow_orderOf_eq_one u
          rw [hu2] at h
          simpa [pow_two] using h
        have hxu2 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
          calc (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
            _ = 1 := by rw [huu]; group
        have hat : (a * s.t) * (a * s.t) = 1 := by rw [← haeq]; exact hxu2
        have haa : a * a = 1 := by
          have hsq : (a * s.t) * (a * s.t) = a * a := by
            calc (a * s.t) * (a * s.t) = a * (s.t * a) * s.t := by group
              _ = a * (a * s.t) * s.t := by rw [s3_comm_t_of_mem_L s (hXL ha)]
              _ = (a * a) * (s.t * s.t) := by group
              _ = a * a := by rw [ht2, mul_one]
          rw [← hsq]
          exact hat
        have ha_ne : a ≠ 1 := by
          intro ha1
          have hxu_t : x * u * x⁻¹ = s.t := by rw [haeq, ha1, one_mul]
          have hconj : x⁻¹ * s.t * (x⁻¹)⁻¹ ∈ L := by
            have hg : x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u := by group
            rw [← hxu_t, hg]
            exact hXL hu
          exact h31.2.2.1 x⁻¹ hconj
        have ha2 : orderOf a = 2 :=
          orderOf_eq_prime (by rw [pow_two]; exact haa) ha_ne
        obtain ⟨l, hlL, hlaeq⟩ :=
          s3_invol_conj hS hZ s (s3_z_mem_L s) (s3_z_order s hA) (hXL ha) ha2
        have hux : x * u * x⁻¹ = (l * x) * s.t * (l * x)⁻¹ := by
          have h1 : x * u * x⁻¹ = l * (x * s.t * x⁻¹) * l⁻¹ := by
            rw [haeq, hlaeq, hxt]
            exact (yfn_conj_mul_eq (s3_comm_t_of_mem_L s hlL)).symm
          rw [h1, yfn_conj_mul l x s.t]
        have hgt : (x⁻¹ * l * x) * s.t * (x⁻¹ * l * x)⁻¹ = u := by
          have hkey : u = x⁻¹ * ((l * x) * s.t * (l * x)⁻¹) * x := by
            rw [← hux]
            group
          rw [hkey]
          group
        exfalso
        exact h31.2.2.1 (x⁻¹ * l * x) (by rw [hgt]; exact hXL hu)
  have hcl : closure (invols X) ≤ X.comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro u hu
    simp only [invols, Set.mem_setOf_eq] at hu
    exact key u hu.1 hu.2
  intro y hy
  have hy' : y ∈ X.comap (MulAut.conj x).toMonoidHom := (hgen ▸ hcl) hy
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using hy'

end CFSG.OddStandard.HigherRank.YamadaG23
