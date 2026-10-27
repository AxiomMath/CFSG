module

public import CFSG.GH74.QTGen4.Recog.Ku.OpenLeaves
public import CFSG.GH74.QTGen4.Recog.Ku.HStruct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

private theorem mem_of_orderOf_three_of_three_dvd [Finite G] {H D : Subgroup G} {x : G}
    (hH : Nat.card H = 384) (hDH : D ≤ H) (hDn : H ≤ Subgroup.normalizer (D : Set G))
    (hxH : x ∈ H) (hx3 : orderOf x = 3) (h3 : 3 ∣ Nat.card D) : x ∈ D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfacH : (Nat.card H).factorization 3 = 1 := by
    rw [hH, show (384 : ℕ) = 3 * 2 ^ 7 by norm_num,
      Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow,
      Nat.Prime.factorization Nat.prime_two]
    simp
  have hsyl : IsSylowIn 3 (Subgroup.zpowers x) H :=
    isSylowIn_of_card_eq (Subgroup.zpowers_le.mpr hxH)
      (by rw [Nat.card_zpowers, hx3, hfacH, pow_one])
  have hsylD := hsyl.inf_normal hDH (Subgroup.normal_subgroupOf_of_le_normalizer hDn)
  have hpos : 0 < (Nat.card D).factorization 3 :=
    Nat.prime_three.factorization_pos_of_dvd Nat.card_pos.ne' h3
  have hge : 3 ≤ Nat.card (Subgroup.zpowers x ⊓ D : Subgroup G) := by
    rw [hsylD.card_eq]
    calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ (Nat.card D).factorization 3 := Nat.pow_le_pow_right (by norm_num) hpos
  have heq : Subgroup.zpowers x ⊓ D = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hx3]; exact hge)
  have hx1 : x ∈ Subgroup.zpowers x ⊓ D := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact (Subgroup.mem_inf.mp hx1).2

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem H_le_normalizer_inf_centralizer_kuW (h : KuHyp G T M H P z) :
    H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (kuW P H : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf_of Subgroup.le_normalizer (le_normalizer_centralizer_of h.H_le_normalizer_kuW)

theorem not_three_dvd_card_inf_centralizer_kuW (h : KuHyp G T M H P z) :
    ¬ 3 ∣ Nat.card ↥(H ⊓ Subgroup.centralizer (kuW P H : Set G)) := by
  intro h3D
  obtain ⟨x, hxH, hx3, hfix⟩ := h.exists_x
  have hxD : x ∈ H ⊓ Subgroup.centralizer (kuW P H : Set G) :=
    mem_of_orderOf_three_of_three_dvd (D := H ⊓ Subgroup.centralizer (kuW P H : Set G))
      h.card_H inf_le_left h.H_le_normalizer_inf_centralizer_kuW hxH hx3 h3D
  obtain ⟨c, hc, hcz⟩ := h.exists_mem_kuW_not_mem_zpowers
  have hcx : c * x = x * c := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxD).2 c hc
  have hxc : x * c * x⁻¹ = c := by rw [← hcx, mul_inv_cancel_right]
  exact hcz (hfix c (h.kuW_le_P hc) hxc)

theorem H_inf_centralizer_kuW_le_pCore (h : KuHyp G T M H P z) :
    H ⊓ Subgroup.centralizer (kuW P H : Set G) ≤ pCoreOf 2 H := by
  have hdvd : Nat.card ↥(H ⊓ Subgroup.centralizer (kuW P H : Set G)) ∣ 2 ^ 7 * 3 := by
    rw [show (2 : ℕ) ^ 7 * 3 = Nat.card H by norm_num [h.card_H]]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(H ⊓ Subgroup.centralizer (kuW P H : Set G))) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      h.not_three_dvd_card_inf_centralizer_kuW).symm
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hcop.dvd_of_dvd_mul_right hdvd)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    h.H_le_normalizer_inf_centralizer_kuW (IsPGroup.of_card hm)

end KuHyp

theorem leafTInfCentralizerKuWLeKuA : LeafTInfCentralizerKuWLeKuA := by
  intro G _ _ T M H P z h
  intro x hx
  have hxT : x ∈ T := (Subgroup.mem_inf.mp hx).1
  have hxC : x ∈ Subgroup.centralizer (kuW P H : Set G) := (Subgroup.mem_inf.mp hx).2
  have hxH : x ∈ H ⊓ Subgroup.centralizer (kuW P H : Set G) :=
    Subgroup.mem_inf.mpr ⟨h.tH hxT, hxC⟩
  exact Subgroup.mem_inf.mpr ⟨h.H_inf_centralizer_kuW_le_pCore hxH, hxC⟩

end CFSG.GH74.QTGen4.Ku
