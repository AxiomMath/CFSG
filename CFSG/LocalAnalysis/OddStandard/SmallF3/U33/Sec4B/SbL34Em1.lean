module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

theorem card_pgroup_le_of_conj {G : Type*} [Group G] [Finite G] {t q g : G}
    (hg : g * t * g⁻¹ = q) (S : Subgroup G) {n : ℕ}
    (hS : S ≤ Subgroup.centralizer ({t} : Set G))
    (hSodd : ¬ 2 ∣ S.relIndex (Subgroup.centralizer ({t} : Set G))) (hSn : Nat.card S = 2 ^ n)
    {D : Subgroup G} (hD2 : IsPGroup 2 D) (hDq : D ≤ Subgroup.centralizer ({q} : Set G)) :
    Nat.card D ≤ 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  let D' : Subgroup G := D.map (MulAut.conj g⁻¹).toMonoidHom
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hD'card : Nat.card D' = Nat.card D := Subgroup.card_map_of_injective hinj
  have hD'2 : IsPGroup 2 D' := hD2.map _
  have hD'C : D' ≤ C := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hq := Subgroup.mem_centralizer_iff.mp (hDq hd) q (Set.mem_singleton q)
    rw [← hg] at hq
    show h * (g⁻¹ * d * g⁻¹⁻¹) = g⁻¹ * d * g⁻¹⁻¹ * h
    have h2 : g * h * g⁻¹ * d = d * (g * h * g⁻¹) := hq
    calc h * (g⁻¹ * d * g⁻¹⁻¹)
        = g⁻¹ * (g * h * g⁻¹ * d) * g := by group
      _ = g⁻¹ * (d * (g * h * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * d * g⁻¹⁻¹ * h := by group
  obtain ⟨m, hm⟩ := hD'2.exists_card_eq
  have hdvd : Nat.card D' ∣ Nat.card C := Subgroup.card_dvd_of_le hD'C
  have hCcard : S.relIndex C * Nat.card S = Nat.card C := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := C)
    rwa [inf_eq_left.mpr hS] at h
  rw [hm, ← hCcard, hSn] at hdvd
  have hcop : Nat.Coprime (2 ^ m) (S.relIndex C) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSodd)
  have hdvd2 : 2 ^ m ∣ 2 ^ n := hcop.dvd_of_dvd_mul_left hdvd
  have hmn : m ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd2
  rw [← hD'card, hm]
  exact Nat.pow_le_pow_right (by norm_num) hmn

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
