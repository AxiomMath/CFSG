module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AutoRows

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open Subgroup

theorem sylow_conj_mem {G : Type*} [Group G] [Finite G] (A B : Sylow 3 G) :
    ∃ u : G, ∀ x, x ∈ (A : Subgroup G) ↔ u * x * u⁻¹ ∈ (B : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq G A B
  refine ⟨u, fun x => ?_⟩
  have h := congrArg (fun S : Sylow 3 G => (S : Subgroup G)) hu
  simp only [Sylow.coe_subgroup_smul] at h
  rw [← h]
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [mul_assoc]

theorem exists_mul_mem_normalizer_of_sup {N : Type*} [Group N] [Finite N] {C R : Subgroup N}
    [hCn : C.Normal] (hR3 : IsPGroup 3 R) (hC3 : ¬ 3 ∣ Nat.card C) {n : N}
    (hn : n ∈ Subgroup.normalizer ((C ⊔ R : Subgroup N) : Set N)) :
    ∃ c ∈ C, c * n ∈ Subgroup.normalizer (R : Set N) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U : Subgroup N := C ⊔ R with hU
  have hRU : R ≤ U := le_sup_right
  have hd : C ⊓ R = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨a, ha⟩ := hR3 ⟨x, hx.2⟩
    have h1 : x ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hd1 : orderOf x ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one h1
    have hd2 : orderOf x ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hx.1
    have hcop : Nat.Coprime (3 ^ a) (Nat.card C) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hC3)
    have := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp this)
  have hUcard : Nat.card U = Nat.card C * Nat.card R :=
    card_sup_of_normal_disjoint rfl
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hCn]; exact le_top) hd
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have key : ∀ R' : Subgroup N, R' ≤ U → IsPGroup 3 R' → Nat.card R' = Nat.card R →
      ∃ S : Sylow 3 ↥U, (S : Subgroup ↥U) = R'.subgroupOf U := by
    intro R' hR'U hR'3 hR'c
    have h1 := Subgroup.relIndex_mul_card R' U
    rw [inf_of_le_left hR'U, hR'c, hUcard] at h1
    have h2 : R'.relIndex U = Nat.card C := by
      have : R'.relIndex U * Nat.card R = Nat.card C * Nat.card R := h1
      exact Nat.eq_of_mul_eq_mul_right hRpos this
    have hp : IsPGroup 3 (R'.subgroupOf U) :=
      hR'3.of_surjective (Subgroup.subgroupOfEquivOfLe hR'U).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hR'U).symm.surjective
    have hidx : ¬ 3 ∣ (R'.subgroupOf U).index := by
      show ¬ 3 ∣ R'.relIndex U
      rw [h2]; exact hC3
    exact ⟨hp.toSylow hidx, rfl⟩
  obtain ⟨A, hA⟩ := key R hRU hR3 rfl
  set R' : Subgroup N := R.map (MulAut.conj n).toMonoidHom with hR'
  have hmemU : ∀ y, y ∈ U ↔ n * y * n⁻¹ ∈ U := fun y => Subgroup.mem_normalizer_iff.mp hn y
  have hR'U : R' ≤ U := by
    rintro _ ⟨r, hr, rfl⟩
    exact (hmemU r).mp (hRU hr)
  have hR'c : Nat.card R' = Nat.card R :=
    (Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective).toEquiv).symm
  obtain ⟨B, hB⟩ := key R' hR'U (hR3.map _) hR'c
  obtain ⟨u, hu⟩ := sylow_conj_mem A B
  have hmemR' : ∀ y, y ∈ R' ↔ n⁻¹ * y * n ∈ R := by
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hr
    · intro hy
      exact ⟨n⁻¹ * y * n, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hm : ∀ y : N, y ∈ R ↔ (n⁻¹ * (u : N)) * y * (n⁻¹ * (u : N))⁻¹ ∈ R := by
    intro y
    have e : (n⁻¹ * (u : N)) * y * (n⁻¹ * (u : N))⁻¹ = n⁻¹ * ((u : N) * y * (u : N)⁻¹) * n := by
      group
    rw [e, ← hmemR']
    constructor
    · intro hy
      have h1 := (hu ⟨y, hRU hy⟩).mp (by rw [hA]; exact hy)
      rw [hB] at h1
      exact h1
    · intro hy
      have hyU : y ∈ U := by
        have h1 : (u : N) * y * (u : N)⁻¹ ∈ U := hR'U hy
        have := U.mul_mem (U.mul_mem (U.inv_mem u.2) h1) u.2
        simpa [mul_assoc] using this
      have h1 := (hu ⟨y, hyU⟩).mpr (by rw [hB]; exact hy)
      rw [hA] at h1
      exact h1
  have hmN : n⁻¹ * (u : N) ∈ Subgroup.normalizer (R : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact hm y
  have hmN' := Subgroup.inv_mem _ hmN
  have hu' : ((u : N)⁻¹) ∈ ((R ⊔ C : Subgroup N) : Set N) := by
    rw [sup_comm]; exact U.inv_mem u.2
  rw [Subgroup.mul_normal] at hu'
  obtain ⟨r, hr, c, hc, hrc⟩ := hu'
  refine ⟨c, hc, ?_⟩
  have h1 : (u : N)⁻¹ * n ∈ Subgroup.normalizer (R : Set N) := by
    have : (n⁻¹ * (u : N))⁻¹ = (u : N)⁻¹ * n := by group
    rwa [this] at hmN'
  rw [← hrc] at h1
  have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hr)) h1
  simpa [mul_assoc] using h2

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
