module

public import CFSG.Certificates.Kernel.Co2Cls.Units

public section

namespace CFSG.KC.Co2Fuse

open CFSG.KC.Co2Cls Subgroup

theorem card_le_of_pgroup {G : Type*} [Group G] [Finite G] {K H : Subgroup G} (hKH : K ≤ H)
    (hK : IsPGroup 2 K) {a m : ℕ} (hH : Nat.card H = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    Nat.card K ≤ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hK
  have hd : 2 ^ e ∣ 2 ^ a * m := he ▸ hH ▸ Subgroup.card_dvd_of_le hKH
  have hc : Nat.Coprime (2 ^ e) m :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
  rw [he]
  exact Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right hd)

theorem factorization_two {a m : ℕ} (hm : ¬ 2 ∣ m) : (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

variable {M : Type*} [Monoid M] [Finite M]

theorem isPGroup_unitsIn {P : Submonoid M} (hP : ∀ x ∈ P, x ^ 32 = 1) :
    IsPGroup 2 (unitsIn P) := fun x => ⟨5, by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  simpa using hP _ x.2⟩

theorem card_le_of_exp {P : Submonoid M} (hPu : ∀ x ∈ P, IsUnit x) (hP : ∀ x ∈ P, x ^ 32 = 1)
    {H : Subgroup Mˣ} (hPH : unitsIn P ≤ H) {a m : ℕ} (hH : Nat.card H = 2 ^ a * m)
    (hm : ¬ 2 ∣ m) : Nat.card P ≤ 2 ^ a := by
  rw [← card_unitsIn hPu]
  exact card_le_of_pgroup hPH (isPGroup_unitsIn hP) hH hm

variable {S : Submonoid M}

theorem conj_into (hS : ∀ x ∈ S, IsUnit x) {T : Submonoid M} (hTS : T ≤ S)
    (hT : ∀ x ∈ T, x ^ 32 = 1) {a m : ℕ} (hSc : Nat.card S = 2 ^ a * m) (hm : ¬ 2 ∣ m)
    (hTc : 2 ^ a ≤ Nat.card T) {x : M} (hx : x ∈ S) (h2 : x * x = 1) :
    ∃ g ∈ S, ∃ y ∈ T, g * x = y * g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTu : ∀ x ∈ T, IsUnit x := fun x hx => hS x (hTS hx)
  have hH : Nat.card (unitsIn S) = 2 ^ a * m := by rw [card_unitsIn hS]; exact hSc
  have hTH : unitsIn T ≤ unitsIn S := fun v hv => hTS hv
  let T' : Subgroup (unitsIn S) := (unitsIn T).subgroupOf (unitsIn S)
  have hT'c : Nat.card T' = Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, card_unitsIn hTu]
  have hT' : Nat.card T' = 2 ^ (Nat.card (unitsIn S)).factorization 2 := by
    rw [hH, factorization_two hm, hT'c]
    exact le_antisymm (card_le_of_exp hTu hT hTH hH hm) hTc
  let P0 : Sylow 2 (unitsIn S) := Sylow.ofCard T' hT'
  obtain ⟨u, hu, hux, -⟩ := exists_unitsIn hS hx
  let s' : unitsIn S := ⟨u, hu⟩
  have hs2 : s' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    change (u : M) ^ 2 = 1
    rw [hux, sq, h2]
  have hp : IsPGroup 2 (Subgroup.zpowers s') := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hs2) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (unitsIn S) P0 Q
  have hsQ : s' ∈ (Q : Subgroup (unitsIn S)) := hQ (Subgroup.mem_zpowers s')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hsQ
  have e : (MulAut.conj g)⁻¹ • s' = g⁻¹ * s' * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e] at hsQ
  have htT : (((g⁻¹ * s' * g : unitsIn S) : Mˣ) : M) ∈ T := Subgroup.mem_subgroupOf.1 hsQ
  refine ⟨((g⁻¹ : unitsIn S) : Mˣ), (g⁻¹ : unitsIn S).2, _, htT, ?_⟩
  rw [← hux]
  change (((g⁻¹ : unitsIn S) : Mˣ) : M) * (((s' : unitsIn S) : Mˣ) : M) = _
  rw [← Units.val_mul, ← Units.val_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
  congr 2
  group

end CFSG.KC.Co2Fuse

end
