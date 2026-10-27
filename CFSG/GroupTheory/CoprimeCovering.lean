module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNontrivialTwoCoreFactor

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_mem_normalizer_of_commutator_mem_of_mem_normalizer {N R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hsolv : Group.IsSolvable ↥N) (hcop : Nat.Coprime (Nat.card N) (Nat.card R))
    {x : G} (hxN : x ∈ Subgroup.normalizer (N : Set G))
    (hxR : ∀ r ∈ R, ⁅x, r⁆ ∈ N) :
    ∃ m ∈ N, x * m ∈ Subgroup.normalizer (R : Set G) := by
  classical
  let C : Subgroup G := N ⊔ R
  let H : Subgroup G := C ⊔ Subgroup.zpowers x
  have hCmap_le : C.map (MulAut.conj x).toMonoidHom ≤ C := by
    change (N ⊔ R).map (MulAut.conj x).toMonoidHom ≤ N ⊔ R
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      have hn' : x * n * x⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp hxN n).mp hn
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        Subgroup.mem_sup_left hn'
    · rintro _ ⟨r, hr, rfl⟩
      have hconj : (MulEquiv.toMonoidHom (MulAut.conj x)) r = ⁅x, r⁆ * r := by
        rw [MulEquiv.coe_toMonoidHom, commutatorElement_def, MulAut.conj_apply]
        group
      rw [hconj]
      exact Subgroup.mul_mem_sup (hxR r hr) hr
  have hCmap : C.map (MulAut.conj x).toMonoidHom = C :=
    Subgroup.eq_of_le_of_card_ge hCmap_le (le_of_eq (Subgroup.card_map_of_injective
      (K := C) (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).symm)
  have hxC : x ∈ Subgroup.normalizer (C : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hCmap
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact Subgroup.zpowers_le.mpr hxC
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    refine sup_le (sup_le Subgroup.le_normalizer hRN) ?_
    exact Subgroup.zpowers_le.mpr hxN
  have hCn : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C := fun h hh c hc =>
    (Subgroup.mem_normalizer_iff.mp (hHC hh) c).mp hc
  have hMn : ∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N := fun h hh m hm =>
    (Subgroup.mem_normalizer_iff.mp (hHN hh) m).mp hm
  obtain ⟨n, hn, m, hm, hx_eq⟩ :=
    CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore.exists_normalizer_mul_of_hall
      (H := H) (C := C) (M := N) (W := R) le_sup_left le_sup_right le_sup_left hCn hMn
      (show N ⊔ R = C from rfl) (Subgroup.inf_eq_bot_of_coprime hcop) hsolv hcop
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  refine ⟨m⁻¹, N.inv_mem hm, ?_⟩
  have hxm : x * m⁻¹ = n := by rw [hx_eq]; group
  rw [hxm]
  exact hn.2

theorem exists_mem_centralizer_of_commutator_mem {X N R : Subgroup G}
    (hNX : N ≤ X) (hN : (N.subgroupOf X).Normal)
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hsolv : Group.IsSolvable ↥N) (hcop : Nat.Coprime (Nat.card N) (Nat.card R))
    {x : G} (hx : x ∈ X) (hxR : ∀ r ∈ R, ⁅x, r⁆ ∈ N) :
    ∃ y ∈ X, (∀ r ∈ R, y * r = r * y) ∧ x⁻¹ * y ∈ N := by
  classical
  have hNR_bot : N ⊓ R = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hXN : X ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mp hN
  have hxN : x ∈ Subgroup.normalizer (N : Set G) := hXN hx
  obtain ⟨m, hmN, hmNorm⟩ :=
    exists_mul_mem_normalizer_of_commutator_mem_of_mem_normalizer hRN hsolv hcop hxN hxR
  refine ⟨x * m, X.mul_mem hx (hNX hmN), ?_, by simpa using hmN⟩
  intro r hr
  have hcr : m * r * m⁻¹ * r⁻¹ ∈ N := by
    have h1 : r * m⁻¹ * r⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hRN hr) m⁻¹).mp (N.inv_mem hmN)
    have h2 : m * (r * m⁻¹ * r⁻¹) ∈ N := N.mul_mem hmN h1
    simpa [mul_assoc] using h2
  have hxcr : x * (m * r * m⁻¹ * r⁻¹) * x⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hxN (m * r * m⁻¹ * r⁻¹)).mp hcr
  have hnN : ((x * m) * r * (x * m)⁻¹) * r⁻¹ ∈ N := by
    have h1 : ((x * m) * r * (x * m)⁻¹) * r⁻¹ =
        (x * (m * r * m⁻¹ * r⁻¹) * x⁻¹) * ⁅x, r⁆ := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact N.mul_mem hxcr (hxR r hr)
  have hnR : ((x * m) * r * (x * m)⁻¹) * r⁻¹ ∈ R :=
    R.mul_mem ((Subgroup.mem_normalizer_iff.mp hmNorm r).mp hr) (R.inv_mem hr)
  have hn1 : ((x * m) * r * (x * m)⁻¹) * r⁻¹ = 1 := by
    have hmem : ((x * m) * r * (x * m)⁻¹) * r⁻¹ ∈ N ⊓ R := ⟨hnN, hnR⟩
    rwa [hNR_bot, Subgroup.mem_bot] at hmem
  have hyr : (x * m) * r * (x * m)⁻¹ = r := mul_inv_eq_one.mp hn1
  calc
    (x * m) * r = ((x * m) * r * (x * m)⁻¹) * (x * m) := by group
    _ = r * (x * m) := by rw [hyr]

theorem exists_mul_mem_inf_centralizer_of_commutator_mem {X N R : Subgroup G}
    (hNX : N ≤ X) (hN : (N.subgroupOf X).Normal)
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hsolv : Group.IsSolvable ↥N) (hcop : Nat.Coprime (Nat.card N) (Nat.card R))
    {x : G} (hx : x ∈ X) (hxR : ∀ r ∈ R, ⁅x, r⁆ ∈ N) :
    ∃ n ∈ N, x * n ∈ X ⊓ Subgroup.centralizer (R : Set G) := by
  obtain ⟨y, hyX, hyC, hxyN⟩ :=
    exists_mem_centralizer_of_commutator_mem hNX hN hRN hsolv hcop hx hxR
  refine ⟨x⁻¹ * y, hxyN, ?_⟩
  constructor
  · simpa using hyX
  · have hycent : y ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hyC h hh).symm
    simpa using hycent

theorem exists_isPGroup_two_mem_normalizer_of_sq_mem {N H : Subgroup G}
    (hN2 : IsPGroup 2 N) (hHodd : Odd (Nat.card H))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    {w : G} (hwN : w ∈ Subgroup.normalizer (N : Set G))
    (hwHN : w ∈ Subgroup.normalizer ((H ⊔ N : Subgroup G) : Set G)) (hw2 : w ^ 2 ∈ N) :
    ∃ w' : G, w'⁻¹ * w ∈ N ∧ w' ∈ Subgroup.normalizer (H : Set G) ∧
      ∃ k : ℕ, orderOf w' = 2 ^ k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := H ⊔ N
  let P : Subgroup G := C ⊔ Subgroup.zpowers w
  haveI : Group.IsNilpotent N := hN2.isNilpotent
  have hNsolv : Group.IsSolvable N := inferInstance
  have hcop : Nat.Coprime (Nat.card N) (Nat.card H) := by
    obtain ⟨a, ha⟩ := hN2.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hHodd)
  have hNH_bot : N ⊓ H = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hPnormC : P ≤ Subgroup.normalizer (C : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact Subgroup.zpowers_le.mpr hwHN
  have hPnormN : P ≤ Subgroup.normalizer (N : Set G) := by
    refine sup_le (sup_le hHN Subgroup.le_normalizer) ?_
    exact Subgroup.zpowers_le.mpr hwN
  have hCn : ∀ h ∈ P, ∀ c ∈ C, h * c * h⁻¹ ∈ C := fun h hh c hc =>
    (Subgroup.mem_normalizer_iff.mp (hPnormC hh) c).mp hc
  have hMn : ∀ h ∈ P, ∀ m ∈ N, h * m * h⁻¹ ∈ N := fun h hh m hm =>
    (Subgroup.mem_normalizer_iff.mp (hPnormN hh) m).mp hm
  obtain ⟨w', hw', m, hm, hw_eq⟩ :=
    CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore.exists_normalizer_mul_of_hall
      (H := P) (C := C) (M := N) (W := H) le_sup_right le_sup_left le_sup_left hCn hMn
      (by rw [sup_comm]) hNH_bot hNsolv hcop (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have hw'2 : w' ^ 2 ∈ N := by
    have hw'_eq : w' = w * m⁻¹ := by rw [hw_eq]; group
    have h1 : w * m⁻¹ * w⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hwN (m⁻¹)).mp (N.inv_mem hm)
    have h3 : (w * m⁻¹) * (w * m⁻¹) = (w * m⁻¹ * w⁻¹) * w ^ 2 * m⁻¹ := by group
    rw [hw'_eq, pow_two, h3]
    exact N.mul_mem (N.mul_mem h1 hw2) (N.inv_mem hm)
  refine ⟨w', ?_, hw'.2, ?_⟩
  · have hwm : w'⁻¹ * w = m := by rw [hw_eq]; group
    rw [hwm]
    exact hm
  · obtain ⟨a, ha⟩ := hN2.exists_card_eq
    have hpow : (w' ^ 2) ^ Nat.card N = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨w' ^ 2, hw'2⟩))
    have hdvd : orderOf w' ∣ 2 * Nat.card N := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact hpow
    have h2pow : 2 * Nat.card N = 2 ^ (a + 1) := by rw [ha, pow_succ]; ring
    rw [h2pow] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hk⟩

end CFSG.GroupTheory
