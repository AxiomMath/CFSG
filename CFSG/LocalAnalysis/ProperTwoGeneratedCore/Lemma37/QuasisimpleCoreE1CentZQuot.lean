module

public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZTau

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

section General

variable {M : Type} [Group M] (Z₀ : Subgroup M) [Z₀.Normal]

@[expose] noncomputable def e1Pi : M →* (M ⧸ Z₀) ⧸ CFSG.pPrimeCore 2 (M ⧸ Z₀) :=
  (QuotientGroup.mk' (CFSG.pPrimeCore 2 (M ⧸ Z₀))).comp (QuotientGroup.mk' Z₀)

theorem e1Pi_surjective : Function.Surjective (e1Pi Z₀) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

variable [Finite M]

theorem ker_e1Pi (hZ : Z₀ ≤ Subgroup.center M) (hZ2 : IsPGroup 2 Z₀) :
    (e1Pi Z₀).ker = CFSG.pPrimeCore 2 M ⊔ Z₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ∀ g : M, e1Pi Z₀ g = 1 ↔ QuotientGroup.mk' Z₀ g ∈ CFSG.pPrimeCore 2 (M ⧸ Z₀) :=
    fun g => QuotientGroup.eq_one_iff (QuotientGroup.mk' Z₀ g)
  ext g
  rw [MonoidHom.mem_ker, h1, CFSG.central_p_subgroup_prime_core_quotient Z₀ hZ hZ2,
    ← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem mem_of_mem_sup_of_pow_eq_one (hZ : Z₀ ≤ Subgroup.center M) (hZ2 : IsPGroup 2 Z₀) {t : M}
    (ht : t ∈ CFSG.pPrimeCore 2 M ⊔ Z₀) {k : ℕ} (htk : t ^ 2 ^ k = 1) : t ∈ Z₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, ho, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ht
  obtain ⟨j, hj⟩ := hZ2 ⟨w, hw⟩
  have hwj : w ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcomm : Commute o w := Subgroup.mem_center_iff.mp (hZ hw) o
  have ho2 : o ^ 2 ^ (k + j) = 1 := by
    have h1 : (o * w) ^ 2 ^ (k + j) = 1 := by rw [pow_add, pow_mul, htk, one_pow]
    have h2 : w ^ 2 ^ (k + j) = 1 := by rw [pow_add, mul_comm, pow_mul, hwj, one_pow]
    rwa [hcomm.mul_pow, h2, mul_one] at h1
  have hodd : Odd (orderOf o) := (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ ho)
  rw [orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _
    hodd.coprime_two_right) (orderOf_dvd_of_pow_eq_one ho2)), one_mul]
  exact hw

theorem conj_mem_sup_of_normal_map (hZ : Z₀ ≤ Subgroup.center M) (hZ2 : IsPGroup 2 Z₀)
    {P : Subgroup M} (hZP : Z₀ ≤ P) (hn : (P.map (e1Pi Z₀)).Normal) (g : M) {r : M}
    (hr : r ∈ P) : g * r * g⁻¹ ∈ P ⊔ CFSG.pPrimeCore 2 M := by
  have h := hn.conj_mem _ (Subgroup.mem_map_of_mem _ hr) (e1Pi Z₀ g)
  rw [← map_inv, ← map_mul, ← map_mul, ← Subgroup.mem_comap, Subgroup.comap_map_eq,
    ker_e1Pi Z₀ hZ hZ2, sup_comm (CFSG.pPrimeCore 2 M), ← sup_assoc, sup_eq_left.mpr hZP] at h
  exact h

theorem exists_e1Pi_eq_of_mem_normalizer {P : Subgroup M} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index) {q : (M ⧸ Z₀) ⧸ CFSG.pPrimeCore 2 (M ⧸ Z₀)}
    (hq : q ∈ Subgroup.normalizer ((P.map (e1Pi Z₀) : Subgroup _) : Set _)) :
    ∃ n : M, (∀ r ∈ P, n * r * n⁻¹ ∈ P) ∧ e1Pi Z₀ n = q := by
  obtain ⟨g, rfl⟩ := e1Pi_surjective Z₀ q
  have hg : ∀ r ∈ P, g * r * g⁻¹ ∈ P ⊔ (e1Pi Z₀).ker := fun r hr => by
    have h := (Subgroup.mem_normalizer_iff.mp hq _).mp (Subgroup.mem_map_of_mem _ hr)
    rwa [← map_inv, ← map_mul, ← map_mul, ← Subgroup.mem_comap, Subgroup.comap_map_eq] at h
  obtain ⟨h, hh, hhg⟩ := exists_mul_conj_mem_of_not_two_dvd hP
    (fun h => hidx (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))) hg
  obtain ⟨p, hp, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh
  refine ⟨k * g, fun r hr => ?_, by rw [map_mul, (e1Pi Z₀).mem_ker.mp hk, one_mul]⟩
  rw [show k * g * r * (k * g)⁻¹ = p⁻¹ * (p * k * g * r * (p * k * g)⁻¹) * p by group]
  exact P.mul_mem (P.mul_mem (P.inv_mem hp) (hhg r hr)) hp

omit [Finite M] in
theorem card_map_mul_card_ker_subgroupOf (P : Subgroup M) :
    Nat.card (P.map (e1Pi Z₀)) * Nat.card ((e1Pi Z₀).ker.subgroupOf P) = Nat.card P := by
  have hker : ((e1Pi Z₀).comp P.subtype).ker = (e1Pi Z₀).ker.subgroupOf P := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
  have hrange : ((e1Pi Z₀).comp P.subtype).range = P.map (e1Pi Z₀) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← hker, ← Nat.card_congr
    (QuotientGroup.quotientKerEquivRange ((e1Pi Z₀).comp P.subtype)).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

end General

variable {G : Type} [Group G]

@[expose] noncomputable def e1ZM (Z : Subgroup G) [Z.Normal] (u m y x : G) :
    Subgroup (e1M0 Z (u * (x * u * x⁻¹))) :=
  (Subgroup.zpowers (caseC3Word Z u m y x 40)).subgroupOf (e1M0 Z (u * (x * u * x⁻¹)))

theorem e1ZM_le_center {Z : Subgroup G} [Z.Normal] {u m y x : G} :
    e1ZM Z u m y x ≤ Subgroup.center (e1M0 Z (u * (x * u * x⁻¹))) := by
  intro w hw
  rw [e1ZM, Subgroup.mem_subgroupOf] at hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hk]
  have hg := e1M0_le_centralizer g.2
  rw [Subgroup.mem_centralizer_singleton_iff, ← CaseC3BCD.caseC3Word_forty (m := m) (y := y)] at hg
  exact Commute.zpow_right (a := (g : G ⧸ Z)) hg k

instance {Z : Subgroup G} [Z.Normal] {u m y x : G} : (e1ZM Z u m y x).Normal :=
  Subgroup.normal_of_le_center e1ZM_le_center

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
