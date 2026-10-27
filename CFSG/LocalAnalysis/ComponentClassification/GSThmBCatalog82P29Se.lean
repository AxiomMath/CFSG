module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PSp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29T

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem exists_t {H : Type} [Group H] [Finite H] {L S : Subgroup H} [L.Normal]
    (hS : IsPGroup 2 S) {n : ℕ} (hSL : Nat.card ↥(S ⊓ L) = 2 ^ n)
    (hL2 : 2 ^ (n + 1) ∣ Nat.card L) (hL4 : ¬ 2 ^ (n + 2) ∣ Nat.card L) :
    ∃ t ∈ L, t ∈ normalizer (S : Set H) ∧ t ∉ S ∧ t * t ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := S ⊔ L with hX
  have h1 : L.relIndex X * Nat.card ↥(L ⊓ X) = Nat.card X := Subgroup.relIndex_mul_card L X
  have h2 : L.relIndex S * Nat.card ↥(L ⊓ S) = Nat.card S := Subgroup.relIndex_mul_card L S
  have h3 : L.relIndex X = L.relIndex S := Subgroup.relIndex_sup_right S L
  rw [inf_of_le_left (le_sup_right : L ≤ X)] at h1
  rw [inf_comm, hSL] at h2
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  rw [ha] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h2)
  rw [hj, ← pow_add] at h2
  have hja : j + n = a := Nat.pow_right_injective (le_refl 2) h2
  obtain ⟨o, ho⟩ := hL2
  have hodd : ¬ 2 ∣ o := by
    rintro ⟨c, rfl⟩
    exact hL4 ⟨c, by rw [ho, pow_succ]; ring⟩
  have hX2 : Nat.card X = 2 ^ (a + 1) * o := by
    rw [← h1, h3, hj, ho, ← mul_assoc, ← pow_add]
    congr 2
    omega
  have hSX : S ≤ X := le_sup_left
  obtain ⟨R, hR⟩ := (hS.comap_subtype (K := X)).exists_le_sylow
  have hRc : Nat.card R = 2 ^ (a + 1) := by
    rw [R.card_eq_multiplicity, hX2, Nat.factorization_def _ Nat.prime_two,
      padicValNat.mul (by positivity) (by rintro rfl; exact hodd (dvd_zero 2)),
      padicValNat.prime_pow, P211.v2_odd (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)),
      add_zero]
  set R' := (R : Subgroup X).map X.subtype with hR'
  have hR'c : Nat.card R' = 2 ^ (a + 1) := by
    rw [hR', Subgroup.card_map_of_injective X.subtype_injective, hRc]
  have hSR' : S ≤ R' := by
    intro s hs
    exact ⟨⟨s, hSX hs⟩, hR (show (⟨s, hSX hs⟩ : X) ∈ S.subgroupOf X from hs), rfl⟩
  have hR'X : R' ≤ X := Subgroup.map_subtype_le _
  have hidx : (S.subgroupOf R').index = 2 := by
    have h4 : S.relIndex R' * Nat.card ↥(S ⊓ R') = Nat.card R' := Subgroup.relIndex_mul_card S R'
    rw [inf_of_le_left hSR', ha, hR'c, pow_succ] at h4
    have h5 : S.relIndex R' * 2 ^ a = 2 * 2 ^ a := by rw [h4, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos a) h5
  have hnorm : (S.subgroupOf R').Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨r₀, hr₀R, hr₀S⟩ : ∃ r₀ ∈ R', r₀ ∉ S := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le hcon
    rw [hR'c, ha] at this
    have := Nat.pow_le_pow_iff_right (by norm_num : 1 < 2) |>.mp this
    omega
  obtain ⟨y, hyS, z, hzL, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp (hR'X hr₀R)
  have hzR : z ∈ R' := by
    have : z = y⁻¹ * r₀ := by rw [← hyz]; group
    rw [this]
    exact mul_mem (inv_mem (hSR' hyS)) hr₀R
  refine ⟨z, hzL, ?_, fun hz => hr₀S (hyz ▸ mul_mem hyS hz), ?_⟩
  · rw [mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have := hnorm.conj_mem ⟨s, hSR' hs⟩ (show (⟨s, hSR' hs⟩ : R') ∈ S.subgroupOf R' from hs)
        ⟨z, hzR⟩
      exact this
    · intro hs
      have hsR : s ∈ R' := by
        have h5 : z * s * z⁻¹ ∈ R' := hSR' hs
        have : s = z⁻¹ * (z * s * z⁻¹) * z := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem hzR) h5) hzR
      have := hnorm.conj_mem ⟨z * s * z⁻¹, hSR' hs⟩
        (show (⟨z * s * z⁻¹, hSR' hs⟩ : R') ∈ S.subgroupOf R' from hs) ⟨z, hzR⟩⁻¹
      have e : (⟨z, hzR⟩⁻¹ * ⟨z * s * z⁻¹, hSR' hs⟩ * (⟨z, hzR⟩⁻¹)⁻¹ : R') = ⟨s, hsR⟩ :=
        Subtype.ext (by simp only [InvMemClass.coe_inv, Subgroup.coe_mul, inv_inv]; group)
      rw [e] at this
      exact this
  · exact Subgroup.mul_self_mem_of_index_two hidx ⟨z, hzR⟩

theorem outer_of_not_mem {H : Type} [Group H] {J₁ : Subgroup H} (hO : pPrimeCore 2 ↥J₁ = ⊥)
    {d : H} (hd : d ∉ J₁ ⊔ coreActionKernel J₁) (j : H) (hj : j ∈ J₁) :
    ∃ w ∈ J₁, (d * w * d⁻¹)⁻¹ * (j * w * j⁻¹) ∉ oddCoreIn J₁ := by
  by_contra h
  push Not at h
  rw [oddCoreIn_eq_bot hO] at h
  apply hd
  have hc : j⁻¹ * d ∈ coreActionKernel J₁ := by
    rw [kernel_eq_centralizer hO, mem_centralizer_iff]
    intro w hw
    have h1 := h w hw
    rw [mem_bot, inv_mul_eq_one] at h1
    calc w * (j⁻¹ * d) = j⁻¹ * (j * w * j⁻¹) * d := by group
      _ = j⁻¹ * (d * w * d⁻¹) * d := by rw [← h1]
      _ = j⁻¹ * d * w := by group
  have : d = j * (j⁻¹ * d) := by group
  rw [this]
  exact mul_mem (mem_sup_left hj) (mem_sup_right hc)

end CFSG.ComponentClassification.GSThmB.P29
