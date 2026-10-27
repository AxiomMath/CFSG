module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAOrbitFixedComponent

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_commutator_eq_of_isKleinFour {V X : Subgroup G} (hV : IsKleinFour V)
    (hVX : V ≤ normalizer (X : Set G)) (hX : Odd (Nat.card X)) : ⁅⁅X, V⁆, V⁆ = ⁅X, V⁆ := by
  have hsqV : ∀ w ∈ V, w * w = 1 := fun w hw =>
    congrArg Subtype.val (@IsKleinFour.mul_self V _ hV ⟨w, hw⟩)
  apply le_antisymm
  · exact commutator_le_self_of_le_normalizer
      (le_normalizer_commutator_of_le_normalizers hVX le_normalizer)
  · rw [commutator_le]
    intro x hx v hv
    have h1 : ⁅x, v⁆ ∈ ⁅X, zpowers v⁆ := commutator_mem_commutator hx (mem_zpowers v)
    rw [← commutator_commutator_zpowers_eq (hsqV v hv) hX (hVX hv)] at h1
    have hle : zpowers v ≤ V := (zpowers_le).mpr hv
    exact commutator_mono (commutator_mono le_rfl hle) hle h1

theorem inf_centralizer_le_commutator_of_involution {Y : Subgroup G} {w : G} (hw : w * w = 1)
    (hY : Odd (Nat.card Y)) (hwY : w ∈ normalizer (Y : Set G)) :
    ⁅Y, zpowers w⁆ ⊓ centralizer ({w} : Set G) ≤ ⁅⁅Y, zpowers w⁆, ⁅Y, zpowers w⁆⁆ := by
  set Z := ⁅Y, zpowers w⁆ with hZ
  have hwZ : w ∈ normalizer (Z : Set G) :=
    le_normalizer_commutator_of_le_normalizers (zpowers_le.mpr hwY) le_normalizer
      (mem_zpowers w)
  have hZodd : Odd (Nat.card Z) :=
    Odd.of_dvd_nat hY (card_dvd_of_le (commutator_le_self_of_le_normalizer (zpowers_le.mpr hwY)))
  let φ : Z →* Z := ((MulAut.conj w).toMonoidHom.comp Z.subtype).codRestrict Z
    (fun z => (mem_normalizer_iff.mp hwZ z).mp z.2)
  let π : Z →* Abelianization Z := Abelianization.of
  have hφ : ∀ z : Z, ((φ z : Z) : G) = w * z * w⁻¹ := fun z => rfl
  have hT : (π.comp φ).eqLocus π⁻¹ = ⊤ := by
    rw [eq_top_iff, ← closure_closure_coe_preimage (k := {g | ∃ g₁ ∈ Y, ∃ g₂ ∈ zpowers w,
      ⁅g₁, g₂⁆ = g})]
    rw [closure_le]
    rintro ⟨z, hz⟩ ⟨y, hy, u, hu, rfl⟩
    rcases UnbalancedGS.OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers hw hu with hu1 | huw
    · have h1 : (⟨⁅y, u⁆, hz⟩ : Z) = 1 := Subtype.ext (by
        show ⁅y, u⁆ = 1
        rw [hu1]
        simp [commutatorElement_def])
      show π (φ _) = π⁻¹ _
      rw [h1, map_one, map_one, map_one]
    · show π (φ _) = π⁻¹ _
      have h1 : φ ⟨⁅y, u⁆, hz⟩ = (⟨⁅y, u⁆, hz⟩ : Z)⁻¹ := Subtype.ext (by
        rw [hφ]
        show w * ⁅y, u⁆ * w⁻¹ = (⁅y, u⁆)⁻¹
        rw [huw]
        exact conj_commutatorElement_eq_inv hw)
      rw [h1, map_inv, MonoidHom.inv_apply]
  intro z hz
  obtain ⟨hzZ, hzw⟩ := mem_inf.mp hz
  set z' : Z := ⟨z, hzZ⟩ with hz'
  have hfix : φ z' = z' := Subtype.ext (by
    rw [hφ]
    have h1 : z * w = w * z := mem_centralizer_singleton_iff.mp hzw
    calc w * z * w⁻¹ = z * w * w⁻¹ := by rw [h1]
      _ = z := by group)
  have h1 : π z' = (π z')⁻¹ := by
    have h := DFunLike.congr_fun (show (π.comp φ) = π⁻¹ from by
      ext x
      have hx : x ∈ (π.comp φ).eqLocus π⁻¹ := hT ▸ mem_top x
      exact hx) z'
    rw [MonoidHom.comp_apply, hfix, MonoidHom.inv_apply] at h
    exact h
  have hsq : π z' ^ 2 = 1 := by
    calc π z' ^ 2 = π z' * π z' := sq _
      _ = π z' * (π z')⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel _
  have hodd : Odd (orderOf (π z')) := Odd.of_dvd_nat
    (by rw [hz', Subgroup.orderOf_mk]; exact odd_orderOf_of_mem_of_odd hZodd hzZ)
    (orderOf_map_dvd π z')
  have h2 : π z' = 1 := by
    have h3 : orderOf (π z') ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h3' : orderOf (π z') ∣ 2 ^ 1 := by rwa [pow_one]
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3'
    rcases j with _ | j
    · rw [pow_zero] at hj'
      exact orderOf_eq_one_iff.mp hj'
    · rw [hj'] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two,
        Nat.succ_ne_zero j⟩))
  have h3 : z' ∈ _root_.commutator Z := by
    rw [← Abelianization.ker_of]
    exact h2
  have h4 := mem_map_of_mem Z.subtype h3
  rw [_root_.commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h4
  exact h4

end CFSG.ComponentClassification.FooteLit
