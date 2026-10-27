module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreInvol
public import CFSG.ClassicalInvolution.Balance.Q27D4Parts

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ClassicalInvolution.Balance.Q27

theorem pPrimeCore_cen_eq_bot_of_equiv {G K : Type} [Group G] [Finite G] [Group K]
    (e : G ≃* K) (hK : InvolutionOddCoreTrivial K) {t : G} (ht : orderOf t = 2) :
    pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ := by
  classical
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  set R : Subgroup ↥C := pPrimeCore 2 ↥C with hR
  have ht2 : t * t = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq ht)
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  have hRnormal : R.Normal := inferInstance
  set N : Subgroup G := R.map C.subtype with hN
  set N' : Subgroup K := N.map e.toMonoidHom with hN'
  have hNC : N ≤ C := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have hu2 : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
  have hu1 : e t ≠ 1 := fun h => ht1 (e.injective (by rw [h, map_one]))
  have hN'c : N' ≤ Subgroup.centralizer ({e t} : Set K) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hNC hx)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  have hnorm : ∀ c ∈ Subgroup.centralizer ({e t} : Set K), ∀ n ∈ N', c * n * c⁻¹ ∈ N' := by
    intro c hc n hn
    obtain ⟨x, hx, rfl⟩ := hn
    obtain ⟨r, hr, rfl⟩ := hx
    have hc' : e.symm c ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact this
    refine ⟨C.subtype (⟨e.symm c, hc'⟩ * r * ⟨e.symm c, hc'⟩⁻¹),
      ⟨_, hRnormal.conj_mem r hr ⟨e.symm c, hc'⟩, rfl⟩, ?_⟩
    simp
  have hodd : Odd (Nat.card N') := by
    have h1 : Nat.card N' = Nat.card R := by
      rw [hN', hN, Subgroup.card_map_of_injective e.injective,
        Subgroup.card_map_of_injective C.subtype_injective]
    rw [h1]
    exact CoreAux.odd_card_pPrimeCore _
  have hbot := hK (e t) hu2 hu1 N' hN'c hnorm hodd
  have hN0 : N = ⊥ := by
    have : N.map e.toMonoidHom = ⊥ := hbot
    exact Subgroup.map_injective (f := e.toMonoidHom) e.injective
      (by rw [Subgroup.map_bot]; exact this)
  have hR0 : R = ⊥ := by
    have : R.map C.subtype = ⊥ := hN0
    exact Subgroup.map_injective (f := C.subtype) C.subtype_injective
      (by rw [Subgroup.map_bot]; exact this)
  exact hR0

end CFSG.OddStandard.Solomon75
