module

public import CFSG.LocalAnalysis.OddStandard.GH71.AhatThree

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

theorem fix_of_odd {Q : Subgroup (Perm (Fin 11))} (hodd : Odd (Nat.card Q))
    (hu : ∀ q ∈ Q, q * u0 = u0 * q) (hN : ∀ k : Fin 8, ∀ q ∈ Q, xo k * q * xo k ∈ Q) :
    ∀ q ∈ Q, ∀ x : Fin 11, x.val < 8 → q x = x := by
  classical
  set O : Set (Fin 11) := MulAction.orbit Q (0 : Fin 11) with hO
  have hmemO : ∀ y, y ∈ O ↔ ∃ q ∈ Q, q 0 = y := fun y =>
    ⟨fun ⟨q, hq⟩ => ⟨q, q.2, hq⟩, fun ⟨q, hq, h⟩ => ⟨⟨q, hq⟩, h⟩⟩
  have hOlt : ∀ y ∈ O, y.val < 8 := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := (hmemO y).1 hy
    exact lt_of_comm_u0 (hu q hq) (by decide)
  have hOodd : Odd (Nat.card O) := by
    rw [Nat.card_coe_set_eq, hO, ← MulAction.index_stabilizer]
    exact Odd.of_dvd_nat hodd (Subgroup.index_dvd_card _)
  have hO0 : ∀ y ∈ O, y = 0 := by
    intro k hk
    by_contra hk0
    have hk8 := hOlt k hk
    have hk0' : (⟨k.val, hk8⟩ : Fin 8) ≠ 0 := fun h => by
      have h' : k.val = 0 := congrArg Fin.val h
      exact hk0 (Fin.ext h')
    have hek : xo ⟨k.val, hk8⟩ k = 0 := xo_self ⟨k.val, hk8⟩
    have hmap : ∀ y ∈ O, xo ⟨k.val, hk8⟩ y ∈ O := by
      intro y hy
      obtain ⟨q, hq, rfl⟩ := (hmemO y).1 hy
      obtain ⟨q', hq', hq'k⟩ := (hmemO k).1 hk
      refine (hmemO _).2 ⟨xo ⟨k.val, hk8⟩ * q * xo ⟨k.val, hk8⟩ * q',
        mul_mem (hN _ q hq) hq', ?_⟩
      simp only [Perm.mul_apply, hq'k, hek]
    let f : Function.End O := fun y => ⟨xo ⟨k.val, hk8⟩ y, hmap y y.2⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype O := Fintype.ofFinite O
    have hf2 : f ^ 2 ^ 1 = 1 := by
      funext y
      apply Subtype.ext
      show xo ⟨k.val, hk8⟩ (xo ⟨k.val, hk8⟩ y) = y
      rw [← Perm.mul_apply, xo_sq, Perm.one_apply]
    have hfix : Function.fixedPoints f = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      exact xo_ne _ hk0' y (hOlt y y.2) (congrArg Subtype.val hy)
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf2
    have : IsEmpty ↑(Function.fixedPoints f) := Set.isEmpty_coe_sort.mpr hfix
    rw [Fintype.card_eq_zero (α := ↑(Function.fixedPoints f))] at hmod
    have h1 := Nat.odd_iff.1 hOodd
    rw [Nat.card_eq_fintype_card] at h1
    have h2 : Fintype.card O % 2 = 0 := hmod
    omega
  intro q hq x hx
  have h := hO0 _ ((hmemO _).2 ⟨_, hN ⟨x.val, hx⟩ q hq, rfl⟩)
  have e0 : xo ⟨x.val, hx⟩ 0 = x := xo_zero ⟨x.val, hx⟩
  simp only [Perm.mul_apply, e0] at h
  have := congrArg (xo ⟨x.val, hx⟩) h
  rwa [← Perm.mul_apply, xo_sq, Perm.one_apply, e0] at this

variable {K : Type} [Group K]

theorem exists_lift_xo (C : CoverSetup 11 K) {v : K} (hv : C.ρ v = u0) (k : Fin 8) :
    ∃ c ∈ centralizer ({v} : Set K), C.ρ c = xo k := by
  by_cases hk : 2 ≤ k.val
  · obtain ⟨c, hc⟩ := C.exists_ρ_eq (show sign (xo k) = 1 by revert k; decide)
    obtain ⟨h1, h2, h3⟩ := xo_isoI k hk
    refine ⟨c, mem_centralizer_singleton_iff.2 ?_, hc⟩
    exact Cov.comm_of_isoI C (by rw [hc]; exact h1) (by rw [hv]; exact isoI_u0)
      (by rw [hc, hv]; exact h2) (by rw [hc, hv]; exact h3)
  · rcases (by decide : ∀ j : Fin 8, ¬ 2 ≤ j.val → j = 0 ∨ j = 1) k hk with rfl | rfl
    · exact ⟨1, one_mem _, by rw [map_one]; decide⟩
    · exact ⟨v, mem_centralizer_singleton_iff.2 rfl, by rw [hv]; decide⟩

theorem specB2 : SpecB2 := by
  intro K _ _ S U hF X hX hXS v hv hvz
  obtain ⟨C, x₀, hSP, hx₀, h3⟩ := exists_std hF.cover hF.sylow hF.card
  rw [eq_zpowers_x0 C hSP hx₀ h3 hX hXS]
  intro c hc
  refine mem_normalizer_x0 C hx₀ h3 ?_
  rw [← rho_eq_u0 C hSP hF hv hvz, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]

theorem specB2' : SpecB2' := by
  intro K _ _ S U hF X hX hXS v hv hvz
  obtain ⟨C, x₀, hSP, hx₀, h3⟩ := exists_std hF.cover hF.sylow hF.card
  rw [eq_zpowers_x0 C hSP hx₀ h3 hX hXS]
  have hρv := rho_eq_u0 C hSP hF hv hvz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cv := centralizer ({v} : Set K)
  have hDodd : Odd (Nat.card (pPrimeCoreOf 2 Cv)) := by
    rw [pPrimeCoreOf, Subgroup.card_map_of_injective Cv.subtype_injective]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hDle : pPrimeCoreOf 2 Cv ≤ Cv := map_subtype_le _
  have hDnorm : ∀ c ∈ Cv, ∀ d ∈ pPrimeCoreOf 2 Cv, c * d * c⁻¹ ∈ pPrimeCoreOf 2 Cv := by
    rintro c hc _ ⟨d, hd, rfl⟩
    exact ⟨⟨c, hc⟩ * d * ⟨c, hc⟩⁻¹, pPrimeCore_normal.conj_mem d hd ⟨c, hc⟩, rfl⟩
  have hfix := fix_of_odd (Q := (pPrimeCoreOf 2 Cv).map C.ρ)
    (Odd.of_dvd_nat hDodd (Subgroup.card_map_dvd _ _))
    (by
      rintro _ ⟨d, hd, rfl⟩
      rw [← hρv, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 (hDle hd)])
    (by
      rintro k _ ⟨d, hd, rfl⟩
      obtain ⟨c, hc, hcρ⟩ := exists_lift_xo C hρv k
      refine ⟨c * d * c⁻¹, hDnorm c hc d hd, ?_⟩
      rw [map_mul, map_mul, map_inv, hcρ, inv_eq_of_mul_eq_one_right (xo_sq k)])
  intro d hd
  refine mem_zpowers_x0 C hx₀ h3 (mem_zpowers_t3 (C.sign_ρ d) (hfix _ ⟨d, hd, rfl⟩)) ?_
  exact Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard _ hd)

theorem specB3 : SpecB3 := by
  intro K _ _ S U hF X hX hXS v hv hvz hle
  obtain ⟨C, x₀, hSP, hx₀, h3⟩ := exists_std hF.cover hF.sylow hF.card
  rw [eq_zpowers_x0 C hSP hx₀ h3 hX hXS] at hle
  have hρv := rho_eq_u0 C hSP hF hv hvz
  obtain ⟨s, hs, hsρ⟩ := exists_lift_mem C hSP sB_mem
  have hsv : s * v = v * s := Cov.comm_of_isoI C
    (by rw [hsρ]; unfold IsoI; decide) (by rw [hρv]; exact isoI_u0)
    (by rw [hsρ, hρv]; unfold IsoI; decide) (by rw [hsρ, hρv]; decide)
  have hcx := hle ⟨hs, mem_centralizer_singleton_iff.2 hsv⟩
  have e := congrArg C.ρ (mem_centralizer_iff.1 hcx x₀ (mem_zpowers x₀))
  rw [map_mul, map_mul, hsρ, hx₀] at e
  exact absurd e (by decide)

end CFSG.OddStandard.GH71.AhatB
