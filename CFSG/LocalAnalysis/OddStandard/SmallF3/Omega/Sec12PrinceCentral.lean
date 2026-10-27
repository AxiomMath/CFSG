module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12PrinceBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12PrinceAlg

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

namespace PrinceData

variable {B V H : Subgroup G} {φ φ₀ : (Fin 5 → ZMod 2) → G}

private def evec : Fin 5 → ZMod 2 := Pi.single 0 1 + Pi.single 1 1

private theorem evec_even : IsEvenVec evec := by
  unfold IsEvenVec evec
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single']
  decide

private theorem evec_ne_zero : evec ≠ 0 := by
  unfold evec; decide +kernel

private theorem phi0_zero (hP : PrinceData B V H φ φ₀) : φ₀ 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h := hP.via.1 0 0 h0 h0
  rw [zero_add] at h
  have h' : φ₀ 0 * 1 = φ₀ 0 * φ₀ 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

private theorem B_isPGroup (hP : PrinceData B V H φ φ₀) : IsPGroup 2 ↥B := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro b
  exact ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using hP.B_sq b.2)⟩

private theorem B_nontrivial (hP : PrinceData B V H φ φ₀) : Nontrivial ↥B := by
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hmem : φ₀ evec ∈ B := (hP.via.2.2.1 (φ₀ evec)).mpr ⟨evec, evec_even, rfl⟩
  have hne : φ₀ evec ≠ 1 := by
    intro h
    exact evec_ne_zero (hP.via.2.1 evec 0 evec_even h0 (h.trans (phi0_zero hP).symm))
  exact ⟨⟨φ₀ evec, hmem⟩, ⟨1, B.one_mem⟩, fun h => hne (Subtype.ext_iff.mp h)⟩

private theorem two_dvd_card_B [Finite G] (hP : PrinceData B V H φ φ₀) : 2 ∣ Nat.card ↥B := by
  rcases IsPGroup.card_eq_or_dvd (B_isPGroup hP) with h1 | h2
  · have hlt : 1 < Nat.card ↥B :=
      Finite.one_lt_card_iff_nontrivial.mpr (B_nontrivial hP)
    omega
  · exact h2

private theorem V_isPGroup [Finite G] (hP : PrinceData B V H φ φ₀) : IsPGroup 2 ↥V :=
  IsPGroup.of_card (p := 2) (G := ↥V) (n := 8) (by rw [hP.card_V]; norm_num)

theorem B_central [Finite G] (hP : PrinceData B V H φ φ₀) {b x : G} (hb : b ∈ B) (hx : x ∈ V) :
    x * b = b * x := by
  classical
  letI : MulAction ↥V ↥B :=
    { smul := fun g c =>
        ⟨(g : G) * (c : G) * (g : G)⁻¹, by
          have hmem : (⟨(c : G), hP.B_le c.2⟩ : ↥V) ∈ B.subgroupOf V :=
            Subgroup.mem_subgroupOf.mpr c.2
          have h := hP.mod.2.1.conj_mem (⟨(c : G), hP.B_le c.2⟩ : ↥V) hmem g
          exact Subgroup.mem_subgroupOf.mp h⟩
      one_smul := fun c => Subtype.ext (by
        change (1 : G) * (c : G) * (1 : G)⁻¹ = (c : G)
        simp)
      mul_smul := fun g h c => Subtype.ext (by
        change ((g : G) * (h : G)) * (c : G) * ((g : G) * (h : G))⁻¹ =
          (g : G) * ((h : G) * (c : G) * (h : G)⁻¹) * (g : G)⁻¹
        group) }
  have hone : (⟨1, B.one_mem⟩ : ↥B) ∈ MulAction.fixedPoints ↥V ↥B := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    change (g : G) * (1 : G) * (g : G)⁻¹ = (1 : G)
    simp
  obtain ⟨b₀, hb₀fix, hb₀ne⟩ :=
    (V_isPGroup hP).exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥B)
      (two_dvd_card_B hP) hone
  have hb₀ne1 : (b₀ : G) ≠ 1 := by
    intro h
    exact hb₀ne (Subtype.ext h.symm)
  obtain ⟨v₀, hv₀even, hv₀eq⟩ := (hP.via.2.2.1 (b₀ : G)).mp b₀.2
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    exact hb₀ne1 (by rw [← hv₀eq, h, phi0_zero hP])
  let S : Set (Fin 5 → ZMod 2) := {v | IsEvenVec v ∧ ∀ x ∈ V, x * φ₀ v = φ₀ v * x}
  have hSadd : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S := by
    intro v hv w hw
    refine ⟨?_, ?_⟩
    · show IsEvenVec (v + w)
      have hv' : ∑ i, v i = 0 := hv.1
      have hw' : ∑ i, w i = 0 := hw.1
      simp only [IsEvenVec, Pi.add_apply, Finset.sum_add_distrib, hv', hw', add_zero]
    · intro x hx
      have h1 := hv.2 x hx
      have h2 := hw.2 x hx
      rw [hP.via.1 v w hv.1 hw.1]
      calc x * (φ₀ v * φ₀ w) = (x * φ₀ v) * φ₀ w := by rw [mul_assoc]
        _ = (φ₀ v * x) * φ₀ w := by rw [h1]
        _ = φ₀ v * (x * φ₀ w) := by rw [mul_assoc]
        _ = φ₀ v * (φ₀ w * x) := by rw [h2]
        _ = (φ₀ v * φ₀ w) * x := by rw [mul_assoc]
  have hSinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ S, permVec σ v ∈ S := by
    intro σ hσ v hv
    obtain ⟨h, hhH, hh⟩ := hP.via.2.2.2.2 σ hσ
    refine ⟨?_, ?_⟩
    · show IsEvenVec (permVec σ v)
      unfold IsEvenVec permVec
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp σ.symm v]
      exact hv.1
    · intro x hx
      have hconj : φ₀ (permVec σ v) = h * φ₀ v * h⁻¹ := (hh v hv.1).symm
      have hxV : h⁻¹ * x * h ∈ V := by
        have := (Subgroup.le_normalizer_iff.mp hP.mod.2.2.1) h⁻¹ (H.inv_mem hhH) x hx
        simpa using this
      have hcomm := hv.2 (h⁻¹ * x * h) hxV
      calc x * φ₀ (permVec σ v)
          = x * (h * φ₀ v * h⁻¹) := by rw [hconj]
        _ = h * ((h⁻¹ * x * h) * φ₀ v) * h⁻¹ := by group
        _ = h * (φ₀ v * (h⁻¹ * x * h)) * h⁻¹ := by rw [hcomm]
        _ = (h * φ₀ v * h⁻¹) * x := by group
        _ = φ₀ (permVec σ v) * x := by rw [hconj]
  have hv₀S : v₀ ∈ S := by
    refine ⟨hv₀even, fun x hx => ?_⟩
    have hfix' : x * (b₀ : G) * x⁻¹ = (b₀ : G) :=
      congrArg Subtype.val (hb₀fix ⟨x, hx⟩)
    calc x * φ₀ v₀ = (x * (b₀ : G) * x⁻¹) * x := by rw [← hv₀eq]; group
      _ = (b₀ : G) * x := by rw [hfix']
      _ = φ₀ v₀ * x := by rw [hv₀eq]
  have hSall := prince_invariant_all S hSadd hSinv (fun v hv => hv.1) hv₀S hv₀ne
  obtain ⟨v, hveven, hveq⟩ := (hP.via.2.2.1 b).mp hb
  have hcomm := (hSall v hveven).2 x hx
  rwa [hveq] at hcomm

end PrinceData

end CFSG.OddStandard.SmallF3.Omega
