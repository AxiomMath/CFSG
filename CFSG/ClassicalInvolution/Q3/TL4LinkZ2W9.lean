module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.ClassicalInvolution.Asc77.AscP1Transfer

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open MulAction Subgroup CFSG.GH74.GLS.Bg.Thompson
open scoped IsMulCommutative

variable {X : Type} [Group X] {p : ℕ} [Fact p.Prime]

theorem false_of_transfer_1515 [Finite X] {P Q R₀ : Subgroup X} {u : X}
    (hhom : ∀ (A : Type) [CommGroup A] (f : X →* A), (∀ x ∈ R₀, f x = 1) → f = 1)
    (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.index)
    (hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q)
    (huP : u ∈ P) (huQ : u ∉ Q)
    (hb : ∀ (g : X) (k : ℕ), g⁻¹ * u ^ (p * k) * g ∈ P → g⁻¹ * u ^ (p * k) * g ∈ Q)
    (hc : ∀ g : X, g⁻¹ * u * g ∈ P → IsExtremalIn p P (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ Q ∨ u⁻¹ * (g⁻¹ * u * g) ∈ Q)
    (hT1 : ∀ g : X, g⁻¹ * u * g ∉ Q)
    (hweak : ∀ y ∈ R₀, y ≠ 1 → ∀ g : X, g⁻¹ * y * g ∈ P → g⁻¹ * y * g ∈ Q) :
    False := by
  classical
  have hex : ¬ ∃ g : X, g⁻¹ * u * g ∈ Q ∧ IsExtremalIn p P (g⁻¹ * u * g) :=
    fun ⟨g, hg, _⟩ => hT1 g hg
  have hn : (Q.subgroupOf P).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hQn g g.2 n hn⟩
  have hcycA : IsCyclic (Qbar P Q) := by
    obtain ⟨b, hbP, hbt⟩ := hcyc
    refine ⟨(QuotientGroup.mk ⟨b, hbP⟩ : Qbar P Q), fun a => ?_⟩
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨k, hk⟩ := hbt t t.2
    refine ⟨k, ?_⟩
    have hmem : (⟨b, hbP⟩ ^ k)⁻¹ * t ∈ Q.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hk
    dsimp only
    rw [← QuotientGroup.mk_zpow]
    exact (QuotientGroup.eq (s := Q.subgroupOf P)).mpr hmem
  have hAp : IsPGroup p (Qbar P Q) := hP.to_quotient _
  have : IsMulCommutative (Qbar P Q) := inferInstance
  have hphi_eq : ∀ y z : ↥P, (y : X)⁻¹ * z ∈ Q → phiQ P Q y = phiQ P Q z := by
    intro y z hyz
    have h := (phiQ_eq_one_iff P Q (y⁻¹ * z)).mpr (by simpa using hyz)
    rw [map_mul, map_inv] at h
    exact inv_mul_eq_one.mp h
  have := Fintype.ofFinite (X ⧸ P)
  obtain ⟨n, hn⟩ : ∃ n, orderOf u = p ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP ⟨u, huP⟩
    exact ⟨n, by simpa using hn⟩
  obtain ⟨D, hDC, hDp, hDsyl, huD⟩ := exists_sylow_centralizer (p := p) ⟨n, hn⟩
  let τ : X →* Qbar P Q := MonoidHom.transfer (phiQ P Q)
  have hτ : τ u = ∏ x : X ⧸ P, valF P Q u x := transfer_eq_prod_valF P Q hP huP hb
  have hcomm : ∀ d : ↥D, (d : X) * u = u * d := fun d =>
    (Subgroup.mem_centralizer_iff.mp (hDC d.2) u (Set.mem_singleton u)).symm
  have h1 : ∏ x : X ⧸ P, valF P Q u x = ∏ x : fixedPoints D (X ⧸ P), valF P Q u x :=
    prod_eq_prod_fixedPoints hDp (valF P Q u)
      (fun d x => valF_smul P Q u d (hcomm d) x) (valF_pow P Q u hb)
  have hfixed : ∀ x : fixedPoints D (X ⧸ P), valF P Q u x = phiQ P Q ⟨u, huP⟩ := by
    intro x
    obtain ⟨hyP, hyext⟩ := extremal_of_fixed hP hDC hDsyl huD x.2
    have hxout : valF P Q u x.1 = phiQ P Q ⟨x.1.out⁻¹ * u * x.1.out, hyP⟩ := by
      rw [valF_eq P Q u x.1 x.1.out (QuotientGroup.out_eq' _), dif_pos hyP]
    rw [hxout]
    rcases hc x.1.out hyP hyext with hyQ | hyQ
    · exact absurd ⟨x.1.out, hyQ, hyext⟩ hex
    · exact (hphi_eq ⟨u, huP⟩ ⟨_, hyP⟩ hyQ).symm
  have hcard : ¬ p ∣ Nat.card (fixedPoints D (X ⧸ P)) := by
    have hmod := hDp.card_modEq_card_fixedPoints (X ⧸ P)
    rw [← Nat.ModEq.dvd_iff hmod dvd_rfl, ← Subgroup.index_eq_card]
    exact hPidx
  have hphi_u : phiQ P Q ⟨u, huP⟩ ≠ 1 := by
    intro h
    exact huQ ((phiQ_eq_one_iff P Q _).mp h)
  have hτu : τ u ≠ 1 := by
    rw [hτ, h1, Finset.prod_congr rfl fun x _ => hfixed x, Finset.prod_const, Finset.card_univ,
      Fintype.card_eq_nat_card]
    intro h
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hAp (phiQ P Q ⟨u, huP⟩)
    have hdvd : p ^ m ∣ Nat.card (fixedPoints D (X ⧸ P)) := by
      rw [← hm]; exact orderOf_dvd_of_pow_eq_one h
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
      exact hphi_u hm
    exact hcard ((dvd_pow_self p hm0).trans hdvd)
  have hVR : ∀ y ∈ R₀, τ y = 1 := by
    intro y hy
    refine CFSG.ClassicalInvolution.Asc77.transfer_apply_eq_one (phiQ P Q) y fun g k hg => ?_
    by_cases hyk : y ^ k = 1
    · have : (⟨g⁻¹ * y ^ k * g, hg⟩ : ↥P) = 1 := Subtype.ext (by simp [hyk])
      rw [this, map_one]
    · exact (phiQ_eq_one_iff P Q _).mpr (hweak (y ^ k) (R₀.pow_mem hy k) hyk g hg)
  exact hτu (by rw [hhom _ τ hVR]; rfl)

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
