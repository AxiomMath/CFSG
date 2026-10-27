module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0Co
public import Certificates.Certificate442350
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

open Matrix Certificates.Asc82NormA6 Certificates.T84Quad
open Certificates.A5GL42 (Mat4 Vec4 ofCode vecOfCode)

theorem mem_matsS0_iff (a : Mat4) :
    a ∈ matsS0 ↔ ∃ p : Equiv.Perm (Fin 6), p.sign = 1 ∧ rho p = a := by
  simp only [matsS0, List.mem_toFinset, List.mem_map, codesS0, Finset.mem_sort, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨rhoCode p, ⟨p, hp, rfl⟩, rfl⟩

end T84Co

open Matrix in
theorem sec8t84FactQuad_of_cert :
    Sec8T84FactQuad := by
  intro G _ B hB H hH q hq1 hqeq _
  have F := Certificates.T84Quad.facts_of_check Certificates.certificate442350
  obtain ⟨e, -, -, hmem⟩ := sec8t84_a6_conj B hB H hH
  have hmem' : ∀ h : MulAut ↥B, h ∈ H ↔
      ∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧ T84Co.ActsAs e h (Certificates.Asc82NormA6.rho a) :=
    hmem
  have hmat : ∀ a ∈ Certificates.T84Quad.matsS0, ∃ h ∈ H, T84Co.ActsAs e h a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := (T84Co.mem_matsS0_iff a).mp ha
    obtain ⟨g, hg⟩ := T84Co.exists_actsAs_rho e p
    exact ⟨g, (hmem' g).mpr ⟨p, hp, hg⟩, hg⟩
  obtain ⟨b1, hb1⟩ : ∃ b1 : ↥B, Multiplicative.toAdd (e b1) = Certificates.T84Quad.e1 :=
    ⟨e.symm (Multiplicative.ofAdd Certificates.T84Quad.e1), by simp⟩
  have hQ : ∀ (h : MulAut ↥B) (a : Matrix (Fin 4) (Fin 4) (ZMod 2)), h ∈ H →
      T84Co.ActsAs e h a →
      Multiplicative.toAdd (e (q (h b1))) = a *ᵥ Multiplicative.toAdd (e (q b1)) := by
    intro h a hh hact
    rw [hqeq h hh b1]
    exact hact (q b1)
  have hfix : Multiplicative.toAdd (e (q b1)) = 0 ∨
      Multiplicative.toAdd (e (q b1)) = Certificates.T84Quad.e1 := by
    refine F.fix _ ?_
    intro a ha hae
    obtain ⟨h, hh, hact⟩ := hmat a ha
    have h1 : h b1 = b1 := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [hact b1, hb1, hae]
    have h2 := hQ h a hh hact
    rw [h1] at h2
    exact h2.symm
  have hall : ∀ x : ↥B, x ≠ 1 → ∃ a ∈ Certificates.T84Quad.matsS0, ∃ h ∈ H,
      T84Co.ActsAs e h a ∧ h b1 = x := by
    intro x hx
    have hne : Multiplicative.toAdd (e x) ≠ 0 := by
      intro h0
      apply hx
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h0]; rfl)
    obtain ⟨a, ha, hax⟩ := F.trans _ hne
    obtain ⟨h, hh, hact⟩ := hmat a ha
    refine ⟨a, ha, h, hh, hact, ?_⟩
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hact b1, hb1, hax]
  rcases hfix with h0 | h1
  · left
    funext x
    by_cases hx : x = 1
    · rw [hx]
      exact hq1
    · obtain ⟨a, ha, h, hh, hact, hhx⟩ := hall x hx
      have h2 : Multiplicative.toAdd (e (q x)) = 0 := by
        rw [← hhx, hQ h a hh hact, h0, Matrix.mulVec_zero]
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h2]; rfl)
  · right
    funext x
    by_cases hx : x = 1
    · rw [hx]
      exact hq1
    · obtain ⟨a, ha, h, hh, hact, hhx⟩ := hall x hx
      have h2 : Multiplicative.toAdd (e (q x)) = Multiplicative.toAdd (e x) := by
        rw [← hhx, hQ h a hh hact, h1, hact b1, hb1]
      exact e.injective (Multiplicative.toAdd.injective h2)

end CFSG.OddStandard.SmallF3.Omega
