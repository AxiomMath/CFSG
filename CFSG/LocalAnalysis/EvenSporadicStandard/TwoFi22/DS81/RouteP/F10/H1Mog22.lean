module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Mog22Gens
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Derivation

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Monster.B.TwoA CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.Code22

@[expose] def mog22H1Cons : List (Option ℕ × List ℕ × List ℕ) :=
  [(none, [0, 0], [2061, 0, 2222, 2287, 2082, 0, 0, 0, 0, 0, 0]),
    (none, [1, 1, 1, 1], [0, 0, 12425, 35364, 0, 0, 0, 0, 0, 0, 0]),
    (none, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
      [10314, 10788, 0, 0, 0, 10982, 0, 0, 0, 0, 0]),
    (none, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
      [8192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (none, [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0,
      1, 1, 1, 0, 1, 1, 1], [0, 0, 10315, 0, 0, 0, 0, 0, 0, 0, 0]),
    (none, [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0,
      1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1], [8741, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]

@[expose] def mog22H1Phi : List ℕ :=
  [0, 0, 0, 0, 1188, 0, 0, 0, 1197, 0, 702, 0, 0, 0, 256, 0, 1064, 903, 412, 1283, 1461, 914]

@[expose] def mog22H1Units : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

theorem mog22H1Units_lt : ∀ w ∈ mog22H1Units, w < 2 ^ 11 := by
  decide +kernel

theorem mog22H1Cons_ok : consOK 11 0 [mog22ColsA, mog22ColsB] (fun _ => []) mog22H1Cons = true := by
  decide +kernel

theorem mog22H1_cert :
    matOf (2 * 11)
        (fun v => v ^^^
          actM (mog22H1Units.map (packB 11 mog22ColsA mog22ColsB)) (actM mog22H1Phi v)) =
      matOf (2 * 11) (conSum [mog22ColsA, mog22ColsB] 11 0 0 mog22H1Cons) := by
  decide +kernel

theorem h1_mog22 :
    ∀ φ : ↥mog22 → W11,
      (∀ g h : ↥mog22, φ (g * h) = φ g * rho11 mog22 mog22_le_autPerm g (φ h)) →
        ∃ w : W11, ∀ g : ↥mog22, φ g = w * (rho11 mog22 mog22_le_autPerm g w)⁻¹ := by
  intro φ hφ
  obtain ⟨δ, hδ, hδ'⟩ := exists_derivation_of_crossedHom (rho11 mog22 mog22_le_autPerm)
    (rho11_injective mog22 mog22_le_autPerm) φ hφ
  obtain ⟨m, -, hm⟩ := eq_inner_std (n := 11) (H₀ := (rho11 mog22 mog22_le_autPerm).range)
    (R := ⊥) (δ := δ) hδ' (p := 0) (z := 0)
    (fun r hr => by
      have h1 : δ r = 1 := by
        rw [Subgroup.mem_bot.1 hr]
        exact deriv_one hδ'
      rw [h1]
      exact Subgroup.one_mem _)
    (by norm_num) (by decide) range_rho11_mog22_le_closure mog22RhoA_mem mog22RhoB_mem
    actsBy_mog22RhoA actsBy_mog22RhoB mog22Cols_lt (K := 0) (tcols := fun _ => [])
    (fun t ht => absurd ht (Nat.not_lt_zero t)) mog22H1Cons_ok mog22H1Units_lt mog22H1_cert
  exact ⟨toW 11 m, fun g => by rw [← hδ g]; exact hm _ ⟨g, rfl⟩⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
