module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.ClassPkg
public import Certificates.Certificate197003

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check

set_option linter.unusedSectionVars false


private theorem ix2_not_bad {N : Subgroup HY} (hN : N ≤ T0Y) (hNn : (N.subgroupOf T0Y).Normal)
    (hR : R0Y ≤ N) {Z : Set (Equiv.Perm (Fin 480))}
    (hD : ∀ g : HY, g * t0Y * g⁻¹ ∈ N → phi (g * t0Y * g⁻¹) ∈ Z) {x : HY} (hx : x ∈ N) :
    ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Z) (phi x) := by
  rintro ⟨d, ⟨g, hg, rfl, hdZ⟩, hdc⟩
  obtain ⟨g', -, rfl⟩ := exists_of_mem_G (by decide) hg
  have hc : ∀ a b : HY, phi (a * b * a⁻¹) = phi a * phi b * (phi a)⁻¹ := fun a b => by
    rw [map_mul, map_mul, map_inv]
  have hle : Subgroup.closure ((Om2Facts.R : Set (Equiv.Perm (Fin 480))) ∪
      {y | ∃ h ∈ Om2Facts.G wT, y = h * phi x * h⁻¹}) ≤ N.map phi := by
    rw [Subgroup.closure_le]
    rintro y (hy | ⟨h, hh, rfl⟩)
    · rw [SetLike.mem_coe, ← map_R0Y] at hy
      exact Subgroup.map_mono hR hy
    · obtain ⟨h', hh', rfl⟩ := exists_of_mem_G (wordYOK_of_sub wT_sub) hh
      rw [classPkg0Y.1] at hh'
      refine ⟨h' * x * h'⁻¹, ?_, hc h' x⟩
      exact Subgroup.mem_subgroupOf.1
        (hNn.conj_mem ⟨x, hN hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨h', hh'⟩)
  obtain ⟨d', hd', e⟩ := hle hdc
  have hd : d' = g' * t0Y * g'⁻¹ := phi_injective (by rw [e, hc, phi_t0Y])
  rw [hd] at hd'
  have := hD g' hd'
  rw [hc, phi_t0Y] at this
  exact hdZ this

private theorem ix2_card_le {p : ℕ} [Fact p.Prime] {ws : List (List ℕ)}
    (hws : ∀ w ∈ ws, wordYOK w = true) (hp : IsPGroup p (closureY ws)) {N : Subgroup HY}
    {Z : Set (Equiv.Perm (Fin 480))}
    (hgood : ∀ x ∈ N, ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Z) (phi x)) {k : ℕ}
    (hk : {x | x ∈ Om2Facts.G ws ∧
      ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Z) x}.ncard < p ^ (k + 1)) :
    Nat.card ↥(N ⊓ closureY ws) ≤ p ^ k := by
  refine OmGen.card_le_of_pgroup_subset (p := p)
    (S := phi ⁻¹' {x | x ∈ Om2Facts.G ws ∧
      ¬ OmGen.BadElt (Om2Facts.G wT) Om2Facts.R (Om2Facts.D Z) x})
    hp.to_inf_right ?_ (Set.toFinite _) (lt_of_le_of_lt ?_ hk)
  · intro x hx
    exact ⟨(mem_closureY_iff hws).1 hx.2, hgood x hx.1⟩
  · exact Set.ncard_le_ncard_of_injOn phi (fun x hx => hx) (fun x _ y _ h => phi_injective h)
      (Set.toFinite _)

theorem card_le_of_avoid1 {N : Subgroup HY} (hN : N ≤ T0Y) (hNn : (N.subgroupOf T0Y).Normal)
    (hR : R0Y ≤ N) (hD : ∀ x : HY, x * t0Y * x⁻¹ ∈ N → x * t0Y * x⁻¹ = t0Y) :
    Nat.card N ≤ 8 := by
  obtain ⟨-, -, hT, h2, h3, hS2, hS3, -, -⟩ := classPkg0Y
  obtain ⟨hs2, hs3, -, -⟩ := Certificates.certificate197003.2.2.2.2.1
  have p2 : IsPGroup 2 (closureY wS0) := IsPGroup.of_card (n := 12) (h2.trans (by norm_num))
  have p3 : IsPGroup 3 (closureY wP3) := IsPGroup.of_card (n := 3) (h3.trans (by norm_num))
  rw [OmGen.card_eq_mul_of_sylow hN hNn hS2 hS3 p2 p3 (by rw [hT, h2, h3])]
  have hgood := fun x (hx : x ∈ N) => ix2_not_bad hN hNn hR (Z := Om2Facts.Zt1) (fun g hg => by
    rw [hD g hg, phi_t0Y, Om2Facts.Zt1]
    exact Set.mem_singleton _) hx
  have b2 : Nat.card ↥(N ⊓ closureY wS0) ≤ 2 ^ 3 :=
    ix2_card_le (wordYOK_of_sub wS0_sub) p2 hgood (lt_of_le_of_lt hs2 (by norm_num))
  have b3 : Nat.card ↥(N ⊓ closureY wP3) ≤ 3 ^ 0 :=
    ix2_card_le (wordYOK_of_sub wP3_sub) p3 hgood (lt_of_le_of_lt hs3 (by norm_num))
  calc _ ≤ 2 ^ 3 * 3 ^ 0 := Nat.mul_le_mul b2 b3
    _ = 8 := by norm_num

theorem card_le_of_avoid4 {N : Subgroup HY} (hN : N ≤ T0Y) (hNn : (N.subgroupOf T0Y).Normal)
    (hR : R0Y ≤ N)
    (hD : ∀ x : HY, x * t0Y * x⁻¹ ∈ N → x * t0Y * x⁻¹ = t0Y ∨ ∃ k < 3, x * t0Y * x⁻¹ = t0Y * cK k) :
    Nat.card N ≤ 9216 := by
  obtain ⟨-, -, hT, h2, h3, hS2, hS3, -, -⟩ := classPkg0Y
  obtain ⟨-, -, hs2, hs3⟩ := Certificates.certificate197003.2.2.2.2.1
  have p2 : IsPGroup 2 (closureY wS0) := IsPGroup.of_card (n := 12) (h2.trans (by norm_num))
  have p3 : IsPGroup 3 (closureY wP3) := IsPGroup.of_card (n := 3) (h3.trans (by norm_num))
  rw [OmGen.card_eq_mul_of_sylow hN hNn hS2 hS3 p2 p3 (by rw [hT, h2, h3])]
  have hgood := fun x (hx : x ∈ N) => ix2_not_bad hN hNn hR (Z := Om2Facts.Zt4) (fun g hg => by
    rw [Om2Facts.Zt4]
    rcases hD g hg with h | ⟨k, hk, h⟩
    · rw [h, phi_t0Y]
      exact Set.mem_insert _ _
    · rw [h, map_mul, phi_t0Y, phi_cK hk]
      interval_cases k
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))) hx
  have b2 : Nat.card ↥(N ⊓ closureY wS0) ≤ 2 ^ 10 :=
    ix2_card_le (wordYOK_of_sub wS0_sub) p2 hgood (lt_of_le_of_lt hs2 (by norm_num))
  have b3 : Nat.card ↥(N ⊓ closureY wP3) ≤ 3 ^ 2 :=
    ix2_card_le (wordYOK_of_sub wP3_sub) p3 hgood (lt_of_le_of_lt hs3 (by norm_num))
  calc _ ≤ 2 ^ 10 * 3 ^ 2 := Nat.mul_le_mul b2 b3
    _ = 9216 := by norm_num

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
