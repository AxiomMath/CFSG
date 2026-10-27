module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.ClassPkg

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

set_option linter.unusedSectionVars false


private theorem ix_not_bad {N : Subgroup WP} (hN : N ≤ T0) (hNn : (N.subgroupOf T0).Normal)
    (hR0 : R0 ≤ N) (hR0' : R0' ≤ N)
    (hD : ∀ x : WP, x * t0 * x⁻¹ ∈ N → x * t0 * x⁻¹ = t0 ∨ x * t0 * x⁻¹ = t0 * zW)
    {x : WP} (hx : x ∈ N) :
    ¬ OmGen.BadElt (Om1Facts.G wT)
      ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') Om1Facts.D
      (x : Equiv.Perm (Fin 240)) := by
  rintro ⟨d, ⟨g, hg, rfl, hd1, hd2⟩, hdc⟩
  let g' : WP := ⟨g, Wp_le hg⟩
  have hc : ∀ a b : WP, ((a * b * a⁻¹ : WP) : Equiv.Perm (Fin 240)) =
      (a : Equiv.Perm (Fin 240)) * b * (a : Equiv.Perm (Fin 240))⁻¹ := fun a b => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hle : Subgroup.closure (((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') ∪
      {y | ∃ h ∈ Om1Facts.G wT, y = h * x * h⁻¹}) ≤ N.map wPlus.subtype := by
    rw [Subgroup.closure_le]
    rintro y ((hy | hy) | ⟨h, hh, rfl⟩)
    · rw [SetLike.mem_coe, ← map_R0] at hy
      exact Subgroup.map_mono hR0 hy
    · rw [SetLike.mem_coe, ← map_R0'] at hy
      exact Subgroup.map_mono hR0' hy
    · obtain ⟨h', hh', rfl⟩ := exists_of_mem_G (wordOK_of_sub wT_sub) hh
      rw [classPkg0.1] at hh'
      refine ⟨h' * x * h'⁻¹, ?_, hc h' x⟩
      exact Subgroup.mem_subgroupOf.1
        (hNn.conj_mem ⟨x, hN hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨h', hh'⟩)
  obtain ⟨d', hd', e⟩ := hle hdc
  have hd : d' = g' * t0 * g'⁻¹ := Subtype.ext (by rw [hc, coe_t0]; exact e)
  rw [hd] at hd'
  rcases hD g' hd' with h | h
  · apply hd1
    have := congrArg Subtype.val h
    rwa [hc, coe_t0] at this
  · apply hd2
    have := congrArg Subtype.val h
    rwa [hc, Subgroup.coe_mul, coe_t0, coe_zW_eq_z] at this

private theorem ix_card_le {p : ℕ} [Fact p.Prime] {ws : List (List ℕ)}
    (hws : ∀ w ∈ ws, wordOK w = true) (hp : IsPGroup p (closureW ws)) {N : Subgroup WP}
    (hgood : ∀ x ∈ N, ¬ OmGen.BadElt (Om1Facts.G wT)
      ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') Om1Facts.D
      (x : Equiv.Perm (Fin 240))) {k : ℕ}
    (hk : {x | x ∈ Om1Facts.G ws ∧ ¬ OmGen.BadElt (Om1Facts.G wT)
      ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') Om1Facts.D x}.ncard <
        p ^ (k + 1)) :
    Nat.card ↥(N ⊓ closureW ws) ≤ p ^ k := by
  refine OmGen.card_le_of_pgroup_subset (p := p)
    (S := (fun x : WP => (x : Equiv.Perm (Fin 240))) ⁻¹' {x | x ∈ Om1Facts.G ws ∧
      ¬ OmGen.BadElt (Om1Facts.G wT)
        ((Om1Facts.R : Set (Equiv.Perm (Fin 240))) ∪ Om1Facts.R') Om1Facts.D x})
    hp.to_inf_right ?_ (Set.toFinite _) (lt_of_le_of_lt ?_ hk)
  · intro x hx
    exact ⟨(mem_closureW_iff hws).1 hx.2, hgood x hx.1⟩
  · exact Set.ncard_le_ncard_of_injOn (fun x : WP => (x : Equiv.Perm (Fin 240))) (fun x hx => hx)
      (fun x _ y _ h => Subtype.ext h) (Set.toFinite _)

theorem card_le_of_avoid {N : Subgroup WP} (hN : N ≤ T0) (hNn : (N.subgroupOf T0).Normal)
    (hR0 : R0 ≤ N) (hR0' : R0' ≤ N)
    (hD : ∀ x : WP, x * t0 * x⁻¹ ∈ N → x * t0 * x⁻¹ = t0 ∨ x * t0 * x⁻¹ = t0 * zW) :
    Nat.card N ≤ 192 := by
  obtain ⟨-, -, hT, h2, h3, hS2, hS3, -⟩ := classPkg0
  obtain ⟨hb2, hb3⟩ := Certificates.certificate197001.2.2.2.2.2.2.2.2.2.2.1
  have p2 : IsPGroup 2 (closureW wS0) := IsPGroup.of_card (n := 12) (h2.trans (by norm_num))
  have p3 : IsPGroup 3 (closureW wP3) := IsPGroup.of_card (n := 3) (h3.trans (by norm_num))
  rw [OmGen.card_eq_mul_of_sylow hN hNn hS2 hS3 p2 p3 (by rw [hT, h2, h3])]
  have hgood := fun x (hx : x ∈ N) => ix_not_bad hN hNn hR0 hR0' hD hx
  have b2 : Nat.card ↥(N ⊓ closureW wS0) ≤ 2 ^ 6 :=
    ix_card_le (wordOK_of_sub wS0_sub) p2 hgood (lt_of_le_of_lt hb2 (by norm_num))
  have b3 : Nat.card ↥(N ⊓ closureW wP3) ≤ 3 ^ 1 :=
    ix_card_le (wordOK_of_sub wP3_sub) p3 hgood (lt_of_le_of_lt hb3 (by norm_num))
  calc _ ≤ 2 ^ 6 * 3 ^ 1 := Nat.mul_le_mul b2 b3
    _ = 192 := by norm_num

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
