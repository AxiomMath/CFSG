module

import CFSG.Quasithin.Background.C126NatDSimple
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E2

theorem inf_biSup_eq_bot_of_isL2Natural {W : Type*} [CommGroup W] {C : Subgroup W}
    {I : Finset (Subgroup (MulAut W))}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hnat : ∀ L ∈ I, ∃ n : ℕ, IsL2Natural L C n) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥ := by
  obtain ⟨n, hn, F, _, _, hF, e, -⟩ := hnat L hL
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn
      (by rw [Nat.card_eq_fintype_card]; exact hF)
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxL, hxJ⟩ := hx
  have hle : (⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L') ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    iSup₂_le fun L' hL' => iSup_le fun hne y hy =>
      Subgroup.mem_centralizer_iff.2 fun a ha => hcomm L hL L' hL' (Ne.symm hne) a ha y hy
  have hcent : ∀ a ∈ L, a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_iff.1 (hle hxJ) a ha
  have hz : e ⟨x, hxL⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨g, rfl⟩ := e.surjective B
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hcent g g.2))
  rw [C126.Nat.center_sl2_eq_bot, Subgroup.mem_bot, map_eq_one_iff e e.injective] at hz
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val hz)

end CFSG.AGLEmbeddingD2.GN
