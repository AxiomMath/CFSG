module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433Reduction
import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Hopf
import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.Blueprint.Multiplier CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LieType.Steinberg.CentralExt

private theorem genericOrders_plus_four (p f : ℕ) :
    genericOrders .POmegaPlus 4 p f = (1, 1) ∨ genericOrders .POmegaPlus 4 p f = (2, 2) := by
  unfold genericOrders
  by_cases h : Even (p ^ f)
  · left
    simp [h]
  · right
    simp [h, Nat.even_iff]

private theorem exceptionalOrders_plus_four (p f : ℕ) :
    exceptionalOrders .POmegaPlus 4 p f = (1, 1) ∨
      exceptionalOrders .POmegaPlus 4 p f = (2, 2) := by
  unfold exceptionalOrders
  split <;> simp_all

private theorem card_table_plus_four (p f : ℕ) :
    ∃ k : ℕ, Nat.card (generic .POmegaPlus 4 p f × exceptional .POmegaPlus 4 p f) = 2 ^ k := by
  have hc : ∀ n : ℕ, Nat.card (Multiplicative (ZMod n)) = n := fun n => by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n), Nat.card_zmod]
  unfold generic exceptional
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, hc, hc, hc, hc]
  rcases genericOrders_plus_four p f with hg | hg <;>
    rcases exceptionalOrders_plus_four p f with he | he <;> rw [hg, he]
  · exact ⟨0, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨4, by norm_num⟩

theorem noThreeCover_omegaPlus_four
    (F : Type) [Field F] [Finite F] :
    LieComp.NoThreeCover (StatedProj (StatedOmega (StatedQuadPlus 4 F))) := by
  intro Y _ _ hY ⟨e⟩ h3
  haveI := Fintype.ofFinite F
  obtain ⟨p, f, hp, hf, hFc⟩ : ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Nat.card F = p ^ f := by
    obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨ringChar F, n, CharP.char_is_prime F _, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 F))) .POmegaPlus 4
      p f := ⟨⟨hp, hf, le_rfl⟩, F, inferInstance, inferInstance, hFc, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, ⟨eM⟩⟩ : commutator (StatedProj (StatedOmega (StatedQuadPlus 4 F))) = ⊤ ∧
      Nonempty (griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadPlus 4 F))) ≃*
        generic .POmegaPlus 4 p f × exceptional .POmegaPlus 4 p f) := by
    by_cases hq : 3 ≤ p ^ f
    · exact GriessClassical.pomegaPlus_row hmod (Or.inl hq)
    · have h2 : p ^ f = 2 := by
        have := le_trans hp.two_le (Nat.le_self_pow (by omega : f ≠ 0) p)
        omega
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 h2
      exact GriessClassical.pomegaPlus_four_two_row ⟨hmod.1, Or.inl hmod⟩
  obtain ⟨k, hk⟩ := card_table_plus_four p f
  haveI : Finite (generic .POmegaPlus 4 p f × exceptional .POmegaPlus 4 p f) :=
    Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ (by norm_num))
  let π : Y →* StatedProj (StatedOmega (StatedQuadPlus 4 F)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Y) y) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hd := i1021_card_ker_dvd π hπs hker.le hY.1 eM
  rw [hker, hk] at hd
  have h32 : 3 ∣ 2 ^ k := h3.trans hd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
  omega

theorem d4CentreTrivial_holds :
    D4CentreTrivial :=
  d4CentreTrivial_of_noThreeCover fun F _ _ => noThreeCover_omegaPlus_four F

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
