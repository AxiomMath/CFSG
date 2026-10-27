module

public import CFSG.HardMathSupport.Timmesfeld.DFour.Even
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Split

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.T1b

@[expose] def DFourCrossThreeDvd : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (r f : ℕ), StatedClassicalModel S .POmegaPlus 4 r f →
    Subgroup.center S = ⊥ → r ≠ 2 → r ≠ 3 → 3 ∣ f →
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) + 1

theorem classical_of_lieModel_plus {X : Type} [Group X] {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel X .POmegaPlus n r f) :
    StatedClassicalModel X .POmegaPlus n r f :=
  CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)

theorem multiplier_orders_dvd_two (r f : ℕ) :
    ((genericOrders .POmegaPlus 4 r f).1 ∣ 2 ∧ (genericOrders .POmegaPlus 4 r f).2 ∣ 2) ∧
      ((exceptionalOrders .POmegaPlus 4 r f).1 ∣ 2 ∧
        (exceptionalOrders .POmegaPlus 4 r f).2 ∣ 2) := by
  refine ⟨?_, ?_⟩
  · simp only [genericOrders]
    split_ifs with h1 h2 <;> first | (simp; done) | exact absurd (by decide : Even 4) h2
  · unfold exceptionalOrders
    split <;> simp_all

theorem not_three_dvd_card_center (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) {r f : ℕ}
    (hm : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus 4 r f) :
    ¬ 3 ∣ Nat.card (Subgroup.center L) := by
  have hcen := center_centerQuotient_eq_bot hq
  have hnc : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.center (L ⧸ Subgroup.center L) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hall y x
    obtain ⟨a, b, hab⟩ := (hq.2.toNontrivial).exists_pair_ne
    have ha : a ∈ Subgroup.center (L ⧸ Subgroup.center L) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.center (L ⧸ Subgroup.center L) := htop ▸ Subgroup.mem_top b
    rw [hcen, Subgroup.mem_bot] at ha hb
    exact hab (ha.trans hb.symm)
  have hq' : CFSG.IsQuasisimple L := ⟨⟨hq.1⟩, hq.2, hnc⟩
  have h := Tables.Multiplier.center_dvd_table hGA hq' (MulEquiv.refl _)
    (Tables.Multiplier.lieModel_of_classical hm)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := multiplier_orders_dvd_two r f
  have h16 : (genericOrders .POmegaPlus 4 r f).1 * (genericOrders .POmegaPlus 4 r f).2 *
      ((exceptionalOrders .POmegaPlus 4 r f).1 * (exceptionalOrders .POmegaPlus 4 r f).2) ∣
        2 * 2 * (2 * 2) :=
    Nat.mul_dvd_mul (Nat.mul_dvd_mul h1 h2) (Nat.mul_dvd_mul h3 h4)
  intro h3d
  have := (h3d.trans h).trans h16
  norm_num at this

theorem t1bLieHardAt_POmegaPlus_of_residual (hGA : CFSG.Open.GriessAllModelsStatement)
    (hres : DFourCrossThreeDvd) : T1bLieHardAt .POmegaPlus := by
  intro L _ _ hLC hq hK p hp hp2 hcond ⟨n, r, f, hm, hE⟩
  have hE' : ¬ (n = 4 → 3 < p) := hE
  have hn4 : n = 4 := by
    by_contra h
    exact hE' fun h' => absurd h' h
  subst hn4
  have hp3 : p = 3 := by
    have hle : ¬ 3 < p := fun h => hE' fun _ => h
    have := hp.two_le
    omega
  subst hp3
  have hcl := classical_of_lieModel_plus hm
  have hZ := not_three_dvd_card_center hGA hq hcl
  have hcen := center_centerQuotient_eq_bot hq
  have hA := pRank_mulAut_le_mulAut_centerQuotient hq.1 hp (L := L)
  have hS := pRank_centerQuotient_le_of_not_dvd hp hZ
  have key : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (L ⧸ Subgroup.center L))) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) + 1 := by
    by_cases hf : 3 ∣ f
    · by_cases hr2 : r = 2
      · subst hr2
        exact pRank_mulAut_le_of_charTwo hcl hcen
      · by_cases hr3 : r = 3
        · subst hr3
          exfalso
          have h7 : CFSG.Open.pRank 3 (⊤ : Subgroup L) < 7 := hcond.resolve_right hZ
          have h12 : 4 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) := by
            obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
            have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
            have h4 := CFSG.SectionRank.ClassicalOdd.four_mul_le_pRank_omegaPlus (K := K)
              (n := 4) le_rfl (p := 3) (f := f) (by norm_num) hK
            rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h4
          have hf1 : 1 ≤ f := hcl.1.2.1
          have hf3 : 3 ≤ f := Nat.le_of_dvd (by omega) hf
          omega
        · exact hres _ r f hcl hcen hr2 hr3 hf
    · exact pRank_mulAut_le_of_not_dvd hcl hcen hf
  omega

end CFSG.HardMathSupport.Timmesfeld.DFour
