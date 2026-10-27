module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
import CFSG.LieType.SeitzGeneration.ExcTorusF4One
import CFSG.LieType.SeitzGeneration.ExcTorusF4Two
import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
import CFSG.LieType.SeitzGeneration.ExcTorusE6Six
import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
import CFSG.LieType.SeitzGeneration.ExcTorusE8Five
import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight
import CFSG.LieType.SeitzGeneration.ExcTorusE8Ten
import CFSG.LieType.SeitzGeneration.ExcTorusE8Twelve
import CFSG.LieType.SeitzGeneration.ExcTorusRankE6
import CFSG.LieType.SeitzGeneration.ExcTorusRankE7
import CFSG.LieType.SeitzGeneration.ExcTorusRankE8
import CFSG.LieType.SeitzGeneration.ExcPlaneF4Rest
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
  CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem seven_le_of_dvd_orderOf {p q d : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ q)
    (hd : 3 ∣ d) (he : orderOf (q : ZMod p) = d) : 7 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have h1 : d ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have h2 : 3 ∣ p - 1 := hd.trans h1
  omega

private theorem orderOf_dvd_two_of_dvd_sq_sub_one {p n : ℕ} (hn : ¬ p ∣ n) (h : p ∣ n ^ 2 - 1) :
    orderOf ((n : ℕ) : ZMod p) ∣ 2 := by
  apply orderOf_dvd_of_pow_eq_one
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero p)
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn0)
  have h1 := (ZMod.natCast_eq_zero_iff (n ^ 2 - 1) p).2 h
  rw [Nat.cast_sub hn1] at h1
  push_cast at h1
  exact sub_eq_zero.1 h1

private theorem degCount_le_two_of {τ : Tag}
    (hτ : τ = Tag.F4 ∨ τ = Tag.E6 ∨ τ = Tag.E7 ∨ τ = Tag.E8) {S : List ℕ}
    (hS : ∀ e ≤ 30, e ∈ S ∨ degCount τ e ≤ 2) {e : ℕ} (he : e ∉ S) : degCount τ e ≤ 2 := by
  by_cases h30 : e ≤ 30
  · exact (hS e h30).resolve_left he
  · have : ¬ 0 < degCount τ e := fun h => h30 (le_thirty_of_degCount_pos hτ h)
    omega

private theorem degCount_E6_eq_two {e : ℕ} (h : degCount Tag.E6 e = 2) : e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E6 e = 2 → e = 4 ∨ e = 6 := by decide
  exact key e h30 h

private theorem degCount_E7_eq_two {e : ℕ} (h : degCount Tag.E7 e = 2) : e = 4 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E7) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E7 e = 2 → e = 4 := by decide
  exact key e h30 h

private theorem degCount_E8_eq_two {e : ℕ} (h : degCount Tag.E8 e = 2) :
    e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E8) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E8 e = 2 → e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by decide
  exact key e h30 h

section Certified

private theorem sdCross_of_adjoint {τ : Tag} {K : Type} [Group K] [Finite K] {ℓ f p : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) (hm : UntwistedChevalleyModel K τ (ℓ ^ f))
    (H : ∀ (F : Type) [Field F] [Finite F], ¬ p ∣ Nat.card F →
      SylowDichotomyAt ↥(adjointGroup τ F) p) : SylowDichotomyAt K p := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  exact SylowDichotomyAt.of_mulEquiv hp
    (e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)) (H F hpF)

private theorem sylow_comm_of_sylowTorus {G : Type} [Group G] {p m : ℕ} (h : SylowTorus G p m) :
    ∀ S : Sylow p G, IsMulCommutative (S : Subgroup G) := by
  intro S
  rw [isMulCommutative_iff]
  intro a b
  exact Subtype.ext (mul_comm_of_sylowTorus h S.isPGroup' a.2 b.2)

private theorem rankLE2_E6_of_degCount_eq_two (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hcnt : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    RankLE2 p ↥(adjointGroup Tag.E6 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  rcases degCount_E6_eq_two hcnt with rfl | rfl
  · exact (sylowTorus_E6_four K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E6_six K hp he).rankLE2 hp le_rfl

private theorem rankLE2_E7_of_degCount_eq_two (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hcnt : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    RankLE2 p ↥(adjointGroup Tag.E7 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  obtain rfl := degCount_E7_eq_two hcnt
  exact (sylowTorus_E7_four K hp he).rankLE2 hp le_rfl

private theorem rankLE2_E8_of_degCount_eq_two (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hcnt : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    RankLE2 p ↥(adjointGroup Tag.E8 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  rcases degCount_E8_eq_two hcnt with rfl | rfl | rfl | rfl
  · exact (sylowTorus_E8_five K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E8_eight K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E8_ten K hp he).rankLE2 hp le_rfl
  · exact (sylowTorus_E8_twelve K hp he).rankLE2 hp le_rfl

private theorem rankLE2_of_degCount_le_two {τ : Tag}
    (hτ : τ = Tag.E6 ∨ τ = Tag.E7 ∨ τ = Tag.E8) (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (hcnt : degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2) :
    RankLE2 p ↥(adjointGroup τ K) := by
  rcases Nat.lt_or_ge (degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p))) 2 with hlt | hge
  · have h1 : degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by omega
    rcases hτ with rfl | rfl | rfl
    · exact (rankLE1_E6 K hp hpK h1).rankLE2
    · exact (rankLE1_E7 K hp hpK h1).rankLE2
    · exact (rankLE1_E8 K hp hpK h1).rankLE2
  · have h2 : degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2 := by omega
    rcases hτ with rfl | rfl | rfl
    · exact rankLE2_E6_of_degCount_eq_two K hp h2
    · exact rankLE2_E7_of_degCount_eq_two K hp h2
    · exact rankLE2_E8_of_degCount_eq_two K hp h2

private theorem sdAdj_F4 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : SylowDichotomyAt ↥(adjointGroup Tag.F4 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpF
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_one F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc le_rfl
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_two F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc le_rfl
  refine SylowDichotomyAt.of_card_elemAbelian_le hp ?_
  have hnd : ¬ p ∣ Nat.card F ^ 2 - 1 := by
    intro h
    have h2' := orderOf_dvd_two_of_dvd_sq_sub_one hpF h
    rw [he] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  exact rankLE2_adjointGroup_F4 F hp (by omega) hpF hnd

private theorem sdAdj_E6 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : SylowDichotomyAt ↥(adjointGroup Tag.E6 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_one F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_two F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc le_rfl
  by_cases h3 : e = 3
  · subst h3
    have h7 := seven_le_of_dvd_orderOf hp h5 hpF (dvd_refl 3) he
    obtain ⟨m, hm⟩ := exists_sylowTorus_E6 F hp h7 hpF (by rw [he]; decide)
    exact SylowDichotomyAt.of_sylow_comm (sylow_comm_of_sylowTorus hm)
  refine SylowDichotomyAt.of_card_elemAbelian_le hp ?_
  exact rankLE2_of_degCount_le_two (Or.inl rfl) F hp hpF (by
    rw [he]
    exact degCount_le_two_of (Or.inr (Or.inl rfl)) (S := [1, 2, 3]) (by decide)
      (by simp [h1, h2, h3]))

private theorem sdAdj_E7 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : SylowDichotomyAt ↥(adjointGroup Tag.E7 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_one F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_two F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h3 : e = 3
  · subst h3
    have h7 := seven_le_of_dvd_orderOf hp h5 hpF (dvd_refl 3) he
    obtain ⟨m, hm⟩ := exists_sylowTorus_E7 F hp h7 hpF (by rw [he]; decide)
      (Or.inr (by rw [he]))
    exact SylowDichotomyAt.of_sylow_comm (sylow_comm_of_sylowTorus hm)
  by_cases h6 : e = 6
  · subst h6
    have h7 := seven_le_of_dvd_orderOf hp h5 hpF (by norm_num) he
    obtain ⟨m, hm⟩ := exists_sylowTorus_E7 F hp h7 hpF (by rw [he]; decide)
      (Or.inr (by rw [he]; norm_num))
    exact SylowDichotomyAt.of_sylow_comm (sylow_comm_of_sylowTorus hm)
  refine SylowDichotomyAt.of_card_elemAbelian_le hp ?_
  exact rankLE2_of_degCount_le_two (Or.inr (Or.inl rfl)) F hp hpF (by
    rw [he]
    exact degCount_le_two_of (Or.inr (Or.inr (Or.inl rfl))) (S := [1, 2, 3, 6]) (by decide)
      (by simp [h1, h2, h3, h6]))

private theorem sdAdj_E8 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : SylowDichotomyAt ↥(adjointGroup Tag.E8 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_one F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_two F hp hp3 he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h3 : e = 3
  · subst h3
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_three F hp he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc le_rfl
  by_cases h4 : e = 4
  · subst h4
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_four F hp he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc le_rfl
  by_cases h6 : e = 6
  · subst h6
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_six F hp he
    exact SylowDichotomyAt.of_elemAbelian hp hE hc le_rfl
  refine SylowDichotomyAt.of_card_elemAbelian_le hp ?_
  exact rankLE2_of_degCount_le_two (Or.inr (Or.inr rfl)) F hp hpF (by
    rw [he]
    exact degCount_le_two_of (Or.inr (Or.inr (Or.inr rfl))) (S := [1, 2, 3, 4, 6]) (by decide)
      (by simp [h1, h2, h3, h4, h6]))

theorem sdLieCross_F4 : SDLieCrossAt .F4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact sdCross_of_adjoint (τ := Tag.F4) hp hℓ hpℓ hm fun F _ _ hpF => sdAdj_F4 F hp h5 hpF

theorem sdLieCross_E6 : SDLieCrossAt .E6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact sdCross_of_adjoint (τ := Tag.E6) hp hℓ hpℓ hm fun F _ _ hpF => sdAdj_E6 F hp h5 hpF

theorem sdLieCross_E7 : SDLieCrossAt .E7 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact sdCross_of_adjoint (τ := Tag.E7) hp hℓ hpℓ hm fun F _ _ hpF => sdAdj_E7 F hp h5 hpF

theorem sdLieCross_E8 : SDLieCrossAt .E8 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact sdCross_of_adjoint (τ := Tag.E8) hp hℓ hpℓ hm fun F _ _ hpF => sdAdj_E8 F hp h5 hpF

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
