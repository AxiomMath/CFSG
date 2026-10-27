module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem not_dvd_cube_mul_cube_add_one {q p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) : ¬ p ∣ q ^ 3 * (q ^ 3 + 1) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · have hq' : p ∣ q := hp.dvd_of_dvd_pow h1
    have h2 : p ∣ q - (q - 1) := Nat.dvd_sub hq' hpq
    have h3 : q - (q - 1) = 1 := by omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  · obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have hr : p ∣ r := by simpa using hpq
    have key : (r + 1) ^ 3 + 1 = r * ((r + 1) ^ 2 + (r + 1) + 1) + 2 := by ring
    have h3 : p ∣ 2 := by
      rw [key] at h1
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right hr ((r + 1) ^ 2 + (r + 1) + 1))).1 h1
    have h4 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    omega

section


theorem reeG2_sylow_cyclic_of_dvd_sub_one (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (P : Sylow p (ReeTag.G2.reeGamma K a)) : IsCyclic (P : Subgroup (ReeTag.G2.reeGamma K a)) := by
  have hp : p.Prime := Fact.out
  have hqpos : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm0 : Nat.card K ^ 3 * (Nat.card K ^ 3 + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 (by omega)) (by omega)
  have hn0 : Nat.card K - 1 ≠ 0 := by omega
  have hle : ReeTag.G2.reeFixedTorus K a ≤ ReeTag.G2.reeGamma K a :=
    ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma
  have hmem : ∀ s : Kˣ, smallReeTorusElt a K s ∈ ReeTag.G2.reeFixedTorus K a :=
    fun s => ReeTag.smallReeTorusElt_mem hK s
  obtain ⟨f, hf⟩ : ∃ f : Kˣ →* ReeTag.G2.reeFixedTorus K a,
      ∀ s : Kˣ, ((f s : ReeTag.G2.reeFixedTorus K a) : ModGL ReeTag.G2.tag K) =
        smallReeTorusElt a K s :=
    ⟨{ toFun := fun s => ⟨smallReeTorusElt a K s, hmem s⟩
       map_one' := Subtype.ext smallReeTorusElt_one
       map_mul' := fun s t => Subtype.ext (smallReeTorusElt_mul s t) }, fun s => rfl⟩
  have hfinj : Function.Injective f := fun s t h =>
    ReeTag.smallReeTorusElt_injective ((hf s).symm.trans ((congrArg Subtype.val h).trans (hf t)))
  have hfsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨s, hs⟩ := ReeTag.exists_smallReeTorusElt_eq hg
    exact ⟨s, Subtype.ext ((hf s).trans hs)⟩
  have hH0cyc : IsCyclic (ReeTag.G2.reeFixedTorus K a) := isCyclic_of_surjective f hfsurj
  have hH0card : Nat.card (ReeTag.G2.reeFixedTorus K a) = Nat.card K - 1 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).toEquiv, Nat.card_units]
  haveI hCcyc : IsCyclic ((ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a)) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hle)).2 hH0cyc
  have hΓcard : Nat.card (ReeTag.G2.reeGamma K a) =
      Nat.card K ^ 3 * (Nat.card K ^ 3 + 1) * (Nat.card K - 1) := by
    rw [CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq hK, ← hK]
  haveI : Finite (ReeTag.G2.reeGamma K a) :=
    Nat.finite_of_card_ne_zero (by rw [hΓcard]; exact mul_ne_zero hm0 hn0)
  have hC : (Nat.card (ReeTag.G2.reeGamma K a)).factorization p ≤
      (Nat.card ((ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a))).factorization
        p := by
    rw [hΓcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hH0card,
      Nat.factorization_mul hm0 hn0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_cube_mul_cube_add_one hp hp5 (by omega) hpq),
      zero_add]
  exact CFSG.SectionRank.sylow_isCyclic_of_cyclic_subgroup
    ((ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a)) hC P

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
