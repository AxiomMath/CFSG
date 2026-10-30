module

public import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem l62_quotient_pRank_le_one {L : Type} [Group L] [Finite L] (hZ : IsPGroup 3 ↥(center L))
    (hno : ∀ E : Subgroup L, IsElemAbelian 3 E → Nat.card E = 9 → False) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ center L)) ≤ 1 := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : (1 : ℕ) < 3) (⊤ : Subgroup (L ⧸ center L))
  generalize hk : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ center L)) = k at hcon hcard
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hZ
  have h9 : 9 ≤ Nat.card E := by
    rw [hcard]
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup L, H = E.comap (QuotientGroup.mk' (center L)) := ⟨_, rfl⟩
  have hmem : ∀ x : L, x ∈ H ↔ (QuotientGroup.mk x : L ⧸ center L) ∈ E := fun x => by
    rw [hH]
    exact Subgroup.mem_comap
  have hHcard : Nat.card H = Nat.card (center L) * Nat.card E := by
    rw [hH]
    exact QuotientGroup.card_preimage_mk (center L) (E : Set (L ⧸ center L))
  have hHp : IsPGroup 3 H := by
    refine IsPGroup.of_card (n := m + k) ?_
    rw [hHcard, hm, hcard, ← pow_add]
  obtain ⟨f, hf⟩ : ∃ f : H →* E, ∀ x : H, (f x).1 = QuotientGroup.mk (x : L) :=
    ⟨((QuotientGroup.mk' (center L)).comp H.subtype).codRestrict E (fun x => (hmem x.1).1 x.2),
      fun x => rfl⟩
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : L ⧸ center L)
    have hxH : x ∈ H := (hmem x).2 (by rw [hx]; exact y.2)
    exact ⟨⟨x, hxH⟩, Subtype.ext (by rw [hf]; exact hx)⟩
  have hHnc : ¬ IsCyclic H := by
    intro hc
    have hEc : IsCyclic E := isCyclic_of_surjective f hfsurj
    have hexp : Monoid.exponent E = Nat.card E := IsCyclic.exponent_eq_card
    have hdvd : Monoid.exponent E ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun x : E => Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ x.2))
    have hle : Monoid.exponent E ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨V, hVH, -, hVc, hVp, hVab⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le (G := L) Nat.prime_three (by norm_num)
      hHp (le_refl H) Subgroup.le_normalizer hHnc
  have hVel : IsElemAbelian 3 V :=
    ⟨⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩, fun x hx => hVp x hx⟩
  exact hno V hVel (hVc.trans (by norm_num))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
