module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralNonsplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.SeitzReduction CFSG.StandardType
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.LieType.Steinberg.Exceptional

noncomputable abbrev C0 (f : ℕ) : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
  graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)

noncomputable abbrev W0 (f : ℕ) (k : Type) [Field k] [Algebra k (GaloisField 2 (2 * f))] :
    Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
  E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f)))

noncomputable abbrev DLevi (f : ℕ) : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
  TwistedE6Pilot.su6Levi (frobQ 2 f)

namespace SplitCentralizer

variable {f : ℕ} {k : Type} [Field k] [Algebra k (GaloisField 2 (2 * f))]

theorem centralizer_eq_sup_of_mem_thetaTorus (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {x : C0 f} (hx : x ∈ (W0 f k).subgroupOf (C0 f)) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (C0 f)) =
      (W0 f k).subgroupOf (C0 f) ⊔ (DLevi f).subgroupOf (C0 f) := by
  set Y : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    Subgroup.zpowers (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) with hY
  have hxT : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k := by
    rwa [Subgroup.mem_subgroupOf] at hx
  have hYT : Y ≤ W0 f k := Subgroup.zpowers_le.2 hxT
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    have hxY : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ Y := Subgroup.mem_zpowers _
    rw [hbot] at hxY
    exact hx1 (Subtype.ext (Subgroup.mem_bot.1 hxY))
  have hYeq : Y.subgroupOf (C0 f) = Subgroup.zpowers x := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, Subtype.ext hn⟩, fun ⟨n, hn⟩ => ⟨n, congrArg Subtype.val hn⟩⟩
  have hcz : Subgroup.centralizer (Subgroup.zpowers x : Set (C0 f)) =
      Subgroup.centralizer ({x} : Set (C0 f)) := by
    refine le_antisymm (Subgroup.centralizer_le (fun y hy => ?_)) fun g hg => ?_
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subgroup.mem_zpowers x
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.1 hg
      exact (hgx.zpow_right n).symm
  rw [← hcz, ← hYeq]
  exact (TwE6Toral.centralizer_subgroupOf_highSplit hf hk hYT hY1).1

private theorem card_galoisField_two_mul {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]

private theorem frobQ_two_pow {f : ℕ} (c : GaloisField 2 (2 * f)) :
    frobQ 2 f c = c ^ 2 ^ f := frobQ_apply 2 f c

theorem su6Levi_subgroupOf_centralizer_normal (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {x : C0 f} (hx : x ∈ (W0 f k).subgroupOf (C0 f)) (hx1 : x ≠ 1) :
    (((DLevi f).subgroupOf (C0 f)).subgroupOf
      (Subgroup.centralizer ({x} : Set (C0 f)))).Normal := by
  have hC := centralizer_eq_sup_of_mem_thetaTorus hf hk hx hx1
  have hK := card_galoisField_two_mul hf
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_two_pow c
  have hcomm := (TwistedE6Pilot.su6Levi_facts hf hk hK hσ).2.2.2.1
  refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
  rw [hC]
  refine sup_le ?_ ?_
  · refine (?_ : (W0 f k).subgroupOf (C0 f) ≤
        Subgroup.centralizer ((DLevi f).subgroupOf (C0 f) : Set (C0 f))).trans
      (Subgroup.centralizer_le_normalizer _)
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    refine Subtype.ext ?_
    simpa using hcomm (n : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
      (show (n : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ DLevi f from hn)
      (w : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
        (show (w : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k from hw)
  · exact Subgroup.le_normalizer

theorem isQuasisimple_su6Levi_subgroupOf_centralizer (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {x : C0 f} (hx : x ∈ (W0 f k).subgroupOf (C0 f)) (hx1 : x ≠ 1) :
    IsQuasisimple ↥(((DLevi f).subgroupOf (C0 f)).subgroupOf
      (Subgroup.centralizer ({x} : Set (C0 f)))) := by
  have hC := centralizer_eq_sup_of_mem_thetaTorus hf hk hx hx1
  have hJC : (DLevi f).subgroupOf (C0 f) ≤ Subgroup.centralizer ({x} : Set (C0 f)) := by
    rw [hC]; exact le_sup_right
  have hq := (TwE6Toral.su6Levi_subgroupOf_props hf hk).1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hJC).symm hq

theorem card_su6Levi_subgroupOf_centralizer (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {x : C0 f} (hx : x ∈ (W0 f k).subgroupOf (C0 f)) (hx1 : x ≠ 1) :
    Nat.card ↥(((DLevi f).subgroupOf (C0 f)).subgroupOf
      (Subgroup.centralizer ({x} : Set (C0 f)))) = CFSG.Open.ordTwistedA 5 (2 ^ f) := by
  have hC := centralizer_eq_sup_of_mem_thetaTorus hf hk hx hx1
  have hJC : (DLevi f).subgroupOf (C0 f) ≤ Subgroup.centralizer ({x} : Set (C0 f)) := by
    rw [hC]; exact le_sup_right
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv]
  exact (TwE6Toral.su6Levi_subgroupOf_props hf hk).2.2

theorem dvd_card_su6Levi_subgroupOf_centralizer (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {x : C0 f} (hx : x ∈ (W0 f k).subgroupOf (C0 f)) (hx1 : x ≠ 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) :
    p ∣ Nat.card ↥(((DLevi f).subgroupOf (C0 f)).subgroupOf
      (Subgroup.centralizer ({x} : Set (C0 f)))) := by
  rw [card_su6Levi_subgroupOf_centralizer hf hk hx hx1]
  exact TwE6Toral.dvd_ordTwistedA_five hf hp hp2 hpq

theorem commute_thetaTorus_su6Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {a b : C0 f} (ha : a ∈ (W0 f k).subgroupOf (C0 f))
    (hb : b ∈ (DLevi f).subgroupOf (C0 f)) : a * b = b * a := by
  have hK := card_galoisField_two_mul hf
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_two_pow c
  have hcomm := (TwistedE6Pilot.su6Levi_facts hf hk hK hσ).2.2.2.1
  refine Subtype.ext ?_
  simpa using (hcomm (b : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
    (show (b : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ DLevi f from hb)
    (a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
      (show (a : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k from ha)).symm

end SplitCentralizer

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
