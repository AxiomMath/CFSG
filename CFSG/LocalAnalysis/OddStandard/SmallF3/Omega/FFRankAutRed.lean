module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutAbRed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem ffOutFFRankAutRed_bdd [Finite G] (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  have h1 : 2 ^ k ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
  exact (Nat.lt_two_pow_self.le).trans h1

private theorem ffOutFFRankAutRed_le_pRank [Finite G] {H E : Subgroup G} (hle : E ≤ H)
    (hel : CFSG.Open.IsElemAbelian 2 E) {k : ℕ} (hk : Nat.card E = 2 ^ k) :
    k ≤ CFSG.Open.pRank 2 H :=
  le_csSup (ffOutFFRankAutRed_bdd H) ⟨E, hle, hel, hk⟩

theorem ffRA_rank_of_aut [Finite G] {Y E : Subgroup G} (hY : IsQuasisimple Y)
    (hs : IsSimpleGroup (↥Y ⧸ oddCore ↥Y)) (hEN : E ≤ normalizer (Y : Set G))
    (hE : CFSG.Open.IsElemAbelian 2 E) {b : ℕ}
    (hbound : ∀ X : Subgroup (MulAut (↥Y ⧸ oddCore ↥Y)), (∀ x ∈ X, x * x = 1) →
      Nat.card X ≤ 2 ^ b) :
    CFSG.Open.pRank 2 E ≤ CFSG.Open.pRank 2 (E ⊓ centralizer (Y : Set G)) + b := by
  haveI : (oddCore ↥Y).Characteristic := oddCore_characteristic_of ↥Y
  obtain ⟨E', hE'E, hE'el, hE'card⟩ : ∃ E' : Subgroup G, E' ≤ E ∧ CFSG.Open.IsElemAbelian 2 E' ∧
      Nat.card E' = 2 ^ CFSG.Open.pRank 2 E := by
    have hne : {k | ∃ E' : Subgroup G, E' ≤ E ∧ CFSG.Open.IsElemAbelian 2 E' ∧
        Nat.card E' = 2 ^ k}.Nonempty :=
      ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩,
        fun x hx => by rw [(Subgroup.mem_bot.mp hx), one_pow]⟩, by simp⟩
    exact Nat.sSup_mem hne (ffOutFFRankAutRed_bdd E)
  have hE'N : E' ≤ normalizer (Y : Set G) := hE'E.trans hEN
  let c : ↥E' →* MulAut ↥Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hE'N)
  let ρ : ↥E' →* MulAut (↥Y ⧸ oddCore ↥Y) := (autQuot ↥Y (oddCore ↥Y)).comp c
  have hsq : ∀ y : ↥E', y * y = 1 := fun y => Subtype.ext (by simpa [pow_two] using hE'el.2 y.1 y.2)
  have hker : ∀ y : ↥E', y ∈ ρ.ker → (y : G) ∈ centralizer (Y : Set G) := by
    intro y hy
    have h1 : c y = 1 := eq_one_of_autQuot_eq_one hY hs hy
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h2 := congrArg (fun a : MulAut ↥Y => ((a ⟨g, hg⟩ : ↥Y) : G)) h1
    simp only [c, MonoidHom.comp_apply, MulAut.one_apply] at h2
    have h3 : (y : G) * g * (y : G)⁻¹ = g := h2
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  set M : Subgroup G := E' ⊓ centralizer (Y : Set G) with hM
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE'el.1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hMel : CFSG.Open.IsElemAbelian 2 M :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2.1 b.1 b.2.1)⟩⟩, fun x hx => hE'el.2 x hx.1⟩
  obtain ⟨s, hs2⟩ := (IsPGroup.iff_card (p := 2)).1
    (show IsPGroup 2 M from fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hMel.2 x.1 x.2)⟩)
  have hMle : M ≤ E ⊓ centralizer (Y : Set G) := inf_le_inf_right _ hE'E
  have hsle : s ≤ CFSG.Open.pRank 2 (E ⊓ centralizer (Y : Set G)) :=
    ffOutFFRankAutRed_le_pRank hMle hMel hs2
  have hkerM : Nat.card ρ.ker ≤ Nat.card M := by
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1.1, y.1.2, hker y.1 y.2⟩) ?_
    intro y z h
    have h' : y.1.1 = z.1.1 := congrArg (fun m : ↥M => (m : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hrange : Nat.card ρ.range ≤ 2 ^ b := by
    refine hbound ρ.range ?_
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, hsq y, map_one]
  have hmul := Subgroup.card_ker_mul_card_range ρ
  have hpow : 2 ^ CFSG.Open.pRank 2 E ≤ 2 ^ (s + b) := by
    rw [← hE'card, ← hmul, pow_add, ← hs2]
    exact Nat.mul_le_mul hkerM hrange
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow
  omega

theorem ffRA_card_autIn_le [Finite G] {Y U : Subgroup G} (hY : IsQuasisimple Y)
    (hs : IsSimpleGroup (↥Y ⧸ oddCore ↥Y)) (hUN : U ≤ normalizer (Y : Set G))
    (hU : IsPGroup 2 U) (hab : ∀ a ∈ autIn U Y, ∀ c ∈ autIn U Y, a * c = c * a) {n : ℕ}
    (hbound : ∀ X : Subgroup (MulAut (↥Y ⧸ oddCore ↥Y)), IsPGroup 2 X → IsMulCommutative X →
      Nat.card X ≤ n) :
    Nat.card (autIn U Y) ≤ n := by
  haveI : (oddCore ↥Y).Characteristic := oddCore_characteristic_of ↥Y
  have hΦ : Function.Injective (autQuot ↥Y (oddCore ↥Y)) := by
    rw [injective_iff_map_eq_one]
    intro α hα
    exact eq_one_of_autQuot_eq_one hY hs hα
  have h2 : IsPGroup 2 (autIn U Y) :=
    (hU.comap_subtype (K := normalizer (Y : Set G))).map Y.normalizerMonoidHom
  have hc : IsMulCommutative ((autIn U Y).map (autQuot ↥Y (oddCore ↥Y))) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    change (a : MulAut (↥Y ⧸ oddCore ↥Y)) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, hab a' ha' b' hb']
  have h := hbound _ (h2.map _) hc
  rwa [Subgroup.card_map_of_injective hΦ] at h

end CFSG.OddStandard.SmallF3.Omega
