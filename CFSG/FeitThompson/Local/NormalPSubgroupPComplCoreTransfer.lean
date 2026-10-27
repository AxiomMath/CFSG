module

public import CFSG.FeitThompson.Local.PComplCoreCentralizerInAmbient
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
public import Mathlib.Data.Rat.Floor

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem le_normalizer_map_pComplCore [Finite G] (p : ℕ) (H : Subgroup G) :
    H ≤ normalizer (((pComplCore p H).map H.subtype : Subgroup G) : Set G) := by
  rw [pComplCore_eq_piCore]
  exact le_normalizer_map_piCore _ _

theorem inf_map_pComplCore_le_map_pComplCore_of_normal_pSubgroup [Finite G] [IsSimpleGroup G]
    (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hp : p.Prime)
    {M D X : Subgroup G} (hM : IsCoatom M) (hDM : D ≤ M) (hDnormal : (D.subgroupOf M).Normal)
    (hD : IsPGroup p D) (hDbot : D ≠ ⊥) (hX : X ≠ ⊤) (hDX : D ≤ X) :
    (pComplCore p M).map M.subtype ⊓ X ≤ (pComplCore p X).map X.subtype := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsSolvable X := hsolv X hX
  have hMnormD : M ≤ normalizer (D : Set G) := le_normalizer_of_normal_subgroupOf hDM
  have hDtop : D < ⊤ := lt_top_iff_ne_top.2 fun h => hM.1 (top_le_iff.1 (h ▸ hDM))
  have hnormlt : normalizer (D : Set G) < ⊤ :=
    normalizer_lt_top_of_isSimpleGroup (bot_lt_iff_ne_bot.2 hDbot) hDtop
  have hNM : normalizer (D : Set G) = M :=
    (hMnormD.lt_or_eq.elim (fun h => absurd (hM.2 _ h) hnormlt.ne) id).symm
  set Q : Subgroup G := (pComplCore p M).map M.subtype with hQ
  set R : Subgroup G := Q ⊓ X with hRdef
  have hQM : Q ≤ M := map_subtype_le _
  have hRX : R ≤ X := inf_le_right
  have hMXR : M ⊓ X ≤ normalizer (R : Set G) :=
    (inf_le_inf (le_normalizer_map_pComplCore p M) le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hpQ : ¬ p ∣ Nat.card Q := by
    rw [hQ, card_map_of_injective M.subtype_injective]
    exact not_dvd_natCard_pComplCore hp M
  have hpR : ¬ p ∣ Nat.card R := fun h => hpQ (h.trans (card_dvd_of_le inf_le_left))
  have hDR : D ⊓ R = ⊥ := by
    obtain ⟨k, hk⟩ := hD.exists_card_eq
    refine (disjoint_of_coprime_natCard ?_).eq_bot
    rw [hk]
    exact (hp.coprime_iff_not_dvd.2 hpR).pow_left k
  have hRC : R ≤ centralizer (D : Set G) :=
    le_centralizer_of_inf_eq_bot (L := M ⊓ X) (le_inf hDM hDX)
      (le_inf (inf_le_left.trans hQM) hRX) (inf_le_left.trans hMnormD) hMXR hDR
  refine fun g hg => mem_map.2 ⟨⟨g, hRX hg⟩, ?_, rfl⟩
  refine le_pComplCore_of_le_normalizer hp (R := D.subgroupOf X)
    (hD.of_equiv (subgroupOfEquivOfLe hDX).symm) ?_ ?_ ?_ (mem_subgroupOf.2 hg)
  ·
    intro x hx
    refine mem_centralizer_iff.2 fun y hy => Subtype.ext ?_
    push_cast
    exact mem_centralizer_iff.1 (hRC (mem_subgroupOf.1 hx)) (y : G)
      (mem_subgroupOf.1 (SetLike.mem_coe.1 hy))
  ·
    rw [← subgroupOf_normalizer_eq hRX]
    intro x hx
    refine mem_subgroupOf.2 (hMXR ⟨?_, x.2⟩)
    have hxc : (x : G) ∈ centralizer (D : Set G) :=
      mem_centralizer_iff.2 fun d hd => congrArg Subtype.val
        (mem_centralizer_iff.1 hx ⟨d, hDX hd⟩ (SetLike.mem_coe.2 (mem_subgroupOf.2 hd)))
    exact hNM ▸ centralizer_le_normalizer _ hxc
  ·
    rwa [Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv]

theorem subgroupOf_map_pComplCore_le_pComplCore_of_normal_pSubgroup [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hp : p.Prime)
    {M D X : Subgroup G} (hM : IsCoatom M) (hDM : D ≤ M) (hDnormal : (D.subgroupOf M).Normal)
    (hD : IsPGroup p D) (hDbot : D ≠ ⊥) (hX : X ≠ ⊤) (hDX : D ≤ X) :
    ((pComplCore p M).map M.subtype).subgroupOf X ≤ pComplCore p X := by
  rw [← map_subtype_le_map_subtype, subgroupOf_map_subtype]
  exact inf_map_pComplCore_le_map_pComplCore_of_normal_pSubgroup hna hodd hsolv hp hM hDM
    hDnormal hD hDbot hX hDX

theorem mem_pComplCore_of_mem_map_pComplCore_of_normal_pSubgroup [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hp : p.Prime)
    {M D X : Subgroup G} (hM : IsCoatom M) (hDM : D ≤ M) (hDnormal : (D.subgroupOf M).Normal)
    (hD : IsPGroup p D) (hDbot : D ≠ ⊥) (hX : X ≠ ⊤) (hDX : D ≤ X) {g : X}
    (hg : (g : G) ∈ (pComplCore p M).map M.subtype) : g ∈ pComplCore p X :=
  subgroupOf_map_pComplCore_le_pComplCore_of_normal_pSubgroup hna hodd hsolv hp hM hDM hDnormal
    hD hDbot hX hDX (mem_subgroupOf.2 hg)

end

end CFSG.FeitThompson
