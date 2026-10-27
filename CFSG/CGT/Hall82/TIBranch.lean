module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenTight
public import CFSG.CGT.PushingUpLit.SolKMT.Lemmas
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.CGT.Hall82

open CFSG.CGT.Timmesfeld75

theorem inCatalog_of_isTI_of_weaklyClosedIn
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {W : Subgroup G} (hW : CFSG.Open.IsElemAbelian 2 W) (hW1 : W ≠ ⊥)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI W)
    (hwc : CFSG.CGT.Timmesfeld75.WeaklyClosedIn W (Subgroup.normalizer (W : Set G))) :
    CFSG.Assembly.InCatalog G := by
  haveI := hs
  haveI : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW1
  obtain ⟨t, htW, ht1⟩ := Subgroup.exists_ne_one_of_nontrivial W
  have ht2 : t * t = 1 := by simpa [pow_two] using hW.2 t htW
  have hord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using ht2) ht1
  have h2dvd : 2 ∣ Nat.card W := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard W htW
  have hcard_ge2 : 2 ≤ Nat.card W := by
    have h1 : 1 < Nat.card W := (Subgroup.one_lt_card_iff_ne_bot (H := W)).mpr hW1
    omega
  by_cases hcard2 : Nat.card W = 2
  ·
    have hWzp : W = Subgroup.zpowers t := by
      have hle : Subgroup.zpowers t ≤ W := Subgroup.zpowers_le.mpr htW
      have hcard : Nat.card W ≤ Nat.card (Subgroup.zpowers t) := by
        rw [Nat.card_zpowers, hord]
        omega
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
    have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
        g * t * g⁻¹ = t := by
      intro g hcomm
      have hK_cent : conjSubgroup g W ≤ Subgroup.centralizer (W : Set G) := by
        rintro h hh
        change h ∈ W.map (MulAut.conj g).toMonoidHom at hh
        rw [Subgroup.mem_map] at hh
        obtain ⟨w, hw, rfl⟩ := hh
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [hWzp] at hw hx
        have hw' : w = 1 ∨ w = t :=
          (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord).mp hw
        have hx' : x = 1 ∨ x = t :=
          (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord).mp hx
        rcases hw' with rfl | rfl <;> rcases hx' with rfl | rfl <;>
          simp [MulAut.conj_apply, hcomm]
      have hKnorm : conjSubgroup g W ≤ Subgroup.normalizer (W : Set G) :=
        hK_cent.trans (Subgroup.centralizer_le_normalizer (W : Set G))
      have hKW : conjSubgroup g W = W := hwc.2 g hKnorm
      have hmem : g * t * g⁻¹ ∈ W := by
        rw [← hKW]
        change g * t * g⁻¹ ∈ W.map (MulAut.conj g).toMonoidHom
        rw [Subgroup.mem_map]
        exact ⟨t, htW, by simp [MulAut.conj_apply]⟩
      have hgt_ne : g * t * g⁻¹ ≠ 1 := by
        intro h1
        apply ht1
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; simp
      have hmem' : g * t * g⁻¹ = 1 ∨ g * t * g⁻¹ = t := by
        rw [hWzp] at hmem
        exact (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord).mp hmem
      rcases hmem' with h | h
      · exact absurd h hgt_ne
      · exact h
    exact (CFSG.CGT.PushingUpLit.SolKMT.false_of_isolated_involution hs hnonab ht1 ht2
      hiso).elim
  ·
    have h4 : 4 ≤ Nat.card W := by
      obtain ⟨k, hk⟩ := h2dvd
      rcases k with _ | _ | k <;> omega
    exact CFSG.RankThree.PartTwo.Sec19.SolSeven.inCatalog_of_listGroup
      (hNode G hnonab W hW h4 (fun g => hTI g⁻¹) (fun g => hwc.2 g⁻¹))

end CFSG.CGT.Hall82
