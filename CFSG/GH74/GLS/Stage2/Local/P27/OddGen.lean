module

public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

theorem odd_card_of_two_elements_central {Y : Type} [Group Y] [Finite Y] {V : Subgroup Y}
    (hgen : V ≤ Subgroup.closure {y : Y | y ∈ V ∧ Odd (orderOf y)})
    (hc : ∀ u ∈ V, IsPGroup 2 ↥(Subgroup.zpowers u) → ∀ v ∈ V, u * v = v * u) :
    Odd (Nat.card ↥V) := by
  have hcomm : ∀ (s : ↥V) (k : ℕ), orderOf s = 2 ^ k → ∀ h : ↥V, h * s = s * h := by
    intro s k hk h
    have hp : IsPGroup 2 ↥(Subgroup.zpowers (s : Y)) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hk])
    exact Subtype.ext (hc (s : Y) s.2 hp (h : Y) h.2).symm
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥V))
  have hScenter : (S : Subgroup ↥V) ≤
      CFSG.centerIn (G := ↥V) (Subgroup.normalizer (S : Subgroup ↥V)) := by
    intro s hs
    refine ⟨Subgroup.le_normalizer hs, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h _
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 S.isPGroup' ⟨s, hs⟩
    exact hcomm s k ((Subgroup.orderOf_mk s hs).symm.trans hk) h
  obtain ⟨N, hN, hcop, hquot⟩ :=
    CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer
      (G := ↥V) 2 S hScenter
  have hodd : ∀ w : ↥V, Odd (orderOf w) → w ∈ N := by
    intro w hw
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hquot (QuotientGroup.mk w)
    have h1 : orderOf (QuotientGroup.mk w : ↥V ⧸ N) ∣ orderOf w :=
      orderOf_map_dvd (QuotientGroup.mk' N) w
    have h2 : orderOf (QuotientGroup.mk w : ↥V ⧸ N) ∣ 2 ^ k := hk ▸ dvd_rfl
    have h3 : Nat.Coprime (2 ^ k) (orderOf w) := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hw)
    exact (QuotientGroup.eq_one_iff w).1
      (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h3 h2 h1))
  have hVtop : ∀ w : ↥V, w ∈ Subgroup.closure {w : ↥V | Odd (orderOf w)} := by
    intro w
    have hB : Subgroup.closure {y : Y | y ∈ V ∧ Odd (orderOf y)} ≤
        (Subgroup.closure {w : ↥V | Odd (orderOf w)}).map V.subtype := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyV, hy⟩
      refine ⟨⟨y, hyV⟩, Subgroup.subset_closure ?_, rfl⟩
      show Odd (orderOf (⟨y, hyV⟩ : ↥V))
      rwa [Subgroup.orderOf_mk]
    obtain ⟨w', hw', hww'⟩ := hB (hgen w.2)
    exact (Subtype.ext hww' : w' = w) ▸ hw'
  have hNtop : N = ⊤ :=
    top_unique fun w _ => (Subgroup.closure_le N).2 (fun w' hw' => hodd w' hw') (hVtop w)
  have hcard : Nat.card ↥N = Nat.card ↥V := by rw [hNtop, Subgroup.card_top]
  rw [← hcard]
  exact Nat.coprime_two_left.1 hcop

theorem odd_card_of_generated_by_odd {Y : Type} [Group Y] [Finite Y] {V : Subgroup Y} {S : Set Y}
    (hS : ∀ s ∈ S, s ∈ V ∧ Odd (orderOf s)) (hgen : V ≤ Subgroup.closure S)
    (hc : ∀ u ∈ V, IsPGroup 2 ↥(Subgroup.zpowers u) → ∀ v ∈ V, u * v = v * u) :
    Odd (Nat.card ↥V) :=
  odd_card_of_two_elements_central
    (hgen.trans (Subgroup.closure_mono fun s hs => hS s hs)) hc

end CFSG.GH74.GLS.Stage2.Local.P27
