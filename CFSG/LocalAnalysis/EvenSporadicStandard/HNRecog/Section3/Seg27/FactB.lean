module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Tools
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Six
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem seg27_six_of_A5 {X : Subgroup (Equiv.Perm (Fin 8))}
    (hX : X ≤ alternatingGroup (Fin 8)) (e : ↥X ≃* alternatingGroup (Fin 5)) {o : Fin 8}
    (h6 : (MulAction.orbit X o).ncard = 6) : ∃ p q : Fin 8, Seg27Six X p q := by
  classical
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup ↥X := e.isSimpleGroup
  have hcardX : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcomp : ((MulAction.orbit X o)ᶜ).ncard = 2 := by
    rw [Set.ncard_compl, h6, Nat.card_fin]
  obtain ⟨p, q, hpq, hpq_eq⟩ := Set.ncard_eq_two.1 hcomp
  have hpO : p ∉ MulAction.orbit X o := by
    have : p ∈ (MulAction.orbit X o)ᶜ := by rw [hpq_eq]; simp
    simpa using this
  have hqO : q ∉ MulAction.orbit X o := by
    have : q ∈ (MulAction.orbit X o)ᶜ := by rw [hpq_eq]; simp
    simpa using this
  have hfix_notmem : ∀ r, r ∉ MulAction.orbit X o → ∀ g ∈ X, g r = r := by
    intro r hr g hg
    have hsub : MulAction.orbit X r ⊆ (MulAction.orbit X o)ᶜ := by
      intro y hy
      rw [Set.mem_compl_iff]
      intro hyO
      exact hr (MulAction.mem_orbit_trans (MulAction.mem_orbit_symm.mp hy) hyO)
    have hle : (MulAction.orbit X r).ncard ≤ 2 := by
      have h1 : (MulAction.orbit X r).ncard ≤ ((MulAction.orbit X o)ᶜ).ncard :=
        Set.ncard_le_ncard hsub
      rw [Set.ncard_compl, h6, Nat.card_fin] at h1
      norm_num at h1
      exact h1
    have hpos : 0 < (MulAction.orbit X r).ncard :=
      Nat.pos_of_ne_zero (Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self r))
    have hcases : (MulAction.orbit X r).ncard = 1 ∨ (MulAction.orbit X r).ncard = 2 := by
      omega
    rcases hcases with h1 | h2
    · have hidx1 : (MulAction.stabilizer X r).index = 1 := by
        rw [MulAction.index_stabilizer, h1]
      have htop : MulAction.stabilizer X r = ⊤ := (Subgroup.index_eq_one).1 hidx1
      have hmem : (⟨g, hg⟩ : ↥X) ∈ MulAction.stabilizer X r := by rw [htop]; trivial
      have := MulAction.mem_stabilizer_iff.mp hmem
      simpa [Equiv.Perm.smul_def] using this
    · exfalso
      have hidx : (MulAction.stabilizer X r).index = 2 := by
        rw [MulAction.index_stabilizer, h2]
      haveI : (MulAction.stabilizer X r).Normal := Subgroup.normal_of_index_eq_two hidx
      have hcardH : Nat.card (MulAction.stabilizer X r) = 30 := by
        have hcm := (MulAction.stabilizer X r).card_mul_index
        rw [hidx, hcardX] at hcm
        omega
      rcases hsimple.eq_bot_or_eq_top_of_normal (MulAction.stabilizer X r) with hbot | htop
      · rw [hbot, Subgroup.card_bot] at hcardH
        omega
      · rw [htop, Subgroup.card_top, hcardX] at hcardH
        omega
  have hfixp : ∀ g ∈ X, g p = p := hfix_notmem p hpO
  have hfixq : ∀ g ∈ X, g q = q := hfix_notmem q hqO
  have hcard_stab : ∀ r, r ≠ p → r ≠ q →
      Nat.card (X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) r :
        Subgroup (Equiv.Perm (Fin 8))) = 10 := by
    intro r hrp hrq
    have hrO : r ∈ MulAction.orbit X o := by
      by_contra hcon
      have hmem : r ∈ (MulAction.orbit X o)ᶜ := by simpa using hcon
      rw [hpq_eq] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      exact hmem.elim hrp hrq
    have horb : MulAction.orbit X r = MulAction.orbit X o := by
      rw [MulAction.orbit_eq_iff]; exact hrO
    have hidx : (MulAction.stabilizer X r).index = 6 := by
      rw [MulAction.index_stabilizer, horb, h6]
    have hcardXr : Nat.card (MulAction.stabilizer X r) = 10 := by
      have hcm := (MulAction.stabilizer X r).card_mul_index
      rw [hidx, hcardX] at hcm
      omega
    have hmap : (MulAction.stabilizer X r).map X.subtype
        = X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) r := by
      rw [← MulAction.stabilizer_subgroupOf X r, ← Subgroup.comap_subtype,
        Subgroup.map_comap_eq, Subgroup.range_subtype]
    rw [← hmap, Subgroup.card_subtype]
    exact hcardXr
  have hinv : ∀ r s : Fin 8, ∃ t ∈ X, orderOf t = 2 ∧ t r = r ∧ t s = s := by
    intro r s
    let Xr : Subgroup (Equiv.Perm (Fin 8)) :=
      X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) r
    let Xs : Subgroup (Equiv.Perm (Fin 8)) :=
      X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) s
    let T : Subgroup (Equiv.Perm (Fin 8)) := Xr ⊓ Xs
    have hXr_le : Xr ≤ X := inf_le_left
    have hXs_le : Xs ≤ X := inf_le_left
    have hT_le_Xr : T ≤ Xr := inf_le_left
    have hT_le_Xs : T ≤ Xs := inf_le_right
    have hTX : T ≤ X := hT_le_Xr.trans hXr_le
    have hstabr : ∀ {g : Equiv.Perm (Fin 8)}, g ∈ Xr → g r = r := by
      intro g hg
      have h2 := (Subgroup.mem_inf.mp
        (show g ∈ X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) r from hg)).2
      simpa [Equiv.Perm.smul_def] using (MulAction.mem_stabilizer_iff.mp h2)
    have hstabs : ∀ {g : Equiv.Perm (Fin 8)}, g ∈ Xs → g s = s := by
      intro g hg
      have h2 := (Subgroup.mem_inf.mp
        (show g ∈ X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) s from hg)).2
      simpa [Equiv.Perm.smul_def] using (MulAction.mem_stabilizer_iff.mp h2)
    have hXa_eq : ∀ a : Fin 8, (a = p ∨ a = q) →
        X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) a = X := by
      intro a ha
      refine inf_eq_left.2 ?_
      intro g hg
      rw [MulAction.mem_stabilizer_iff]
      rcases ha with rfl | rfl
      · simpa [Equiv.Perm.smul_def] using hfixp g hg
      · simpa [Equiv.Perm.smul_def] using hfixq g hg
    have hcard_bad : ∀ a : Fin 8, ¬(a = p ∨ a = q) →
        Nat.card (X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) a :
          Subgroup (Equiv.Perm (Fin 8))) = 10 := by
      intro a ha
      push Not at ha
      exact hcard_stab a ha.1 ha.2
    have h2dvdT : 2 ∣ Nat.card T := by
      by_cases hr : r = p ∨ r = q
      · by_cases hs : s = p ∨ s = q
        · have hT_eq : T = X := by
            change Xr ⊓ Xs = X
            rw [show Xr = X from hXa_eq r hr, show Xs = X from hXa_eq s hs, inf_idem]
          rw [hT_eq, hcardX]
          norm_num
        · have hXs10 : Nat.card Xs = 10 := hcard_bad s hs
          have hT_eq : T = Xs := by
            change Xr ⊓ Xs = Xs
            rw [show Xr = X from hXa_eq r hr, inf_eq_right.mpr hXs_le]
          rw [hT_eq, hXs10]
          norm_num
      · by_cases hs : s = p ∨ s = q
        · have hXr10 : Nat.card Xr = 10 := hcard_bad r hr
          have hT_eq : T = Xr := by
            change Xr ⊓ Xs = Xr
            rw [show Xs = X from hXa_eq s hs, inf_eq_left.mpr hXr_le]
          rw [hT_eq, hXr10]
          norm_num
        · have hXr10 : Nat.card Xr = 10 := hcard_bad r hr
          have hXs10 : Nat.card Xs = 10 := hcard_bad s hs
          by_cases hrs : r = s
          · have hXs_eq_Xr : Xs = Xr := by
              change X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) s
                = X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) r
              rw [hrs]
            have hT_eq : T = Xr := by
              change Xr ⊓ Xs = Xr
              rw [hXs_eq_Xr, inf_idem]
            rw [hT_eq, hXr10]
            norm_num
          · have hprod := seg27_card_mul_card_le (A := Xr) (B := Xs) (C := X)
              hXr_le hXs_le
            change Nat.card Xr * Nat.card Xs ≤ Nat.card X * Nat.card T at hprod
            rw [hXr10, hXs10, hcardX] at hprod
            have hge2 : 2 ≤ Nat.card T := by omega
            have hTdvd : Nat.card T ∣ 10 := by
              have h := Subgroup.card_dvd_of_le hT_le_Xr
              rwa [hXr10] at h
            have h5not : ¬ 5 ∣ Nat.card T := by
              intro h5
              obtain ⟨g, hgT, hg5⟩ := seg27_exists_orderOf_prime T Nat.prime_five h5
              have hgX : g ∈ X := hTX hgT
              have hgr : g r = r := hstabr (hT_le_Xr hgT)
              have hgs : g s = s := hstabs (hT_le_Xs hgT)
              push Not at hr hs
              exact seg27_not_fix_four_of_orderOf_five hg5 hpq hr.1.symm hs.1.symm hr.2.symm
                hs.2.symm hrs (hfixp g hgX) (hfixq g hgX) hgr hgs
            by_contra h2
            have hcop : Nat.Coprime 2 (Nat.card T) :=
              Nat.prime_two.coprime_iff_not_dvd.mpr h2
            have hd5 : Nat.card T ∣ 5 := by
              have h : Nat.card T ∣ 5 * 2 := by
                rw [show 5 * 2 = 10 by norm_num]
                exact hTdvd
              exact (hcop.symm).dvd_of_dvd_mul_right h
            have heq5 : Nat.card T = 5 := (Nat.dvd_prime_two_le Nat.prime_five hge2).1 hd5
            exact h5not (heq5.symm ▸ dvd_rfl)
    obtain ⟨t, htT, ht2⟩ := seg27_exists_orderOf_two T h2dvdT
    exact ⟨t, hTX htT, ht2, hstabr (hT_le_Xr htT), hstabs (hT_le_Xs htT)⟩
  exact ⟨p, q, ⟨hX, hcardX, hpq, hfixp, hfixq, hcard_stab, hinv⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
