module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralDerivedInvolutions

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open CFSG.Open

theorem isSimpleGroup_of_semisimple_dihedral {Q : Type} [Group Q] [Finite Q] (A : Subgroup Q)
    (hA : CFSG.Open.aschbacherThm5IsSemisimple A)
    (hO : ∀ N : Subgroup A, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hd : AschbacherKnownGroup.HasDihedralSylowTwo A) : IsSimpleGroup A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect A := AschbacherTheorem5.semisimple_perfect A hA
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hd
  obtain ⟨-, -, -, -, hconj⟩ :=
    CFSG.Semidihedral.Principal.dihedral_derived_involutions_conjugate S hn ⟨e.symm⟩
  have hall := hconj hperf.commutator_eq_top
  have hm : 1 < 2 ^ (n - 1) := Nat.one_lt_two_pow (by omega)
  have : Fact (1 < 2 ^ (n - 1)) := ⟨hm⟩
  have hsr : ∀ i : ZMod (2 ^ (n - 1)), orderOf ((e.symm (DihedralGroup.sr i) : A)) = 2 := by
    intro i
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hs12 : (e.symm (DihedralGroup.sr 0) : A) ≠ (e.symm (DihedralGroup.sr 1) : A) := by
    intro h
    have h01 := DihedralGroup.sr.inj (e.symm.injective (Subtype.ext h))
    exact zero_ne_one h01
  have hnoc : ∀ z : A, z ∈ Subgroup.center A → orderOf z = 2 → False := by
    intro z hz hz2
    have h1 : ∀ t : A, orderOf t = 2 → t = z := by
      intro t ht
      obtain ⟨c, hc⟩ := isConj_iff.mp (hall z t hz2 ht)
      rw [← hc, Subgroup.mem_center_iff.mp hz c, mul_inv_cancel_right]
    exact hs12 ((h1 _ (hsr 0)).trans (h1 _ (hsr 1)).symm)
  have hZ : Subgroup.center A = ⊥ := by
    by_contra hne
    have hcard : Nat.card (Subgroup.center A) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hzo : orderOf (z : A) = p := by rw [Subgroup.orderOf_coe, hz]
    by_cases hp2 : p = 2
    · exact hnoc z z.2 (hzo.trans hp2)
    · have hN : (Subgroup.zpowers (z : A)).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2)
      have hodd : Odd (Nat.card (Subgroup.zpowers (z : A))) := by
        rw [Nat.card_zpowers, hzo]
        exact hp.odd_of_ne_two hp2
      have hbot := hO _ hN hodd
      have hz1 : (z : A) = 1 := by
        have h := Subgroup.mem_zpowers (z : A)
        rwa [hbot, Subgroup.mem_bot] at h
      rw [hz1, orderOf_one] at hzo
      exact hp.one_lt.ne hzo
  obtain ⟨k, K, hk, hK, hcomm, hgen⟩ := hA
  have hinvK : ∀ l, ∃ u ∈ K l, orderOf u = 2 := by
    intro l
    have : Group.IsPerfect (K l) := ⟨(hK l).2.1⟩
    have : Nontrivial (K l) := Quasisimple.nontrivial (hK l).2
    have heven := SectionSix.TwoGroups.even_natCard_of_perfect (K l)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    exact ⟨u, u.2, by rw [Subgroup.orderOf_coe, hu]⟩
  have hnorm : ∀ l, A ≤ Subgroup.normalizer (K l : Set Q) := by
    intro l
    rw [← hgen]
    apply iSup_le
    intro j
    by_cases hjl : j = l
    · subst hjl
      exact Subgroup.le_normalizer
    · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm j l hjl x hx y hy).symm
  have hk1 : k = 1 := by
    by_contra hk1
    obtain ⟨i0, hi0⟩ : ∃ i : Fin k, i.val = 0 := ⟨⟨0, hk⟩, rfl⟩
    obtain ⟨i1, hi1⟩ : ∃ i : Fin k, i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
    have hi : i1 ≠ i0 := by
      intro h
      rw [h] at hi1
      omega
    obtain ⟨u, hu, hu2⟩ := hinvK i0
    obtain ⟨v, hv, hv2⟩ := hinvK i1
    have huA : u ∈ A := (hK i0).1 hu
    have hvA : v ∈ A := (hK i1).1 hv
    obtain ⟨c, hc⟩ := isConj_iff.mp (hall ⟨u, huA⟩ ⟨v, hvA⟩
      (by rw [Subgroup.orderOf_mk]; exact hu2) (by rw [Subgroup.orderOf_mk]; exact hv2))
    have hcv : (c : Q) * u * (c : Q)⁻¹ = v := congrArg Subtype.val hc
    have hv0 : v ∈ K i0 := by
      rw [← hcv]
      exact (Subgroup.mem_normalizer_iff.mp (hnorm i0 c.2) u).mp hu
    have hle : (⨆ l, K l) ≤ Subgroup.centralizer ({v} : Set Q) := by
      apply iSup_le
      intro l x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hl : l = i0
      · subst hl
        exact (hcomm i1 l hi v hv x hx).symm
      · exact hcomm l i0 hl x hx v hv0
    have hvc : (⟨v, hvA⟩ : A) ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgA : (g : Q) ∈ ⨆ l, K l := hgen ▸ g.2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle hgA))
    exact hnoc _ hvc (by rw [Subgroup.orderOf_mk]; exact hv2)
  subst hk1
  have hKA : K 0 = A := by
    rw [← hgen, iSup_unique]
    rfl
  subst hKA
  have : IsSimpleGroup (K 0 ⧸ Subgroup.center (K 0)) := (hK 0).2.2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
