module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutLinDet
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutLinRank
public import CFSG.Adapters.LinearCatalog
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner innAutDerived inner_map_congr
  mem_innAutDerived_congr)
open CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem le_pRank_of_elemAbelian_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {H E : Subgroup G} {k : ℕ} (hEH : E ≤ H) (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEH, hE, hc⟩
  rintro j ⟨F, -, -, hj⟩
  have h1 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
  have h2 : j < p ^ j := Nat.lt_pow_self hp
  rw [hj] at h1
  omega

theorem isElemAbelian_three_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    {E : Subgroup G} (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 (E.map φ.toMonoidHom) := by
  have hcomm : IsMulCommutative ↥(E.map φ.toMonoidHom) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    have hab := congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at hab
    show (a : G') * b = (b : G') * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, hab]
  refine ⟨hcomm, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_pow, hE.2 y hy, map_one]

theorem A2_excluded (q : TauCeti.PrimePower) (h : 3 ∣ q.card - 1) :
    k2Lie 3 (TauCeti.LieTypeIndex.A 2 q) ∨ k3Lie (TauCeti.LieTypeIndex.A 2 q) := by
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hp := q.prime_p
  have hq1 : 1 ≤ q.card := by rw [hq]; exact Nat.one_le_pow _ _ hp.pos
  by_cases h2 : q.p = 2
  · left
    have hev : Even q.exponent := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨k, hk⟩ := hodd
      rw [hq, h2, hk] at h
      have h4 : ∀ j : ℕ, 4 ^ j % 3 = 1 := by
        intro j
        rw [Nat.pow_mod]
        norm_num
      have h2k : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
        rw [pow_succ, pow_mul]
        norm_num
        ring
      rw [h2k] at h
      have := h4 k
      omega
    exact Or.inl ⟨rfl, h2, hev⟩
  · right
    have hodd : Odd q.card := by
      rw [hq]
      rcases hp.eq_two_or_odd' with h' | h'
      · exact absurd h' h2
      · exact h'.pow
    obtain ⟨j, hj⟩ := hodd
    show q.card % 6 = 1
    omega

theorem three_not_dvd_card_of_char_ne_three (q : TauCeti.PrimePower) (h : q.p ≠ 3) :
    ¬ 3 ∣ q.card := by
  intro h3
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [hq] at h3
  have h3p : 3 ∣ q.p := Nat.prime_three.dvd_of_dvd_pow h3
  exact h ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).mp h3p).symm

theorem kd264Y1OutLin_holds : ∀ (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group],
    (∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = TauCeti.LieTypeIndex.A r q) →
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ 3 →
    ∀ a ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, a ^ 3 = 1 →
      a ∈ inner (TauCeti.CFSGIndex.lie d).Group := by
  rintro ⟨e, hv⟩ hfin ⟨r, q, hd⟩ hR hk2 hk3 hpR a ha ha3
  simp only at hd
  subst hd
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  ·
    exfalso
    have hr1 : r = 1 := by omega
    subst hr1
    by_cases hp3 : q.p = 3
    · apply hR
      exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩,
        by simp [CFSG.Yardstones.Md0ec50421ce4.onLie, hp3], ⟨MulEquiv.refl _⟩⟩
    · apply hk2
      exact ⟨rfl, three_not_dvd_card_of_char_ne_three q hp3⟩
  set K : Type := GaloisField q.p q.exponent with hKdef
  have hcardK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  let eS : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩).Group ≃*
      projectiveSL (r + 1) K :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (r + 1) K).symm)
  by_cases hdiv : 3 ∣ Nat.gcd (r + 1) (Nat.card K - 1)
  ·
    exfalso
    have h3r : 3 ∣ r + 1 := dvd_trans hdiv (Nat.gcd_dvd_left _ _)
    have h3N : 3 ∣ Nat.card K - 1 := dvd_trans hdiv (Nat.gcd_dvd_right _ _)
    rcases Nat.lt_or_ge (r + 1) 6 with hsmall | hbig
    ·
      have hr3 : r = 2 := by omega
      subst hr3
      rw [hcardK] at h3N
      rcases A2_excluded q h3N with h | h
      · exact hk2 h
      · exact hk3 h
    ·
      obtain ⟨E, hE, hc⟩ := exists_elemAbelian_card_81 (K := K) (m := r + 1) hbig h3N
      have hEs := isElemAbelian_three_map eS.symm hE
      have hcs : Nat.card (E.map eS.symm.toMonoidHom) = 3 ^ 4 := by
        rw [Subgroup.card_map_of_injective eS.symm.injective, hc]
      have h4 := le_pRank_of_elemAbelian_card (p := 3) (by norm_num) (le_top) hEs hcs
      omega
  ·
    have ha' : MulAut.congr eS a ∈ innAutDerived (projectiveSL (r + 1) K) :=
      (mem_innAutDerived_congr eS).2 ha
    have ha3' : (MulAut.congr eS a) ^ 3 = 1 := by
      rw [← map_pow, ha3, map_one]
    have hin := inner_of_pow_three_of_not_dvd (K := K) (m := r + 1) (by omega) hdiv ha' ha3'
    rw [← inner_map_congr eS] at hin
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hin
    have hba' : b = a := (MulAut.congr eS).injective hba
    rw [hba'] at hb
    exact hb

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
