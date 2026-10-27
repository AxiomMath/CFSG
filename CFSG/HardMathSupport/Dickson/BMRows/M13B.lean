module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.CentralizerCIsolation
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.IsolatedFive

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open

section Generic

theorem isSolvable_of_card_dvd_312 {X : Type*} [Group X] [Finite X] (h : Nat.card X ∣ 312) :
    Group.IsSolvable X := by
  classical
  by_cases h13 : 13 ∣ Nat.card X
  · haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨P⟩ : Nonempty (Sylow 13 X) := inferInstance
    have hpos : Nat.card X ≠ 0 := Nat.card_pos.ne'
    have hfac : (Nat.card X).factorization 13 = 1 := by
      have h1 : 1 ≤ (Nat.card X).factorization 13 :=
        (Nat.Prime.dvd_iff_one_le_factorization (Fact.out) hpos).1 h13
      by_contra hne
      have h2 : 2 ≤ (Nat.card X).factorization 13 := by omega
      have h3 : 13 ^ 2 ∣ Nat.card X :=
        (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) hpos).2 h2
      have := h3.trans h
      norm_num at this
    have hPcard : Nat.card (P : Subgroup X) = 13 := by
      rw [Sylow.card_eq_multiplicity, hfac, pow_one]
    have hmul := Subgroup.card_mul_index (P : Subgroup X)
    rw [hPcard] at hmul
    have hidx : (P : Subgroup X).index ∣ 24 := by
      have h' : 13 * (P : Subgroup X).index ∣ 13 * 24 := by
        rw [hmul]
        exact h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
    have hn : Nat.card (Sylow 13 X) ∣ 24 := (Sylow.card_dvd_index P).trans hidx
    have hmod : Nat.card (Sylow 13 X) % 13 = 1 := card_sylow_modEq_one 13 X
    have hn1 : Nat.card (Sylow 13 X) = 1 := by
      have hle : Nat.card (Sylow 13 X) ≤ 24 := Nat.le_of_dvd (by norm_num) hn
      have hpos' : 0 < Nat.card (Sylow 13 X) := Nat.card_pos
      generalize Nat.card (Sylow 13 X) = n at hn hmod hle hpos'
      interval_cases n <;> first | rfl | omega | (exfalso; norm_num at hn)
    haveI : Subsingleton (Sylow 13 X) := (Nat.card_eq_one_iff_unique.1 hn1).1
    haveI : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
    haveI : Group.IsSolvable (P : Subgroup X) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)
    haveI : Group.IsSolvable (X ⧸ (P : Subgroup X)) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by
        rw [← Subgroup.index_eq_card]
        exact lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) hidx) (by norm_num))
    exact Group.isSolvable_of_subgroup_quotient (P : Subgroup X)
  · apply CFSG.GroupTheory.groups_order_below_sixty_solvable
    have hcop : Nat.Coprime (Nat.card X) 13 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 13)).2 h13).symm
    have h24 : Nat.card X ∣ 24 :=
      hcop.dvd_of_dvd_mul_right (by rw [show 24 * 13 = 312 by norm_num]; exact h)
    exact lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) h24) (by norm_num)

theorem isSolvable_of_zStar {H : Type} [Group H] [Finite H] {v : H} (hv : v * v = 1) (hv1 : v ≠ 1)
    (hiso : ∀ g : H, (g * v * g⁻¹) * v = v * (g * v * g⁻¹) → g * v * g⁻¹ = v)
    (hC : Group.IsSolvable ↥(Subgroup.centralizer ({v} : Set H))) : Group.IsSolvable H := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar H v hv1 hv hiso
  have hfr := CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_mul_centralizer_of_zStar hv hNodd hNc
  haveI : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  haveI : N.Normal := hNn
  let φ : ↥(Subgroup.centralizer ({v} : Set H)) →* H ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.centralizer ({v} : Set H)).subtype
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨m, hm, k, hk, rfl⟩ := hfr h
    refine ⟨⟨k, hk⟩, ?_⟩
    show QuotientGroup.mk' N k = QuotientGroup.mk' N (m * k)
    refine (QuotientGroup.eq).2 ?_
    simpa [mul_assoc] using hNn.conj_mem m hm k⁻¹
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({v} : Set H)) := hC
  haveI : Group.IsSolvable (H ⧸ N) := Group.isSolvable_of_surjective hφ
  exact Group.isSolvable_of_subgroup_quotient N

theorem noComp_of_conj_pow {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {t s m : G}
    (hto : orderOf t = p) {k : ℕ} (hk : k % p ≠ 0) (h : m * s * m⁻¹ = t ^ k)
    (ht : ∀ I : Subgroup G, ¬ GLAPComponent p (Subgroup.centralizer ({t} : Set G)) I) :
    ∀ I : Subgroup G, ¬ GLAPComponent p (Subgroup.centralizer ({s} : Set G)) I := by
  have hk1 : t ^ k ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hto] at this
    exact hk (Nat.mod_eq_zero_of_dvd this)
  have h1 : ∀ I : Subgroup G, ¬ GLAPComponent p (Subgroup.centralizer ({t ^ k} : Set G)) I := by
    rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime hto hk1]
    exact ht
  have hs : (MulAut.conj m⁻¹) (t ^ k) = s := by
    rw [MulAut.conj_apply, ← h]
    group
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp.out
    (MulAut.conj m) hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv] at hI'
  have hms : (MulAut.conj m) s = t ^ k := by
    rw [MulAut.conj_apply]
    exact h
  rw [hms] at hI'
  exact h1 _ hI'

end Generic

section Monster

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Dickson.Sec6.I1431


theorem isSolvable_centralizer_c13 :
    Group.IsSolvable ↥(Subgroup.centralizer ({gw genD13W1} : Set Gmat)) := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  have hcx : gw genD13W1 * xGmat = xGmat * gw genD13W1 :=
    Subgroup.mem_centralizer_singleton_iff.1 c_mem_cent
  have hxC : xGmat ∈ Subgroup.centralizer ({gw genD13W1} : Set Gmat) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcx.symm
  have hdvd := card_inf_centralizer_dvd (u := xGmat) (h := 1) (f := gw genD13W1)
    (by rw [one_mul, inv_one, mul_one]) hcx orderOf_c13
  refine isSolvable_of_zStar (v := ⟨xGmat, hxC⟩) (Subtype.ext xGmat_mul_self')
    (fun h => xGmat_ne_one' (congrArg Subtype.val h))
    (isolated_of_unique_involution xGmat_mul_self' xGmat_ne_one' hcx.symm hxC
      (fun t ht htx htc => eq_one_or_eq_xGmat_of_involution ht htx htc)) ?_
  apply isSolvable_of_card_dvd_312
  rw [card_centralizer_subtype_eq hxC]
  exact hdvd

theorem noComp_c13 :
    ∀ I : Subgroup Gmat,
      ¬ GLAPComponent 13 (Subgroup.centralizer ({gw genD13W1} : Set Gmat)) I := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  exact fun I hI => CFSG.LocalAnalysis.GLTheoremA.KDSpor.false_of_glaPComponent_of_solvable
    (by norm_num) isSolvable_centralizer_c13 hI

theorem noComp_conj_c13 {s m : Gmat} {k : ℕ} (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = gw genD13W1 ^ k) :
    ∀ I : Subgroup Gmat, ¬ GLAPComponent 13 (Subgroup.centralizer ({s} : Set Gmat)) I := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact noComp_of_conj_pow orderOf_c13 hk h noComp_c13

theorem levelOK_conj_c13 {s m : Gmat} {k : ℕ} (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = gw genD13W1 ^ k) : CFSG.LocalAnalysis.GLTheoremA.KDSpor.LevelOK 13 s :=
  fun I hI => (noComp_conj_c13 hk h I hI).elim

theorem acompOK_conj_c13 {s m : Gmat} {k : ℕ} (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = gw genD13W1 ^ k) : CFSG.LocalAnalysis.GLTheoremA.I1415Rows.ACompOK 13 s :=
  CFSG.LocalAnalysis.GLTheoremA.I1415Rows.acompOK_of_no_comp (noComp_conj_c13 hk h)

theorem compOK_conj_c13 {s m : Gmat} {k : ℕ} (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = gw genD13W1 ^ k) : CFSG.LocalAnalysis.GLTheoremA.I1416Rows.CompOK 13 s :=
  CFSG.LocalAnalysis.GLTheoremA.I1416Rows.compOK_of_no_comp (noComp_conj_c13 hk h)

theorem qcompOK_conj_c13 {s m : Gmat} {k : ℕ} (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = gw genD13W1 ^ k) : CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QCompOK 13 s :=
  CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qcompOK_of_no_comp (noComp_conj_c13 hk h)

end Monster

end CFSG.HardMathSupport.Dickson.BMRows
