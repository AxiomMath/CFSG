module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthB
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinC
import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePlanes
import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Plane
import CFSG.GroupTheory.QuasisimpleCenterDivisibility

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Polynomial Module Matrix CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry isometryCentralizer supportedBlock
  specialBlock reciprocalPolynomial)

section Mixed

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] {Q : QuadraticForm K (Fin n → K)}
  {E0 : Subgroup (SpecialLinearGroup (Fin n) K)} [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

omit [Fintype E0] in
private theorem le_orthDerived_of_commutator_eq_top {P : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K))}
    (hP : commutator ↥P = ⊤) (hPO : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    P ≤ orthDerived Q := by
  have hPP := CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hP
  intro g hg
  rw [← hPP] at hg
  exact Subgroup.commutator_mono hPO hPO hg

omit [Fintype E0] in
private theorem mul_comm_of_commute {g g' : (Fin n → K) ≃ₗ[K] (Fin n → K)}
    (hc : Commute g.toLinearMap g'.toLinearMap) : g' * g = g * g' :=
  LinearEquiv.ext fun v => (LinearMap.congr_fun hc.eq v).symm

private theorem actEquiv_symm_toLinearMap (e : ↥E0) :
    (actEquiv e).symm.toLinearMap = act ρ₀ e⁻¹ := by
  refine LinearMap.ext fun v => (actEquiv e).injective ?_
  change actEquiv e ((actEquiv e).symm v) = actEquiv e (actEquiv e⁻¹ v)
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.mul_apply, ← actEquiv_mul, mul_inv_cancel,
    actEquiv_one]
  rfl

variable (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
include hP hpK

theorem mem_zpowers_of_smul {L L' : Subgroup ↥E0} (hL : L ∈ lines p E0)
    (hL' : L' ∈ lines p E0) (hLL' : L ≠ L') {b' c : ↥E0} (hb' : b' ∈ L) (hcL' : c ∈ L')
    (hcL : c ∉ L) {h : K[X]} [Fact (Irreducible h)] {u y : Fin n → K}
    (hu : u ∈ primaryComponent (act ρ₀ (b' * c)) h)
    (huL : u ∈ LinearMap.range (projLine ρ₀ L)) (hu0 : u ≠ 0)
    (hy : y ∈ primaryComponent (act ρ₀ (b' * c)) h)
    (hyL' : y ∈ LinearMap.range (projLine ρ₀ L')) (hy0 : y ≠ 0) {â : ↥E0} {s : AdjoinRoot h}
    (hs : ∀ w : primaryComponent (act ρ₀ (b' * c)) h,
      act ρ₀ â (w : Fin n → K) = ((s • w : primaryComponent (act ρ₀ (b' * c)) h) : Fin n → K)) :
    â ∈ Subgroup.zpowers (b' * c) := by
  obtain ⟨l, hl, t, rfl⟩ := exists_mem_mul_pow hP hL hcL â
  have hpowa : (b' * c) ^ t = b' ^ t * c ^ t :=
    Commute.mul_pow ((IsMulCommutative.is_comm (M := ↥E0)).comm b' c) t
  have hu1 : act ρ₀ (l * c ^ t) u = act ρ₀ ((b' * c) ^ t) u := by
    have hcu := stable_range_projLine E0 (c ^ t) L u huL
    rw [hpowa, act_mul, act_mul, Module.End.mul_apply, Module.End.mul_apply,
      fix_range_projLine E0 hl _ hcu, fix_range_projLine E0 (L.pow_mem hb' t) _ hcu]
  have hs1 : s = AdjoinRoot.mk h (X ^ t) := by
    by_contra hne
    have h1 : (s - AdjoinRoot.mk h (X ^ t)) •
        (⟨u, hu⟩ : primaryComponent (act ρ₀ (b' * c)) h) = 0 := by
      rw [sub_smul, sub_eq_zero]
      apply Subtype.ext
      rw [← hs ⟨u, hu⟩, coe_mk_smul_primaryComponent, aeval_X_pow, ← act_pow]
      exact hu1
    have h2 := congrArg ((s - AdjoinRoot.mk h (X ^ t))⁻¹ • ·) h1
    simp only [smul_zero, inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h2
    exact hu0 (congrArg Subtype.val h2)
  have hy1 : act ρ₀ l y = act ρ₀ (b' ^ t) y := by
    have h1 := hs ⟨y, hy⟩
    have h2 : act ρ₀ (l * c ^ t) y = act ρ₀ l y := by
      rw [act_mul, Module.End.mul_apply, fix_range_projLine E0 (L'.pow_mem hcL' t) y hyL']
    have h3 : ((AdjoinRoot.mk h (X ^ t) • (⟨y, hy⟩ : primaryComponent (act ρ₀ (b' * c)) h) :
        primaryComponent (act ρ₀ (b' * c)) h) : Fin n → K) = act ρ₀ (b' ^ t) y := by
      rw [coe_mk_smul_primaryComponent, aeval_X_pow, ← act_pow, hpowa, act_mul,
        Module.End.mul_apply, fix_range_projLine E0 (L'.pow_mem hcL' t) y hyL']
    rw [← h2, ← h3, ← hs1]
    exact h1
  have hfix : act ρ₀ ((b' ^ t)⁻¹ * l) y = y := by
    rw [act_mul, Module.End.mul_apply, hy1, ← Module.End.mul_apply, ← act_mul, inv_mul_cancel,
      act_one, Module.End.one_apply]
  have hmemL' : (b' ^ t)⁻¹ * l ∈ L' := by
    by_contra hn
    exact hy0 (eq_zero_of_mem_range_projLine hP hpK hL' hn hyL' hfix)
  have h1 : (b' ^ t)⁻¹ * l = 1 := by
    have hmem : (b' ^ t)⁻¹ * l ∈ L ⊓ L' := ⟨L.mul_mem (L.inv_mem (L.pow_mem hb' t)) hl, hmemL'⟩
    rwa [hP.inf_eq_bot (mem_lines.mp hL) (mem_lines.mp hL') hLL', Subgroup.mem_bot] at hmem
  have hl' : l = b' ^ t := (inv_mul_eq_one.mp h1).symm
  rw [hl', ← hpowa]
  exact (Subgroup.zpowers (b' * c)).pow_mem (Subgroup.mem_zpowers _) t

theorem exists_mixed_element [Finite K] (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) (hp2 : p ≠ 2)
    {L L' : Subgroup ↥E0} (hL : L ∈ lines p E0) (hL' : L' ∈ lines p E0) (hL'L : L' ≠ L)
    (hL'0 : projLine ρ₀ L' ≠ 0) {c : ↥E0} (hcL' : c ∈ L') (hcL : c ∉ L) {h : K[X]}
    (hh : h ∈ primaryFactors (auxEnd E0 c 1 L)) (hX : h ≠ X - C 1)
    (hself : reciprocalPolynomial h = h) (â : ↥E0) :
    ∃ b' ∈ L, b' * c ∉ Subgroup.zpowers â ∧ ∃ y ∈ primaryComponent (act ρ₀ (b' * c)) h,
      y ∈ LinearMap.range (projLine ρ₀ L') ∧ y ≠ 0 := by
  have hp := hP.prime
  obtain ⟨b, hbL, hb1⟩ := RankThree.PartOne.KCLinPlane.exists_ne_one_mem E0 hL hP
  obtain ⟨h₂, hh₂, hX₂, hne₂⟩ := exists_factor E0 hP hpK hL' hL hL'L hL'0 hbL hb1
  obtain ⟨v₂, hv₂⟩ : ∃ v, (projLine ρ₀ L' * primaryProjection (act ρ₀ b) h₂) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne₂ (LinearMap.ext hcon)
  have hbp : act ρ₀ b ^ p = 1 := by rw [← act_pow, hP.pow b, act_one]
  have hsqb := KCLinComm.squarefree_minpoly_of_pow_eq_one hpK hbp
  set y₂ := projLine ρ₀ L' (primaryProjection (act ρ₀ b) h₂ v₂) with hy₂
  have hy₂0 : y₂ ≠ 0 := hv₂
  have hy₂M : y₂ ∈ LinearMap.range (projLine ρ₀ L') := LinearMap.mem_range_self _ _
  have hy₂h : y₂ ∈ primaryComponent (act ρ₀ b) h₂ :=
    apply_mem_primaryComponent (commute_act_projLine E0 b L').symm
      (primaryProjection_mem hsqb hh₂ v₂)
  have hxp := auxEnd_pow_eq_one hP hpK hL c 1
  have hd₁ : h ∣ X ^ p - 1 :=
    (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd K _ (by simp [hxp]))
  have hd₂ : h₂ ∣ X ^ p - 1 :=
    (mem_primaryFactors.mp hh₂).2.2.trans (minpoly.dvd K _ (by simp [hbp]))
  obtain ⟨j, hj⟩ := exists_dvd_comp_pow hp (irreducible_of_mem_primaryFactors hh₂)
    (monic_of_mem_primaryFactors hh₂) hd₁ hd₂ hX₂
    (irreducible_of_mem_primaryFactors hh).natDegree_pos
  have hyA : y₂ ∈ primaryComponent (act ρ₀ (b ^ j * c)) h :=
    mem_primaryComponent_mul_pow hcL' hj hy₂M hy₂h
  have hyB : y₂ ∈ primaryComponent (act ρ₀ (b⁻¹ ^ j * c)) h := by
    have hx := oddOrderIsometry_auxEquiv hP hpK hEQ hreg hL c 1
    have h0 : h.coeff 0 ≠ 0 := hx.coeff_zero_ne hh
    have h1 : y₂ ∈ primaryComponent (actEquiv (b ^ j * c)).toLinearMap
        (reciprocalPolynomial h) := by
      rw [hself]
      exact hyA
    rw [KCOrthogonal.mem_primaryComponent_reciprocalPolynomial h0,
      actEquiv_symm_toLinearMap] at h1
    have hagree : ∀ w ∈ LinearMap.range (projLine ρ₀ L'),
        act ρ₀ (b⁻¹ ^ j * c) w = act ρ₀ (b ^ j * c)⁻¹ w := by
      intro w hw
      rw [act_mul, Module.End.mul_apply, fix_range_projLine E0 hcL' w hw, _root_.mul_inv_rev,
        act_mul, Module.End.mul_apply, fix_range_projLine E0 (L'.inv_mem hcL') _
          (stable_range_projLine E0 _ L' w hw), inv_pow]
    rw [mem_primaryComponent,
      aeval_apply_eq_of_agree (stable_range_projLine E0 _ L') hagree h hy₂M]
    exact h1
  by_cases hA : b ^ j * c ∈ Subgroup.zpowers â
  · by_cases hB : b⁻¹ ^ j * c ∈ Subgroup.zpowers â
    · exfalso
      have hb2 : b ^ j * b ^ j ∈ Subgroup.zpowers â := by
        have h3 := (Subgroup.zpowers â).mul_mem hA ((Subgroup.zpowers â).inv_mem hB)
        have h4 : b ^ j * c * (b⁻¹ ^ j * c)⁻¹ = b ^ j * b ^ j := by
          rw [_root_.mul_inv_rev, inv_pow, inv_inv]
          group
        rwa [h4] at h3
      by_cases hbj : b ^ j * b ^ j = 1
      ·
        have hbj1 : b ^ j = 1 := by
          have h2 : (b ^ j) ^ 2 = 1 := by rw [sq]; exact hbj
          have hord : orderOf (b ^ j) ∣ Nat.gcd 2 p :=
            Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one (hP.pow _))
          rw [(Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2), Nat.dvd_one,
            orderOf_eq_one_iff] at hord
          exact hord
        rw [hbj1, one_mul] at hyA
        have hcy : act ρ₀ c y₂ = y₂ := fix_range_projLine E0 hcL' y₂ hy₂M
        have hy₂1 : y₂ ∈ primaryComponent (act ρ₀ c) (X - C 1) := by
          rw [mem_primaryComponent]
          simp [hcy]
        have hh1 := mem_primaryFactors_of_ne_zero (irreducible_of_mem_primaryFactors hh)
          (monic_of_mem_primaryFactors hh) hy₂0 hyA
        have hX1 := mem_primaryFactors_of_ne_zero (irreducible_X_sub_C 1) (monic_X_sub_C 1)
          hy₂0 hy₂1
        exact hy₂0 (eq_zero_of_mem_primaryComponent_ne hh1 hX1 hX hyA hy₂1)
      ·
        have hbjL : b ^ j * b ^ j ∈ L := L.mul_mem (L.pow_mem hbL j) (L.pow_mem hbL j)
        have hLeq : L = Subgroup.zpowers (b ^ j * b ^ j) := eq_zpowers_of_mem hP hL hbjL hbj
        have hle : L ≤ Subgroup.zpowers â := hLeq ▸ Subgroup.zpowers_le.mpr hb2
        have hâ1 : â ≠ 1 := by
          rintro rfl
          rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hb2
          exact hbj hb2
        have hLâ : L = Subgroup.zpowers â := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by
          rw [mem_lines.mp hL, mem_lines.mp (hP.zpowers_mem_lines hâ1)]))
        apply hcL
        have h3 := (Subgroup.zpowers â).mul_mem ((Subgroup.zpowers â).inv_mem
          (hle (L.pow_mem hbL j))) hA
        rw [inv_mul_cancel_left] at h3
        rw [hLâ]
        exact h3
    · exact ⟨b⁻¹ ^ j, L.pow_mem (L.inv_mem hbL) j, hB, y₂, hyB, hy₂M, hy₂0⟩
  · exact ⟨b ^ j, L.pow_mem hbL j, hA, y₂, hyA, hy₂M, hy₂0⟩

theorem orthBlockConcl_of_piece [Finite K] [CharP K 2]
    (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {â : ↥E0} (hâ1 : â ≠ 1) {L L' : Subgroup ↥E0}
    (hL : L ∈ lines p E0) (hL' : L' ∈ lines p E0) (hL'L : L' ≠ L) (hL'0 : projLine ρ₀ L' ≠ 0)
    {c : ↥E0} (hcL' : c ∈ L') (hc1 : c ≠ 1) {h : K[X]}
    (hh : h ∈ primaryFactors (auxEnd E0 c 1 L)) (hX : h ≠ X - C 1)
    (hns : ¬ Group.IsSolvable ↥(supportedBlock Q (auxEquiv hP hpK hL c 1) h)) :
    OrthBlockConcl Q E0 p â := by
  have hp := hP.prime
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have : Finite ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
    Finite.of_injective (fun g : (Fin n → K) ≃ₗ[K] (Fin n → K) => (g : (Fin n → K) → Fin n → K))
      DFunLike.coe_injective
  have hcL : c ∉ L := fun hcL => hc1 (by
    have hmem : c ∈ L' ⊓ L := ⟨hcL', hcL⟩
    rwa [hP.inf_eq_bot (mem_lines.mp hL') (mem_lines.mp hL) hL'L, Subgroup.mem_bot] at hmem)
  have hx := oddOrderIsometry_auxEquiv hP hpK hEQ hreg hL c 1
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hX1 : h ≠ X - 1 := by rwa [C_1] at hX
  have hself : reciprocalPolynomial h = h := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hX1
  have hgood : ∀ {z : (Fin n → K) ≃ₗ[K] (Fin n → K)}, OddOrderIsometry Q p z →
      h ∈ primaryFactors z.toLinearMap → ¬ Group.IsSolvable ↥(supportedBlock Q z h) →
      CFSG.IsQuasisimple ↥(specialBlock Q z h) ∧ 2 ≤ primaryMultiplicity z.toLinearMap h := by
    intro z hz hhz hnz
    have hm : ¬ (primaryMultiplicity z.toLinearMap h ≤ 1 ∨ (Nat.card (AdjoinRoot h) = 4 ∧
        primaryMultiplicity z.toLinearMap h ≤ 3)) := fun hbad =>
      hnz (isSolvable_supportedBlock_of_bad hz hp2' hhz hX1 hself.symm hbad)
    push Not at hm
    exact ⟨isQuasisimple_specialBlock_of_good hz hp2' hhz hX1 hself.symm (by omega)
      fun h4 => by have := hm.2 h4; omega, by omega⟩
  obtain ⟨hPq, hm2⟩ := hgood hx hh hns
  set P := specialBlock Q (auxEquiv hP hpK hL c 1) h with hPdef
  haveI : Group.IsPerfect ↥P := hPq.1
  have hPdvd : p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.dvd_card_quotient_center_of_quasisimple hPq hp
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_dvd_card_orthSpecialBlock hx hp hp2 hh
        hX1 hm2)
  have hPO : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    (Subgroup.mem_inf.mp (KCOrthogonal.specialBlock_le_isometryCentralizer h hg)).1
  have hPΩ := le_orthDerived_of_commutator_eq_top hPq.1.commutator_eq_top hPO
  have hPc : ∀ g ∈ P, ∀ e : ↥E0, Commute g.toLinearMap (act ρ₀ e) := fun g hg e =>
    commute_act_of_mem_supportedBlock hP hpK hL hcL hX hself
      (KCOrthogonal.specialBlock_le_supportedBlock h hg) e
  have hPn : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ e : ↥E0, Commute g.toLinearMap (act ρ₀ e)) → ∀ y ∈ P, g * y * g⁻¹ ∈ P :=
    fun g hgO hgc y hy => KCOrthogonal.conj_mem_specialBlock
      (mem_isometryCentralizer_auxEquiv hP hpK hgO hgc hL c 1) hy
  obtain ⟨b', hb'L, hb'â, y, hyh, hyL', hy0⟩ :=
    exists_mixed_element hP hpK hEQ hreg hp2 hL hL' hL'L hL'0 hcL' hcL hh hX hself â
  have hz := oddOrderIsometry_actEquiv hP hpK hEQ hreg (b' * c)
  have hle : primaryComponent (auxEquiv hP hpK hL c 1).toLinearMap h ≤
      primaryComponent (actEquiv (b' * c)).toLinearMap h := by
    have h1 := primaryComponent_auxEnd_le hP hpK hL hb'L hcL 1 hh hX
    rw [pow_one] at h1
    exact h1
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot (squarefree_minpoly_auxEnd hP hpK hL c 1) hh)
  have huL := mem_range_projLine_of_mem_primaryComponent hP hpK hL hcL hh hX hu
  have hhz : h ∈ primaryFactors (actEquiv (b' * c)).toLinearMap :=
    mem_primaryFactors_of_ne_zero (irreducible_of_mem_primaryFactors hh)
      (monic_of_mem_primaryFactors hh) hu0 (hle hu)
  have hxz : Commute (auxEquiv hP hpK hL c 1).toLinearMap (actEquiv (b' * c)).toLinearMap :=
    (commute_act_auxEnd E0 (b' * c) c 1 L).symm
  have hPz : P ≤ supportedBlock Q (actEquiv (b' * c)) h := fun g hg =>
    mem_supportedBlock_of_le hx hself hhz hle hxz
      (KCOrthogonal.specialBlock_le_supportedBlock h hg)
      (Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_commute (hPc g hg (b' * c))).symm)
  have hPnt : ∃ g : ↥P, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hPq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hcon a, hcon b] at hab
    exact hab rfl
  have hnsz : ¬ Group.IsSolvable ↥(supportedBlock Q (actEquiv (b' * c)) h) := by
    intro hsol
    obtain ⟨g, hg1⟩ := hPnt
    exact hg1 (Subtype.ext
      (congrArg Subtype.val (eq_one_of_perfect_of_isSolvable (Subgroup.inclusion hPz) g) :))
  obtain ⟨hMq, hm2z⟩ := hgood hz hhz hnsz
  have hPM : P ≤ specialBlock Q (actEquiv (b' * c)) h := le_specialBlock_of_perfect hPz
  have hMO : specialBlock Q (actEquiv (b' * c)) h ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g hg => (Subgroup.mem_inf.mp (KCOrthogonal.specialBlock_le_isometryCentralizer h hg)).1
  have hâM : actEquiv â ∉ Subgroup.centralizer
      (specialBlock Q (actEquiv (b' * c)) h : Set ((Fin n → K) ≃ₗ[K] (Fin n → K))) := by
    intro hâc
    have hGz : actEquiv â ∈ Subgroup.centralizer
        ({actEquiv (b' * c)} : Set ((Fin n → K) ≃ₗ[K] (Fin n → K))) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← actEquiv_mul, ← actEquiv_mul,
        (IsMulCommutative.is_comm (M := ↥E0)).comm]
    obtain ⟨s, hs⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_exists_smul_of_commute_specialBlock hz
        hp2' hhz hX1 hself.symm hm2z hGz
        (fun f hf => ((Subgroup.mem_centralizer_iff.mp hâc) f hf).symm)
    have hmem := mem_zpowers_of_smul hP hpK hL hL' (Ne.symm hL'L) hb'L hcL' hcL (hle hu) huL hu0
      hyh hyL' hy0 (s := s) hs
    have ha'1 : b' * c ≠ 1 := fun h1 => hb'â (h1 ▸ (Subgroup.zpowers â).one_mem)
    have heq := eq_zpowers_of_mem hP (hP.zpowers_mem_lines ha'1) hmem hâ1
    exact hb'â (heq ▸ Subgroup.mem_zpowers (b' * c))
  exact ⟨b' * c, hb'â, P, P, specialBlock Q (actEquiv (b' * c)) h, le_rfl,
    fun g hg y hy => P.mul_mem (P.mul_mem hg hy) (P.inv_mem hg), hPΩ, hPc, hPn, hPq, hPdvd,
    le_orthDerived_of_commutator_eq_top hMq.1.commutator_eq_top hMO,
    KCOrthogonal.specialBlock_le_isometryCentralizer h,
    fun g hg y hy => KCOrthogonal.conj_mem_specialBlock hg hy, hMq, hPM,
    dvd_card_quot_center_of_le hPM hPdvd, hâM⟩

end Mixed

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
