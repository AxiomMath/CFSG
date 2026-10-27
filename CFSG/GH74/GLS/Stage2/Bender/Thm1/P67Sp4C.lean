module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Inn
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldCentralizer
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartTwo.KFacts
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

variable {K : Type} [Field K]

theorem noOddNormal_of_solvableRadical_bot {Y : Type} [Group Y] {M : Subgroup Y}
    (h : solvableRadical ↥M = ⊥) (r : ℕ) : NoOddNormal M r := by
  intro N hNM hNn hNab _ _
  set N' : Subgroup ↥M := N.subgroupOf M with hN'
  have hnorm : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Y) ∈ N := hn
    rw [hN', Subgroup.mem_subgroupOf]
    have := hNn (g : Y) g.2 (n : Y) hn'
    simpa using this
  have hsolv : Group.IsSolvable ↥N' := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact hNab _ a.2 _ b.2
  have hle : N' ≤ solvableRadical ↥M := le_sSup ⟨hnorm, hsolv⟩
  rw [h] at hle
  rw [eq_bot_iff]
  intro n hn
  have h1 : (⟨n, hNM hn⟩ : ↥M) ∈ N' := hn
  have := hle h1
  rw [Subgroup.mem_bot] at this ⊢
  exact congrArg Subtype.val this


theorem caseC_core [Finite K] (hodd : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hcen : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥) {r : ℕ}
    (hr : r.Prime) {V Z : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (h2 : N2Cfg (StatedProj (StatedSp 2 K)) r V Z) (h3 : N3Full (StatedProj (StatedSp 2 K)) V Z)
    {σ : K ≃+* K} (hσ : orderOf σ = r) (hbV : fieldAut 2 K σ ∈ V) : False := by
  classical
  have hr2 : Odd r := h2.2.1
  have hσp : σ ^ r = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  set b := fieldAut 2 K σ with hb
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    exact hr.one_lt.ne hσ
  have hb1 : b ≠ 1 := by
    intro h
    apply hσ1
    exact (fieldAut_mem_range_conjAut_iff (r := 2) (K := K) (by norm_num)).mp
      ⟨1, by rw [map_one, ← h]⟩
  set M : Subgroup (StatedProj (StatedSp 2 K)) := spFixedGroup b with hM
  have hMle : M ≤ fixSub b := fun x hx => hx
  have hMinv : ∀ z ∈ Z, ∀ c ∈ M, z c ∈ M := by
    intro z hz c hc
    have hcomm : b * z = z * b := h2.2.2.2.2.2.2.2.2 b hbV z hz
    show b (z c) = z c
    have h1 : b (z c) = z (b c) := by
      have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ c) hcomm
      simpa using this
    rw [h1, show b c = c from hc]
  have hMno : NoOddNormal M r :=
    noOddNormal_of_solvableRadical_bot (solvableRadical_fixedGroup (le_refl 2) hr2 hσp) r
  have hfix := fix_step hcen h2 h3 hbV hb1 hMle hMinv hMno
  obtain ⟨-, -, -, -, -, hZodd, hZcop, hZbot, -⟩ := h2
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  obtain ⟨A, τ, hzAτ⟩ :=
    psp4_odd_automorphism_normal_form hodd (z : MulAut (StatedProj (StatedSp 2 K)))
  have hzE : (z : MulAut (StatedProj (StatedSp 2 K))) ∈ spSemilinearAutGroup 2 K :=
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.mem_spSemilinearAutGroup_iff).mpr
      ⟨A, τ, hzAτ⟩
  have hfixk : ∀ g : StatedSp 2 (descentField σ),
      (z : MulAut (StatedProj (StatedSp 2 K))) (proj 2 K (subfieldSpHom 2 (descentField σ) g)) =
        proj 2 K (subfieldSpHom 2 (descentField σ) g) := by
    intro g
    refine hfix z z.2 _ ?_
    rw [hM, spFixedGroup_fieldAut_eq_range hr2 hσp]
    exact ⟨g, rfl⟩
  obtain ⟨τ', hτ'k, hzτ'⟩ := exists_fieldAut_of_fixes_subfield (descentField σ) hzE hfixk
  have hτ'mem : τ' ∈ Subgroup.zpowers σ := mem_zpowers_of_forall_fixed_prime hℓ hf hr hK hσ hτ'k
  have hbr : b ^ r = 1 := by rw [hb, ← map_pow, hσp, map_one]
  have hzr : (z : MulAut (StatedProj (StatedSp 2 K))) ^ r = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hτ'mem
    rw [hzτ', ← hn, map_zpow, ← hb, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hbr, _root_.one_zpow]
  have hdvd : orderOf (z : MulAut (StatedProj (StatedSp 2 K))) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have hord : orderOf (z : MulAut (StatedProj (StatedSp 2 K))) ∣ r := orderOf_dvd_of_pow_eq_one hzr
  have hcop : Nat.Coprime (orderOf (z : MulAut (StatedProj (StatedSp 2 K)))) r :=
    Nat.Coprime.coprime_dvd_left hdvd hZcop
  have h1 : orderOf (z : MulAut (StatedProj (StatedSp 2 K))) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hord
  exact hz1 (Subtype.ext (orderOf_eq_one_iff.mp h1))


theorem caseC [Finite K] (hodd : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hcen : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥) {r : ℕ}
    (hr : r.Prime) {V Z : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (h2 : N2Cfg (StatedProj (StatedSp 2 K)) r V Z) (h3 : N3Full (StatedProj (StatedSp 2 K)) V Z)
    (hout : ¬ ∀ v ∈ V, ∃ g : StatedProj (StatedSp 2 K), MulAut.conj g = v) : False := by
  classical
  have hr2 : Odd r := h2.2.1
  have : Fact r.Prime := ⟨hr⟩
  have hVe : IsElementaryAbelian r ↥V := h2.2.2.1
  push Not at hout
  obtain ⟨b, hbV, hbg⟩ := hout
  have hbr : b ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian b hbV
  obtain ⟨A, τ, hbAτ⟩ := psp4_odd_automorphism_normal_form hodd b
  have hbE : b ∈ spSemilinearAutGroup 2 K :=
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.mem_spSemilinearAutGroup_iff).mpr
      ⟨A, τ, hbAτ⟩
  have hbD : b ∉ spLinearAutGroup 2 K := by
    intro hD
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup_eq_range] at hD
    obtain ⟨B, hB⟩ := hD
    obtain ⟨g, hg⟩ := exists_conj_of_conjAut_pow hr2 B (by rw [hB]; exact hbr)
    exact hbg g (hg.trans hB)
  have hb1 : b ≠ 1 := fun h => hbg 1 (by rw [map_one, h])
  have hord : orderOf b = r := orderOf_eq_prime hbr hb1
  obtain ⟨-, -, -, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf
      (le_refl 2) hK
  obtain ⟨-, σ, hσ, -, h, -, hbh⟩ := hdesc r hr b hbE hbD hord
  let e : StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 K) := h⁻¹
  have h2' := N2Cfg.map_mulEquiv (MulAut.congr e) h2
  have h3' := N3Full.map_mulEquiv e h3
  refine caseC_core hodd hℓ hf hK hcen hr h2' h3' hσ ⟨b, hbV, ?_⟩
  ext y
  show e (b (e.symm y)) = fieldAut 2 K σ y
  have hb' : b = h * fieldAut 2 K σ * h⁻¹ := hbh
  rw [hb']
  show h⁻¹ ((h * fieldAut 2 K σ * h⁻¹) (h y)) = _
  simp [MulAut.mul_apply]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
