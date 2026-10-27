module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

theorem le_center_of_generalizedFitting_le_center [Group.IsPerfect Y] {X : Subgroup Y} [X.Normal]
    (h : (CFSG.generalizedFitting ↥X).map X.subtype ≤ center Y) : X ≤ center Y := by
  intro x hx
  have hmem : ∀ y : Y, x * y * x⁻¹ * y⁻¹ ∈ X := by
    intro y
    have hy : y * x⁻¹ * y⁻¹ ∈ X :=
      (inferInstance : X.Normal).conj_mem x⁻¹ (X.inv_mem hx) y
    simpa only [mul_assoc] using X.mul_mem hx hy
  have hcentral : ∀ y : Y, x * y * x⁻¹ * y⁻¹ ∈ center Y := by
    intro y
    have hB : (⟨x * y * x⁻¹ * y⁻¹, hmem y⟩ : ↥X) ∈ CFSG.generalizedFitting ↥X := by
      apply CFSG.centralizer_generalizedFitting_le ↥X
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (h (Subgroup.mem_map_of_mem X.subtype hg)) _).symm
    exact h (Subgroup.mem_map_of_mem X.subtype hB)
  have hmul : ∀ y₁ y₂ : Y,
      x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
        (x * y₁ * x⁻¹ * y₁⁻¹) * (x * y₂ * x⁻¹ * y₂⁻¹) := by
    intro y₁ y₂
    have hc₂ := Subgroup.mem_center_iff.mp (hcentral y₂)
    calc
      x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹
          = (x * y₁ * x⁻¹) * (x * y₂ * x⁻¹) * (y₂⁻¹ * y₁⁻¹) := by group
      _ = (x * y₁ * x⁻¹) * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹ := by group
      _ = (x * y₁ * x⁻¹) * ((x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
      _ = (x * y₁ * x⁻¹) * (y₁⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹)) := by
            rw [← hc₂ y₁⁻¹]
      _ = (x * y₁ * x⁻¹ * y₁⁻¹) * (x * y₂ * x⁻¹ * y₂⁻¹) := by group
  let f : Y →* ↥(center Y) :=
    MonoidHom.mk' (fun y => ⟨x * y * x⁻¹ * y⁻¹, hcentral y⟩) (by
      intro y₁ y₂
      exact Subtype.ext (hmul y₁ y₂))
  have hf : f = 1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one f
  rw [Subgroup.mem_center_iff]
  intro y
  have hfy : f y = 1 := by rw [hf]; rfl
  have hone : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hfy
  have h2 : x * y * x⁻¹ = y := by
    simpa [mul_assoc] using congrArg (fun z => z * y) hone
  have h3 : x * y = y * x := by
    simpa [mul_assoc] using congrArg (fun z => z * x) h2
  exact h3.symm

theorem exists_pCore_not_le_center [Group.IsPerfect Y] (h2 : CFSG.pCore 2 Y = ⊥)
    {X : Subgroup Y} [X.Normal] (hE : CFSG.layer ↥X = ⊥) (hc : ¬ X ≤ center Y) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ¬ (CFSG.pCore r ↥X).map X.subtype ≤ center Y := by
  by_contra hall
  push Not at hall
  have h2map : (CFSG.pCore 2 ↥X).map X.subtype ≤ center Y := by
    have hP2 : (CFSG.pCore 2 ↥X).map X.subtype ≤ CFSG.pCore 2 Y := by
      refine le_sSup ⟨?_, ?_⟩
      · exact inferInstance
      · exact (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
    rw [h2] at hP2
    exact hP2.trans bot_le
  have hfit : (CFSG.fittingSubgroup ↥X).map X.subtype ≤ center Y := by
    rw [CFSG.fitting_eq_sup_pCore]
    rw [Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    by_cases hp2 : p.1.1 = 2
    · rw [hp2]
      exact h2map
    · exact hall p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) hp2
  have hgen : (CFSG.generalizedFitting ↥X).map X.subtype ≤ center Y := by
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup, hE, Subgroup.map_bot, sup_bot_eq]
    exact hfit
  exact hc (le_center_of_generalizedFitting_le_center hgen)

theorem exists_mulAut_surjective_of_not_le_center {p : ℕ} (hp : p.Prime) [Group.IsPerfect Y]
    (hgen : closure {y : Y | ∃ n : ℕ, orderOf y = p ^ n} = ⊤) (h2 : CFSG.pCore 2 Y = ⊥)
    (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pPrimeCore p Y))
    (hE : CFSG.layer ↥(CFSG.pPrimeCore p Y) = ⊥)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (CFSG.pPrimeCore p Y) ≤ 3)
    (hc : ¬ CFSG.pPrimeCore p Y ≤ center Y) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ V : Subgroup Y, IsPGroup q ↥V ∧
      CFSG.Open.pRank q (⊤ : Subgroup ↥V) ≤ 3 ∧
      ∃ (A : Subgroup (MulAut ↥V))
        (φ : ↥A →* (Y ⧸ CFSG.pPrimeCore p Y) ⧸ center (Y ⧸ CFSG.pPrimeCore p Y)),
        Function.Surjective φ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq_prime, hq_ne_two, hVnc⟩ :=
    exists_pCore_not_le_center (Y := Y) h2 hE hc
  have hq_gt_one : 1 < q := hq_prime.one_lt
  let X : Subgroup Y := CFSG.pPrimeCore p Y
  haveI hXnorm : X.Normal := CFSG.pPrimeCore_normal (p := p) (G := Y)
  let V : Subgroup Y := (CFSG.pCore q ↥X).map X.subtype
  have hVX : V ≤ X := Subgroup.map_subtype_le (H := X) (CFSG.pCore q ↥X)
  have hVnc' : ¬ V ≤ center Y := hVnc
  have hVp : IsPGroup q ↥V := (CFSG.pCore_isPGroup (p := q) (G := ↥X)).map X.subtype
  haveI hVnorm : V.Normal := inferInstance
  have hq_ne_p : q ≠ p := by
    intro hqp
    have hVp' : IsPGroup p ↥V := hqp ▸ hVp
    have hVcop : Nat.Coprime p (Nat.card V) :=
      (CFSG.pPrimeCore_coprime_card (p := p) (G := Y)).coprime_dvd_right
        (Subgroup.card_dvd_of_le hVX)
    rcases hVp'.card_eq_or_dvd with h1 | hdiv
    · exact hVnc' (by rw [Subgroup.eq_bot_of_card_eq (H := V) h1]; exact bot_le)
    · have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hVcop dvd_rfl hdiv
      exact absurd hp1 hp.ne_one
  have hrank : CFSG.Open.pRank q (⊤ : Subgroup ↥V) ≤ 3 := by
    have h1 : CFSG.Open.pRank q (⊤ : Subgroup ↥V) ≤
        CFSG.Open.pRank q ((⊤ : Subgroup ↥V).map V.subtype) :=
      CFSG.SectionRank.pRank_le_map hq_gt_one V.subtype V.subtype_injective ⊤
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1.trans ((CFSG.SectionRank.pRank_mono hq_gt_one hVX).trans (hrk q hq_prime hq_ne_two))
  let ψ : Y →* MulAut ↥V := MulAut.conjNormal
  let Q := Y ⧸ X
  let π : Y →* Q ⧸ center Q :=
    (QuotientGroup.mk' (center Q)).comp (QuotientGroup.mk' X)
  have hπ_surj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective (center Q)).comp (QuotientGroup.mk'_surjective X)
  have hker_le : ψ.ker ≤ π.ker := by
    let N : Subgroup Q := (ψ.ker).map (QuotientGroup.mk' X)
    have hNnormal : N.Normal :=
      (inferInstance : ψ.ker.Normal).map (QuotientGroup.mk' X)
        (QuotientGroup.mk'_surjective X)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNnormal with hNtop | hNcenter
    · exfalso
      have hpElem_mem : ∀ y : Y, (∃ n : ℕ, orderOf y = p ^ n) → y ∈ ψ.ker := by
        rintro y ⟨n, hn⟩
        rw [MonoidHom.mem_ker]
        have hyN : QuotientGroup.mk' X y ∈ N := by
          rw [hNtop]; exact Subgroup.mem_top _
        obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hyN
        have hx : y * c⁻¹ ∈ X := by
          have := QuotientGroup.eq_iff_div_mem.mp hcy.symm
          simpa [div_eq_mul_inv] using this
        have hψ : ψ y = ψ (y * c⁻¹) := by
          have hy : y = (y * c⁻¹) * c := by group
          conv_lhs => rw [hy]
          rw [map_mul, MonoidHom.mem_ker.mp hc, mul_one]
        have hy_pow : y ^ (p ^ n) = 1 := by
          rw [← orderOf_dvd_iff_pow_eq_one, hn]
        have horder_y : orderOf (ψ y) ∣ p ^ n := by
          rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hy_pow, map_one]
        have horder_x : orderOf (ψ (y * c⁻¹)) ∣ Nat.card X :=
          (orderOf_map_dvd ψ (y * c⁻¹)).trans (Subgroup.orderOf_dvd_natCard X hx)
        have hcop : Nat.Coprime (Nat.card X) (p ^ n) :=
          (CFSG.pPrimeCore_coprime_card (p := p) (G := Y)).symm.pow_right n
        have horder_one : orderOf (ψ (y * c⁻¹)) = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop horder_x (by rw [← hψ]; exact horder_y)
        rw [hψ, orderOf_eq_one_iff.mp horder_one]
      have hker_top : ψ.ker = ⊤ := by
        rw [eq_top_iff, ← hgen]
        exact (Subgroup.closure_le ψ.ker).mpr hpElem_mem
      have hVcenter : V ≤ center Y := by
        intro v hv
        rw [Subgroup.mem_center_iff]
        intro y
        have hy : y ∈ ψ.ker := by rw [hker_top]; exact Subgroup.mem_top y
        have h1 : ψ y = 1 := MonoidHom.mem_ker.mp hy
        have hconj : y * v * y⁻¹ = v := by
          have hv' : (MulAut.conjNormal y) ⟨v, hv⟩ = ⟨v, hv⟩ := by
            have := congrArg (fun (f : MulAut ↥V) => f ⟨v, hv⟩) h1
            simpa [ψ] using this
          have := congrArg (fun w : ↥V => (w : Y)) hv'
          simpa [MulAut.conjNormal_apply] using this
        calc
          y * v = (y * v * y⁻¹) * y := by group
          _ = v * y := by rw [hconj]
      exact hVnc' hVcenter
    · intro c hc
      rw [MonoidHom.mem_ker]
      have hmem : QuotientGroup.mk' X c ∈ center Q :=
        hNcenter (Subgroup.mem_map_of_mem (QuotientGroup.mk' X) hc)
      show QuotientGroup.mk' (center Q) (QuotientGroup.mk' X c) = 1
      exact (QuotientGroup.eq_one_iff (QuotientGroup.mk' X c)).mpr hmem
  let A : Subgroup (MulAut ↥V) := ψ.range
  let e : ↥A ≃* Y ⧸ ψ.ker := (QuotientGroup.quotientKerEquivRange ψ).symm
  let φ : ↥A →* Q ⧸ center Q :=
    (QuotientGroup.lift ψ.ker π hker_le).comp e.toMonoidHom
  have hφ_surj : Function.Surjective φ := by
    have hL : Function.Surjective (QuotientGroup.lift ψ.ker π hker_le) := by
      intro z
      obtain ⟨y, hy⟩ := hπ_surj z
      exact ⟨QuotientGroup.mk' ψ.ker y, by simpa using hy⟩
    simpa [φ] using hL.comp e.surjective
  exact ⟨q, hq_prime, hq_ne_two, hq_ne_p, V, hVp, hrank, A, φ, hφ_surj⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

