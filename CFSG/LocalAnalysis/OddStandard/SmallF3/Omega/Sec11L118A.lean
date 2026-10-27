module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Alt2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11A_z_mem_secB [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) : z ∈ secB S L := by
  obtain ⟨-, -, hBC, -⟩ := sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  rw [← hBC]
  exact ⟨Subgroup.mem_centralizer_iff.mpr fun b hb' => hctx.central b (secB_le_S S L hb'), hzL⟩

private theorem sec11A_vec_add_self (v : Fin 5 → ZMod 2) : v + v = 0 := by
  revert v
  decide +kernel

private theorem sec11A_other_weight4 (v₀ : Fin 5 → ZMod 2) (h : vecWeight v₀ = 4) :
    ∃ v : Fin 5 → ZMod 2, vecWeight v = 4 ∧ v ≠ v₀ ∧ vecWeight (v + v₀) = 2 ∧
      IsEvenVec (v + v₀) := by
  revert v₀
  unfold vecWeight IsEvenVec
  decide +kernel

theorem sec11A_exists_u0 [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∃ u : G, u ∈ secB S L ∧ orderOf u = 2 ∧ InducesTypeSome L u 5 1 2 (-1) ∧
      ¬ IsI4PlusIn L u := by
  obtain ⟨hpsp, -⟩ := hp.basic G t L S z hctx.toSec10Z
  obtain ⟨-, hz2, -, -, -⟩ := sec11_invols hctx
  have hz : IsI4PlusIn L z := hctx.toSec10Z.pocket
  obtain ⟨-, -, -, -, -, φ, hperm, h4, h2, -⟩ :=
    sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z
  obtain ⟨hadd, hinj, himg, -, -⟩ := hperm
  have hφ1 : φ 0 = 1 := by
    have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have := hadd 0 0 h0 h0
    simpa using this
  have hzB : z ∈ secB S L := sec11A_z_mem_secB hp hctx
  obtain ⟨v₀, hv₀, hφv₀⟩ := (himg z).1 hzB
  have hv₀4 : vecWeight v₀ = 4 := by
    rcases even_weight_cases_five v₀ hv₀ with h0 | h02 | h04
    · exfalso
      have := hz.1
      rw [← hφv₀, h0, hφ1, orderOf_one] at this
      omega
    · exact absurd (hφv₀ ▸ hz) (h2 v₀ hv₀ h02)
    · exact h04
  obtain ⟨v, hv4, hvv₀, hw2, hwev⟩ := sec11A_other_weight4 v₀ hv₀4
  have hv : IsEvenVec v := isEvenVec_of_weight_four v hv4
  have hxB : φ v ∈ secB S L := (himg (φ v)).2 ⟨v, hv, rfl⟩
  have hx : IsI4PlusIn L (φ v) := h4 v hv hv4
  have hx2 : φ v * φ v = 1 := by rw [← hadd v v hv hv, sec11A_vec_add_self, hφ1]
  have hxz : φ v * z = z * φ v := by
    have e1 := hadd v v₀ hv hv₀
    have e2 := hadd v₀ v hv₀ hv
    rw [hφv₀] at e1 e2
    rw [← e1, ← e2, add_comm]
  have hzx : z ≠ φ v := by
    intro hzx
    exact hvv₀ (hinj v v₀ hv hv₀ (hzx.symm.trans hφv₀.symm))
  have hu0ty : InducesTypeSome L (φ v * z) 5 1 2 (-1) :=
    hp.facts.f218c G L hpsp z (φ v) hz hx hzx hxz.symm
  have hu0B : φ v * z ∈ secB S L := (secB S L).mul_mem hxB hzB
  have hu0o : orderOf (φ v * z) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc φ v * z * (φ v * z) = φ v * (z * φ v) * z := by group
        _ = φ v * (φ v * z) * z := by rw [← hxz]
        _ = (φ v * φ v) * (z * z) := by group
        _ = 1 := by rw [hx2, hz2, one_mul]
    · intro h1
      apply hzx
      have e : φ v = z⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [e]
      exact (inv_eq_of_mul_eq_one_right hz2).symm
  have hu0n : ¬ IsI4PlusIn L (φ v * z) := by
    have e : φ v * z = φ (v + v₀) := by rw [hadd v v₀ hv hv₀, hφv₀]
    rw [e]
    exact h2 (v + v₀) hwev hw2
  exact ⟨φ v * z, hu0B, hu0o, hu0ty, hu0n⟩

theorem sec11A_no_conj [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) (hyp : Hyp111 t S L) {q : G}
    (hq : q ∈ secQ K1 K2) (hq2 : q * q = 1) (hqz : q ∉ zpowers z) :
    ¬ ∃ k : G, k⁻¹ * t * k = t * q := by
  rintro ⟨k, hk⟩
  obtain ⟨hpsp, htC, -⟩ := hp.basic G t L S z hctx.toSec10Z
  obtain ⟨-, -, hQL, -, -⟩ := sec11_Q_facts hp hctx
  have hqL : q ∈ L := hQL hq
  have hqty : InducesTypeSome L q 5 1 2 (-1) :=
    hp.facts.factsB.q2m G L hpsp z K1 K2 hctx.toSec10Z.pocket hctx.pocket1 hctx.pocket2
      hctx.ne q hq hq2 hqz
  obtain ⟨u0, hu0B, hu02, hu0ty, hu0n⟩ := sec11A_exists_u0 hp hctx
  obtain ⟨l, hl, hlu⟩ := hp.facts.factsC.i2m G L hpsp u0 q (secB_le_L S L hu0B) hqL hu0ty hqty
  have hlt : l * t = t * l := Subgroup.mem_centralizer_iff.mp htC l hl
  have hconj : (k * l⁻¹)⁻¹ * t * (k * l⁻¹) = t * u0 := by
    rw [← hlu] at hk
    calc (k * l⁻¹)⁻¹ * t * (k * l⁻¹) = l * (k⁻¹ * t * k) * l⁻¹ := by group
      _ = l * (t * (l⁻¹ * u0 * l)) * l⁻¹ := by rw [hk]
      _ = (l * t) * l⁻¹ * u0 := by group
      _ = (t * l) * l⁻¹ * u0 := by rw [hlt]
      _ = t * u0 := by group
  have hA : t * u0 ∈ secA t S L :=
    (secA t S L).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_left hu0B)
  have hTop : t * u0 ∈ conjClassIn ⊤ t :=
    ⟨(k * l⁻¹)⁻¹, Subgroup.mem_top _, by rw [inv_inv]; exact hconj.symm⟩
  rcases hp.r10.l1011 G t L S z K1 K2 hctx with h | ⟨-, hcls, hM, -, -⟩
  · exact sec11_not_alt1 hyp h
  · have hmem : t * u0 ∈ conjClassIn (secM t S L) t := by
      rw [← hcls]
      exact ⟨hTop, hA⟩
    rw [hM] at hmem
    rcases hmem with h1 | ⟨m, hm, hmeq⟩
    · have hu01 : u0 = 1 := by
        have h1' : t * u0 = t * 1 := by rw [mul_one]; exact h1
        exact mul_left_cancel h1'
      rw [hu01, orderOf_one] at hu02
      omega
    · obtain ⟨-, hmL⟩ := hm
      have hmt : m * t = t * m := Subgroup.mem_centralizer_iff.mp htC m hmL
      have hu0eq : u0 = m * z * m⁻¹ := by
        have e : t * u0 = t * (m * z * m⁻¹) := by
          rw [hmeq]
          calc m * (t * z) * m⁻¹ = (m * t) * z * m⁻¹ := by group
            _ = (t * m) * z * m⁻¹ := by rw [hmt]
            _ = t * (m * z * m⁻¹) := by group
        exact mul_left_cancel e
      exact hu0n (hu0eq ▸ IsI4PlusIn.conj_of_mem hctx.toSec10Z.pocket hmL)

theorem sec11_strClosed_secW [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) (hyp : Hyp111 t S L) :
    IsStrClosedModZ t z (secW t K1 K2) := by
  intro h _ hmem
  obtain ⟨ht2, hz2, htz, -, -⟩ := sec11_invols hctx
  obtain ⟨hzQ, -, hQL, -, hQt⟩ := sec11_Q_facts hp hctx
  have hWz : secW t K1 K2 ⊔ zpowers z = secW t K1 K2 := by
    refine sup_eq_left.mpr ((Subgroup.zpowers_le).mpr ?_)
    exact Subgroup.mem_sup_left hzQ
  rw [hWz] at hmem
  obtain ⟨q, hq, hs | hs⟩ := sec10J_mem_W hp.facts.pockets5 hp.basic hctx _ hmem
  · exfalso
    refine hp.r10.l108 G t L S z K1 K2 hctx h ?_
    rw [hs]
    exact hQL hq
  · have hqt : q * t = t * q := (hQt q hq).symm
    have hs2 : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
      calc (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
        _ = 1 := by rw [ht2]; group
    have hq2 : q * q = 1 := by
      have e : (q * t) * (q * t) = (q * q) * (t * t) := by
        calc (q * t) * (q * t) = q * (t * q) * t := by group
          _ = q * (q * t) * t := by rw [hqt]
          _ = (q * q) * (t * t) := by group
      rw [← hs, hs2, ht2, mul_one] at e
      exact e.symm
    by_cases hqz : q ∈ zpowers z
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqz
      rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
      · left
        have hq1 : q = 1 := by
          rw [← hk, zpow_mul, zpow_two, hz2, one_zpow]
        rw [hs, hq1, one_mul]
      · right
        have hqzz : q = z := by
          rw [← hk, zpow_add, zpow_mul, zpow_two, hz2, one_zpow, one_mul, zpow_one]
        rw [hs, hqzz, htz]
    · exfalso
      refine sec11A_no_conj hp hctx hyp hq hq2 hqz ⟨h, ?_⟩
      rw [hs]
      exact hqt

end CFSG.OddStandard.SmallF3.Omega
