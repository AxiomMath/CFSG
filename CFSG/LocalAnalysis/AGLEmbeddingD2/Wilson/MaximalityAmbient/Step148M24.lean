module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofOuter
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.M24ThreeLocal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AutTrivialModCentral
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec14.Main148 CFSG.RankThree.PartTwo.Sec14.HJRes148 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_comm_of_commutator_mem {A Y : Subgroup G} [(ker148 A Y).Normal] {g h : G}
    (hg : g ∈ Y ⊔ A) (hh : h ∈ Y ⊔ A) (hc : g * h * g⁻¹ * h⁻¹ ∈ pPrimeCoreOf 3 Y) :
    QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ * QuotientGroup.mk' (ker148 A Y) ⟨h, hh⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨h, hh⟩ * QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ := by
  have hmem : g * h * g⁻¹ * h⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hg hh) ((Y ⊔ A).inv_mem hg))
      ((Y ⊔ A).inv_mem hh)
  have h1 : QuotientGroup.mk' (ker148 A Y) ⟨g * h * g⁻¹ * h⁻¹, hmem⟩ = 1 :=
    mk'_ker148_eq_one_iff.mpr hc
  have e1 : QuotientGroup.mk' (ker148 A Y) ⟨g * h * g⁻¹ * h⁻¹, hmem⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ * QuotientGroup.mk' (ker148 A Y) ⟨h, hh⟩ *
        (QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩)⁻¹ *
        (QuotientGroup.mk' (ker148 A Y) ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e1] at h1
  set X := QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩
  set W := QuotientGroup.mk' (ker148 A Y) ⟨h, hh⟩
  calc X * W = (X * W * X⁻¹ * W⁻¹) * (W * X) := by group
    _ = W * X := by rw [h1, one_mul]

section M24


theorem exists_sectionCentralizer_of_m24 {A Y J Yd : Subgroup G} [(ker148 A Y).Normal]
    (hAF : A ∈ partTwoF G) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    {d : G} (hd : d ∈ A) (hd1 : d ≠ 1)
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYdJ : Yd ≤ J)
    (hAYd : A ≤ Subgroup.normalizer (Yd : Set G)) (hdYd : d ∈ Yd)
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    {b : G} (hb : b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd))
    (e : ↥(img148 A Y J) ≃* NativeSporadic.M24) :
    ∃ n : ℕ, b * (d ^ n)⁻¹ ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hbA : b ∈ A := hb.1
  have hd3 : d ^ 3 = 1 := hA3 d hd
  have hdJ : d ∈ J := hYdJ hdYd
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  set Jα := img148 A Y J with hJα
  set P := img148 A Y Yd with hP
  obtain ⟨h1080, hPle⟩ := card_img148_yd_of_a6 hAY hd hd3 hYd hJ hYdJ hAJ hA6 hθ
  have hdαJ : alpha148 A Y d hd ∈ Jα :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hd, hdJ, rfl⟩
  let c : ↥Jα := ⟨alpha148 A Y d hd, hdαJ⟩
  have hc3 : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact alpha148_pow_three hA3 hd
    · intro h
      exact alpha148_ne_one hd hd1 hd3 (congrArg Subtype.val h)
  have hPJ : P ≤ Jα := hPle.trans inf_le_left
  set P' : Subgroup ↥Jα := P.subgroupOf Jα with hP'
  have hP'card : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv
  have hP'le : P' ≤ Subgroup.centralizer ({c} : Set ↥Jα) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hPle (Subgroup.mem_subgroupOf.1 hx)).2
  have hCP : Subgroup.centralizer (P' : Set ↥Jα) = Subgroup.zpowers c :=
    (M24ThreeLocal.m24_centralizer_eq_of_le e hc3 hP'le (by rw [hP'card]; exact h1080)).2
  set β := alpha148 A Y b hbA with hβ
  have hβJ : β ∈ Subgroup.normalizer (Jα : Set _) :=
    img148_le_normalizer hAJ (alpha148_mem_img148 hbA)
  have hβP : β ∈ Subgroup.normalizer (P : Set _) :=
    img148_le_normalizer hAYd (alpha148_mem_img148 hbA)
  let σ : MulAut ↥P := Subgroup.normalizerMonoidHom P ⟨β, hβP⟩
  have hσ : ∀ x : ↥P, ((σ x : ↥P) : _) = β * x * β⁻¹ := fun x => rfl
  have hΘYd : inSubgroup (aschbacherSolvableCore 3) Yd ≤ Yd := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hΘP : img148 A Y (inSubgroup (aschbacherSolvableCore 3) Yd) ≤ P := img148_mono hΘYd
  let Z : Subgroup ↥P := (img148 A Y (inSubgroup (aschbacherSolvableCore 3) Yd)).subgroupOf P
  have hZc : ∀ z ∈ Z, z ∈ Subgroup.center ↥P := by
    intro z hz
    obtain ⟨t, htM, htΘ, ht⟩ := mem_img148_iff.mp (Subgroup.mem_subgroupOf.mp hz)
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    obtain ⟨g, hgM, hgYd, hg⟩ := mem_img148_iff.mp w.2
    have hcomm : g * t * g⁻¹ * t⁻¹ ∈ pPrimeCoreOf 3 Y := by
      have h1 : t * g * t⁻¹ * g⁻¹ ∈ pPrimeCoreOf 3 Y := hθ (Subgroup.commutator_mem_commutator htΘ hgYd)
      have h2 : g * t * g⁻¹ * t⁻¹ = (t * g * t⁻¹ * g⁻¹)⁻¹ := by group
      rw [h2]
      exact Subgroup.inv_mem _ h1
    have := mk_comm_of_commutator_mem (A := A) (Y := Y) hgM htM hcomm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hg, ← ht]
    exact this
  have hα : ∀ x : ↥P, σ x * x⁻¹ ∈ Z := by
    intro x
    obtain ⟨g, hgM, hgYd, hg⟩ := mem_img148_iff.mp x.2
    refine Subgroup.mem_subgroupOf.mpr (mem_img148_iff.mpr ⟨b * g * b⁻¹ * g⁻¹, ?_, hb.2 g hgYd, ?_⟩)
    · exact (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem (Subgroup.mem_sup_right hbA) hgM)
        ((Y ⊔ A).inv_mem (Subgroup.mem_sup_right hbA))) ((Y ⊔ A).inv_mem hgM)
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, ← hg, hβ, alpha148_eq_mk']
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
  have hperf : (⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ : Subgroup ↥P) = ⊤ := by
    obtain ⟨-, -, hPperf, -, -⟩ := ydAlpha_facts hAY hd hd3 hYd hJ hYdJ hAJ
      (three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))) hθ
    exact Group.isPerfect_def.1 hPperf
  have hβfix : ∀ y ∈ P, β * y * β⁻¹ = y := by
    intro y hy
    have := Proving.aut_trivial_of_mod_central hperf Z hZc σ hα ⟨y, hy⟩
    exact congrArg Subtype.val this
  let τ : MulAut ↥Jα := Subgroup.normalizerMonoidHom Jα ⟨β, hβJ⟩
  obtain ⟨x, hx⟩ := M24ThreeLocal.mulAut_eq_inner_of_m24 e τ
  set xq : ↥(Y ⊔ A) ⧸ ker148 A Y := (x : ↥(Y ⊔ A) ⧸ ker148 A Y) with hxq
  have hxc : ∀ y ∈ Jα, β * y * β⁻¹ = xq * y * xq⁻¹ := by
    intro y hy
    have h1 : (((MulAut.conj x : MulAut ↥Jα) ⟨y, hy⟩ : ↥Jα) : ↥(Y ⊔ A) ⧸ ker148 A Y) =
        ((τ ⟨y, hy⟩ : ↥Jα) : ↥(Y ⊔ A) ⧸ ker148 A Y) := by rw [hx]
    rw [MulAut.conj_apply] at h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1.symm
  have hxmem : x ∈ Subgroup.centralizer (P' : Set ↥Jα) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply Subtype.ext
    set hq : ↥(Y ⊔ A) ⧸ ker148 A Y := (h : ↥(Y ⊔ A) ⧸ ker148 A Y) with hhq
    have hhP : hq ∈ P := Subgroup.mem_subgroupOf.mp hh
    have h1 := hxc hq h.2
    rw [hβfix _ hhP] at h1
    show hq * xq = xq * hq
    calc hq * xq = (xq * hq * xq⁻¹) * xq := by rw [← h1]
      _ = xq * hq := by group
  rw [hCP] at hxmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hn : x = c ^ ((k % 3).toNat) := by
    have h3 : c ^ (k % (orderOf c : ℤ)) = c ^ k := zpow_mod_orderOf c k
    rw [hc3] at h3
    rw [← hk, ← h3, ← zpow_natCast]
    congr 1
    exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm
  set n : ℕ := (k % 3).toNat
  have huA : d ^ n ∈ A := A.pow_mem hd n
  have hu : alpha148 A Y (d ^ n) huA = xq := by
    rw [alpha148_pow hd n, hxq, hn, Subgroup.coe_pow]
  have hxJ : xq ∈ Jα := x.2
  refine ⟨n, A.mul_mem hbA (A.inv_mem huA), fun g hg => ?_⟩
  have hgM : g ∈ Y ⊔ A := hJM hg
  set gb := QuotientGroup.mk' (ker148 A Y) ⟨g, hgM⟩
  have hgb : gb ∈ img148 A Y J := mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩
  have hmem : (b * (d ^ n)⁻¹) * g * (b * (d ^ n)⁻¹)⁻¹ * g⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem (Subgroup.mem_sup_right
      (A.mul_mem hbA (A.inv_mem huA))) hgM) ((Y ⊔ A).inv_mem (Subgroup.mem_sup_right
      (A.mul_mem hbA (A.inv_mem huA))))) ((Y ⊔ A).inv_mem hgM)
  refine (mk'_ker148_eq_one_iff (g := ⟨_, hmem⟩)).mp ?_
  have e1 : QuotientGroup.mk' (ker148 A Y) ⟨_, hmem⟩ =
      (alpha148 A Y b hbA * xq⁻¹) * gb * (alpha148 A Y b hbA * xq⁻¹)⁻¹ * gb⁻¹ := by
    rw [← hu, ← alpha148_inv huA, ← alpha148_mul hbA (A.inv_mem huA), alpha148_eq_mk']
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hxg : xq⁻¹ * gb * xq ∈ img148 A Y J :=
    (img148 A Y J).mul_mem ((img148 A Y J).mul_mem ((img148 A Y J).inv_mem hxJ) hgb) hxJ
  rw [e1]
  calc (alpha148 A Y b hbA * xq⁻¹) * gb * (alpha148 A Y b hbA * xq⁻¹)⁻¹ * gb⁻¹
      = alpha148 A Y b hbA * (xq⁻¹ * gb * xq) * (alpha148 A Y b hbA)⁻¹ * gb⁻¹ := by
        group
    _ = xq * (xq⁻¹ * gb * xq) * xq⁻¹ * gb⁻¹ := by
        rw [hxc _ hxg]
    _ = 1 := by group

end M24

section Reduce



@[expose] def Step148HJM24Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) →
        ∀ a ∈ B, a ≠ 1 → a ^ 3 = 1 → a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y


theorem step148HJM24Outer2_of_cent (h : Step148HJM24Cent) : Step148HJM24Outer2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb hM
  have hker : (ker148 A Y).Normal := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, hb1, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hdYd : d ∈ Yd := hYBYd hdYB
  obtain ⟨e⟩ := hM
  obtain ⟨n, hcent⟩ := exists_sectionCentralizer_of_m24 hS.mem_partTwoF hY.2 hJ hAJ hdA hd1 hYd
    hYdJ hAYd hdYd hA6 hθ hb e
  refine h G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb ⟨e⟩ (b * (d ^ n)⁻¹) ?_ ?_ ?_ hcent
  · exact B.mul_mem hbB (B.inv_mem (B.pow_mem hdB n))
  · intro h1
    have hbd : b = d ^ n := by
      calc b = (b * (d ^ n)⁻¹) * d ^ n := by group
        _ = d ^ n := by rw [h1, one_mul]
    have hBle : B ≤ Subgroup.zpowers d := by
      have hcl : B = Subgroup.closure {b, d} := hc.1
      rw [hcl, Subgroup.closure_le]
      intro z hz
      rcases hz with hz | hz
      · rw [hz, hbd]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) n
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Subgroup.mem_zpowers d
    have hd3 : d ^ 3 = 1 := hS.mem_partTwoF.1.2 d hdA
    have hz3 : Nat.card (Subgroup.zpowers d) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
    have h27 : Nat.card A = 27 := hA.2
    have h9 : 3 * Nat.card B = 27 := by rw [← hB.2, h27]
    have := Subgroup.card_le_of_le hBle
    omega
  · have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hS.mem_partTwoF.1.2
    exact hA3 _ (A.mul_mem (hB.1 hbB) (A.inv_mem (A.pow_mem hdA n)))

end Reduce

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24
