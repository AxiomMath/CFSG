module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGElt
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G} {g : G}

@[expose] def twoSecMap (x : G) (H : Subgroup G) : Subgroup (TwoSec x) :=
  (H.subgroupOf (centralizer ({x} : Set G))).map (QuotientGroup.mk' (zpowers (selfC x)))

theorem mem_twoSecMap_iff {x : G} {H : Subgroup G} {y : TwoSec x} :
    y ∈ twoSecMap x H ↔ ∃ (c : G) (hc : c ∈ centralizer ({x} : Set G)), c ∈ H ∧
      (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) = y := by
  rw [twoSecMap, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, hcy⟩
    exact ⟨(c : G), c.2, (Subgroup.mem_subgroupOf).1 hc, hcy⟩
  · rintro ⟨c, hc, hcH, rfl⟩
    exact ⟨⟨c, hc⟩, (Subgroup.mem_subgroupOf).2 hcH, rfl⟩

theorem GElt.mem_centralizer_x₂ (hC : CentData z ι) (hg : GElt z ι g) :
    g ∈ centralizer ({z * ι τ₀} : Set G) :=
  mem_centralizer_singleton_iff.2 (GElt.comm_x₂ hC hg)

private lemma CEgrp_le_centralizer_x₂ (hC : CentData z ι) :
    CEgrp z ι ≤ centralizer ({z * ι τ₀} : Set G) := by
  intro c hc
  rw [mem_centralizer_singleton_iff]
  have hz : c * z = z * c := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).1
  have hx1 : c * ι τ₀ = ι τ₀ * c := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2
  calc c * (z * ι τ₀) = (c * z) * ι τ₀ := by group
    _ = (z * c) * ι τ₀ := by rw [hz]
    _ = z * (c * ι τ₀) := by group
    _ = z * (ι τ₀ * c) := by rw [hx1]
    _ = (z * ι τ₀) * c := by group

private lemma Siggrp_le_centralizer_x₂ (hC : CentData z ι) :
    Siggrp ι ≤ centralizer ({z * ι τ₀} : Set G) :=
  (Siggrp_le_CEgrp hC).trans (CEgrp_le_centralizer_x₂ hC)

private lemma Agrp_le_centralizer_x₂ (hC : CentData z ι) :
    Agrp ι ≤ centralizer ({z * ι τ₀} : Set G) :=
  Agrp_le_Siggrp.trans (Siggrp_le_centralizer_x₂ hC)

private lemma commute_x1_of_mem_centralizer_x₂_of_commute_z (hC : CentData z ι) {c : G}
    (hc : c ∈ centralizer ({z * ι τ₀} : Set G)) (hcz : c * z = z * c) :
    c * ι τ₀ = ι τ₀ * c := by
  calc c * ι τ₀ = c * ((z * z) * ι τ₀) := by rw [hC.mul_self, one_mul]
    _ = c * (z * (z * ι τ₀)) := by rw [mul_assoc]
    _ = (c * z) * (z * ι τ₀) := by rw [← mul_assoc]
    _ = (z * c) * (z * ι τ₀) := by rw [hcz]
    _ = z * (c * (z * ι τ₀)) := by rw [mul_assoc]
    _ = z * ((z * ι τ₀) * c) := by rw [mem_centralizer_singleton_iff.1 hc]
    _ = (z * (z * ι τ₀)) * c := by rw [← mul_assoc]
    _ = ((z * z) * ι τ₀) * c := by rw [← mul_assoc]
    _ = ι τ₀ * c := by rw [hC.mul_self, one_mul]

private lemma mk_z_mul_mk_siggrp (hC : CentData z ι) {s : G} (hs : s ∈ Siggrp ι)
    (hsc : s ∈ centralizer ({z * ι τ₀} : Set G))
    (hzC : z ∈ centralizer ({z * ι τ₀} : Set G)) :
    (QuotientGroup.mk ⟨z, hzC⟩ : TwoSec (z * ι τ₀)) * QuotientGroup.mk ⟨s, hsc⟩ =
      QuotientGroup.mk ⟨s, hsc⟩ * QuotientGroup.mk ⟨z, hzC⟩ := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (Siggrp_le_CEgrp hC hs)).1).symm

private lemma mk_g_mul_mk_siggrp_eq (hC : CentData z ι) (hg : GElt z ι g) {s : G}
    (hs : s ∈ Siggrp ι) (hsc : s ∈ centralizer ({z * ι τ₀} : Set G))
    (hgc : g ∈ centralizer ({z * ι τ₀} : Set G)) :
    (QuotientGroup.mk ⟨g, hgc⟩ : TwoSec (z * ι τ₀)) * QuotientGroup.mk ⟨s, hsc⟩ =
      QuotientGroup.mk ⟨s, hsc⟩ * QuotientGroup.mk ⟨g, hgc⟩ := by
  obtain ⟨ρ, rfl⟩ := mem_Siggrp_iff.mp hs
  obtain ⟨e, he, hconj⟩ := hg.e₀
  set e' : G := if sign ρ = 1 then 1 else e with he'def
  have he'_cases : e' = 1 ∨ e' = z * ι τ₀ := by
    rw [he'def]
    rcases he with he | he
    · left; rw [he]; by_cases h : sign ρ = 1 <;> simp [h]
    · by_cases h : sign ρ = 1
      · left; rw [if_pos h]
      · right; rw [if_neg h, he]
  have he'C : e' ∈ centralizer ({z * ι τ₀} : Set G) := by
    rcases he'_cases with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_centralizer_singleton_iff.2 rfl
  have he'mem : (⟨e', he'C⟩ : ↥(centralizer ({z * ι τ₀} : Set G))) ∈
      Subgroup.zpowers (selfC (z * ι τ₀)) := by
    rw [mem_zpowers_selfC_iff (x₂_mul_self hC)]
    rcases he'_cases with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcomm : (ι (liftS8 ρ)) * e' = e' * (ι (liftS8 ρ)) := by
    rcases he'_cases with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]; exact mem_centralizer_singleton_iff.1 hsc
  have hgs : g * ι (liftS8 ρ) = ι (liftS8 ρ) * e' * g := by
    rw [← hconj ρ]; group
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
  have hdiv : (⟨g, hgc⟩ * ⟨ι (liftS8 ρ), hsc⟩) / (⟨ι (liftS8 ρ), hsc⟩ * ⟨g, hgc⟩) =
      (⟨e', he'C⟩ : ↥(centralizer ({z * ι τ₀} : Set G))) := by
    apply Subtype.ext
    simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g * ι (liftS8 ρ)) / (ι (liftS8 ρ) * g)
        = (ι (liftS8 ρ) * e' * g) / (ι (liftS8 ρ) * g) := by rw [hgs]
      _ = ι (liftS8 ρ) * e' * (ι (liftS8 ρ))⁻¹ := by
        rw [div_eq_mul_inv, mul_inv_rev]
        group
      _ = e' := by rw [hcomm]; group
  rw [hdiv]
  exact he'mem

private lemma zpow_mem_Dgrp (i : ℕ) : z ^ i ∈ Dgrp z g :=
  (Dgrp z g).pow_mem (Subgroup.subset_closure (by simp)) i

private lemma x1_mem_Dgrp (hg : GElt z ι g) : ι τ₀ ∈ Dgrp z g := by
  have hgD : g ∈ Dgrp z g := Subgroup.subset_closure (by simp)
  have hzD : z ∈ Dgrp z g := Subgroup.subset_closure (by simp)
  rw [← hg.conj_z]
  exact (Dgrp z g).mul_mem ((Dgrp z g).mul_mem hgD hzD) ((Dgrp z g).inv_mem hgD)

private lemma mk_mem_sup_of_mem_CEgrp (hC : CentData z ι) (hg : GElt z ι g) {c : G}
    (hcC : c ∈ centralizer ({z * ι τ₀} : Set G)) (hcE : c ∈ CEgrp z ι) :
    (QuotientGroup.mk ⟨c, hcC⟩ : TwoSec (z * ι τ₀)) ∈
      twoSecMap (z * ι τ₀) (Dgrp z g) ⊔ twoSecMap (z * ι τ₀) (Siggrp ι) := by
  obtain ⟨i, j, ρ, hc⟩ := (mem_CEgrp_iff hC).1 hcE
  subst hc
  have hA : z ^ (i : ℕ) ∈ centralizer ({z * ι τ₀} : Set G) :=
    (centralizer ({z * ι τ₀} : Set G)).pow_mem (z_mem_centralizer_x₂ hC) _
  have hB : (ι τ₀) ^ (j : ℕ) ∈ centralizer ({z * ι τ₀} : Set G) :=
    (centralizer ({z * ι τ₀} : Set G)).pow_mem (x₁_mem_centralizer_x₂ hC) _
  have hD : ι (liftS8 ρ) ∈ centralizer ({z * ι τ₀} : Set G) :=
    Siggrp_le_centralizer_x₂ hC (mem_Siggrp_iff.2 ⟨ρ, rfl⟩)
  have hsplit : (⟨z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι (liftS8 ρ), hcC⟩ :
      ↥(centralizer ({z * ι τ₀} : Set G))) =
      ⟨z ^ (i : ℕ), hA⟩ * ⟨(ι τ₀) ^ (j : ℕ), hB⟩ * ⟨ι (liftS8 ρ), hD⟩ :=
    Subtype.ext rfl
  have h1 : (QuotientGroup.mk ⟨z ^ (i : ℕ), hA⟩ : TwoSec (z * ι τ₀)) ∈
      twoSecMap (z * ι τ₀) (Dgrp z g) :=
    (mem_twoSecMap_iff).2 ⟨z ^ (i : ℕ), hA, zpow_mem_Dgrp i, rfl⟩
  have h2 : (QuotientGroup.mk ⟨(ι τ₀) ^ (j : ℕ), hB⟩ : TwoSec (z * ι τ₀)) ∈
      twoSecMap (z * ι τ₀) (Dgrp z g) :=
    (mem_twoSecMap_iff).2 ⟨(ι τ₀) ^ (j : ℕ), hB, (Dgrp z g).pow_mem (x1_mem_Dgrp hg) j, rfl⟩
  have h3 : (QuotientGroup.mk ⟨ι (liftS8 ρ), hD⟩ : TwoSec (z * ι τ₀)) ∈
      twoSecMap (z * ι τ₀) (Siggrp ι) :=
    (mem_twoSecMap_iff).2 ⟨ι (liftS8 ρ), hD, mem_Siggrp_iff.2 ⟨ρ, rfl⟩, rfl⟩
  rw [hsplit, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
  exact (twoSecMap (z * ι τ₀) (Dgrp z g) ⊔ twoSecMap (z * ι τ₀) (Siggrp ι)).mul_mem
    (Subgroup.mem_sup_left ((twoSecMap (z * ι τ₀) (Dgrp z g)).mul_mem h1 h2))
    (Subgroup.mem_sup_right h3)

private lemma disjoint_zpowers_of_order_two {M : Type*} [Group M] {x y : M}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) :
    Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ← hy]; exact pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := by intro h; rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  have hy1 : y ≠ 1 := by intro h; rw [h, orderOf_one] at hy; exact absurd hy (by norm_num)
  rw [Subgroup.disjoint_def]
  intro w hw hw'
  rcases Subgroup.mem_zpowers_iff.mp hw with ⟨m, rfl⟩
  rcases Subgroup.mem_zpowers_iff.mp hw' with ⟨n, hn⟩
  have hmn : x ^ m = y ^ n := hn.symm
  rw [zpow_eq_zpow_emod m hx2, zpow_eq_zpow_emod n hy2] at hmn
  rw [zpow_eq_zpow_emod m hx2]
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · rw [hm, zpow_zero]
  · rw [hm, zpow_one]
    rcases Int.emod_two_eq_zero_or_one n with hn' | hn'
    · rw [hm, hn', zpow_one, zpow_zero] at hmn
      exact absurd hmn hx1
    · rw [hm, hn', zpow_one, zpow_one] at hmn
      exact absurd hmn hxy

theorem mk_mem_centralizer_iff (hC : CentData z ι) (hz : z ∈ centralizer ({z * ι τ₀} : Set G))
    {c : G} (hc : c ∈ centralizer ({z * ι τ₀} : Set G)) :
    (QuotientGroup.mk ⟨c, hc⟩ : TwoSec (z * ι τ₀)) ∈
        centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : TwoSec (z * ι τ₀))} :
          Set (TwoSec (z * ι τ₀))) ↔
      c * z * c⁻¹ = z ∨ c * z * c⁻¹ = ι τ₀ := by
  rw [mem_centralizer_singleton_iff]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
  have hcoe : (((⟨c, hc⟩ * ⟨z, hz⟩) / (⟨z, hz⟩ * ⟨c, hc⟩) :
      ↥(centralizer ({z * ι τ₀} : Set G))) : G) = c * z * c⁻¹ * z⁻¹ := by
    simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [div_eq_mul_inv, mul_inv_rev]
    group
  rw [mem_zpowers_selfC_iff (x₂_mul_self hC), hcoe]
  have h1 : c * z * c⁻¹ * z⁻¹ = 1 ↔ c * z * c⁻¹ = z := by
    rw [inv_eq_of_mul_eq_one_right hC.mul_self]
    constructor
    · intro h
      exact mul_right_cancel (h.trans hC.mul_self.symm)
    · intro h
      rw [h]; exact hC.mul_self
  have h2 : c * z * c⁻¹ * z⁻¹ = z * ι τ₀ ↔ c * z * c⁻¹ = ι τ₀ := by
    rw [inv_eq_of_mul_eq_one_right hC.mul_self]
    have hzτ : z * ι τ₀ * z = ι τ₀ := by
      rw [mul_assoc, ← hC.comm τ₀, ← mul_assoc, hC.mul_self, one_mul]
    constructor
    · intro h
      apply mul_right_cancel (b := z)
      rw [h, hC.comm τ₀]
    · intro h
      rw [h, hC.comm τ₀]
  rw [h1, h2]

private lemma mk_zpow_eq_pow_of_mem {x w : G} {hw : w ∈ centralizer ({x} : Set G)} (n : ℤ) :
    (QuotientGroup.mk ⟨w ^ n, (centralizer ({x} : Set G)).zpow_mem hw n⟩ : TwoSec x) =
      (QuotientGroup.mk ⟨w, hw⟩ : TwoSec x) ^ n := by
  have h : (⟨w ^ n, (centralizer ({x} : Set G)).zpow_mem hw n⟩ :
      ↥(centralizer ({x} : Set G))) = ⟨w, hw⟩ ^ n :=
    Subtype.ext rfl
  rw [h, QuotientGroup.mk_zpow]

private lemma mem_closure_pair_of_commute {M : Type*} [Group M] {x y z : M} (h : Commute x y) :
    z ∈ Subgroup.closure ({x, y} : Set M) ↔ ∃ m n : ℤ, x ^ m * y ^ n = z := by
  constructor
  · intro hz
    refine Subgroup.closure_induction (p := fun g _ => ∃ m n : ℤ, x ^ m * y ^ n = g)
      ?_ ?_ ?_ ?_ hz
    · rintro w (rfl | rfl)
      · exact ⟨1, 0, by rw [zpow_one, zpow_zero, mul_one]⟩
      · exact ⟨0, 1, by rw [zpow_zero, zpow_one, one_mul]⟩
    · exact ⟨0, 0, by rw [zpow_zero, zpow_zero, mul_one]⟩
    · rintro a b _ _ ⟨m, n, rfl⟩ ⟨p, q, rfl⟩
      refine ⟨m + p, n + q, ?_⟩
      have hxy : x ^ p * y ^ n = y ^ n * x ^ p := ((h.zpow_right n).zpow_left p).eq
      calc x ^ (m + p) * y ^ (n + q)
          = (x ^ m * x ^ p) * (y ^ n * y ^ q) := by rw [zpow_add, zpow_add]
        _ = x ^ m * (x ^ p * y ^ n) * y ^ q := by group
        _ = x ^ m * (y ^ n * x ^ p) * y ^ q := by rw [hxy]
        _ = x ^ m * y ^ n * (x ^ p * y ^ q) := by group
    · rintro a _ ⟨m, n, rfl⟩
      refine ⟨-m, -n, ?_⟩
      have hinv : (x ^ m)⁻¹ * (y ^ n)⁻¹ = (y ^ n)⁻¹ * (x ^ m)⁻¹ :=
        ((h.zpow_right n).zpow_left m).inv_left.inv_right.eq
      calc x ^ (-m) * y ^ (-n)
          = (x ^ m)⁻¹ * (y ^ n)⁻¹ := by rw [zpow_neg, zpow_neg]
        _ = (y ^ n)⁻¹ * (x ^ m)⁻¹ := hinv
        _ = (x ^ m * y ^ n)⁻¹ := by rw [mul_inv_rev]
  · rintro ⟨m, n, rfl⟩
    exact Subgroup.mul_mem _
      ((Subgroup.closure ({x, y} : Set M)).zpow_mem (Subgroup.subset_closure (by simp)) m)
      ((Subgroup.closure ({x, y} : Set M)).zpow_mem (Subgroup.subset_closure (by simp)) n)

theorem commutator_twoSecMap_Siggrp (hC : CentData z ι) :
    ⁅twoSecMap (z * ι τ₀) (Siggrp ι), twoSecMap (z * ι τ₀) (Siggrp ι)⁆ =
      twoSecMap (z * ι τ₀) (Agrp ι) := by
  have hSigC : Siggrp ι ≤ centralizer ({z * ι τ₀} : Set G) := Siggrp_le_centralizer_x₂ hC
  have hAC : Agrp ι ≤ centralizer ({z * ι τ₀} : Set G) := Agrp_le_centralizer_x₂ hC
  have hcommG : ⁅Siggrp ι, Siggrp ι⁆ = Agrp ι := by
    unfold Siggrp Agrp
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  have hkey : ⁅(Siggrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G)),
      (Siggrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))⁆ =
      (Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G)) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (centralizer ({z * ι τ₀} : Set G)))
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSigC,
      Subgroup.map_subgroupOf_eq_of_le hAC, hcommG]
  calc ⁅twoSecMap (z * ι τ₀) (Siggrp ι), twoSecMap (z * ι τ₀) (Siggrp ι)⁆
      = ((⁅(Siggrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G)),
          (Siggrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))⁆).map
            (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀))))) := by
        unfold twoSecMap
        rw [← Subgroup.map_commutator]
    _ = ((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
          (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀)))) := by rw [hkey]
    _ = twoSecMap (z * ι τ₀) (Agrp ι) := rfl

theorem swapShape_twoSec (hC : CentData z ι) (hg : GElt z ι g)
    (hz : z ∈ centralizer ({z * ι τ₀} : Set G)) :
    SwapShape (QuotientGroup.mk ⟨z, hz⟩ : TwoSec (z * ι τ₀))
      (twoSecMap (z * ι τ₀) (Siggrp ι)) (twoSecMap (z * ι τ₀) (Dgrp z g)) := by
  classical
  have htau0 : τ₀ ≠ 1 := by decide
  have hgC : g ∈ centralizer ({z * ι τ₀} : Set G) := GElt.mem_centralizer_x₂ hC hg
  have hzι : Commute z (ι τ₀) := (commute_iff_eq z (ι τ₀)).mpr (hC.comm τ₀)
  have hinvιτ : (ι τ₀)⁻¹ = ι τ₀ := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right τ₀_mul_self]
  set t : TwoSec (z * ι τ₀) := QuotientGroup.mk ⟨z, hz⟩ with ht
  set gb : TwoSec (z * ι τ₀) := QuotientGroup.mk ⟨g, hgC⟩ with hgb
  set V : Subgroup (TwoSec (z * ι τ₀)) := twoSecMap (z * ι τ₀) (Dgrp z g) with hV
  set Sg : Subgroup (TwoSec (z * ι τ₀)) := twoSecMap (z * ι τ₀) (Siggrp ι) with hSg
  have hVgen : V = Subgroup.closure ({t, gb} : Set (TwoSec (z * ι τ₀))) := by
    have hDgrpC : Dgrp z g ≤ centralizer ({z * ι τ₀} : Set G) := by
      rw [Dgrp, Subgroup.closure_le]
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hz
      · exact hgC
    have hsub : (Dgrp z g).subgroupOf (centralizer ({z * ι τ₀} : Set G)) =
        Subgroup.closure ({⟨z, hz⟩, ⟨g, hgC⟩} :
          Set ↥(centralizer ({z * ι τ₀} : Set G))) := by
      apply Subgroup.map_injective
        (Subgroup.subtype_injective (centralizer ({z * ι τ₀} : Set G)))
      rw [Subgroup.map_subgroupOf_eq_of_le hDgrpC, MonoidHom.map_closure, Dgrp]
      congr 1
      ext y
      simp
    rw [hV]
    unfold twoSecMap
    rw [hsub, MonoidHom.map_closure]
    congr 1
    ext y
    simp [t, gb]
  have ht2 : t * t = 1 := by
    rw [ht, ← QuotientGroup.mk_mul]
    refine (QuotientGroup.eq_one_iff _).2 ?_
    rw [mem_zpowers_selfC_iff (x₂_mul_self hC)]
    left
    simp only [Subgroup.coe_mul]
    exact hC.mul_self
  have hgb2 : gb * gb = 1 := by
    rw [hgb, ← QuotientGroup.mk_mul]
    refine (QuotientGroup.eq_one_iff _).2 ?_
    rw [mem_zpowers_selfC_iff (x₂_mul_self hC)]
    rcases hg.sq with h | h
    · left; simp only [Subgroup.coe_mul]; exact h
    · right; simp only [Subgroup.coe_mul]; exact h
  have ht_ne_one : t ≠ 1 := by
    rw [ht]
    intro h
    have hmem : (⟨z, hz⟩ : ↥(centralizer ({z * ι τ₀} : Set G))) ∈
        Subgroup.zpowers (selfC (z * ι τ₀)) :=
      (QuotientGroup.eq_one_iff (⟨z, hz⟩ : ↥(centralizer ({z * ι τ₀} : Set G)))).1 h
    rcases (mem_zpowers_selfC_iff (x₂_mul_self hC)).1 hmem with h1 | h1
    · exact hC.ne_z 1 (by rw [map_one]; exact h1.symm)
    · apply htau0
      apply hC.inj
      have hι : ι τ₀ = 1 := by
        calc ι τ₀ = (z * z) * ι τ₀ := by rw [hC.mul_self, one_mul]
          _ = z * (z * ι τ₀) := by rw [mul_assoc]
          _ = z * z := by rw [← h1]
          _ = 1 := hC.mul_self
      rw [hι, map_one]
  have hgb_ne_one : gb ≠ 1 := by
    rw [hgb]
    intro h
    have hmem : (⟨g, hgC⟩ : ↥(centralizer ({z * ι τ₀} : Set G))) ∈
        Subgroup.zpowers (selfC (z * ι τ₀)) :=
      (QuotientGroup.eq_one_iff (⟨g, hgC⟩ : ↥(centralizer ({z * ι τ₀} : Set G)))).1 h
    rcases (mem_zpowers_selfC_iff (x₂_mul_self hC)).1 hmem with h1 | h1
    · change g = 1 at h1
      apply hC.ne_z τ₀
      rw [← hg.conj_z, h1]
      group
    · change g = z * ι τ₀ at h1
      apply hC.ne_z τ₀
      rw [← hg.conj_z, h1, inv_eq_of_mul_eq_one_right (x₂_mul_self hC)]
      calc (z * ι τ₀) * z * (z * ι τ₀)
          = z * (ι τ₀ * z) * (z * ι τ₀) := by group
        _ = z * (z * ι τ₀) * (z * ι τ₀) := by rw [← hC.comm τ₀]
        _ = z * ((z * ι τ₀) * (z * ι τ₀)) := by group
        _ = z * 1 := by rw [x₂_mul_self hC]
        _ = z := by rw [mul_one]
  have ht_ne_gb : t ≠ gb := by
    rw [ht, hgb]
    intro h
    have hmem : (⟨z, hz⟩ : ↥(centralizer ({z * ι τ₀} : Set G)))⁻¹ * ⟨g, hgC⟩ ∈
        Subgroup.zpowers (selfC (z * ι τ₀)) := (QuotientGroup.eq).1 h
    have h1' : z⁻¹ * g = 1 ∨ z⁻¹ * g = z * ι τ₀ := by
      have := (mem_zpowers_selfC_iff (x₂_mul_self hC)).1 hmem
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    rw [inv_eq_of_mul_eq_one_right hC.mul_self] at h1'
    rcases h1' with h1 | h1
    · apply hC.ne_z τ₀
      rw [← hg.conj_z]
      have hg_eq : g = z := mul_left_cancel (h1.trans hC.mul_self.symm)
      rw [hg_eq]
      group
    · apply hC.ne_z τ₀
      rw [← hg.conj_z]
      have hg_eq : g = ι τ₀ := mul_left_cancel h1
      rw [hg_eq, hinvιτ]
      calc ι τ₀ * z * ι τ₀ = z * ι τ₀ * ι τ₀ := by rw [← hC.comm τ₀]
        _ = z * (ι τ₀ * ι τ₀) := by rw [mul_assoc]
        _ = z := by rw [← map_mul, τ₀_mul_self, map_one, mul_one]
  have hcomm_gb_t : gb * t = t * gb := by
    have hgb_cent : gb ∈ centralizer ({t} : Set (TwoSec (z * ι τ₀))) := by
      rw [hgb, ht]
      exact (mk_mem_centralizer_iff hC hz hgC).2 (Or.inr hg.conj_z)
    exact mem_centralizer_singleton_iff.1 hgb_cent
  have ht_order : orderOf t = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact ht2) ht_ne_one
  have hgb_order : orderOf gb = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hgb2) hgb_ne_one
  have hdisj : Disjoint (Subgroup.zpowers t) (Subgroup.zpowers gb) :=
    disjoint_zpowers_of_order_two ht_order hgb_order ht_ne_gb
  let ψ : Perm (Fin 8) →* ↥(centralizer ({z * ι τ₀} : Set G)) :=
    { toFun := fun ρ => ⟨ι (liftS8 ρ), Siggrp_le_centralizer_x₂ hC (mem_Siggrp_iff.2 ⟨ρ, rfl⟩)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun ρ σ => Subtype.ext (by simp [map_mul]) }
  let φ : Perm (Fin 8) →* TwoSec (z * ι τ₀) :=
    (QuotientGroup.mk' (Subgroup.zpowers (selfC (z * ι τ₀)))).comp ψ
  have hψrange : ψ.range = (Siggrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G)) := by
    apply le_antisymm
    · rintro c ⟨ρ, rfl⟩
      exact (Subgroup.mem_subgroupOf).2 (mem_Siggrp_iff.2 ⟨ρ, rfl⟩)
    · intro c hc
      obtain ⟨ρ, hρ⟩ := mem_Siggrp_iff.1 ((Subgroup.mem_subgroupOf).1 hc)
      exact ⟨ρ, Subtype.ext hρ⟩
  have hφrange : φ.range = Sg := by
    rw [show φ = (QuotientGroup.mk' (Subgroup.zpowers (selfC (z * ι τ₀)))).comp ψ from rfl,
      MonoidHom.range_comp, hψrange, hSg]
    rfl
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro ρ hρ
    have hρ' : (QuotientGroup.mk' (Subgroup.zpowers (selfC (z * ι τ₀)))) (ψ ρ) = 1 := hρ
    have hψmem : ψ ρ ∈ Subgroup.zpowers (selfC (z * ι τ₀)) := by
      rw [← QuotientGroup.ker_mk' (N := Subgroup.zpowers (selfC (z * ι τ₀)))]
      exact MonoidHom.mem_ker.2 hρ'
    have h1' : ι (liftS8 ρ) = 1 ∨ ι (liftS8 ρ) = z * ι τ₀ := by
      have := (mem_zpowers_selfC_iff (x₂_mul_self hC)).1 hψmem
      simpa [ψ] using this
    rcases h1' with h1 | h1
    · apply liftS8_injective
      rw [map_one]
      exact hC.inj (by rw [h1, map_one])
    · exfalso
      have hmemS : ι (liftS8 ρ) ∈ Siggrp ι := mem_Siggrp_iff.2 ⟨ρ, rfl⟩
      have hmemE : ι (liftS8 ρ) ∈ Egrp z ι := by
        rw [h1]
        change z * ι τ₀ ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers (ι τ₀)
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) (Subgroup.mem_zpowers (ι τ₀))
      have hbot : ι (liftS8 ρ) ∈ (⊥ : Subgroup G) := by
        have := Subgroup.mem_inf.2 ⟨hmemE, hmemS⟩
        rwa [Egrp_inf_Siggrp hC] at this
      rw [Subgroup.mem_bot] at hbot
      exact x₂_ne_one hC (by rw [← h1, hbot])
  have hiso_sg : Nonempty (Sg ≃* Equiv.Perm (Fin 8)) :=
    ⟨((MonoidHom.ofInjective hφ_inj).trans (MulEquiv.subgroupCongr hφrange)).symm⟩
  have hK : IsKleinFour V := by
    rw [hVgen]
    exact CFSG.Wreathed.isKleinFour_closure_pair ht_order hgb_order hcomm_gb_t.symm hdisj
  haveI : IsKleinFour V := hK
  have hiso_v : Nonempty (V ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
    obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := V)
      (G₂ := Multiplicative (ZMod 2 × ZMod 2))
    exact ⟨e.trans (MulEquiv.prodMultiplicative (G := ZMod 2) (H := ZMod 2))⟩
  have hcent_eq : centralizer ({t} : Set (TwoSec (z * ι τ₀))) = V ⊔ Sg := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
        (N := Subgroup.zpowers (selfC (z * ι τ₀))) y
      have hy' : (QuotientGroup.mk ⟨c.1, c.2⟩ : TwoSec (z * ι τ₀)) ∈
          centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : TwoSec (z * ι τ₀))} :
            Set (TwoSec (z * ι τ₀))) := hy
      rcases (mk_mem_centralizer_iff hC hz c.2).1 hy' with hcz | hcz
      · have hcz_comm : c.1 * z = z * c.1 := by
          calc c.1 * z = (c.1 * z * c.1⁻¹) * c.1 := by group
            _ = z * c.1 := by rw [hcz]
        have hcE : c.1 ∈ CEgrp z ι := by
          rw [CEgrp, Subgroup.mem_inf]
          exact ⟨mem_centralizer_singleton_iff.2 hcz_comm,
            mem_centralizer_singleton_iff.2
              (commute_x1_of_mem_centralizer_x₂_of_commute_z hC c.2 hcz_comm)⟩
        exact mk_mem_sup_of_mem_CEgrp hC hg c.2 hcE
      · set c' : G := g⁻¹ * c.1 with hc'def
        have hc'C : c' ∈ centralizer ({z * ι τ₀} : Set G) :=
          (centralizer ({z * ι τ₀} : Set G)).mul_mem
            ((centralizer ({z * ι τ₀} : Set G)).inv_mem hgC) c.2
        have hc'z : c' * z * c'⁻¹ = z := by
          have h1 : c' * z * c'⁻¹ = g⁻¹ * (c.1 * z * c.1⁻¹) * g := by
            simp only [c']; group
          rw [h1, hcz, ← hg.conj_z]; group
        have hc'z_comm : c' * z = z * c' := by
          calc c' * z = (c' * z * c'⁻¹) * c' := by group
            _ = z * c' := by rw [hc'z]
        have hc'E : c' ∈ CEgrp z ι := by
          rw [CEgrp, Subgroup.mem_inf]
          refine ⟨mem_centralizer_singleton_iff.2 hc'z_comm, mem_centralizer_singleton_iff.2 ?_⟩
          exact commute_x1_of_mem_centralizer_x₂_of_commute_z hC hc'C hc'z_comm
        have hc'mem := mk_mem_sup_of_mem_CEgrp hC hg hc'C hc'E
        have hsplit : (⟨c.1, c.2⟩ : ↥(centralizer ({z * ι τ₀} : Set G))) =
            ⟨g, hgC⟩ * ⟨c', hc'C⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          rw [hc'def]; group
        have hy_eq : (QuotientGroup.mk' (Subgroup.zpowers (selfC (z * ι τ₀)))) c =
            gb * (QuotientGroup.mk' (Subgroup.zpowers (selfC (z * ι τ₀)))) ⟨c', hc'C⟩ := by
          change (QuotientGroup.mk ⟨c.1, c.2⟩ : TwoSec (z * ι τ₀)) =
            gb * (QuotientGroup.mk ⟨c', hc'C⟩ : TwoSec (z * ι τ₀))
          rw [hsplit, QuotientGroup.mk_mul]
        rw [hy_eq]
        have hgbV : gb ∈ V := by
          rw [hgb, hV]
          exact (mem_twoSecMap_iff).2 ⟨g, hgC, Subgroup.subset_closure (by simp), rfl⟩
        exact (V ⊔ Sg).mul_mem (Subgroup.mem_sup_left hgbV) hc'mem
    · rw [sup_le_iff]
      constructor
      · rw [hVgen, Subgroup.closure_le]
        intro a ha
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
        · exact Subgroup.mem_centralizer_singleton_iff.2 hcomm_gb_t
      · intro s hs
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨s₀, hs₀C, hs₀Sig, rfl⟩ := (mem_twoSecMap_iff).1 hs
        exact (mk_z_mul_mk_siggrp hC hs₀Sig hs₀C hz).symm
  have hcomm_eq : ⁅V, Sg⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hVgen, Subgroup.closure_le]
    intro a ha
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro s hs
      obtain ⟨s₀, hs₀C, hs₀Sig, rfl⟩ := (mem_twoSecMap_iff).1 hs
      exact (mk_z_mul_mk_siggrp hC hs₀Sig hs₀C hz).symm
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro s hs
      obtain ⟨s₀, hs₀C, hs₀Sig, rfl⟩ := (mem_twoSecMap_iff).1 hs
      exact (mk_g_mul_mk_siggrp_eq hC hg hs₀Sig hs₀C hgC).symm
  have hinf_eq : V ⊓ Sg = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyV, hySg⟩ := hy
    rw [Subgroup.mem_bot]
    rw [hVgen] at hyV
    obtain ⟨m, n, hmn⟩ := (mem_closure_pair_of_commute hcomm_gb_t.symm).mp hyV
    obtain ⟨s, hsc, hsSig, hs_eq⟩ := (mem_twoSecMap_iff).1 hySg
    obtain ⟨ρ, rfl⟩ := mem_Siggrp_iff.1 hsSig
    obtain ⟨a, ha⟩ : ∃ a : ℤ, a = m % 2 := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℤ, b = n % 2 := ⟨_, rfl⟩
    have ht2z : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
    have hgb2z : gb ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hgb2
    have htm : t ^ m = t ^ a := by rw [ha]; exact zpow_eq_zpow_emod m ht2z
    have hgn : gb ^ n = gb ^ b := by rw [hb]; exact zpow_eq_zpow_emod n hgb2z
    have hb_cases : b = 0 ∨ b = 1 := by rw [hb]; exact Int.emod_two_eq_zero_or_one n
    have hta : (QuotientGroup.mk ⟨z ^ a,
        (centralizer ({z * ι τ₀} : Set G)).zpow_mem hz a⟩ : TwoSec (z * ι τ₀)) = t ^ a :=
      mk_zpow_eq_pow_of_mem (hw := hz) a
    have hga : (QuotientGroup.mk ⟨g ^ b,
        (centralizer ({z * ι τ₀} : Set G)).zpow_mem hgC b⟩ : TwoSec (z * ι τ₀)) = gb ^ b :=
      mk_zpow_eq_pow_of_mem (hw := hgC) b
    have hmul : (QuotientGroup.mk ⟨z ^ a * g ^ b,
        (centralizer ({z * ι τ₀} : Set G)).mul_mem
          ((centralizer ({z * ι τ₀} : Set G)).zpow_mem hz a)
          ((centralizer ({z * ι τ₀} : Set G)).zpow_mem hgC b)⟩ :
        TwoSec (z * ι τ₀)) = t ^ a * gb ^ b := by
      rw [← hta, ← hga, ← QuotientGroup.mk_mul]
      congr 1
    have hy_lift : (QuotientGroup.mk ⟨z ^ a * g ^ b,
        (centralizer ({z * ι τ₀} : Set G)).mul_mem
          ((centralizer ({z * ι τ₀} : Set G)).zpow_mem hz a)
          ((centralizer ({z * ι τ₀} : Set G)).zpow_mem hgC b)⟩ :
        TwoSec (z * ι τ₀)) = QuotientGroup.mk ⟨ι (liftS8 ρ), hsc⟩ := by
      rw [hmul, ← htm, ← hgn, hmn, ← hs_eq]
    have hdiv : z ^ a * g ^ b * (ι (liftS8 ρ))⁻¹ = 1 ∨
        z ^ a * g ^ b * (ι (liftS8 ρ))⁻¹ = z * ι τ₀ := by
      have hmem := (QuotientGroup.eq_iff_div_mem).1 hy_lift
      rw [mem_zpowers_selfC_iff (x₂_mul_self hC)] at hmem
      simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv] using hmem
    rcases hb_cases with hb0 | hb1
    · have hg_b : g ^ b = 1 := by rw [hb0, zpow_zero]
      rw [hg_b, mul_one] at hdiv
      have hsinvE : (ι (liftS8 ρ))⁻¹ ∈ Egrp z ι := by
        rcases hdiv with h | h
        · have hz : (ι (liftS8 ρ))⁻¹ = (z ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
          rw [hz]
          exact (Egrp z ι).inv_mem ((Egrp z ι).zpow_mem
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) a)
        · have hz : (ι (liftS8 ρ))⁻¹ = (z ^ a)⁻¹ * (z * ι τ₀) := by
            have := congrArg (fun t => (z ^ a)⁻¹ * t) h
            simpa using this
          rw [hz]
          exact (Egrp z ι).mul_mem ((Egrp z ι).inv_mem ((Egrp z ι).zpow_mem
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) a))
            (Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) (Subgroup.mem_zpowers (ι τ₀)))
      have hsSig' : (ι (liftS8 ρ))⁻¹ ∈ Siggrp ι :=
        (Siggrp ι).inv_mem (mem_Siggrp_iff.2 ⟨ρ, rfl⟩)
      have hsbot : (ι (liftS8 ρ))⁻¹ ∈ (⊥ : Subgroup G) := by
        have := Subgroup.mem_inf.2 ⟨hsinvE, hsSig'⟩
        rwa [Egrp_inf_Siggrp hC] at this
      rw [Subgroup.mem_bot] at hsbot
      have hs1 : ι (liftS8 ρ) = 1 := inv_eq_one.mp hsbot
      have hs_eq1 : (QuotientGroup.mk ⟨ι (liftS8 ρ), hsc⟩ : TwoSec (z * ι τ₀)) = 1 := by
        refine (QuotientGroup.eq_one_iff _).2 ?_
        rw [mem_zpowers_selfC_iff (x₂_mul_self hC)]
        exact Or.inl hs1
      rw [← hs_eq]
      exact hs_eq1
    · have hg_b : g ^ b = g := by rw [hb1, zpow_one]
      rw [hg_b] at hdiv
      have hsz : ι (liftS8 ρ) ∈ centralizer ({z} : Set G) :=
        (Subgroup.mem_inf.1 (Siggrp_le_CEgrp hC hsSig)).1
      have hsz_comm : ι (liftS8 ρ) * z = z * ι (liftS8 ρ) :=
        mem_centralizer_singleton_iff.1 hsz
      have hcomm_zag : (z ^ a * g) * z = z * (z ^ a * g) := by
        rcases hdiv with h | h
        · have hzag : z ^ a * g = ι (liftS8 ρ) := by
            calc z ^ a * g = (z ^ a * g * (ι (liftS8 ρ))⁻¹) * ι (liftS8 ρ) := by group
              _ = 1 * ι (liftS8 ρ) := by rw [h]
              _ = ι (liftS8 ρ) := by group
          rw [hzag]
          exact hsz_comm
        · have hzag : z ^ a * g = (z * ι τ₀) * ι (liftS8 ρ) := by
            calc z ^ a * g = (z ^ a * g * (ι (liftS8 ρ))⁻¹) * ι (liftS8 ρ) := by group
              _ = (z * ι τ₀) * ι (liftS8 ρ) := by rw [h]
          rw [hzag]
          have hxz : (z * ι τ₀) * z = z * (z * ι τ₀) :=
            (mem_centralizer_singleton_iff.1 (z_mem_centralizer_x₂ hC)).symm
          calc ((z * ι τ₀) * ι (liftS8 ρ)) * z
              = (z * ι τ₀) * (ι (liftS8 ρ) * z) := by group
            _ = (z * ι τ₀) * (z * ι (liftS8 ρ)) := by
                rw [hsz_comm]
            _ = ((z * ι τ₀) * z) * ι (liftS8 ρ) := by group
            _ = (z * (z * ι τ₀)) * ι (liftS8 ρ) := by rw [hxz]
            _ = z * ((z * ι τ₀) * ι (liftS8 ρ)) := by group
      have hconj : (z ^ a * g) * z * (z ^ a * g)⁻¹ = ι τ₀ := by
        calc (z ^ a * g) * z * (z ^ a * g)⁻¹
            = z ^ a * (g * z * g⁻¹) * (z ^ a)⁻¹ := by group
          _ = z ^ a * ι τ₀ * (z ^ a)⁻¹ := by rw [hg.conj_z]
          _ = ι τ₀ := by rw [(hzι.zpow_left a).eq]; group
      have hconj' : (z ^ a * g) * z * (z ^ a * g)⁻¹ = z := by
        rw [hcomm_zag]; group
      exact absurd (by rw [← hconj, hconj'] : ι τ₀ = z) (hC.ne_z τ₀)
  exact ⟨ht_order, hiso_sg, hiso_v, hcent_eq, hcomm_eq, hinf_eq⟩

theorem twoSec_oddCore_eq_bot [Finite G] {L : Subgroup G} (h : Setting G L 10)
    (hC : CentData z ι) : CFSG.oddCore (TwoSec (z * ι τ₀)) = ⊥ :=
  oddCore_twoSec_eq_bot h (orderOf_x₂ hC)

theorem twoSec_isKGroupCat [Finite G] {L : Subgroup G} (h : Setting G L 10)
    (hC : CentData z ι) : CFSG.SectionRank.IsKGroupCat (TwoSec (z * ι τ₀)) :=
  isKGroupCat_twoSec h (x₂_ne_one hC)

end CFSG.OddStandard.AltStdSec.SwapPartner
