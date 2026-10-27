module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductPerfect
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section Swap

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem hperf_isSolvable_outer_of_swapDiag {t : G} (htt : t * t = 1) {L G₁ : Subgroup G}
    (hOut : Group.IsSolvable (Outer L)) (hZ : center L = ⊥)
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    Group.IsSolvable (Outer G₁) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcomm : ⁅G₁, G₁.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
    rw [htinv, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.2 h₁₂
  have hdiag : ∀ x : G, x * (t⁻¹ * x * t) = x * (t * x * t⁻¹) := fun x => by rw [htinv]
  have hrange : (Common.diagonalHom G₁ t hcomm).range = L := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [Common.diagonalHom_apply, hdiag]
      exact hδ x x.2
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj y hy
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [Common.diagonalHom_apply, hdiag]
      exact hxy
  set δ := Common.diagonalHom G₁ t hcomm with hδdef
  have hker : δ.ker = center G₁ := by
    refine le_antisymm (Common.ker_diagonalHom_le_center hcomm) ?_
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzL : δ z ∈ L := by
      rw [← hrange]
      exact ⟨z, rfl⟩
    have hmem : (⟨δ z, hzL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      obtain ⟨a, ha⟩ : (l : G) ∈ δ.range := by
        rw [hrange]
        exact l.2
      apply Subtype.ext
      change (l : G) * δ z = δ z * l
      rw [← ha, ← map_mul, ← map_mul, mem_center_iff.1 hz a]
    rw [hZ, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  haveI : Group.IsPerfect G₁ := ⟨hq.1⟩
  let e : G₁ ⧸ center G₁ ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange δ).trans (MulEquiv.subgroupCongr hrange))
  haveI := hOut
  haveI : Group.IsSolvable (Outer (G₁ ⧸ center G₁)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient G₁

theorem hperf_card_sup_zpowers_of_mem_normalizer {t : G} (htt : t * t = 1) {Y : Subgroup G}
    (htN : t ∈ normalizer (Y : Set G)) (htY : t ∉ Y) :
    Nat.card (Y ⊔ zpowers t : Subgroup G) = 2 * Nat.card Y := by
  have hrel := CFSG.SeitzReduction.relIndex_inf_eq_two htt htN htY (le_refl (Y ⊔ zpowers t))
    (mem_sup_right (mem_zpowers t))
  rw [inf_eq_right.2 le_sup_left] at hrel
  have h := Subgroup.relIndex_mul_card Y (Y ⊔ zpowers t)
  rw [inf_eq_left.2 le_sup_left, hrel] at h
  exact h.symm

theorem hperf_odd_card_centralizer_sup_of_not_four_dvd {L G₀ : Subgroup G} {t : G}
    (htt : t * t = 1) (htL : t ∈ centralizer (L : Set G))
    (h4 : ¬ 4 ∣ Nat.card (centralizer (L : Set G)))
    (hq : CFSG.Open.IsQuasisimple G₀)
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y) :
    Odd (Nat.card (centralizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) :
      Set G))) := by
  set G₂ : Subgroup G := G₀.map (MulAut.conj t).toMonoidHom with hG₂
  set D : Subgroup G := G₀ ⊔ G₂ with hD
  set C : Subgroup G := centralizer (D : Set G) with hC
  have hLD : L ≤ D := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)
  have hCL : C ≤ centralizer (L : Set G) := centralizer_le (SetLike.coe_subset_coe.2 hLD)
  have htD : t ∈ normalizer (D : Set G) :=
    CFSG.SeitzReduction.F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
  have htC : t ∈ normalizer (C : Set G) :=
    CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup D htD
  have htnC : t ∉ C := by
    intro htC'
    obtain ⟨hpA, hbA, -⟩ :=
      CFSG.SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
    have hG₁c : G₀ ≤ centralizer (G₀ : Set G) := by
      intro x hx
      have hxt : t * x * t⁻¹ = x := by
        have := mem_centralizer_iff.mp htC' x (mem_sup_left hx)
        calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [← this]
          _ = x := by group
      exact h₁₂ ⟨x, hx, hxt⟩
    exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hG₁c])
  by_contra hodd
  have hev : 2 ∣ Nat.card C := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  have hH := hperf_card_sup_zpowers_of_mem_normalizer htt htC htnC
  have hHL : C ⊔ zpowers t ≤ centralizer (L : Set G) := sup_le hCL (zpowers_le.2 htL)
  apply h4
  refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hHL)
  rw [hH]
  exact Nat.mul_dvd_mul_left 2 hev

theorem hperf_perfect_le_sup_of_swap {L G₀ : Subgroup G} {t : G} (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) (h4 : ¬ 4 ∣ Nat.card (centralizer (L : Set G)))
    (hOut : Group.IsSolvable (Outer L)) (hZ : center L = ⊥)
    (hq : CFSG.Open.IsQuasisimple G₀)
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y) :
    ∀ H : Subgroup G,
      H ≤ normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      ⁅H, H⁆ = H → H ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom := by
  intro H hHN hH
  have hq₂ := CFSG.Fischer.Classification.Recognition.isQuasisimple_map_mulEquiv
    (MulAut.conj t) hq
  have hOut₁ : Group.IsSolvable (Outer G₀) :=
    hperf_isSolvable_outer_of_swapDiag htt hOut hZ hq h₁₂ hδ hsurj
  have hOut₂ : Group.IsSolvable (Outer (G₀.map (MulAut.conj t).toMonoidHom)) := by
    haveI := hOut₁
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (G₀.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)
  exact CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct.perfect_le_of_le_normalizer_sup hq hq₂
    h₁₂ hOut₁ hOut₂
    (hperf_odd_card_centralizer_sup_of_not_four_dvd htt htL h4 hq h₁₂ hsurj) hH hHN

end Swap

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem Hyp.hperf_isSolvable_outer_L (hd : d.Hyp) : Group.IsSolvable (Outer ↥d.L) := by
  rcases hd.setting.model with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
      hcl).2
  all_goals exact absurd h0 (by norm_num)

theorem Hyp.hperf_isSylowOf_zpowers_t (hd : d.Hyp) :
    IsSylowOf 2 (zpowers d.t) (centralizer (d.L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (d.L : Set G) := ⟨d.t, hd.t_mem⟩ with htc
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ← orderOf_coe, pow_one]; exact hd.t_two)
  obtain ⟨P, hPt⟩ := hz.exists_le_sylow
  have htP : tc ∈ P := hPt (mem_zpowers _)
  have hPc := hd.isCyclic_sylow P
  refine ⟨P, le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← hd.sec3_1'.1]
    refine ⟨y.2, mem_centralizer_singleton_iff.2 ?_⟩
    have := hPc.isMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨tc, htP⟩
    exact congrArg (fun z : (P : Subgroup (centralizer (d.L : Set G))) => ((z : _) : G)) this
  · rw [zpowers_le]
    exact ⟨tc, htP, rfl⟩

theorem Hyp.hperf_not_four_dvd_card_centralizer (hd : d.Hyp) :
    ¬ 4 ∣ Nat.card (centralizer (d.L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h4
  have hcard := hd.hperf_isSylowOf_zpowers_t.card_eq
  rw [hd.card_zpowers_t] at hcard
  have hne : Nat.card (centralizer (d.L : Set G)) ≠ 0 := Nat.card_pos.ne'
  have h1 : (Nat.card (centralizer (d.L : Set G))).factorization 2 = 1 :=
    Nat.pow_right_injective (le_refl 2) (hcard.symm.trans (pow_one 2).symm)
  have h2 : 2 ≤ (Nat.card (centralizer (d.L : Set G))).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 (by simpa using h4)
  omega

theorem Hyp.hperf_perfect_le_sup (hd : d.Hyp) {G₀ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₀)
    (h₁₂ : G₀.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (d.t * x * d.t⁻¹) ∈ d.L)
    (hsurj : ∀ y ∈ d.L, ∃ x ∈ G₀, x * (d.t * x * d.t⁻¹) = y) :
    ∀ H : Subgroup G,
      H ≤ normalizer ((G₀ ⊔ G₀.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) →
      ⁅H, H⁆ = H → H ≤ G₀ ⊔ G₀.map (MulAut.conj d.t).toMonoidHom :=
  hperf_perfect_le_sup_of_swap hd.t_mul_t hd.t_mem hd.hperf_not_four_dvd_card_centralizer
    hd.hperf_isSolvable_outer_L hd.setting.center_eq_bot hq h₁₂ hδ hsurj

namespace CaseBData

theorem perfect_le_Hc (hB : d.CaseBHyp) (c : d.CaseBData) (h52 : CaseBData.Sec52 c)
    (H : Subgroup G) (hHN : H ≤ normalizer (c.Hc : Set G)) (hH : ⁅H, H⁆ = H) : H ≤ c.Hc :=
  hB.hyp.hperf_perfect_le_sup h52.quasisimple h52.commute h52.diag_mem h52.diag_surj H hHN hH

end CaseBData

end Data

namespace CaseBParts

theorem perfectNormalizer : PerfectNormalizerStatement :=
  fun _ _ _ _ _ _ _ _ hB c h52 H hHN hH => Data.CaseBData.perfect_le_Hc hB c h52 H hHN hH

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
