module

public import CFSG.GH74.Generic.S3.NbrR
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.y_sq (hnd : NbrData G t p f x y Iw Iv) : y * y = 1 := by
  have := pow_orderOf_eq_one y
  rwa [hnd.y_inv, pow_two] at this

theorem NbrData.y_ne_one (hnd : NbrData G t p f x y Iw Iv) : y ≠ 1 := by
  intro h
  have := hnd.y_inv
  rw [h, orderOf_one] at this
  omega

theorem NbrData.Iv_central (hnd : NbrData G t p f x y Iw Iv) : ∀ i ∈ Iv, i * y = y * i := by
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have hoddF : Odd (Nat.card F) := by
    rw [hF]; exact (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
  exact central_of_involution_of_equiv_sl2 hoddF e hnd.y_Iv hnd.y_sq hnd.y_ne_one

theorem NbrData.Iv_le_centralizer (hnd : NbrData G t p f x y Iw Iv) :
    Iv ≤ centralizer ({y} : Set G) := fun i hi =>
  Subgroup.mem_centralizer_singleton_iff.2 (hnd.Iv_central i hi)

theorem NbrData.Iv_quasisimple (hnd : NbrData G t p f x y Iw Iv) : IsQuasisimple ↥Iv := by
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have h5 := hnd.prime.2.2
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by rw [hF]; omega))

theorem NbrData.x_mem_centralizer_y (hnd : NbrData G t p f x y Iw Iv) :
    x ∈ centralizer ({y} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 hnd.comm.symm

omit [Finite G] in
theorem NbrData.y_mem_centralizer_y (y : G) : y ∈ centralizer ({y} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem NbrData.isPCompIn_Iv (hnd : NbrData G t p f x y Iw Iv) :
    CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) Iv := by
  have hIvC := hnd.Iv_le_centralizer
  have hIvV : Iv ≤ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := fun i hi =>
    ⟨hnd.comp_w.1.1 (hnd.Iv_le hi), hIvC hi⟩
  have hnormalizer : centralizer ({x} : Set G) ≤ normalizer (Iw : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnd.comp_w.1.1).1 hnd.comp_w.2
  have hsubV :
      (Iv.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G))).IsSubnormal := by
    refine isSubnormal_of_normal_chain (B := Iw ⊓ centralizer ({y} : Set G)) ?_ ?_ ?_
    · exact le_inf hnd.Iv_le hIvC
    · intro b hb a ha
      exact hnd.Iv_norm b hb.1 (Subgroup.mem_centralizer_singleton_iff.1 hb.2) a ha
    · intro v hv b hb
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hnormalizer hv.1) b).1 hb.1,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hvy : v * y = y * v := Subgroup.mem_centralizer_singleton_iff.1 hv.2
      have hby : b * y = y * b := Subgroup.mem_centralizer_singleton_iff.1 hb.2
      have hvy' : v⁻¹ * y = y * v⁻¹ := by
        calc v⁻¹ * y = v⁻¹ * y * (v * v⁻¹) := by group
          _ = v⁻¹ * (y * v) * v⁻¹ := by group
          _ = v⁻¹ * (v * y) * v⁻¹ := by rw [hvy]
          _ = y * v⁻¹ := by group
      calc v * b * v⁻¹ * y = v * b * (v⁻¹ * y) := by rw [mul_assoc]
        _ = v * b * (y * v⁻¹) := by rw [hvy']
        _ = v * (b * y) * v⁻¹ := by group
        _ = v * (y * b) * v⁻¹ := by rw [hby]
        _ = (v * y) * b * v⁻¹ := by group
        _ = (y * v) * b * v⁻¹ := by rw [hvy]
        _ = y * (v * b * v⁻¹) := by group
  exact isPCompIn_of_subnormal_block hIvV hsubV hnd.Iv_quasisimple

end Basic

section Pumpup

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.pumpup (hnd : NbrData G t p f x y Iw Iv) :
    ∃ L : Subgroup (barQ ↥(centralizer ({y} : Set G))), CFSG.IsComponent L ∧
      ((conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L = L ∧ S45.barSub y Iv ≤ L) ∨
        (conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L ≠ L ∧
          ∃ hAB : ⁅L, conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L⁆ = ⊥,
            S45.barSub y Iv ≤ (swapDiag hAB).range)) := by
  have hs' := orderOf_mk_centralizer hnd.x_mem_centralizer_y hnd.x_inv
  have hB := hnd.isPCompIn_Iv
  have hΛC := le_centralizer_mk hB.1 hnd.x_mem_centralizer_y
  have hΛ := isTwoComponent_centralizer_mk hB hnd.x_mem_centralizer_y
  obtain ⟨-, -, L, hL, hcases, -⟩ := pumpupY_structure hs' hΛC hΛ
  exact ⟨L, hL, hcases⟩

end Pumpup

section Bar

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.proj_injective (hnd : NbrData G t p f x y Iw Iv) :
    Function.Injective ((proj y).comp (Subgroup.inclusion hnd.Iv_le_centralizer) :
      ↥Iv →* CentralizerBar y) := by
  set φ₀ : ↥Iv →* CentralizerBar y := (proj y).comp (Subgroup.inclusion hnd.Iv_le_centralizer)
    with hφ₀
  rw [← MonoidHom.ker_eq_bot_iff]
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have h5 := hnd.prime.2.2
  have hy1 : φ₀ ⟨y, hnd.y_Iv⟩ ≠ 1 := by
    intro h1
    exact hnd.y_ne_one (S45.eq_one_of_proj_eq_one_of_sq (hnd.Iv_le_centralizer hnd.y_Iv) h1 hnd.y_sq)
  have hycen : (⟨y, hnd.y_Iv⟩ : ↥Iv) ∈ Subgroup.center ↥Iv := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hnd.Iv_central g g.2)
  rcases CFSG.ClassicalInvolution.normal_cases_of_equiv_sl2 (by rw [hF]; omega) e.symm φ₀.ker (MonoidHom.normal_ker φ₀) with
    h | h | h
  · exact h
  · exact absurd (h ▸ hycen) (fun hy => hy1 (MonoidHom.mem_ker.1 hy))
  · exact absurd (show (⟨y, hnd.y_Iv⟩ : ↥Iv) ∈ φ₀.ker by rw [h]; trivial) (fun hy => hy1 hy)

theorem NbrData.barSub_equiv (hnd : NbrData G t p f x y Iw Iv) :
    ∃ φ : ↥Iv ≃* ↥(S45.barSub y Iv),
      ∀ w : ↥Iv, ((φ w : ↥(S45.barSub y Iv)) : CentralizerBar y) =
        proj y ⟨(w : G), hnd.Iv_le_centralizer w.2⟩ := by
  set φ₀ : ↥Iv →* CentralizerBar y := (proj y).comp (Subgroup.inclusion hnd.Iv_le_centralizer)
    with hφ₀
  have hrange : φ₀.range = S45.barSub y Iv := by
    ext c
    constructor
    · rintro ⟨j, rfl⟩
      exact S45.proj_mem_barSub (hnd.Iv_le_centralizer j.2) j.2
    · intro hc
      obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 hc
      exact ⟨⟨g, hgJ⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hnd.proj_injective).trans (MulEquiv.subgroupCongr hrange),
    fun w => rfl⟩

theorem NbrData.barSub_isQuasisimple (hnd : NbrData G t p f x y Iw Iv) :
    IsQuasisimple ↥(S45.barSub y Iv) := by
  obtain ⟨φ, -⟩ := hnd.barSub_equiv
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hnd.Iv_quasisimple

theorem NbrData.xbar_mem_barSub (hnd : NbrData G t p f x y Iw Iv) : xbar y ∈ S45.barSub y Iv :=
  S45.proj_mem_barSub (NbrData.y_mem_centralizer_y y) hnd.y_Iv

theorem NbrData.xbar_ne_one (hnd : NbrData G t p f x y Iw Iv) : xbar y ≠ 1 :=
  CFSG.GH74.L5U5.xbar_ne_one hnd.y_inv

theorem NbrData.xbar_mem_center_barSub (hnd : NbrData G t p f x y Iw Iv) :
    (⟨xbar y, hnd.xbar_mem_barSub⟩ : ↥(S45.barSub y Iv)) ∈ Subgroup.center ↥(S45.barSub y Iv) := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.1 (xbar_mem_center y) g)

theorem NbrData.center_barSub_ne_bot (hnd : NbrData G t p f x y Iw Iv) :
    Subgroup.center ↥(S45.barSub y Iv) ≠ ⊥ := by
  intro h
  have := hnd.xbar_mem_center_barSub
  rw [h, Subgroup.mem_bot] at this
  exact hnd.xbar_ne_one (congrArg Subtype.val this)

theorem NbrData.barSub_inB2 (hnd : NbrData G t p f x y Iw Iv) :
    GLS.InB2 ↥(S45.barSub y Iv) := by
  obtain ⟨φ, -⟩ := hnd.barSub_equiv
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have hoddF : Odd (Nat.card F) := by
    rw [hF]; exact (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
  refine ⟨⟨hnd.barSub_isQuasisimple, Or.inr (Or.inl ⟨F, hFf, hFfin, hoddF, ⟨?_⟩⟩)⟩,
    hnd.center_barSub_ne_bot⟩
  exact (φ.symm.trans e.symm).trans
    (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F).symm

end Bar

end CFSG.GH74.Generic.S3
