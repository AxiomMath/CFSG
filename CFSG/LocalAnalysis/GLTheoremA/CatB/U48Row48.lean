module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Transv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Dict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (fieldFactor4 mem_range_conj_of_fieldFactor4_eq_one
  SU4 fieldSU4 fieldFactor4)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K)
open scoped Pointwise

noncomputable def eSU4 : SU4 ≃* unitarySU 2 3 K 4 :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU card_K 4)

theorem cenIn_one (r : ℕ) [Fact r.Prime] {H : Type} [Group H] [Finite H] : CenIn r (1 : H) := by
  obtain ⟨Q, -⟩ := IsPGroup.exists_le_sylow (P := (⊥ : Subgroup H)) IsPGroup.of_bot
  refine (cenIn_iff_maxP 1).mpr ⟨Q, MaxP.of_sylow Q, (Q : Subgroup H).one_mem, fun u _ => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp

section Descent

variable {f : ℕ} {F : Type} [Field F]

theorem descent_transvection (h : UnitaryFieldData 2 f F) (S : Subfield F)
    (hS : ∀ x ∈ S, h.bar x = x ^ 2) {w : Fin 4 → F} {c : F} (hw : IsIsoVec h w) (hc : c ≠ 0)
    (hcb : h.bar c = c) (hent : ∀ i j, (tvMat h w c) i j ∈ S) :
    ∃ b : Fin 4 → F, (∀ i, b i ∈ S) ∧ IsIsoVec h b ∧ tvMat h w c = tvMat h b 1 := by
  obtain ⟨hw0, hwn⟩ : w ≠ 0 ∧ vnorm h w = 0 := hw
  obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := Function.ne_iff.mp hw0
  have hlam0 : c * h.bar (w j₀) ≠ 0 := mul_ne_zero hc ((map_ne_zero h.bar).mpr hj₀)
  set lam : F := c * h.bar (w j₀) with hlamdef
  let b : Fin 4 → F := fun i => tvMat h w c i j₀ - (1 : Matrix (Fin 4) (Fin 4) F) i j₀
  have hb : ∀ i, b i = lam * w i := by
    intro i
    simp only [b, tvMat, wMat, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      hlamdef]
    ring
  have hbS : ∀ i, b i ∈ S := by
    intro i
    simp only [b]
    refine S.sub_mem (hent i j₀) ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have hbeq : b = lam • w := funext fun i => by simp [hb]
  have hbj₀ : b j₀ ≠ 0 := by rw [hb]; exact mul_ne_zero hlam0 hj₀
  obtain ⟨i₀, hi₀⟩ : ∃ i, b i ≠ 0 := ⟨j₀, hbj₀⟩
  have hbiso : IsIsoVec h b := by
    show b ≠ 0 ∧ vnorm h b = 0
    refine ⟨fun h0 => hbj₀ (by rw [h0]; rfl), ?_⟩
    rw [hbeq, vnorm_smul, hwn, mul_zero]
  set c' : F := c * (lam⁻¹ * h.bar lam⁻¹) with hc'def
  have hw' : w = lam⁻¹ • b := by
    rw [hbeq, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have h1 : tvMat h w c = tvMat h b c' := by
    rw [hw', tvMat_smul_vec]
  have hc'0 : c' ≠ 0 := mul_ne_zero hc (mul_ne_zero (inv_ne_zero hlam0)
    ((map_ne_zero _).mpr (inv_ne_zero hlam0)))
  have hcS : c' ∈ S := by
    have e1 : (tvMat h b c') i₀ j₀ ∈ S := h1 ▸ hent i₀ j₀
    have e0 : (1 : Matrix (Fin 4) (Fin 4) F) i₀ j₀ ∈ S := by
      rw [Matrix.one_apply]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have e2 : c' * (b i₀ * h.bar (b j₀)) ∈ S := by
      have := S.sub_mem e1 e0
      simpa [tvMat, wMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc] using this
    have hbarb : h.bar (b j₀) ∈ S := by
      rw [hS _ (hbS j₀)]
      exact S.pow_mem (hbS j₀) 2
    have e3 : b i₀ * h.bar (b j₀) ∈ S := S.mul_mem (hbS i₀) hbarb
    have e4 : b i₀ * h.bar (b j₀) ≠ 0 :=
      mul_ne_zero hi₀ ((map_ne_zero _).mpr hbj₀)
    have hdecomp : c' = (c' * (b i₀ * h.bar (b j₀))) * (b i₀ * h.bar (b j₀))⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ e4, mul_one]
    rw [hdecomp]
    exact S.mul_mem e2 (S.inv_mem e3)
  have hc'b : h.bar c' = c' := by
    rw [hc'def, map_mul, map_mul, map_inv₀, map_inv₀, h.bar_bar, hcb]
    ring
  have hc'1 : c' = 1 := by
    have h2 : c' ^ 2 = c' := by rw [← hS c' hcS, hc'b]
    have h3 : c' * (c' - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact absurd h0 hc'0
    · linear_combination h0
  refine ⟨b, hbS, hbiso, ?_⟩
  rw [h1, hc'1]

end Descent

section FieldFix

open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K)

theorem pow_four_of_mem_fixField {φ : K ≃+* K} (hφ : orderOf φ = 3) {x : K}
    (hx : x ∈ fixField φ) : x ^ 4 = x := by
  haveI := Fintype.ofFinite (fixField φ)
  have h4 := FiniteField.pow_card (⟨x, hx⟩ : fixField φ)
  rw [← Nat.card_eq_fintype_card, card_fixField hφ] at h4
  simpa using congrArg Subtype.val h4

theorem bar_of_mem_fixField {φ : K ≃+* K} (hφ : orderOf φ = 3) {x : K} (hx : x ∈ fixField φ) :
    hK.bar x = x ^ 2 := by
  rw [UnitaryFieldData.bar_apply]
  have h4 := pow_four_of_mem_fixField hφ hx
  calc x ^ 2 ^ 3 = (x ^ 4) ^ 2 := by rw [← pow_mul]; norm_num
    _ = x ^ 2 := by rw [h4]

theorem map_tvMat_fix {φ : K ≃+* K} (hφ : orderOf φ = 3) (v : Fin 4 → fixField φ) :
    (tvMat (unitaryFieldData_fixField hφ) v 1).map (fixField φ).subtype =
      tvMat hK (fun i => (v i : K)) 1 := by
  have hb : ∀ j, ((unitaryFieldData_fixField hφ).bar (v j) : K) = hK.bar (v j : K) := by
    intro j
    rw [bar_of_mem_fixField hφ (v j).2, UnitaryFieldData.bar_apply]
    push_cast
    norm_num
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [tvMat, wMat, hb]
  · simp [tvMat, wMat, Matrix.one_apply, hij, hb]

end FieldFix

section Row48


theorem u48CentInvFieldAt_holds (G : Type) [Group G] [Finite G] : U48CentInvFieldAt G := by
  intro X L b z hL hcat hFO _hz2 hzC hzb
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hFO.1
  have hcatP := catalogIs_psimple hL hcat
  obtain ⟨hγ3, hγ1⟩ := dict_outer hcatP hFO (psModel hL hcat) (indAut (lModel hcat) b hb)
    (indAut_psModel hL hcat b hb)
  have hff : fieldFactor4 (indAut (lModel hcat) b hb) ≠ 1 := fun h =>
    hγ1 (mem_range_conj_of_fieldFactor4_eq_one h)
  have hzL : z ∈ L := hzC.1
  have hzLC : z ∈ L ⊓ Subgroup.centralizer ({b} : Set G) := ⟨hzL, hzb⟩
  rw [isCentralIn_iff_cenIn 2 _ hzLC]
  have hkey : CenIn 2 (centEquiv (lModel hcat) b hb ⟨z, hzLC⟩) := by
    set γ := indAut (lModel hcat) b hb with hγdef
    set φ := fieldFactor4 γ with hφdef
    have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hγ3, map_one]
    have hφord : orderOf φ = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime hφ3 hff
    have hζ : CenIn 2 (lModel hcat ⟨z, hzL⟩) :=
      CenIn.congr (lModel hcat) ((isCentralIn_iff_cenIn 2 L hzL).mp hzC)
    obtain ⟨ζ, hζdef⟩ : ∃ ζ : SU4, ζ = lModel hcat ⟨z, hzL⟩ := ⟨_, rfl⟩
    rw [← hζdef] at hζ
    have hγζ : γ ζ = ζ := by
      rw [hζdef, hγdef, indAut_apply]
      congr 1
      exact (conjL_eq_iff b hb ⟨z, hzL⟩).mpr hzb
    obtain ⟨h₀, hh₀⟩ := exists_conj_fieldSU4 hγ3 hff
    obtain ⟨z', hz'def⟩ : ∃ z' : SU4, z' = h₀⁻¹ * ζ * h₀ := ⟨_, rfl⟩
    have hζz' : h₀ * z' * h₀⁻¹ = ζ := by rw [hz'def]; group
    have hz'F : fieldSU4 φ z' = z' := by
      have h1 := hh₀ z'
      rw [hζz', hγζ, ← hφdef] at h1
      have h2 : fieldSU4 φ z' = h₀⁻¹ * ζ * h₀ := by
        rw [h1]
        group
      rw [h2, ← hz'def]
    have hfix : z' ∈ fixSub (fieldSU4 φ) := mem_fixSub.mpr hz'F
    have hz'C : CenIn 2 z' := by
      have := CenIn.congr (MulAut.conj h₀⁻¹) hζ
      rw [hz'def]
      convert this using 1
      simp [MulAut.conj_apply]
    rcases (cenIn_two_iff hK (eSU4 z')).mp (CenIn.congr eSU4 hz'C) with h1 | ⟨w, c, hw, hc0, hcb, hwc⟩
    · have hz'1 : z' = 1 := Subtype.ext (by simpa using h1)
      have hζ1 : ζ = 1 := by rw [← hζz', hz'1, mul_one, mul_inv_cancel]
      have hval1 : centEquiv (lModel hcat) b hb ⟨z, hzLC⟩ = 1 := by
        apply Subtype.ext
        show lModel hcat ⟨z, hzL⟩ = 1
        rw [← hζdef, hζ1]
      rw [hval1]
      exact cenIn_one 2
    · have hent : ∀ i j, (tvMat hK w c) i j ∈ fixField φ := by
        intro i j
        rw [← hwc]
        exact mem_fixField.mpr (entry_fixed_of_mem_fixSub hfix i j)
      obtain ⟨b₀, hb₀S, hb₀iso, htv⟩ :=
        descent_transvection hK (fixField φ) (fun x hx => bar_of_mem_fixField hφord hx) hw hc0 hcb
          hent
      obtain ⟨hb0, hbn⟩ : b₀ ≠ 0 ∧ vnorm hK b₀ = 0 := hb₀iso
      obtain ⟨bS, hbS⟩ : ∃ bS : Fin 4 → fixField φ, ∀ i, (bS i : K) = b₀ i :=
        ⟨fun i => ⟨b₀ i, hb₀S i⟩, fun i => rfl⟩
      have hSdata := unitaryFieldData_fixField hφord
      have hbSne : bS ≠ 0 := by
        intro h0
        apply hb0
        funext i
        have h3 := congrFun h0 i
        rw [← hbS i, h3]
        rfl
      have hbS_bar : ∀ i, ((hSdata.bar (bS i) : fixField φ) : K) = hK.bar (b₀ i) := by
        intro i
        rw [bar_of_mem_fixField hφord (hb₀S i), UnitaryFieldData.bar_apply, ← hbS i]
        push_cast
        norm_num
      have hvnS : vnorm hSdata bS = 0 := by
        apply Subtype.ext
        rw [show ((0 : fixField φ) : K) = 0 from rfl, ← hbn]
        unfold vnorm
        simp [hbS, hbS_bar]
      have hM0mem : tvGL hSdata bS 1 hvnS ∈ unitarySU 2 1 (fixField φ) 4 := by
        rw [CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU]
        exact tvGL_mem hSdata hvnS (map_one _)
      have hcenS : CenIn 2 (⟨tvGL hSdata bS 1 hvnS, hM0mem⟩ : unitarySU 2 1 (fixField φ) 4) :=
        (cenIn_two_iff hSdata _).mpr (Or.inr ⟨bS, 1, (show IsIsoVec hSdata bS from ⟨hbSne, hvnS⟩),
          one_ne_zero, map_one _, rfl⟩)
      have hSF : Nat.card (fixField φ) = (2 ^ 1) ^ 2 := by
        rw [card_fixField hφord]
        norm_num
      let eS : unitarySU 2 1 (fixField φ) 4 ≃* ↥(fixSub (fieldSU4 φ)) :=
        (MulEquiv.subgroupCongr (SUid_eq_statedSU hSF 4).symm).trans (fixSubEquiv hφord)
      have hval : ((eS ⟨tvGL hSdata bS 1 hvnS, hM0mem⟩ : fixSub (fieldSU4 φ)) : SU4) = z' := by
        apply Subtype.ext
        apply Units.ext
        change ((emb (fixField φ) (tvGL hSdata bS 1 hvnS : GL (Fin 4) (fixField φ)) :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (((eSU4 z' : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
        rw [coe_emb, coe_tvGL, map_tvMat_fix hφord bS, hwc, htv]
        congr 1
        funext i
        exact hbS i
      have hcenF : CenIn 2 (⟨z', hfix⟩ : fixSub (fieldSU4 φ)) := by
        have hEq : eS ⟨tvGL hSdata bS 1 hvnS, hM0mem⟩ = ⟨z', hfix⟩ := Subtype.ext hval
        rw [← hEq]
        exact CenIn.congr eS hcenS
      have hconj := CenIn.congr (fixSubEquivOfConj h₀ hh₀) hcenF
      have hEq2 : fixSubEquivOfConj h₀ hh₀ ⟨z', hfix⟩ = centEquiv (lModel hcat) b hb ⟨z, hzLC⟩ := by
        apply Subtype.ext
        show h₀ * z' * h₀⁻¹ = lModel hcat ⟨z, hzL⟩
        rw [hζz', hζdef]
      rw [hEq2] at hconj
      exact hconj
  have := CenIn.congr (centEquiv (lModel hcat) b hb).symm hkey
  rwa [MulEquiv.symm_apply_apply] at this

end Row48

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48

end

