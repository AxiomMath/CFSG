module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs

import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LU5
import CFSG.GroupTheory.CentralExtensionPGroup
import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6 CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartOne.Q1327C (exists_unitary_conj_diag_m)
open Matrix

private theorem card_ZG_ge_three : 3 ≤ Nat.card ZG := by
  let f : F4ˣ → ZG := fun c =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c,
        scalar_mem_primeFormUnitary_one (n := 6) hF4 (norm_units c)⟩,
      mem_ZG.mpr ⟨c, rfl⟩⟩
  have hf : Function.Injective f := by
    intro c d h
    have hval : ((f c : ZG) : Gu) = ((f d : ZG) : Gu) := congrArg Subtype.val h
    have hmat : (Matrix.GeneralLinearGroup.scalar (Fin 6) c :
        Matrix (Fin 6) (Fin 6) F4) =
        (Matrix.GeneralLinearGroup.scalar (Fin 6) d :
          Matrix (Fin 6) (Fin 6) F4) :=
      congrArg (fun g : Gu => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) hval
    have h00 := congrFun (congrFun hmat (0 : Fin 6)) 0
    exact Units.ext (by simpa using h00)
  have h := Nat.card_le_card_of_injective f hf
  have hcard : Nat.card F4ˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, F4.card]
  rwa [hcard] at h

private theorem exists_ne_ne_fin_six (a b : Fin 6) :
    ∃ c : Fin 6, c ≠ a ∧ c ≠ b := by
  have hcard : ({a, b} : Finset (Fin 6)).card <
      (Finset.univ : Finset (Fin 6)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    calc ({a, b} : Finset (Fin 6)).card ≤ 2 := Finset.card_le_two
      _ < 6 := by norm_num
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨c, by simpa using hc⟩

private theorem exists_two_ne_zero_of_sum_cube_eq_zero {x : Fin 6 → F4}
    (hx : x ≠ 0) (hsum : ∑ i, x i ^ 3 = 0) :
    ∃ i₁ i₂ : Fin 6, i₁ ≠ i₂ ∧ x i₁ ≠ 0 ∧ x i₂ ≠ 0 := by
  obtain ⟨i₁, hi₁⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  by_contra h
  have hother : ∀ i, i ≠ i₁ → x i = 0 := by
    intro i hi
    by_contra hxi
    exact h ⟨i, i₁, hi, hxi, hi₁⟩
  have hsum' : ∑ i, x i ^ 3 = x i₁ ^ 3 := by
    refine Finset.sum_eq_single i₁ ?_ ?_
    · intro i _ hi
      rw [hother i hi]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i₁) hi
  rw [hsum'] at hsum
  exact pow_ne_zero 3 hi₁ hsum

private abbrev DiagEq (i₁ i₂ : Fin 6) : Type :=
  {z : Fin 6 → F4ˣ // z i₁ = z i₂}

private def diagTrunc {i₁ i₂ : Fin 6} (z : DiagEq i₁ i₂) :
    {i : Fin 6 // i ≠ i₂} → F4ˣ := fun i => z.1 i.1

private theorem diagTrunc_injective {i₁ i₂ : Fin 6} (hne : i₁ ≠ i₂) :
    Function.Injective (diagTrunc (i₁ := i₁) (i₂ := i₂)) := by
  intro z w h
  apply Subtype.ext
  funext i
  by_cases hi : i = i₂
  · subst i
    calc z.1 i₂ = z.1 i₁ := z.2.symm
      _ = w.1 i₁ := congrFun h ⟨i₁, hne⟩
      _ = w.1 i₂ := w.2
  · exact congrFun h ⟨i, hi⟩

private theorem card_DiagEq_le (i₁ i₂ : Fin 6) (hne : i₁ ≠ i₂) :
    Fintype.card (DiagEq i₁ i₂) ≤ 243 := by
  have hcardSub : Fintype.card {i : Fin 6 // i ≠ i₂} = 5 := by
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter fun i : Fin 6 => i ≠ i₂) =
        Finset.univ.erase i₂ := by
      ext i
      simp
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i₂), Finset.card_univ,
      Fintype.card_fin]
  have hcardFun : Fintype.card ({i : Fin 6 // i ≠ i₂} → F4ˣ) = 243 := by
    rw [Fintype.card_fun, hcardSub, Fintype.card_units, F4.card]
    norm_num
  calc Fintype.card (DiagEq i₁ i₂)
      ≤ Fintype.card ({i : Fin 6 // i ≠ i₂} → F4ˣ) :=
        Fintype.card_le_of_injective (diagTrunc (i₁ := i₁) (i₂ := i₂))
          (diagTrunc_injective hne)
    _ = 243 := hcardFun

private theorem gramForm_idGram_eq_sum_cubes (v : Fin 6 → F4) :
    gramForm hF4 (idGram F4 6) v v = ∑ i, v i ^ 3 := by
  rw [gramForm_apply]
  have h1 : (idGram F4 6 : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v := by
    simpa [idGram] using (Matrix.one_mulVec (v := v))
  rw [h1]
  simp only [dotProduct, UnitaryFieldData.bar_apply hF4]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem mem_center_of_mem_ZG {z : Gu} (hz : z ∈ ZG) :
    z ∈ Subgroup.center Gu := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨c, hc⟩ := mem_ZG.mp hz
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  exact (Matrix.GeneralLinearGroup.scalar_commute c (g : GL (Fin 6) F4)).symm

theorem prFromTwoGroup_holds :
    ∀ A U : Subgroup PGU6,
      (∀ a ∈ A.comap (QuotientGroup.mk' ZG), ∀ b ∈ A.comap (QuotientGroup.mk' ZG), a * b = b * a) →
      (∀ a ∈ A.comap (QuotientGroup.mk' ZG), a ^ 3 = 1) → 81 ≤ Nat.card A →
      IsPGroup 2 U → U ≠ ⊥ → A ≤ Subgroup.normalizer (U : Set PGU6) → ∃ a ∈ A, IsPR a := by
  intro A U hcomm hexp hAcard hU2 hUne hAnorm
  classical
  let Â : Subgroup Gu := A.comap (QuotientGroup.mk' ZG)
  let φ : ↥Â →* ↥A :=
    ((QuotientGroup.mk' ZG).comp Â.subtype).codRestrict A (fun x => x.2)
  have hφsurj : Function.Surjective φ := by
    intro a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective ZG (a : PGU6)
    refine ⟨⟨g, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hg]
      exact a.2
    · apply Subtype.ext
      exact hg
  have hZGA : ZG ≤ Â := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : QuotientGroup.mk' ZG z = 1 := by
      have hzker : z ∈ (QuotientGroup.mk' ZG).ker := by
        rwa [QuotientGroup.ker_mk']
      exact MonoidHom.mem_ker.mp hzker
    rw [hz1]
    exact A.one_mem
  have hker_le : ZG.subgroupOf Â ≤ φ.ker := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show QuotientGroup.mk' ZG (z : Gu) = 1
    exact (QuotientGroup.eq_one_iff (z : Gu)).mpr hz
  have hker3 : 3 ≤ Nat.card φ.ker := by
    have hcard_sub : Nat.card (ZG.subgroupOf Â) = Nat.card ZG :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZGA).toEquiv
    calc 3 ≤ Nat.card ZG := card_ZG_ge_three
      _ = Nat.card (ZG.subgroupOf Â) := hcard_sub.symm
      _ ≤ Nat.card φ.ker := Subgroup.card_le_of_le hker_le
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hrange_card : Nat.card φ.range = Nat.card A := by
    rw [MonoidHom.range_eq_top.mpr hφsurj, Subgroup.card_top]
  have hcardAhat : 243 ≤ Nat.card Â := by
    calc 243 = 3 * 81 := by norm_num
      _ ≤ Nat.card φ.ker * Nat.card A := Nat.mul_le_mul hker3 hAcard
      _ = Nat.card φ.ker * Nat.card φ.range := by rw [← hrange_card]
      _ = Nat.card Â := hmul
  let Û : Subgroup Gu := U.comap (QuotientGroup.mk' ZG)
  let φU : ↥Û →* ↥U :=
    ((QuotientGroup.mk' ZG).comp Û.subtype).codRestrict U (fun x => x.2)
  have hφUsurj : Function.Surjective φU := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective ZG (u : PGU6)
    refine ⟨⟨g, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hg]
      exact u.2
    · apply Subtype.ext
      exact hg
  have hkerU_center : φU.ker ≤ Subgroup.center ↥Û := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : Gu) * (x : Gu) = (x : Gu) * (y : Gu)
    have hxZ : (x : Gu) ∈ ZG := by
      have h1 : QuotientGroup.mk' ZG (x : Gu) = 1 := by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        exact h
      exact (QuotientGroup.eq_one_iff (x : Gu)).mp h1
    exact Subgroup.mem_center_iff.mp (mem_center_of_mem_ZG hxZ) (y : Gu)
  haveI : Group.IsNilpotent ↥U := hU2.isNilpotent
  haveI : Group.IsNilpotent ↥Û := Subgroup.isNilpotent_of_ker_le_center φU hkerU_center
  obtain ⟨Q : Sylow 2 ↥Û⟩ := (inferInstance : Nonempty (Sylow 2 ↥Û))
  have hQne : (Q : Subgroup ↥Û) ≠ ⊥ := by
    have h2U0 : 2 ∣ Nat.card ↥U := by
      obtain ⟨k, hkpos, hk⟩ :=
        hU2.nontrivial_iff_card.mp ((Subgroup.nontrivial_iff_ne_bot U).mpr hUne)
      rw [hk]
      simpa using Nat.pow_dvd_pow 2 hkpos
    have h2U : 2 ∣ Nat.card ↥Û :=
      dvd_trans h2U0 (Subgroup.card_dvd_of_surjective (f := φU) hφUsurj)
    exact Sylow.ne_bot_of_dvd_card Q h2U
  let QG : Subgroup Gu := (Q : Subgroup ↥Û).map Û.subtype
  have hQGp : IsPGroup 2 QG := Q.isPGroup'.map Û.subtype
  have hQGne : QG ≠ ⊥ := by
    intro hbot
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective (f := Û.subtype)
      (H := (Q : Subgroup ↥Û)) Subtype.coe_injective).mp hbot)
  let QG_GL : Subgroup (GL (Fin 6) F4) := QG.map (Subgroup.subtype Gu)
  have hQG_GLp : IsPGroup 2 QG_GL :=
    IsPGroup.map hQGp (Subgroup.subtype Gu)
  have hQG_GLne : QG_GL ≠ ⊥ := by
    intro hbot
    exact hQGne ((Subgroup.map_eq_bot_iff_of_injective (f := Subgroup.subtype Gu)
      (H := QG) Subtype.coe_injective).mp hbot)
  have hQG_GL_le_SU : QG_GL ≤ StatedSU 6 (2 ^ 1) F4 := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨x, hxQ, rfl⟩ := Subgroup.mem_map.mp hq₀
    obtain ⟨k, hk⟩ := Q.isPGroup' (⟨x, hxQ⟩ : ↥(Q : Subgroup ↥Û))
    have hqpow : (x : Gu) ^ 2 ^ k = 1 := by
      have h := congrArg (fun z : ↥(Q : Subgroup ↥Û) => ((z : ↥Û) : Gu)) hk
      simpa using h
    have hqpowGL : (((x : Gu) : GL (Fin 6) F4)) ^ 2 ^ k = 1 := by
      rw [← Subgroup.coe_pow, hqpow, Subgroup.coe_one]
    have hdet : (((x : Gu) : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4).det = 1 :=
      CFSG.ClassicalGroups.SpecialLinear.det_eq_one_of_pow_two_pow_eq_one
        (g := ((x : Gu) : GL (Fin 6) F4)) hqpowGL
    have hgram : ((x : Gu) : GL (Fin 6) F4) ∈ gramSU hF4 (idGram F4 6) :=
      (mem_gramSU_iff_unitary hF4).mpr ⟨(x : Gu).2, hdet⟩
    rwa [gramSU_idGram_six] at hgram
  let QSU : Subgroup (StatedSU 6 (2 ^ 1) F4) :=
    QG_GL.comap (Subgroup.subtype (StatedSU 6 (2 ^ 1) F4))
  have hQSUmap : QSU.map (Subgroup.subtype (StatedSU 6 (2 ^ 1) F4)) = QG_GL := by
    apply Subgroup.map_comap_eq_self
    rwa [Subgroup.range_subtype]
  have hU0p : IsPGroup 2 ↥QSU :=
    hQG_GLp.comap_of_injective (Subgroup.subtype (StatedSU 6 (2 ^ 1) F4))
      Subtype.coe_injective
  have hU0ne : QSU ≠ ⊥ := by
    intro hbot
    exact hQG_GLne (by rw [← hQSUmap, hbot, Subgroup.map_bot])
  have hÂnormÛ : Â ≤ Subgroup.normalizer (Û : Set Gu) := by
    rw [Subgroup.le_normalizer_iff]
    intro â hâ x hx
    rw [Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.le_normalizer_iff.mp hAnorm)
      (QuotientGroup.mk' ZG â) hâ (QuotientGroup.mk' ZG x) hx
  have hÂnormQG : Â ≤ Subgroup.normalizer (QG : Set Gu) := by
    rw [Subgroup.le_normalizer_iff]
    intro â hâ q hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    have hmemÛ : â * (y : Gu) * â⁻¹ ∈ Û :=
      (Subgroup.le_normalizer_iff.mp hÂnormÛ) â hâ (y : Gu) y.2
    have hQnormal : (Q : Subgroup ↥Û).Normal := inferInstance
    obtain ⟨k, hk⟩ := Q.isPGroup' (⟨y, hy⟩ : ↥(Q : Subgroup ↥Û))
    have hqpow : (y : Gu) ^ 2 ^ k = 1 := by
      have h := congrArg (fun z : ↥(Q : Subgroup ↥Û) => ((z : ↥Û) : Gu)) hk
      simpa using h
    have hy2 : (⟨â * (y : Gu) * â⁻¹, hmemÛ⟩ : ↥Û) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      show (â * (y : Gu) * â⁻¹) ^ 2 ^ k = 1
      rw [conj_pow, hqpow]
      simp
    have hyQ : (⟨â * (y : Gu) * â⁻¹, hmemÛ⟩ : ↥Û) ∈ Q :=
      CFSG.GroupTheory.mem_sylow_of_pow_eq_one hQnormal hy2
    exact Subgroup.mem_map.mpr ⟨_, hyQ, rfl⟩
  let E : Subgroup (GL (Fin 6) F4) := Â.map (Subgroup.subtype Gu)
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa using congrArg (Subgroup.subtype Gu) (hcomm a₀ ha₀ b₀ hb₀)
  have hexpE : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    simpa using congrArg (Subgroup.subtype Gu) (hexp e₀ he₀)
  have hE_QSU : ∀ e ∈ E, ∀ u ∈ QSU, ∃ u' ∈ QSU,
      e * (u : GL (Fin 6) F4) * e⁻¹ = (u' : GL (Fin 6) F4) := by
    intro e he u hu
    obtain ⟨â, hâ, rfl⟩ := Subgroup.mem_map.mp he
    have huGL : (u : GL (Fin 6) F4) ∈ QG_GL := Subgroup.mem_comap.mp hu
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp huGL
    have hconjQ : â * q * â⁻¹ ∈ QG :=
      (Subgroup.le_normalizer_iff.mp hÂnormQG) â hâ q hq
    let u' : StatedSU 6 (2 ^ 1) F4 :=
      ⟨((â * q * â⁻¹ : Gu) : GL (Fin 6) F4),
        hQG_GL_le_SU (Subgroup.mem_map.mpr ⟨â * q * â⁻¹, hconjQ, rfl⟩)⟩
    refine ⟨u', ?_, ?_⟩
    · exact Subgroup.mem_comap.mpr
        (Subgroup.mem_map.mpr ⟨â * q * â⁻¹, hconjQ, rfl⟩)
    · rw [← hqeq]
      rfl
  obtain ⟨x, hx0, hxsum, hxeig⟩ :=
    exists_isotropic_common_eigenvector E QSU hE_QSU hcommE hexpE hU0p hU0ne
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag_m hF4 F4_omega_primitive (by norm_num)
    Â hcomm hexp
  let M : Gu → Matrix (Fin 6) (Fin 6) F4 := fun â =>
    (((P⁻¹ * â * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  let d : Gu → Fin 6 → F4 := fun â => (M â).diag
  have hdiag (â : Gu) (hâ : â ∈ Â) : M â = Matrix.diagonal (d â) :=
    (hP â hâ).diagonal_diag.symm
  have hcube (â : Gu) (hâ : â ∈ Â) (i : Fin 6) : d â i ^ 3 = 1 := by
    have h3 : (P⁻¹ * â * P) ^ 3 = 1 := by
      have hâ3 : â ^ 3 = 1 := hexp â hâ
      calc (P⁻¹ * â * P) ^ 3 = P⁻¹ * â ^ 3 * P := by
            simpa [inv_inv] using (conj_pow (a := P⁻¹) (b := â) (i := 3))
        _ = 1 := by rw [hâ3]; simp
    have hmat3 : (M â) ^ 3 = 1 :=
      congrArg (fun g : Gu => (((g : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4))) h3
    have h := congrFun (congrFun hmat3 i) i
    rw [hdiag â hâ, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h
    exact h
  let z (â : ↥Â) : Fin 6 → F4ˣ := fun i =>
    Units.mk0 (d â.1 i) (by
      intro hzero
      have h := hcube â.1 â.2 i
      rw [hzero, zero_pow (by norm_num : 3 ≠ 0)] at h
      exact zero_ne_one h)
  let y : Fin 6 → F4 := ((P⁻¹ : Gu) : GL (Fin 6) F4) • x
  have hy0 : y ≠ 0 := by
    intro hy
    apply hx0
    have hPinv : ((P : Gu) : GL (Fin 6) F4) * ((P⁻¹ : Gu) : GL (Fin 6) F4) = 1 := by
      rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
    have h := congrArg (fun v : Fin 6 → F4 =>
      ((P : Gu) : GL (Fin 6) F4) • v) hy
    simpa [y, smul_smul, hPinv] using h
  have hyform : gramForm hF4 (idGram F4 6) y y = ∑ i, y i ^ 3 :=
    gramForm_idGram_eq_sum_cubes y
  have hxform : gramForm hF4 (idGram F4 6) x x = ∑ i, x i ^ 3 :=
    gramForm_idGram_eq_sum_cubes x
  have hiso : gramForm hF4 (idGram F4 6) y y =
      gramForm hF4 (idGram F4 6) x x := by
    have hmem : ((P⁻¹ : Gu) : GL (Fin 6) F4) ∈
        primeFormUnitary hF4 (idGram F4 6) := (P⁻¹).2
    have h := (gramForm_isometry_iff hF4 (idGram F4 6)
      ((P⁻¹ : Gu) : GL (Fin 6) F4)).mpr (mem_primeFormUnitary.mp hmem) x x
    change gramForm hF4 (idGram F4 6)
        (((P⁻¹ : Gu) : GL (Fin 6) F4) • x)
        (((P⁻¹ : Gu) : GL (Fin 6) F4) • x) =
      gramForm hF4 (idGram F4 6) x x
    exact h
  have hysum : ∑ i, y i ^ 3 = 0 := by
    calc ∑ i, y i ^ 3 = gramForm hF4 (idGram F4 6) y y := hyform.symm
      _ = gramForm hF4 (idGram F4 6) x x := hiso
      _ = ∑ i, x i ^ 3 := hxform
      _ = 0 := hxsum
  have hy_eig : ∀ â : ↥Â, ∃ c : F4, (M â.1) *ᵥ y = c • y := by
    intro â
    obtain ⟨c, hc⟩ := hxeig (Subgroup.subtype Gu â.1)
      (Subgroup.mem_map.mpr ⟨â.1, â.2, rfl⟩)
    refine ⟨c, ?_⟩
    change (((P⁻¹ * â.1 * P : Gu) : GL (Fin 6) F4) •
      (((P⁻¹ : Gu) : GL (Fin 6) F4) • x) =
        c • (((P⁻¹ : Gu) : GL (Fin 6) F4) • x))
    have h1 : ((P⁻¹ * â.1 * P : Gu) : GL (Fin 6) F4) *
        ((P⁻¹ : Gu) : GL (Fin 6) F4) = ((P⁻¹ * â.1 : Gu) : GL (Fin 6) F4) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [smul_smul, h1]
    rw [show ((P⁻¹ * â.1 : Gu) : GL (Fin 6) F4) =
        ((P⁻¹ : Gu) : GL (Fin 6) F4) * ((â.1 : Gu) : GL (Fin 6) F4) from by
      rw [Subgroup.coe_mul]]
    rw [← smul_smul]
    rw [show ((â.1 : Gu) : GL (Fin 6) F4) • x = c • x from hc]
    rw [smul_comm]
  obtain ⟨i₁, i₂, hne, hy1, hy2⟩ :=
    exists_two_ne_zero_of_sum_cube_eq_zero hy0 hysum
  have hz_eq (â : ↥Â) : z â i₁ = z â i₂ := by
    obtain ⟨c, hc⟩ := hy_eig â
    have h1 : d â.1 i₁ * y i₁ = c * y i₁ := by
      have h := congrFun hc i₁
      rw [hdiag â.1 â.2, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
      exact h
    have h2 : d â.1 i₂ * y i₂ = c * y i₂ := by
      have h := congrFun hc i₂
      rw [hdiag â.1 â.2, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
      exact h
    have hd1 : d â.1 i₁ = c := mul_right_cancel₀ hy1 h1
    have hd2 : d â.1 i₂ = c := mul_right_cancel₀ hy2 h2
    apply Units.ext
    show d â.1 i₁ = d â.1 i₂
    rw [hd1, hd2]
  let Φ : ↥Â → DiagEq i₁ i₂ := fun â => ⟨z â, hz_eq â⟩
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have hz : z a = z b := congrArg Subtype.val hab
    have hd : d a.1 = d b.1 := by
      funext i
      have h := congrArg (fun u : Fin 6 → F4ˣ => (u i : F4)) hz
      simpa [z] using h
    have hM : M a.1 = M b.1 := by
      rw [hdiag a.1 a.2, hdiag b.1 b.2]
      exact congrArg Matrix.diagonal hd
    have hconj : P⁻¹ * a.1 * P = P⁻¹ * b.1 * P := by
      apply Subtype.ext
      apply Units.ext
      exact hM
    apply Subtype.ext
    calc (a : Gu) = P * (P⁻¹ * a.1 * P) * P⁻¹ := by group
      _ = P * (P⁻¹ * b.1 * P) * P⁻¹ := by rw [hconj]
      _ = b.1 := by group
  have hcard_domain : Fintype.card ↥Â = Fintype.card (DiagEq i₁ i₂) := by
    have h1 : Nat.card Â = Fintype.card ↥Â := Nat.card_eq_fintype_card
    have h2 : 243 ≤ Fintype.card ↥Â := by rwa [← h1]
    have h3 : Fintype.card ↥Â ≤ Fintype.card (DiagEq i₁ i₂) :=
      Fintype.card_le_of_injective Φ hΦinj
    have h4 : Fintype.card (DiagEq i₁ i₂) ≤ 243 := card_DiagEq_le i₁ i₂ hne
    omega
  have hbij : Function.Bijective Φ :=
    (Fintype.bijective_iff_injective_and_card Φ).2 ⟨hΦinj, hcard_domain⟩
  obtain ⟨i₀, hi₀₁, hi₀₂⟩ := exists_ne_ne_fin_six i₁ i₂
  let ωu : F4ˣ := Units.mk0 F4.ω (by
    intro h0
    have h3 : F4.ω ^ 3 = 1 := by rfl
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at h3
    exact zero_ne_one h3)
  let z₀ : Fin 6 → F4ˣ := Function.update (fun _ => 1) i₀ ωu
  have hz₀ : z₀ i₁ = z₀ i₂ := by
    have h1 : z₀ i₁ = 1 := by
      simp [z₀, Function.update, Ne.symm hi₀₁]
    have h2 : z₀ i₂ = 1 := by
      simp [z₀, Function.update, Ne.symm hi₀₂]
    rw [h1, h2]
  obtain ⟨â₀, hâ₀⟩ := hbij.2 ⟨z₀, hz₀⟩
  refine ⟨QuotientGroup.mk â₀.1, ?_, ?_⟩
  · show QuotientGroup.mk' ZG â₀.1 ∈ A
    exact â₀.2
  · have hω1 : (1 : F4) ≠ F4.ω := by
      intro h
      exact absurd (congrArg F4.code h) (by decide)
    refine ⟨â₀.1, P, 1, F4.ω, i₀, rfl, hω1, ?_⟩
    have hzval : d â₀.1 = Function.update (fun _ => (1 : F4)) i₀ F4.ω := by
      have hz : z â₀ = z₀ := congrArg Subtype.val hâ₀
      funext i
      have h := congrArg (fun u : Fin 6 → F4ˣ => (u i : F4)) hz
      simpa [z, z₀, ωu, Function.update, apply_ite, Units.val_mk0, Units.val_one] using h
    change M â₀.1 = Matrix.diagonal (Function.update (fun _ => (1 : F4)) i₀ F4.ω)
    rw [hdiag â₀.1 â₀.2, hzval]

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
