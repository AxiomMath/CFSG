module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
import CFSG.Adapters.StatedSLPerfect
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearMat
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups Matrix

private theorem largeEvenScalars_eq_center {d : ℕ} {F : Type} [Field F] :
    LargeEvenScalars (Fin d) F = Subgroup.center (GL (Fin d) F) := by
  rw [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]

private theorem odd_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  refine ⟨2 ^ (m - 1) - 1, ?_⟩
  have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_add, pow_one, mul_comm]
  have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by norm_num)
  omega

private theorem card_scalars_subgroupOf_dvd {d : ℕ} {F : Type} [Field F] [Finite F]
    (H : Subgroup (GL (Fin d) F)) :
    Nat.card ((LargeEvenScalars (Fin d) F).subgroupOf H) ∣ Nat.card F - 1 := by
  have h1 : Nat.card ((LargeEvenScalars (Fin d) F).subgroupOf H) ∣
      Nat.card (LargeEvenScalars (Fin d) F) :=
    Subgroup.card_dvd_of_injective
      ((H.subtype.comp ((LargeEvenScalars (Fin d) F).subgroupOf H).subtype).codRestrict _
        fun x => Subgroup.mem_subgroupOf.mp x.2)
      fun x y hxy => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : LargeEvenScalars (Fin d) F => (z : GL (Fin d) F)) hxy
  have h2 : Nat.card (LargeEvenScalars (Fin d) F) ∣ Nat.card Fˣ := by
    rw [largeEvenScalars_def]
    exact Subgroup.card_range_dvd _
  rw [Nat.card_units] at h2
  exact h1.trans h2

private theorem odd_card_proj_ker {d : ℕ} {F : Type} [Field F] [Finite F]
    (H : Subgroup (GL (Fin d) F)) (hodd : Odd (Nat.card F - 1)) :
    Odd (Nat.card (LargeEvenProjMk H).ker) := by
  have hker : (LargeEvenProjMk H).ker = (LargeEvenScalars (Fin d) F).subgroupOf H :=
    QuotientGroup.ker_mk' _
  rw [hker]
  exact hodd.of_dvd_nat (card_scalars_subgroupOf_dvd H)

private theorem center_proj_eq_bot {d : ℕ} {F : Type} [Field F] (H : Subgroup (GL (Fin d) F))
    (hb : ∀ A : GL (Fin d) F, (∀ u ∈ H, ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) →
      A ∈ LargeEvenScalars (Fin d) F) :
    Subgroup.center (LargeEvenProj H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (N := (LargeEvenScalars (Fin d) F).subgroupOf H) x
  have hg : (g : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
    apply hb
    intro u hu
    have hcentral : QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf H) g *
        QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf H) (⟨u, hu⟩ : ↥H) =
        QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf H) (⟨u, hu⟩ : ↥H) *
        QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf H) g := by
      simpa only [QuotientGroup.mk'_apply] using
        (Subgroup.mem_center_iff.mp hx (⟨u, hu⟩ : ↥H)).symm
    have h1 : QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf H) (g * ⟨u, hu⟩) =
        QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf H) (⟨u, hu⟩ * g) := by
      simpa only [map_mul] using hcentral
    have h2 : g * ⟨u, hu⟩ * (⟨u, hu⟩ * g)⁻¹ ∈
        (LargeEvenScalars (Fin d) F).subgroupOf H := by
      rw [← QuotientGroup.eq_one_iff]
      rw [← QuotientGroup.mk'_apply]
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : ((g * ⟨u, hu⟩ * (⟨u, hu⟩ * g)⁻¹ : ↥H) : GL (Fin d) F) =
        ⁅(g : GL (Fin d) F), u⁆ := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [h3] at h2
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hg)

private def guSubgroup (n d : ℕ) (F : Type) [Field F] [CharP F 2] :
    Subgroup (GL (Fin d) F) where
  carrier := LargeEvenGUSet (Fin d) F (2 ^ n)
  mul_mem' := by
    intro A B hA hB
    obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
    obtain ⟨ν, hν0, hνq, hBν⟩ := hB
    refine ⟨μ * ν, mul_ne_zero hμ0 hν0, by rw [mul_pow, hμq, hνq], ?_⟩
    have hfun : (fun x : F => x ^ (2 ^ n)) = iterateFrobenius F 2 n := by
      funext x; rw [iterateFrobenius_def]
    have hAμ' : Matrix.transpose (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (iterateFrobenius F 2 n)) * ((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        μ • 1 := by
      rw [← hfun]; exact hAμ
    have hBν' : Matrix.transpose (((B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (iterateFrobenius F 2 n)) * ((B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ν • 1 := by
      rw [← hfun]; exact hBν
    change Matrix.transpose (((A * B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (iterateFrobenius F 2 n)) * ((A * B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      (μ * ν) • 1
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    have hassoc : Matrix.transpose (((B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
          (iterateFrobenius F 2 n)) *
          Matrix.transpose (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
          (iterateFrobenius F 2 n)) *
          (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
            ((B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) =
        Matrix.transpose (((B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
          (iterateFrobenius F 2 n)) *
          (Matrix.transpose (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
          (iterateFrobenius F 2 n)) *
            ((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) *
          ((B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by noncomm_ring
    rw [hassoc, hAμ', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hBν', smul_smul,
      mul_comm]
  one_mem' := by
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    change Matrix.transpose (((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (iterateFrobenius F 2 n)) * ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 • 1
    rw [Units.val_one, Matrix.map_one (iterateFrobenius F 2 n) (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul, one_smul]
  inv_mem' := by
    intro A hA
    obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
    refine ⟨μ⁻¹, inv_ne_zero hμ0, by rw [inv_pow, hμq], ?_⟩
    change Matrix.transpose (((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (iterateFrobenius F 2 n)) * ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      μ⁻¹ • 1
    have hAA : ((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hfun : (fun x : F => x ^ (2 ^ n)) = iterateFrobenius F 2 n := by
      funext x; rw [iterateFrobenius_def]
    have hAμ' : Matrix.transpose (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (iterateFrobenius F 2 n)) * ((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        μ • 1 := by
      rw [← hfun]; exact hAμ
    have h1 : (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
          (iterateFrobenius F 2 n))ᵀ =
        μ • ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      calc (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
              (iterateFrobenius F 2 n))ᵀ =
            (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
                (iterateFrobenius F 2 n))ᵀ *
              (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
                ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) := by
            rw [hAA, Matrix.mul_one]
        _ = μ • ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
            rw [← Matrix.mul_assoc, hAμ', Matrix.smul_mul, Matrix.one_mul]
    have h2 : ((((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
          (iterateFrobenius F 2 n))ᵀ) *
        (μ • ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) = 1 := by
      rw [← h1, ← Matrix.transpose_mul, ← Matrix.map_mul, hAA,
        Matrix.map_one (iterateFrobenius F 2 n) (map_zero _) (map_one _), Matrix.transpose_one]
    rw [Matrix.mul_smul] at h2
    rw [← h2, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

theorem proj_ker_le_center {d : ℕ} {F : Type} [Field F] (U : Subgroup (GL (Fin d) F)) :
    (LargeEvenProjMk U).ker ≤ Subgroup.center ↥U := by
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  have hg' : (g : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
    have hker : (LargeEvenProjMk U).ker = (LargeEvenScalars (Fin d) F).subgroupOf U :=
      QuotientGroup.ker_mk' _
    rw [hker] at hg
    exact Subgroup.mem_subgroupOf.mp hg
  have hgc : (g : GL (Fin d) F) ∈ Subgroup.center (GL (Fin d) F) := by
    rw [← largeEvenScalars_eq_center]
    exact hg'
  exact Subgroup.mem_center_iff.mp hgc (h : GL (Fin d) F)

theorem lin_normalizes {d : ℕ} {F : Type} [Field F] (A : GL (Fin d) F) :
    A ∈ Subgroup.normalizer (↑(LargeEvenSLGroup (Fin d) F) : Set (GL (Fin d) F)) := by
  have hker : LargeEvenSLGroup (Fin d) F =
      (Matrix.GeneralLinearGroup.det : GL (Fin d) F →* Fˣ).ker := by
    rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.statedSL_eq_ker_det]
  rw [hker, Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top A

theorem uni_GU_facts {d n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) :
    (∀ A : GL (Fin d) F, A ∈ MGU n d F ↔ A ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) ∧
      MGU n d F ≤
        Subgroup.normalizer (↑(LargeEvenSUGroup (Fin d) F (2 ^ n)) : Set (GL (Fin d) F)) ∧
      LargeEvenScalars (Fin d) F ≤ MGU n d F ∧
      LargeEvenSUGroup (Fin d) F (2 ^ n) ≤ MGU n d F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hlt := Finite.one_lt_card (α := F)
      rw [hF] at hlt
      norm_num at hlt
    · exact hpos
  haveI hUFD : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hn1, by rw [hF, ← pow_mul, Nat.mul_comm n 2]⟩
  haveI hCharP : CharP F 2 := hUFD.charP
  have hMGU : MGU n d F = guSubgroup n d F := by
    rw [MGU]
    exact le_antisymm ((Subgroup.closure_le _).mpr (fun _ hA => hA)) Subgroup.subset_closure
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    rw [hMGU]
    rfl
  · rw [hMGU]
    exact CFSG.StandardType.TableBUE.gu_subset_normalizer (n := n) (d := d) hUFD
  · intro c hc
    rw [hMGU]
    rw [largeEvenScalars_def] at hc
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hc
    refine ⟨(a : F) ^ (2 ^ n + 1), pow_ne_zero _ (Units.ne_zero a), ?_, ?_⟩
    · have hbar : ((a : F) ^ (2 ^ n)) ^ (2 ^ n) = (a : F) := by
        simpa only [UnitaryFieldData.bar_apply] using hUFD.bar_bar (a : F)
      calc ((a : F) ^ (2 ^ n + 1)) ^ (2 ^ n)
          = (a : F) ^ ((2 ^ n + 1) * (2 ^ n)) := by rw [pow_mul]
        _ = (a : F) ^ (2 ^ n * 2 ^ n + 2 ^ n) := by congr 1; ring
        _ = (a : F) ^ (2 ^ n * 2 ^ n) * (a : F) ^ (2 ^ n) := by rw [pow_add]
        _ = (a : F) * (a : F) ^ (2 ^ n) := by rw [pow_mul, hbar]
        _ = (a : F) ^ (2 ^ n) * (a : F) := by rw [mul_comm]
        _ = (a : F) ^ (2 ^ n + 1) := by rw [pow_succ]
    · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      rw [Matrix.diagonal_map (f := fun x : F => x ^ (2 ^ n))
          (by rw [zero_pow (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))]),
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      rw [pow_succ]
  · intro A hA
    rw [hMGU]
    have hform := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hUFD).mp hA
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    have hbarmap : (A : Matrix (Fin d) (Fin d) F).map hUFD.bar =
        (A : Matrix (Fin d) (Fin d) F).map (· ^ (2 ^ n)) := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]
    rw [← hbarmap, hform.2, one_smul]

theorem lin_model_facts {d n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) (hd : 3 ≤ d) :
    Group.IsPerfect ↥(LargeEvenSLGroup (Fin d) F) ∧
      (∀ A : GL (Fin d) F, (∀ u ∈ LargeEvenSLGroup (Fin d) F,
        ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) → A ∈ LargeEvenScalars (Fin d) F) ∧
      Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) = ⊥ ∧
      Odd (Nat.card (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)).ker) := by
  haveI hPerf : Group.IsPerfect ↥(LargeEvenSLGroup (Fin d) F) := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hd F
  have hb : ∀ A : GL (Fin d) F, (∀ u ∈ LargeEvenSLGroup (Fin d) F,
      ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) → A ∈ LargeEvenScalars (Fin d) F := by
    intro A hA
    have hH : ⁅LargeEvenSLGroup (Fin d) F, LargeEvenSLGroup (Fin d) F⁆ =
        LargeEvenSLGroup (Fin d) F :=
      (Subgroup.isPerfect_iff (H := LargeEvenSLGroup (Fin d) F)).1 hPerf
    have hcenter : ∀ u ∈ LargeEvenSLGroup (Fin d) F,
        ⁅A, u⁆ ∈ Subgroup.center (GL (Fin d) F) := by
      intro u hu
      rw [← largeEvenScalars_eq_center]
      exact hA u hu
    have hcomm : ∀ u ∈ LargeEvenSLGroup (Fin d) F, Commute A u :=
      fun u hu => CFSG.StandardType.LinearFieldFix.commute_of_commutator_mem_center hH hcenter hu
    exact CFSG.StandardType.LinearFieldFix.mem_scalars_of_commute_elemSL A
      (fun i j hij => hcomm _
        (CFSG.StandardType.LinearFieldFix.elemSL F hij).2)
  refine ⟨hPerf, hb, ?_, ?_⟩
  · exact center_proj_eq_bot _ hb
  · have hodd : Odd (Nat.card F - 1) := by
      rw [hF]
      exact odd_two_pow_sub_one (by omega)
    exact odd_card_proj_ker _ hodd

theorem uni_model_facts {d n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hdn : d = 3 → 2 ≤ n) :
    Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) ∧
      (∀ A : GL (Fin d) F, (∀ u ∈ LargeEvenSUGroup (Fin d) F (2 ^ n),
        ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) → A ∈ LargeEvenScalars (Fin d) F) ∧
      Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) = ⊥ ∧
      Odd (Nat.card (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))).ker) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hUFD : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hn, by rw [hF, ← pow_mul, Nat.mul_comm n 2]⟩
  haveI hCharP : CharP F 2 := hUFD.charP
  haveI hPerf : Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) := by
    have hnq : (d, 2 ^ n) ≠ (3, 2) := by
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hd3, h2n⟩ := h
      have hn1 : n = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using h2n)
      have := hdn hd3
      omega
    exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := n) (K := F) hF
      (n := d) hd hnq
  have hb : ∀ A : GL (Fin d) F, (∀ u ∈ LargeEvenSUGroup (Fin d) F (2 ^ n),
      ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) → A ∈ LargeEvenScalars (Fin d) F := by
    intro A hA
    have hH : ⁅LargeEvenSUGroup (Fin d) F (2 ^ n), LargeEvenSUGroup (Fin d) F (2 ^ n)⁆ =
        LargeEvenSUGroup (Fin d) F (2 ^ n) :=
      (Subgroup.isPerfect_iff (H := LargeEvenSUGroup (Fin d) F (2 ^ n))).1 hPerf
    have hcenter : ∀ u ∈ LargeEvenSUGroup (Fin d) F (2 ^ n),
        ⁅A, u⁆ ∈ Subgroup.center (GL (Fin d) F) := by
      intro u hu
      rw [← largeEvenScalars_eq_center]
      exact hA u hu
    have hcomm : ∀ u ∈ LargeEvenSUGroup (Fin d) F (2 ^ n), Commute A u :=
      fun u hu => CFSG.StandardType.LinearFieldFix.commute_of_commutator_mem_center hH hcenter hu
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd
      (show 2 ^ n + 1 ≠ 1 by have := Nat.one_le_two_pow (n := n); omega)
    exact CFSG.StandardType.TableBUE.mem_scalars_of_commute (n := n) (d := d) hUFD hr hrdvd
      (fun g hg => (hcomm g hg).eq)
  refine ⟨hPerf, hb, ?_, ?_⟩
  · exact center_proj_eq_bot _ hb
  · have hodd : Odd (Nat.card F - 1) := by
      rw [hF, ← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    exact odd_card_proj_ker _ hodd

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
