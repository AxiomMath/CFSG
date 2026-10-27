module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureEmbed
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamily
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthRefl

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.Classical2 CFSG.StandardType.QTwo CFSG.ClassicalGroups.Unitary
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem herm_eq_one_of_Qn_eq_one {n : ℕ} {x : Fin n → K} (h : Qn E n x = 1) :
    herm (unitaryInvolution K 2 f) x x = 1 := by
  have h1 := algebraMap_Qn E n x
  rw [h, map_one] at h1
  calc
    herm (unitaryInvolution K 2 f) x x =
        ∑ i, unitaryInvolution K 2 f (x i) * x i := rfl
    _ = ∑ i, x i * unitaryInvolution K 2 f (x i) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = 1 := h1.symm

theorem orthDerived_Qn_three_eq_su_sup_conj
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (suEndN (F := F) (unitaryInvolution K 2 f) 3).range ⊔
      ((suEndN (F := F) (unitaryInvolution K 2 f) 3).range).map
        (MulAut.conj (tauAt E (Fin.last 2))).toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (Qn E 3) := by
  classical
  let U : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)) :=
    (suEndN (F := F) (unitaryInvolution K 2 f) 3).range
  let r : (Fin 3 → K) ≃ₗ[F] (Fin 3 → K) := tauAt E (Fin.last 2)
  let φ : MulAut ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)) := MulAut.conj r
  let H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)) := U ⊔ U.map φ.toMonoidHom
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) :=
    tauAt_mem_orthogonalGroup E (Fin.last 2)
  have hr2 : r * r = 1 := tauAt_mul_self E (Fin.last 2)
  have hφO : (TauCeti.QuadraticMap.orthogonalGroup (Qn E 3)).map φ.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      simpa [φ, MulAut.conj_apply, r] using
        tauAt_conj_mem_orthogonalGroup E (Fin.last 2) hg
    · intro g hg
      have hg' : r * g * r⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) :=
        tauAt_conj_mem_orthogonalGroup E (Fin.last 2) hg
      have hgg : r * (r * g * r⁻¹) * r⁻¹ = g := by
        rw [inv_eq_of_mul_eq_one_left hr2]
        calc
          r * (r * g * r) * r = (r * r) * g * (r * r) := by group
          _ = g := by rw [hr2]; group
      exact Subgroup.mem_map.mpr ⟨r * g * r⁻¹, hg',
        by simpa [φ, MulAut.conj_apply] using hgg⟩
  have hUO : U ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := by
    rintro _ ⟨g, rfl⟩
    exact suEndN_mem_orthogonalGroup E 3 g
  have hConjO : U.map φ.toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := by
    calc
      U.map φ.toMonoidHom ≤
          (TauCeti.QuadraticMap.orthogonalGroup (Qn E 3)).map φ.toMonoidHom :=
        Subgroup.map_mono hUO
      _ = TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := hφO
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := sup_le hUO hConjO
  have hφφ : ∀ x, φ (φ x) = x := by
    intro x
    calc
      φ (φ x) = r * (r * x * r⁻¹) * r⁻¹ := by
        simp [φ, MulAut.conj_apply]
      _ = x := by
        rw [inv_eq_of_mul_eq_one_left hr2]
        calc
          r * (r * x * r) * r = (r * r) * x * (r * r) := by group
          _ = x := by rw [hr2]; group
  have hφUmap : (U.map φ.toMonoidHom).map φ.toMonoidHom = U := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      simpa [hφφ z] using hz
    · intro x hx
      exact Subgroup.mem_map.mpr
        ⟨φ x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, hφφ x⟩
  have hHmap : H.map φ.toMonoidHom = H := by
    rw [show H = U ⊔ U.map φ.toMonoidHom from rfl, Subgroup.map_sup, hφUmap]
    exact sup_comm _ _
  have hcompO (c : Fin 3) :
      ((suEndN (F := F) (unitaryInvolution K 2 f) 3).comp
        (embSUid (unitaryInvolution K 2 f) c)).range ≤
        TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := by
    rw [MonoidHom.range_comp]
    rintro _ ⟨g, -, rfl⟩
    exact suEndN_mem_orthogonalGroup E 3 g
  have h12 := range_le_commutator_of_su2 E 2 hK hq
    ((suEndN (F := F) (unitaryInvolution K 2 f) 3).comp
      (embSUid (unitaryInvolution K 2 f) 2)) (hcompO 2)
  have h23 := range_le_commutator_of_su2 E 2 hK hq
    ((suEndN (F := F) (unitaryInvolution K 2 f) 3).comp
      (embSUid (unitaryInvolution K 2 f) 0)) (hcompO 0)
  have hUΩ : U ≤ CFSG.RankThree.Classical2.orthDerived (Qn E 3) :=
    range_le_commutator_of_su3 E 2 hK hq
      (suEndN (F := F) (unitaryInvolution K 2 f) 3) h12 h23
  have hφΩ : (CFSG.RankThree.Classical2.orthDerived (Qn E 3)).map φ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (Qn E 3) := by
    change (⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E 3),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E 3)⁆).map φ.toMonoidHom = _
    rw [Subgroup.map_commutator, hφO]
  have hConjΩ : U.map φ.toMonoidHom ≤
      CFSG.RankThree.Classical2.orthDerived (Qn E 3) := by
    calc
      U.map φ.toMonoidHom ≤
          (CFSG.RankThree.Classical2.orthDerived (Qn E 3)).map φ.toMonoidHom :=
        Subgroup.map_mono hUΩ
      _ = CFSG.RankThree.Classical2.orthDerived (Qn E 3) := hφΩ
  have hHΩ : H ≤ CFSG.RankThree.Classical2.orthDerived (Qn E 3) := sup_le hUΩ hConjΩ
  have hΩH : CFSG.RankThree.Classical2.orthDerived (Qn E 3) ≤ H := by
    haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
    haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
    haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
    apply orthDerived_le_of_reflect
      (Q := Qn E 3) (hQ := Qn_polarBilin_nondegenerate E 3)
      (h6 := by norm_num [finrank_Qn E 3])
      (H := H) hHO (v₀ := Pi.single (Fin.last 2) 1) (hv₀ := Qn_single_one E (Fin.last 2))
    · intro h hh
      have hφh : φ h ∈ H := by
        rw [← hHmap]
        exact Subgroup.mem_map_of_mem φ.toMonoidHom hh
      have hconj : r * h * r ∈ H := by
        rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_left hr2] at hφh
        exact hφh
      have hrefl : CFSG.ClassicalGroups.Orthogonal.reflect (Qn E 3)
          (Pi.single (Fin.last 2) 1) = r := (tauAt_eq_reflect E (Fin.last 2)).symm
      rw [hrefl]
      exact hconj
    · intro w hw
      have hσ : IsUnitaryInvolution (unitaryInvolution K 2 f) :=
        isUnitaryInvolution_unitaryInvolution hK
      have hs : ∃ s : K, s ≠ 0 ∧ unitaryInvolution K 2 f s * s ≠ 1 :=
        exists_norm_ne_one (p := 2) (f := f) hK (pow_ne_two_of_four_le hq)
      obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_norm_one hσ (n := 3)
        (Or.inr ⟨by norm_num, hs⟩)
        (herm_eq_one_of_Qn_eq_one E (Qn_single_one E (Fin.last 2)))
        (herm_eq_one_of_Qn_eq_one E hw)
      exact ⟨suEndN (F := F) (unitaryInvolution K 2 f) 3 t,
        Subgroup.mem_sup_left ⟨t, rfl⟩, by rw [suEndN_apply]; exact ht⟩
  change H = CFSG.RankThree.Classical2.orthDerived (Qn E 3)
  exact le_antisymm hHΩ hΩH

private theorem suEndN_blockEmb3_succEmb_three
    (A : SUid (unitaryInvolution K 2 f) 3) :
    suEndN (F := F) (unitaryInvolution K 2 f) 4
        (blockEmb3 K 2 f 3 (⟨1, by norm_num⟩ : Fin 3) (by norm_num) A) =
      coordExt (F := F) (K := K) (Fin.succEmb 3)
        (suEndN (F := F) (unitaryInvolution K 2 f) 3 A) := by
  classical
  let M : Matrix (Fin 3) (Fin 3) K :=
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  apply LinearEquiv.ext
  intro x
  funext j
  by_cases hj0 : j = 0
  · subst j
    rw [suEndN_apply, smul_def, coe_coe_blockEmb3,
      blockMat_mulVec_of_not_mem (i := 1) (k := 3) _ _ (by norm_num)]
    rw [coordExt_apply, Function.extend_apply' _ _ _ (by
      rintro ⟨i, hi⟩
      exact Fin.succ_ne_zero i (by simpa [Fin.succEmb] using hi))]
  · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
    rw [suEndN_apply, smul_def, coe_coe_blockEmb3]
    rw [show (Fin.succ i : Fin 4) = blockIdx 1 (by norm_num : 1 + 3 ≤ 4) i by
      ext
      simp [blockIdx, Fin.succ]
      omega]
    rw [blockMat_mulVec_blockIdx (i := 1) (k := 3) (h := by norm_num)]
    rw [coordExt_apply]
    rw [show blockIdx 1 (by norm_num : 1 + 3 ≤ 4) i = (Fin.succEmb 3) i by
      ext
      simp [blockIdx, Fin.succEmb]
      omega]
    rw [(Fin.succEmb 3).injective.extend_apply]
    rw [suEndN_apply, smul_def]
    congr 1
    funext y
    congr 1
    exact Fin.ext (by
      simp [blockIdx, Fin.succEmb]
      omega)

private theorem coordExt_conj_last_two
    (u : (Fin 3 → K) ≃ₗ[F] (Fin 3 → K)) :
    coordExt (F := F) (K := K) (Fin.succEmb 3)
        (MulAut.conj (tauAt E (Fin.last 2)) u) =
      MulAut.conj (tauAt E (Fin.last 3))
        (coordExt (F := F) (K := K) (Fin.succEmb 3) u) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [coordExt_tauAt E (Fin.succEmb 3) (Fin.last 2)]
  rfl

theorem stdFamilyΩ_right_edge_range_sup
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 2).range ⊔
      ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 3).range =
        (qnExtΩ E (Fin.succEmb 3)).range := by
  classical
  let e : Fin 3 ↪ Fin 4 := Fin.succEmb 3
  let U : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)) :=
    (suEndN (F := F) (unitaryInvolution K 2 f) 3).range
  let r : (Fin 3 → K) ≃ₗ[F] (Fin 3 → K) := tauAt E (Fin.last 2)
  let φ : MulAut ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)) := MulAut.conj r
  let J : Subgroup ((Fin 4 → K) ≃ₗ[F] (Fin 4 → K)) :=
    CFSG.RankThree.Classical2.orthDerived (Qn E 4)
  let S := stdFamilyΩ E 3 le_rfl hK hq
  change (S.θ 1 2).range ⊔ (S.θ 1 3).range = (qnExtΩ E e).range
  have hchain_range :
      (stdChainTheta (F := F) (f := f) 3 (⟨1, by norm_num⟩ : Fin 3) (by norm_num)).range =
        U.map (coordExt (F := F) (K := K) e) := by
    rw [stdChainTheta, MonoidHom.range_comp]
    apply le_antisymm
    · rintro _ ⟨A, hA, rfl⟩
      obtain ⟨a, rfl⟩ := hA
      exact Subgroup.mem_map.mpr
        ⟨suEndN (F := F) (unitaryInvolution K 2 f) 3 a, ⟨a, rfl⟩,
          (suEndN_blockEmb3_succEmb_three (F := F) (K := K) (f := f) a).symm⟩
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨a, rfl⟩ := hu
      exact ⟨blockEmb3 K 2 f 3 (⟨1, by norm_num⟩ : Fin 3) (by norm_num) a,
        ⟨a, rfl⟩, suEndN_blockEmb3_succEmb_three (F := F) (K := K) (f := f) a⟩
  have hfork_range :
      (stdForkTheta E 3 le_rfl).range =
        (U.map φ.toMonoidHom).map (coordExt (F := F) (K := K) e) := by
    rw [stdForkTheta, MonoidHom.range_comp, hchain_range]
    have hcomp : (stdConj E 3).toMonoidHom.comp (coordExt (F := F) (K := K) e) =
        (coordExt (F := F) (K := K) e).comp φ.toMonoidHom := by
      refine MonoidHom.ext fun u => LinearEquiv.ext fun v => ?_
      funext a
      dsimp only [stdConj, stdTau, φ, r, e]
      exact congrFun (congrArg (fun f : (Fin 4 → K) ≃ₗ[F] (Fin 4 → K) => f v)
        (coordExt_conj_last_two E u).symm) a
    calc
      (U.map (coordExt (F := F) (K := K) e)).map (stdConj E 3).toMonoidHom =
          U.map ((stdConj E 3).toMonoidHom.comp (coordExt (F := F) (K := K) e)) := by
        rw [Subgroup.map_map]
      _ = U.map ((coordExt (F := F) (K := K) e).comp φ.toMonoidHom) := by rw [hcomp]
      _ = (U.map φ.toMonoidHom).map (coordExt (F := F) (K := K) e) := by
        rw [Subgroup.map_map]
  have hθ12_std :
      (S.θ 1 2).range.map J.subtype =
        (stdChainTheta (F := F) (f := f) 3 (⟨1, by norm_num⟩ : Fin 3) (by norm_num)).range := by
    dsimp only [S]
    rw [MonoidHom.map_range, coe_stdFamilyΩ_θ]
    simp only [stdFamilyV_θ]
    rw [show (2 : Fin 4) = Fin.castSucc (⟨2, by norm_num⟩ : Fin 3) from rfl,
      stdTheta_castSucc]
    unfold stdThetaAt
    rw [dif_pos (by norm_num : (1 : Fin 4).val + 1 = (⟨2, by norm_num⟩ : Fin 3).val)]
    rfl
  have hθ13_std :
      (S.θ 1 3).range.map J.subtype = (stdForkTheta E 3 le_rfl).range := by
    dsimp only [S]
    rw [MonoidHom.map_range, coe_stdFamilyΩ_θ]
    simp only [stdFamilyV_θ]
    rw [show (3 : Fin 4) = Fin.last 3 from rfl, stdTheta_last]
  have hcomp_qn : J.subtype.comp (qnExtΩ E e) =
      (coordExt (F := F) (K := K) e).comp
        (CFSG.RankThree.Classical2.orthDerived (Qn E 3)).subtype := by
    refine MonoidHom.ext fun g => LinearEquiv.ext fun v => ?_
    funext a
    exact congrFun (congrArg (fun f : (Fin 4 → K) ≃ₗ[F] (Fin 4 → K) => f v)
      (qnExtΩ_apply E e g)) a
  have hqn_range : ((qnExtΩ E e).range).map J.subtype =
      (CFSG.RankThree.Classical2.orthDerived (Qn E 3)).map
        (coordExt (F := F) (K := K) e) := by
    rw [MonoidHom.map_range, hcomp_qn, MonoidHom.range_comp, Subgroup.range_subtype]
  have htarget : U ⊔ U.map φ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (Qn E 3) := by
    simpa [U, r, φ] using orthDerived_Qn_three_eq_su_sup_conj E hK hq
  rw [← Subgroup.map_subtype_inj (H := J), Subgroup.map_sup, hθ12_std, hθ13_std,
    hchain_range, hfork_range, hqn_range]
  rw [← Subgroup.map_sup, htarget]

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
