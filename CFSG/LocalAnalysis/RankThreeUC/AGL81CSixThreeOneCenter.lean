module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.PCore.Defs
import CFSG.Open.StatedAPI
import CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Flag
import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup

theorem pCore_eq_bot_of_isIrreducibleOn {p : ℕ} [Fact p.Prime] {σ : Type} [Fintype σ]
    [DecidableEq σ] {G : Subgroup (GL σ (ZMod p))}
    (hG : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G) : CFSG.pCore p ↥G = ⊥ := by
  let ρ : ↥G →* ((σ → ZMod p) ≃ₗ[ZMod p] (σ → ZMod p)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp G.subtype)
  refine @CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial.pCore_eq_bot p _
    ↥G (σ → ZMod p) _ _ (Pi.module _ _ _) _ _ ρ ?_ ?_
  · intro a b hab
    exact Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).injective hab))
  · intro W hW
    exact hG W (fun g hg w hw => hW ⟨g, hg⟩ w hw)

theorem isCyclic_center_of_isIrreducibleOn {K : Type} [Field K] [Finite K] {σ : Type} [Fintype σ]
    [DecidableEq σ] [Nonempty σ] {G : Subgroup (GL σ K)}
    (hG : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G) :
    IsCyclic ↥(Subgroup.center ↥G) := by
  classical
  let C := CFSG.RankThree.SubgroupLists.commutant G
  letI : Field C := CFSG.RankThree.SubgroupLists.commutantField hG
  have hmem : ∀ z : ↥G, z ∈ Subgroup.center ↥G → ((z : GL σ K) : Matrix σ σ K) ∈ C := by
    intro z hz
    rw [CFSG.RankThree.SubgroupLists.mem_commutant]
    intro g hg
    have hc := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
    have hgl : (((⟨g, hg⟩ : ↥G)) : GL σ K) * (z : GL σ K) =
        (z : GL σ K) * ((⟨g, hg⟩ : ↥G) : GL σ K) :=
      congrArg (fun u : ↥G => (u : GL σ K)) hc
    simpa only [Units.val_mul] using congrArg (fun u : GL σ K => (u : Matrix σ σ K)) hgl
  let f : ↥(Subgroup.center ↥G) →* Cˣ :=
    { toFun := fun z =>
        Units.mk ⟨((z.1 : GL σ K) : Matrix σ σ K), hmem z.1 z.2⟩
          ⟨((z.1 : GL σ K)⁻¹ : Matrix σ σ K),
            CFSG.RankThree.SubgroupLists.inv_mem_commutant (hmem z.1 z.2)⟩
          (by apply Subtype.ext; simp) (by apply Subtype.ext; simp)
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Units.ext (Subtype.ext (by simp)) }
  haveI : IsCyclic Cˣ := instIsCyclicUnitsOfFinite
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have := congrArg (fun u : Cˣ => ((u : C) : Matrix σ σ K)) hab
    simpa [f] using this
  exact isCyclic_of_injective f hf

theorem eq_neg_one_of_mem_center {K : Type} [Field K] {σ : Type} [Fintype σ] [DecidableEq σ]
    {G : Subgroup (GL σ K)} (hG : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G) {z : ↥G}
    (hz : z ∈ Subgroup.center ↥G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    (z : GL σ K) = -1 :=
  CFSG.LocalAnalysis.UniquenessCase.UC22.K318.eq_neg_one_of_commute hG
    (fun g hg => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩))
    (by simpa [pow_two] using congrArg Subtype.val hz2) (fun h => hz1 (Subtype.ext h))

private theorem exists_orderOf_eq_four_of_isPGroup_two {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (hA : IsPGroup 2 A) (hcard : 2 < Nat.card A) : ∃ y : A, orderOf y = 4 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := A)).mp hA
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n
    · rw [pow_zero] at hn
      omega
    · rw [pow_one] at hn
      omega
    · omega
  have hdvd : 2 ^ 2 ∣ Nat.card A := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn2
  obtain ⟨B, hBcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2 (n := 2) hdvd
  haveI : IsCyclic ↥B := Subgroup.isCyclic B
  obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥B)
  refine ⟨(y : ↥B), ?_⟩
  rw [Subgroup.orderOf_coe, hy, hBcard]
  norm_num

private theorem eq_scalar_two_or_neg_two_of_mem_center_of_sq_eq_neg_one {K : Type} [Field K]
    [Finite K] (h2 : (2 : K) ^ 2 = -1) {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {G : Subgroup (GL σ K)} (hG : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G) {y : ↥G}
    (hy : y ∈ Subgroup.center ↥G) (hy2 : (y : GL σ K) ^ 2 = -1) :
    ((y : GL σ K) : Matrix σ σ K) = Matrix.scalar σ 2 ∨
      ((y : GL σ K) : Matrix σ σ K) = Matrix.scalar σ (-2) := by
  classical
  let C := CFSG.RankThree.SubgroupLists.commutant G
  letI : Field C := CFSG.RankThree.SubgroupLists.commutantField hG
  have hmem : ((y : GL σ K) : Matrix σ σ K) ∈ C := by
    rw [CFSG.RankThree.SubgroupLists.mem_commutant]
    intro g hg
    have hc := Subgroup.mem_center_iff.mp hy ⟨g, hg⟩
    have hgl : (((⟨g, hg⟩ : ↥G)) : GL σ K) * (y : GL σ K) =
        (y : GL σ K) * ((⟨g, hg⟩ : ↥G) : GL σ K) :=
      congrArg (fun u : ↥G => (u : GL σ K)) hc
    simpa only [Units.val_mul] using congrArg (fun u : GL σ K => (u : Matrix σ σ K)) hgl
  let c : C := ⟨((y : GL σ K) : Matrix σ σ K), hmem⟩
  have hc2 : c ^ 2 = -1 := by
    apply Subtype.ext
    simpa [c] using congrArg (fun u : GL σ K => (u : Matrix σ σ K)) hy2
  have h2C : (algebraMap K C 2) ^ 2 = -1 := by
    calc (algebraMap K C 2) ^ 2 = algebraMap K C ((2 : K) ^ 2) := by rw [map_pow]
      _ = algebraMap K C (-1) := by rw [h2]
      _ = -1 := by rw [map_neg, map_one]
  have hc : c = algebraMap K C 2 ∨ c = -algebraMap K C 2 := by
    have h : (c - algebraMap K C 2) * (c + algebraMap K C 2) = 0 := by
      have h' : (c - algebraMap K C 2) * (c + algebraMap K C 2) =
          c ^ 2 - (algebraMap K C 2) ^ 2 := by ring
      rw [h', hc2, h2C]
      ring
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
  have hdiag : ∀ s : K, ((algebraMap K C s : C) : Matrix σ σ K) = Matrix.scalar σ s := by
    intro s
    rw [Subalgebra.coe_algebraMap, Matrix.algebraMap_eq_diagonal]
    simp [Matrix.scalar_apply]
  rcases hc with hc | hc
  · left
    rw [show ((y : GL σ K) : Matrix σ σ K) =
        ((algebraMap K C 2 : C) : Matrix σ σ K) from
      congrArg (fun u : C => (u : Matrix σ σ K)) (by simpa [c] using hc)]
    exact hdiag 2
  · right
    rw [show ((y : GL σ K) : Matrix σ σ K) =
        ((-algebraMap K C 2 : C) : Matrix σ σ K) from
      congrArg (fun u : C => (u : Matrix σ σ K)) (by simpa [c] using hc)]
    rw [← map_neg]
    exact hdiag (-2)

private theorem false_of_mem_center_of_orderOf_eq_four {p : ℕ} [Fact p.Prime] (hp5 : p = 5)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hG : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G) {y : ↥G}
    (hy : y ∈ Subgroup.center ↥G) (hy4 : orderOf y = 4) : False := by
  classical
  have h20 : (2 : ZMod 5) ≠ 0 := by decide
  have h2sq : (2 : ZMod 5) ^ 2 = -1 := by decide
  have h2one : (2 : ZMod 5) ^ 2 ≠ 1 := by decide
  have hn20 : (-2 : ZMod 5) ≠ 0 := by decide
  have hn2one : (-2 : ZMod 5) ^ 2 ≠ 1 := by decide
  subst hp5
  let z : ↥G := y ^ 2
  have hz_center : z ∈ Subgroup.center ↥G := (Subgroup.center ↥G).pow_mem hy 2
  have hz2 : z ^ 2 = 1 := by
    show (y ^ 2) ^ 2 = 1
    rw [← pow_mul, show 2 * 2 = orderOf y by rw [hy4], pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun hz => by
    have h := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 from hz)
    rw [hy4] at h
    norm_num at h
  have hzneg : ((z : ↥G) : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = -1 :=
    eq_neg_one_of_mem_center (K := ZMod 5) (σ := Fin 2 ⊕ Fin 2) hG hz_center hz2 hz1
  have hy2 : (y : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) ^ 2 = -1 := by
    simpa [z] using hzneg
  have hM := eq_scalar_two_or_neg_two_of_mem_center_of_sq_eq_neg_one h2sq hG hy hy2
  have hcontra : ∀ s : ZMod 5, s ≠ 0 → s ^ 2 ≠ 1 →
      ((y : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) =
        Matrix.scalar (Fin 2 ⊕ Fin 2) s → False := by
    intro s hs0 hs hM
    let u : (ZMod 5)ˣ := Units.mk0 s hs0
    have hscalar : (y : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) =
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u := by
      apply Units.ext
      rw [hM]
      simp [u, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hmemSp : (y : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) ∈ CFSG.Open.StatedSp 2 (ZMod 5) :=
      hGS y.2
    rw [hscalar] at hmemSp
    have hu2 : u ^ 2 = 1 :=
      (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 2) (K := ZMod 5) (by norm_num) u).mp
        hmemSp
    apply hs
    have := congrArg (fun v : (ZMod 5)ˣ => (v : ZMod 5)) hu2
    simpa [u] using this
  rcases hM with hM | hM
  · exact hcontra 2 h20 h2one hM
  · exact hcontra (-2) hn20 hn2one hM

theorem card_le_two_of_le_center {p : ℕ} [Fact p.Prime] (hp5 : p = 5)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hG : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G) {A : Subgroup ↥G} (hA : IsPGroup 2 ↥A)
    (hAZ : A ≤ Subgroup.center ↥G) : Nat.card ↥A ≤ 2 := by
  classical
  haveI : IsCyclic ↥(Subgroup.center ↥G) := isCyclic_center_of_isIrreducibleOn hG
  haveI : IsCyclic ↥A :=
    isCyclic_of_injective (Subgroup.inclusion hAZ) (Subgroup.inclusion_injective hAZ)
  by_contra hle
  have h2lt : 2 < Nat.card ↥A := by omega
  obtain ⟨y, hy4⟩ := exists_orderOf_eq_four_of_isPGroup_two hA h2lt
  let yG : ↥G := (y : ↥G)
  have hyG4 : orderOf yG = 4 := by
    rw [show yG = (y : ↥G) from rfl, Subgroup.orderOf_coe, hy4]
  exact false_of_mem_center_of_orderOf_eq_four hp5 hGS hG (hAZ y.2) hyG4

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
