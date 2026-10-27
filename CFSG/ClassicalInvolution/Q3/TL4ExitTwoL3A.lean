module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1C
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3X

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic Matrix
  QuaternionGroup
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
  CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

namespace L3

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

omit [Finite G] in
theorem sl_facts (h4 : 4 ≤ Nat.card K) {N : Subgroup G} [N.Normal] {w : G}
    {π : (⊤ : Subgroup (GL (Fin 2) K)) →* G}
    (hrange : π.range = N ⊓ Subgroup.centralizer ({w} : Set G)) (hk : CubeKer π)
    (hπ1 : π ⟨-1, Subgroup.mem_top _⟩ = w) :
    (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π ≤ Subgroup.centralizer ({w} : Set G) ∧
      CFSG.IsComponent (((slPart (⊤ : Subgroup (GL (Fin 2) K))).map π).subgroupOf
        (Subgroup.centralizer ({w} : Set G))) ∧
      w ∈ (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π := by
  set J₀ := (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π
  set C := Subgroup.centralizer ({w} : Set G)
  have hJNC : J₀ ≤ N ⊓ C := hrange ▸ Subgroup.map_le_range π _
  have hJC : J₀ ≤ C := hJNC.trans inf_le_right
  have hJr : J₀ = (π.comp (slPart (⊤ : Subgroup (GL (Fin 2) K))).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eJ : ↥J₀ ≃* SL(2, K) := (MulEquiv.subgroupCongr hJr).trans
    ((MonoidHom.ofInjective (injective_slPart hk)).symm.trans slPartTopEquiv)
  have hq : CFSG.IsQuasisimple ↥J₀ := LocalCores.isQuasisimple_of_mulEquiv eJ.symm
    (RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl h4)
  have : Group.IsPerfect ↥J₀ := isPerfect_of_equiv_sl2 h4 eJ
  have hJn : ∀ c ∈ C, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀ := by
    intro c hc j hj
    have hle : J₀.map (MulAut.conj c).toMonoidHom ≤ π.range := by
      rw [hrange]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp (hJNC hx)
      exact Subgroup.mem_inf.mpr ⟨(inferInstance : N.Normal).conj_mem _ hxN c,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hxC) (Subgroup.inv_mem _ hc)⟩
    have hM : J₀.map (MulAut.conj c).toMonoidHom ≤ J₀ :=
      calc J₀.map (MulAut.conj c).toMonoidHom
          = ⁅J₀.map (MulAut.conj c).toMonoidHom, J₀.map (MulAut.conj c).toMonoidHom⁆ := by
            rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
        _ ≤ ⁅π.range, π.range⁆ := Subgroup.commutator_mono hle hle
        _ ≤ J₀ := commutator_range_le π
    exact hM ⟨j, hj, rfl⟩
  refine ⟨hJC, ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hq,
    Subgroup.Normal.isSubnormal ⟨fun j hj c => ?_⟩⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hj ⊢
    exact hJn c c.2 j hj
  · rw [← hπ1]
    refine ⟨⟨-1, Subgroup.mem_top _⟩, mem_slPart.mpr ?_, rfl⟩
    ext
    simp [Matrix.det_neg]

theorem exists_scalar_four (h4 : 4 ≤ Nat.card K) {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) (e : ↥N ≃* projectiveSL 3 K) {w : G}
    {π : (⊤ : Subgroup (GL (Fin 2) K)) →* G}
    (hrange : π.range = N ⊓ Subgroup.centralizer ({w} : Set G)) (hk : CubeKer π)
    (hπ1 : π ⟨-1, Subgroup.mem_top _⟩ = w) (hπN : ∀ A, π A ∈ N)
    (hπe : ∀ A, e ⟨π A, hπN A⟩ = proj 3 K (blkP 1 (A : GL (Fin 2) K)))
    {Δ : Set (Subgroup G)} (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {M : Subgroup G}
    (hM : M ∈ Δ) (hMw : IsUniqueInvolution M w) :
    ∃ A : (⊤ : Subgroup (GL (Fin 2) K)),
      (∃ c : Kˣ, (A : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) c) ∧ π A ∈ M ∧
        orderOf (π A) = 4 := by
  obtain ⟨hJC, hJc, hwJ⟩ := sl_facts h4 hrange hk hπ1
  have hcomm := commute_of_component hΔ hM hMw hJC hJc hwJ
  let ι : G →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut ↥N)
  have hιapp : ∀ (y : G) (n : ↥N), ι y (e n) = e (MulAut.conjNormal y n) := fun y n => by
    show e ((MulAut.conjNormal y) (e.symm (e n))) = _
    rw [MulEquiv.symm_apply_apply]
  have hfix : ∀ x ∈ M, ∀ B : SL(2, K),
      ι x (proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B)) =
        proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B) := by
    intro x hx B
    let A : (⊤ : Subgroup (GL (Fin 2) K)) := ⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩
    have hAJ : π A ∈ (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π :=
      ⟨A, mem_slPart.mpr (SpecialLinearGroup.coeToGL_det B), rfl⟩
    have hxA : x * π A = π A * x := hcomm x hx _ hAJ
    have hconj : MulAut.conjNormal x ⟨π A, hπN A⟩ = ⟨π A, hπN A⟩ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show x * π A * x⁻¹ = π A
      rw [hxA, mul_inv_cancel_right]
    show ι x (proj 3 K (blkP 1 (A : GL (Fin 2) K))) = proj 3 K (blkP 1 (A : GL (Fin 2) K))
    rw [← hπe A, hιapp, hconj]
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := M) (IsPGroup.of_bot (p := 2)) bot_le
  obtain ⟨eP⟩ := hΔ.quat M hM P hP
  let φ : QuaternionGroup 2 →* G := P.subtype.comp eP.symm.toMonoidHom
  have hφi : Function.Injective φ := fun q₁ q₂ h => eP.symm.injective (Subtype.ext h)
  have hφM : ∀ q, φ q ∈ M := fun q => hP.1 (eP.symm q).2
  have hq4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have hE : ∃ q : QuaternionGroup 2, ¬ q ^ 2 ^ 1 = 1 ∧ ι (φ q) ∈ semilinearAutGroup 3 K := by
    by_cases ha : ι (φ (a 1)) ∈ semilinearAutGroup 3 K
    · exact ⟨a 1, by decide, ha⟩
    by_cases hb : ι (φ (xa 0)) ∈ semilinearAutGroup 3 K
    · exact ⟨xa 0, by decide, hb⟩
    refine ⟨a 1 * xa 0, by decide, ?_⟩
    rw [map_mul φ, map_mul ι]
    exact mul_mem_semilinearAutGroup ha hb
  obtain ⟨q, hq2, hqE⟩ := hE
  have hqD := mem_linearAutGroup_of_fix h4 ((blkP 1).comp SpecialLinearGroup.toGL)
    (trace_blkP 1) hqE (hfix _ (hφM q))
  have hq4' : ι (φ q) ^ 2 ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, hq4, map_one, map_one]
  have hsN : φ q ∈ N := MF163.mem_of_congr_mem_inner hC e (mem_inner_of_pow hqD hq4')
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs4 : orderOf (φ q) = 4 := by
    rw [orderOf_injective φ hφi q]
    exact orderOf_eq_prime_pow hq2 (by rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]; exact hq4 q)
  have hsC := le_centralizer_of_isUniqueInvolution hMw (hφM q)
  obtain ⟨A, hA⟩ : φ q ∈ π.range := hrange ▸ Subgroup.mem_inf.mpr ⟨hsN, hsC⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_commute hk slCentScalar_top fun B hB => by
    rw [hA]
    exact hcomm _ (hφM q) _ ⟨B, hB, rfl⟩
  exact ⟨A, ⟨c, hc⟩, hA ▸ hφM q, hA ▸ hs4⟩

end L3

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
