module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25YO01
public import CFSG.ClassicalInvolution.Asc77.AscCX9X8
public import CFSG.ClassicalInvolution.Asc77.AscCX4L4

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77.CX.MF2L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution.Asc77.CX.MF2L
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
    CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups
variable {F : Type} [Field F]
section Blocks
end Blocks
section Fix
variable {Y : Type} [Group Y] [Finite Y]

theorem spM_perfect [Finite F] (h4 : Nat.card F = 3) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⁅spM (spForm m n), spM (spForm m n)⁆ = spM (spForm m n) := by
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inr (Or.inl ⟨h4, le_rfl⟩))).1
  rw [← kappa_range hm hn, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact hperf.commutator_eq_top

theorem perfRes_fix_eq [Finite F] (h4 : Nat.card F = 3) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (θ : SL(4, F) →* Y) (hθ : Function.Surjective θ) (hker : θ.ker = scalars 4 F)
    (A : GL (Fin 4) F) (hA : (A : Matrix (Fin 4) (Fin 4) F) = spForm m n) (β : MulAut Y)
    (hβ : ∀ s, β (θ s) = θ (slConjugation 4 F A ((s⁻¹).transpose))) :
    Goldschmidt75.perfRes (fixSubgroup β) = (spM (spForm m n)).map θ := by
  apply le_antisymm
  ·
    have hfix : fixSubgroup β ≤ (simM (spForm m n)).map θ := by
      intro y hy
      obtain ⟨s, rfl⟩ := hθ y
      have hy' : β (θ s) = θ s := hy
      rw [hβ] at hy'
      have hs : proj 4 F (slConjugation 4 F A ((s⁻¹).transpose)) = proj 4 F s := by
        rw [proj_eq_proj_iff, ← hker, MonoidHom.mem_ker, map_mul, map_inv, hy', inv_mul_cancel]
      have := mem_simM_of_proj_eq A hs
      rw [hA] at this
      exact Subgroup.mem_map_of_mem θ this
    calc Goldschmidt75.perfRes (fixSubgroup β)
        ≤ Goldschmidt75.perfRes ((simM (spForm m n)).map θ) :=
          Goldschmidt75.le_perfRes ((Goldschmidt75.perfRes_le _).trans hfix)
            (Goldschmidt75.commutator_perfRes _)
      _ = (Goldschmidt75.perfRes (simM (spForm m n))).map θ :=
          (Goldschmidt75.map_perfRes θ _).symm
      _ ≤ (spM (spForm m n)).map θ := by
          refine Subgroup.map_mono ?_
          calc Goldschmidt75.perfRes (simM (spForm m n))
              = ⁅Goldschmidt75.perfRes (simM (spForm m n)),
                  Goldschmidt75.perfRes (simM (spForm m n))⁆ :=
                (Goldschmidt75.commutator_perfRes _).symm
            _ ≤ ⁅simM (spForm m n), simM (spForm m n)⁆ :=
                Subgroup.commutator_mono (Goldschmidt75.perfRes_le _)
                  (Goldschmidt75.perfRes_le _)
            _ ≤ spM (spForm m n) := commutator_simM_le_spM _
  ·
    refine Goldschmidt75.le_perfRes ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      show β (θ s) = θ s
      rw [hβ, slConj_eq_of_mem_spM A (by rw [hA]; exact hs)]
    · rw [← Subgroup.map_commutator, spM_perfect h4 hm hn]
end Fix
end Asc77.CX.MF2L

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX.MF2L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution.Asc77.CX.MF2L
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
    CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups
variable {F : Type} [Field F] {Y : Type} [Group Y] [Finite Y]
variable {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) (θ : SL(4, F) →* Y) (T : Subgroup Y)
  (hT : T = (spM (spForm m n)).map θ)
section Lie

@[expose] noncomputable def lieT {m n : GaloisField 3 1} (hm : m ≠ 0)
    (hn : n ≠ 0) (θ : SL(4, GaloisField 3 1) →* Y)
    (hker : θ.ker = scalars 4 (GaloisField 3 1)) (T : Subgroup Y)
    (hT : T = (spM (spForm m n)).map θ) :
    LieSystemData 3 1 ↥T (famT (homT hm hn θ T hT)) where
  card := 1
  tag := fun _ => .PSp
  rank := fun _ => 2
  exp := fun _ => 1
  hom := fun _ => homT hm hn θ T hT
  isFundTag := fun _ => trivial
  admissible := fun _ => ⟨Fact.out, le_rfl, le_refl 2, fun h => by
    have : 3 ^ 1 = 2 := (Prod.mk.inj h).2
    norm_num at this⟩
  exp_eq := fun _ => Or.inl rfl
  ker_le_center := fun _ => ker_homT_le_center hm hn θ T hT hker
  commute := fun i j hij => absurd (Subsingleton.elim i j) hij
  generate := eq_top_iff.mpr fun x _ =>
    Subgroup.mem_iSup_of_mem 0 (homT_surjective hm hn θ T hT x)
  fundamental := by
    rintro L ⟨P, hP, rfl⟩
    refine ⟨0, planeGroup P, (mem_fundamentalSubgroups_PSp_iff ⟨Fact.out, le_rfl, le_refl 2,
      fun h => by have : 3 ^ 1 = 2 := (Prod.mk.inj h).2; norm_num at this⟩ _).mpr ⟨P, hP, rfl⟩, rfl⟩
  meets := fun _ => ⟨planeGroup (stdPlane (GaloisField 3 1) 2 0),
    (mem_fundamentalSubgroups_PSp_iff ⟨Fact.out, le_rfl, le_refl 2,
      fun h => by have : 3 ^ 1 = 2 := (Prod.mk.inj h).2; norm_num at this⟩ _).mpr
      ⟨_, isHyperbolicPlane_stdPlane 0, rfl⟩,
    ⟨_, isHyperbolicPlane_stdPlane 0, rfl⟩⟩

theorem om5Data_T {m n : GaloisField 3 1} (hm : m ≠ 0)
    (hn : n ≠ 0) (θ : SL(4, GaloisField 3 1) →* Y)
    (hker : θ.ker = scalars 4 (GaloisField 3 1)) (T : Subgroup Y)
    (hT : T = (spM (spForm m n)).map θ) {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y}
    (htw : TwinSect0 Φ ((blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ)
      ((blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) :
    C5O.Om5Data ↥T (famT (homT hm hn θ T hT))
      (((blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ).subgroupOf T)
      (((blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ).subgroupOf T)
      ⟨z', block0_le_T θ T hT htw.hzA.mem⟩ ⟨a₀, block0_le_T θ T hT htw.ha₀⟩
      ⟨b₀, block2_le_T θ T hT htw.hb₀⟩ := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField 3 1) 3 2).1 (by exact_mod_cast h0)
    exact absurd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd) (by norm_num)
  exact ⟨⟨lieT hm hn θ hker T hT, rfl, ⟨0, Nat.one_pos⟩,
    Or.inl ⟨rfl, rfl, rfl⟩⟩,
    twinSect0_T hm hn θ T hT h2 htw hconj,
    fun J hJ y => conjSub_mem_famT (homT_surjective hm hn θ T hT) hJ y⟩
end Lie
end Asc77.CX.MF2L

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX.MF2L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution.Asc77.CX.MF2L
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
    CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups
variable {F : Type} [Field F] {Y : Type} [Group Y] [Finite Y]
variable (θ : SL(4, F) →* Y) (hθ : Function.Surjective θ) (hker : θ.ker = scalars 4 F)
include hθ hker in

theorem diagWit_of_graph [CharP F 3] [Finite F]
    (hsq : ¬ IsSquare (-1 : F)) (h4 : Nat.card F = 3) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (A₁ A₂ : GL (Fin 4) F) (hA₁ : (A₁ : Matrix (Fin 4) (Fin 4) F) = spForm m n)
    (hA₂ : (A₂ : Matrix (Fin 4) (Fin 4) F) = spForm (-m) n) (β β' : MulAut Y)
    (hβ : ∀ s, β (θ s) = θ (slConjugation 4 F A₁ ((s⁻¹).transpose)))
    (hβ' : ∀ s, β' (θ s) = θ (slConjugation 4 F A₂ ((s⁻¹).transpose)))
    (hA : (blockSL F 4 2 0 (by norm_num)).range.map θ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : (blockSL F 4 2 2 (by norm_num)).range.map θ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : (blockSL F 4 2 0 (by norm_num)).range.map θ ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : (blockSL F 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β')) :
    DiagWit 3 (centTG _ _ β hA hA') (centTG _ _ β' hB hB') := by
  have hX₁ := perfRes_fix_eq h4 hm hn θ hθ hker A₁ hA₁ β hβ
  have hX₂ := perfRes_fix_eq h4 (neg_ne_zero.mpr hm) hn θ hθ hker A₂ hA₂ β' hβ'
  have hmapX : (Goldschmidt75.perfRes (fixSubgroup β)).map (cHat θ hθ hker).toMonoidHom =
      Goldschmidt75.perfRes (fixSubgroup β') := by
    rw [hX₁, hX₂, map_cHat, map_d0_spM]
  set φ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')) :=
    ((cHat θ hθ hker).subgroupMap (Goldschmidt75.perfRes (fixSubgroup β))).trans
      (MulEquiv.subgroupCongr hmapX) with hφ
  have hφv : ∀ x, (φ x : Y) = cHat θ hθ hker x := fun x => rfl
  have h0 := map_cHat_block0 θ hθ hker
  have hφA : (((blockSL F 4 2 0 (by norm_num)).range.map θ).subgroupOf
      (Goldschmidt75.perfRes (fixSubgroup β))).map (φ : _ →* _) =
      ((blockSL F 4 2 0 (by norm_num)).range.map θ).subgroupOf
        (Goldschmidt75.perfRes (fixSubgroup β')) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : Y) ∈ (blockSL F 4 2 0 (by norm_num)).range.map θ := hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (φ x : Y) ∈ _
      rw [hφv, ← h0]
      exact Subgroup.mem_map_of_mem _ hx'
    · intro hy
      rw [Subgroup.mem_subgroupOf, ← h0] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, hA hx⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext ?_⟩
      exact hxy
  have hφA' : (((blockSL F 4 2 2 (by norm_num)).range.map θ).subgroupOf
      (Goldschmidt75.perfRes (fixSubgroup β))).map (φ : _ →* _) =
      ((blockSL F 4 2 2 (by norm_num)).range.map θ).subgroupOf
        (Goldschmidt75.perfRes (fixSubgroup β')) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : Y) ∈ (blockSL F 4 2 2 (by norm_num)).range.map θ := hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (φ x : Y) ∈ _
      rw [hφv, cHat_fix_block2 θ hθ hker hx']
      exact hx'
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      refine ⟨⟨y, hA' hy⟩, Subgroup.mem_subgroupOf.mpr hy, Subtype.ext ?_⟩
      exact cHat_fix_block2 θ hθ hker hy
  refine ⟨φ, hφA, hφA', fun hiff => ?_⟩
  have hr' : DiagTriv 3 (TwinGroup.restr' (L₁ := centTG _ _ β hA hA')
      (L₂ := centTG _ _ β' hB hB') φ hφA') := by
    intro u _
    refine ⟨1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    apply Subtype.ext
    exact (congrArg Subtype.val (TwinGroup.restr'_apply (L₁ := centTG _ _ β hA hA')
      (L₂ := centTG _ _ β' hB hB') φ hφA' u)).trans (cHat_fix_block2 θ hθ hker u.2)
  have hr := hiff.mpr hr'
  have hinj := theta_block0_injective θ hker
  set u : ↥((blockSL F 4 2 0 (by norm_num)).range.map θ) :=
    ⟨θ (blockSL F 4 2 0 (by norm_num) (uT 1)), Subgroup.mem_map_of_mem θ ⟨uT 1, rfl⟩⟩ with hu
  have hou : orderOf u = 3 := by
    rw [← Subgroup.orderOf_coe, hu]
    show orderOf ((θ.comp (blockSL F 4 2 0 (by norm_num))) (uT 1)) = 3
    rw [orderOf_injective _ hinj, orderOf_upT_one 3]
  obtain ⟨g, hg⟩ := hr u hou
  obtain ⟨_, ⟨b, rfl⟩, hgb⟩ := g.2
  have e1 : (TwinGroup.restr (L₁ := centTG _ _ β hA hA') (L₂ := centTG _ _ β' hB hB') φ hφA u :
      Y) = θ (blockSL F 4 2 0 (by norm_num) (uT (-1))) := by
    show cHat θ hθ hker (θ (blockSL F 4 2 0 (by norm_num) (uT 1))) = _
    rw [cHat_apply, d0_block0, c0_upT]
  have e2 := congrArg Subtype.val hg
  rw [e1] at e2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu] at e2
  rw [← hgb, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at e2
  exact upT_not_conj hsq (hinj e2).symm
end Asc77.CX.MF2L

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX.MF2L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution.Asc77.CX.MF2L
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups
variable {F : Type} [Field F]
section Wit

theorem reflWit_std (hsq : ¬ IsSquare (-1 : GaloisField 3 1))
    {Y : Type} [Group Y] [Finite Y] (θ : SL(4, GaloisField 3 1) →* Y)
    (hθ : Function.Surjective θ) (hθker : θ.ker = scalars 4 (GaloisField 3 1))
    {Φ : Set (Subgroup Y)} {a₀ b₀ : Y}
    (htw : TwinSect0 Φ ((blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ)
      ((blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ)
      (θ (rootInv (GaloisField 3 1) (show 2 ≤ 4 by norm_num))) a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ (blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ, β y = y)
    (hβA' : ∀ y ∈ (blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ, β y = y)
    (hβ2 : β * β = 1) (hβ1 : β ≠ 1)
    (hβz : β ≠ MulAut.conj (θ (rootInv (GaloisField 3 1) (show 2 ≤ 4 by norm_num)))) :
    ∃ (hA : (blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : (blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup β))
      (hB : (blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup
          (β * MulAut.conj (θ (rootInv (GaloisField 3 1) (show 2 ≤ 4 by norm_num))))))
      (hB' : (blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup
          (β * MulAut.conj (θ (rootInv (GaloisField 3 1) (show 2 ≤ 4 by norm_num)))))),
      IsOm5 (centTG _ _ β hA hA') ∧ IsOm5 (centTG _ _ _ hB hB') ∧
        DiagWit 3 (centTG _ _ β hA hA') (centTG _ _ _ hB hB') := by
  classical
  have h2 : (2 : GaloisField 3 1) ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField 3 1) 3 2).1 (by exact_mod_cast h0)
    exact absurd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd) (by norm_num)
  have h4 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  set r := rootInv (GaloisField 3 1) (show 2 ≤ 4 by norm_num) with hr
  set e := eTheta θ hθ hθker with he
  set β₀ : MulAut (projectiveSL 4 (GaloisField 3 1)) := (e.trans β).trans e.symm with hβ₀
  have hβ₀e : ∀ x, e (β₀ x) = β (e x) := fun x => e.apply_symm_apply _
  have hep : ∀ s, e (proj 4 (GaloisField 3 1) s) = θ s := fun s => rfl
  have hfix : CX4.L4.FixBlocks β₀ := by
    refine ⟨fun s hs => e.injective ?_, fun s hs => e.injective ?_⟩
    · rw [hβ₀e, hep, hβA _ ⟨s, hs, rfl⟩]
    · rw [hβ₀e, hep, hβA' _ ⟨s, hs, rfl⟩]
  have hββ : ∀ y, β (β y) = y := fun y => by
    rw [← MulAut.mul_apply, hβ2, MulAut.one_apply]
  have hk : β₀ ^ (2 ^ 1) = 1 := by
    ext x
    apply e.injective
    rw [pow_one, sq, MulAut.mul_apply, hβ₀e, hβ₀e, hββ, MulAut.one_apply]
  rcases CX4.L4.two_elem_cases h2 hsq hfix hk with (h | h) | ⟨M, m, n, hm, hn, hM, hβ₀M⟩
  · exfalso
    apply hβ1
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hβ₀e, h, MulAut.one_apply, MulAut.one_apply]
  · exfalso
    apply hβz
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hβ₀e, h, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rfl
  have hβθ : ∀ s, β (θ s) = θ (slConjugation 4 (GaloisField 3 1) M ((s⁻¹).transpose)) := by
    intro s
    rw [← hep, ← hβ₀e, hβ₀M, MulAut.mul_apply, dualAut_proj, conjAut_proj, hep]
  set M' := M * Matrix.SpecialLinearGroup.toGL r with hM'def
  have hM' : (M' : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) = spForm (-m) n := by
    rw [hM'def, Units.val_mul, hM, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hr,
      coe_rootInv_four]
    exact spForm_mul_z m n
  have hβθ' : ∀ s, (β * MulAut.conj (θ r)) (θ s) =
      θ (slConjugation 4 (GaloisField 3 1) M' ((s⁻¹).transpose)) := by
    intro s
    rw [MulAut.mul_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hβθ, hM'def,
      slConj_rootInv]
  have hX₁ := perfRes_fix_eq h4 hm hn θ hθ hθker M hM β hβθ
  have hX₂ := perfRes_fix_eq h4 (neg_ne_zero.mpr hm) hn θ hθ hθker M' hM' _ hβθ'
  have hA : (blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β) := by
    rw [hX₁]
    exact Subgroup.map_mono (block0_le_spM m n)
  have hA' : (blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β) := by
    rw [hX₁]
    exact Subgroup.map_mono (block2_le_spM m n)
  have hB : (blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj (θ r))) := by
    rw [hX₂]
    exact Subgroup.map_mono (block0_le_spM (-m) n)
  have hB' : (blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj (θ r))) := by
    rw [hX₂]
    exact Subgroup.map_mono (block2_le_spM (-m) n)
  exact ⟨hA, hA', hB, hB', ⟨_, _, _, _, om5Data_T hm hn θ hθker _ hX₁ htw hconj⟩,
    ⟨_, _, _, _, om5Data_T (neg_ne_zero.mpr hm) hn θ hθker _ hX₂ htw hconj⟩,
    diagWit_of_graph θ hθ hθker hsq h4 hm hn M M' hM hM' β _ hβθ hβθ' hA hA' hB hB'⟩
end Wit
end Asc77.CX.MF2L

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX.MF2L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution.Asc77.CX.MF2L
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

theorem reflWit_psl4 (hsq : ¬ IsSquare (-1 : GaloisField 3 1))
    {Y : Type} [Group Y] [Finite Y] (ψ : SL(4, GaloisField 3 1) →* Y)
    (hker : ψ.ker ≤ Subgroup.center SL(4, GaloisField 3 1)) (hsurj : Function.Surjective ψ)
    {R R' : Subgroup SL(4, GaloisField 3 1)}
    (hR : R ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num))
    {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y} (htw : TwinSect0 Φ (R.map ψ) (R'.map ψ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ R.map ψ, β y = y) (hβA' : ∀ y ∈ R'.map ψ, β y = y) (hβ2 : β * β = 1)
    (hβ1 : β ≠ 1) (hβz : β ≠ MulAut.conj z') :
    ∃ (hA : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hB : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
      (hB' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
      IsOm5 (centTG _ _ β hA hA') ∧ IsOm5 (centTG _ _ (β * MulAut.conj z') hB hB') ∧
        DiagWit 3 (centTG _ _ β hA hA') (centTG _ _ (β * MulAut.conj z') hB hB') := by
  classical
  have h2 : (2 : GaloisField 3 1) ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField 3 1) 3 2).1 (by exact_mod_cast h0)
    exact absurd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd) (by norm_num)
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hRR : R ≠ R' := fun h => htw.ne (by rw [h])
  obtain ⟨hiR, hi2, hi1, hψi⟩ := CX4.L4.twin_data h2 ψ hker hi htw.hzA
  obtain ⟨hi'R, hi'2, hi'1, hψi'⟩ := CX4.L4.twin_data h2 ψ hker hi' htw.hzA'
  have hc : i' * i⁻¹ ∈ Subgroup.center SL(4, GaloisField 3 1) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hig⟩ := twin_std h2 ⟨i, hi⟩ ⟨i', hi'⟩ hRR hiR hi2 hi1 hi'R hi'2 hi'1 hc
  have hk := CX4.L4.ker_eq_scalars h2 hsq ψ hker hi hi' hRR htw.hzA htw.hzA'
  set θ := ψ.comp (MulAut.conj g).toMonoidHom with hθdef
  have hθ : Function.Surjective θ := fun y => by
    obtain ⟨s, rfl⟩ := hsurj y
    refine ⟨g⁻¹ * s * g, ?_⟩
    simp only [hθdef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    congr 1
    group
  have hθker : θ.ker = scalars 4 (GaloisField 3 1) := by
    ext x
    rw [MonoidHom.mem_ker]
    show ψ (g * x * g⁻¹) = 1 ↔ x ∈ scalars 4 (GaloisField 3 1)
    rw [← MonoidHom.mem_ker, hk]
    constructor
    · intro h
      have hcen := Subgroup.mem_center_iff.mp ((scalars_eq_center 4 (GaloisField 3 1)).le h)
      have e : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = (g * x * g⁻¹) * g⁻¹ * g := by rw [hcen g⁻¹]
          _ = g * x * g⁻¹ := by group
      rw [e]
      exact h
    · intro h
      have hcen := Subgroup.mem_center_iff.mp ((scalars_eq_center 4 (GaloisField 3 1)).le h)
      have e : g * x * g⁻¹ = x := by rw [hcen g]; group
      rw [e]
      exact h
  have hAθ : R.map ψ = (blockSL (GaloisField 3 1) 4 2 0 (by norm_num)).range.map θ := by
    rw [hRg, Subgroup.map_map]
  have hA'θ : R'.map ψ = (blockSL (GaloisField 3 1) 4 2 2 (by norm_num)).range.map θ := by
    rw [hR'g, Subgroup.map_map]
  have hzθ : z' = θ (rootInv (GaloisField 3 1) (show 2 ≤ 4 by norm_num)) := by
    rw [← hψi, hig]
    rfl
  rw [hAθ] at htw hβA ⊢
  rw [hA'θ] at htw hβA' ⊢
  subst hzθ
  exact reflWit_std hsq θ hθ hθker htw hconj β hβA hβA' hβ2 hβ1 hβz
end Asc77.CX.MF2L

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem MF2L.reflWit_of_hom {Y : Type} [Group Y] [Finite Y] (t : StatedLieTag)
    (k e : ℕ) (hadm : StatedLieAdmissible t k 3 e)
    (ψ : (Generic.modelUniv t k 3 e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k 3 e Fact.out).K)
    (hsurj : Function.Surjective ψ) (hcase : t = .PSL ∧ k = 4 ∧ ¬ 3 ^ e % 4 = 1)
    (he1 : e = 1) {R R' : Subgroup (Generic.modelUniv t k 3 e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k 3 e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k 3 e Fact.out).D)
    {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y} (htw : TwinSect0 Φ (R.map ψ) (R'.map ψ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ R.map ψ, β y = y) (hβA' : ∀ y ∈ R'.map ψ, β y = y) (hβ2 : β * β = 1)
    (hβ1 : β ≠ 1) (hβz : β ≠ MulAut.conj z') :
    ∃ (hA : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hB : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
      (hB' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
      IsOm5 (centTG _ _ β hA hA') ∧ IsOm5 (centTG _ _ (β * MulAut.conj z') hB hB') ∧
        DiagWit 3 (centTG _ _ β hA hA') (centTG _ _ (β * MulAut.conj z') hB hB') := by
  obtain ⟨rfl, rfl, h4⟩ := hcase
  subst he1
  have hsq : ¬ IsSquare (-1 : GaloisField 3 1) := by
    have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card,
      GaloisField.card 3 1 (by norm_num)]
    norm_num
  exact MF2L.reflWit_psl4 hsq ψ hker hsurj
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    htw hconj β hβA hβA' hβ2 hβ1 hβz

theorem om6ReflWit_proved : Om6ReflWit := by
  intro Y _ _ Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  have h1 : ¬ 3 ^ 1 % 4 = 1 := by norm_num
  obtain ⟨D, hD1, i, hi⟩ := hY.lie
  have htw := hY.twin
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom i).range := by
      intro l
      rw [Subsingleton.elim l i]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : D.tag i = .PSL ∧ D.rank i = 4 ∧ ¬ 3 ^ 1 % 4 = 1 := by
    simp only [IsOrthTag] at hi
    rcases hi with ⟨h5, -⟩ | ⟨-, -, ht, hn⟩ | ⟨-, hε, -, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · omega
    · exact ⟨ht, hn, h1⟩
    · exfalso
      simp only [piSign, Bool.not_eq_false', decide_eq_true_eq] at hε
      exact h1 hε
    · omega
    · omega
    · omega
  have hexp : D.exp i = 1 := by
    rcases D.exp_eq i with h | ⟨hT, -⟩
    · exact h
    · rw [hcase.1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₁ : i₁ = i := Subsingleton.elim _ _
  have h₂ : i₂ = i := Subsingleton.elim _ _
  subst h₁ h₂
  subst hAR hAR'
  obtain ⟨hA, hA', hB, hB', h5, h5', hw⟩ := MF2L.reflWit_of_hom (D.tag i₂) (D.rank i₂)
    (D.exp i₂) (D.admissible i₂) (D.hom i₂) (D.ker_le_center i₂) hsurj
    ⟨hcase.1, hcase.2.1, by rw [hexp]; exact h1⟩ hexp hR hR' htw hY.conj β hβA hβA' hβ2 hβ1 hβz
  exact ⟨hA, hA', hB, hB', h5, h5', hw⟩
end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
