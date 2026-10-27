module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsEngLU
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open scoped IsMulCommutative

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}

section Blocks

variable [Finite K] {p : ℕ} {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
variable {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

theorem glRep_preserves_weightFamily (a : ↥Aε) :
    ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      (glRep Aε a).toAddMonoidHom v ∈ weightFamily (p := p) (glRep Aε) i := fun i v hv =>
  preserves_weightFamily_of_semilinear (glRep Aε) (RingHom.id K) (glRep Aε a).toAddMonoidHom
    (fun c v => map_smul (glRep Aε a) c v)
    (fun a' v => by
      show glRep Aε a (glRep Aε a' v) = glRep Aε a' (glRep Aε a v)
      rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]) i hv

theorem preserves_wtU_wtW (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    (I : Finset (Hyperplane ↥Aε p)) (f : (ι → K) →+ (ι → K))
    (hf : ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      f v ∈ weightFamily (p := p) (glRep Aε) i) :
    (∀ u ∈ wtU Aε I, f u ∈ wtU Aε I) ∧ ∀ w ∈ wtW Aε I, f w ∈ wtW Aε I := by
  refine ⟨fun u hu => ?_, fun w hw => ?_⟩
  · rw [LinearMap.mem_ker] at hu ⊢
    rw [projI_comm_of_preserves (glRep Aε) hp hA hpK I f hf, hu, map_zero]
  · obtain ⟨v, rfl⟩ := hw
    exact ⟨f v, projI_comm_of_preserves (glRep Aε) hp hA hpK I f hf v⟩

theorem weightSpace_le_ker_projI (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    {I : Finset (Hyperplane ↥Aε p)} {H' : Hyperplane ↥Aε p} (hH' : H' ∉ I) :
    weightSpace (glRep Aε) H'.1 ≤ wtU Aε I := by
  intro v hv
  rw [LinearMap.mem_ker]
  have hi : ∀ H₁ ∈ I, (some H' : Option (Hyperplane ↥Aε p)) ≠ some H₁ := by
    intro H₁ hH₁ h
    exact hH' (by rw [Option.some.inj h]; exact hH₁)
  exact projI_apply_of_not_mem (glRep Aε) hp hA hpK hi (by rw [weightFamily_some]; exact hv)

theorem supported_mem_blkSub (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    (hAεβ : Aε ≤ isomGL β) [DecidableEq (Hyperplane ↥Aε p)] (I : Finset (Hyperplane ↥Aε p))
    {H' : Hyperplane ↥Aε p} (hH'I : H' ∉ I) {x : ↥Aε} (hx : ∀ H ∈ ({H'} : Finset _), x ∉ H.1)
    (hx' : ∀ H'' : Hyperplane ↥Aε p, H'' ∉ ({H'} : Finset _) →
      weightSpace (glRep Aε) H''.1 ≠ ⊥ → x ∈ H''.1) :
    (x : GL ι K) ∈ blkSub β (wtU Aε I) (wtW Aε I) ∧ orderOf (x : GL ι K) = p := by
  refine ⟨⟨hAεβ x.2, fun u hu => ?_, fun w hw => ?_⟩, ?_⟩
  · have := (preserves_wtU_wtW hp hA hpK I _ (glRep_preserves_weightFamily x)).1 u hu
    simpa only [LinearMap.toAddMonoidHom_coe, glRep_apply_eq_glEquiv] using this
  · obtain ⟨v, rfl⟩ := hw
    have h := (apply_eq_self_iff_projI (glRep Aε) hp hA hpK hx hx' (projI (glRep Aε) I v)).mpr
      (by
        rw [projI_projI_eq_inter (glRep Aε) hp hA hpK]
        have : ({H'} : Finset (Hyperplane ↥Aε p)) ∩ I = ∅ := by
          rw [Finset.singleton_inter_of_notMem hH'I]
        rw [this, projI_apply, Finset.sum_empty])
    rwa [glRep_apply_eq_glEquiv] at h
  · haveI : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime ?_ fun h1 => hx H' (Finset.mem_singleton_self H') ?_
    · exact congrArg Subtype.val (hA x)
    · have : x = 1 := Subtype.ext h1
      rw [this]
      exact H'.1.one_mem

theorem mem_wtU_insert (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    [DecidableEq (Hyperplane ↥Aε p)] {I : Finset (Hyperplane ↥Aε p)} {H₂ : Hyperplane ↥Aε p}
    (hH₂ : H₂ ∉ I) (v : ι → K) :
    v ∈ wtU Aε (insert H₂ I) ↔ v ∈ wtU Aε I ∧ v ∈ wtU Aε {H₂} := by
  have hsum : projI (glRep Aε) (insert H₂ I) v =
      projI (glRep Aε) {H₂} v + projI (glRep Aε) I v := by
    rw [projI_apply, Finset.sum_insert hH₂, projI_apply, projI_apply, Finset.sum_singleton]
  simp only [LinearMap.mem_ker]
  rw [hsum]
  constructor
  · intro h
    have h1 := congrArg (projI (glRep Aε) I) h
    rw [map_add, projI_projI_of_disjoint (glRep Aε) hp hA hpK
      (Finset.disjoint_singleton_right.mpr hH₂), projI_projI (glRep Aε) hp hA hpK, zero_add,
      map_zero] at h1
    rw [h1, add_zero] at h
    exact ⟨h1, h⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, add_zero]

theorem wtW_insert (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    [DecidableEq (Hyperplane ↥Aε p)] {I : Finset (Hyperplane ↥Aε p)} {H₂ : Hyperplane ↥Aε p}
    (hH₂ : H₂ ∉ I) :
    wtW Aε I ≤ wtW Aε (insert H₂ I) ∧ wtW Aε {H₂} ≤ wtW Aε (insert H₂ I) ∧
      ∀ w ∈ wtW Aε (insert H₂ I), w = projI (glRep Aε) I w + projI (glRep Aε) {H₂} w := by
  have hsub : ∀ J : Finset (Hyperplane ↥Aε p), J ⊆ insert H₂ I →
      wtW Aε J ≤ wtW Aε (insert H₂ I) := by
    rintro J hJ _ ⟨v, rfl⟩
    refine ⟨projI (glRep Aε) J v, ?_⟩
    rw [projI_projI_eq_inter (glRep Aε) hp hA hpK, Finset.inter_eq_right.mpr hJ]
  refine ⟨hsub I (Finset.subset_insert H₂ I),
    hsub {H₂} (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self H₂ I)), ?_⟩
  rintro _ ⟨v, rfl⟩
  rw [projI_projI_eq_inter (glRep Aε) hp hA hpK, projI_projI_eq_inter (glRep Aε) hp hA hpK,
    Finset.inter_eq_left.mpr (Finset.subset_insert H₂ I),
    Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self H₂ I)),
    projI_apply, Finset.sum_insert hH₂, projI_apply, projI_apply, Finset.sum_singleton, add_comm]

theorem glaPLayer_ne_bot_of_subBlock (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (hAεβ : Aε ≤ isomGL β) [DecidableEq (Hyperplane ↥Aε p)]
    (I : Finset (Hyperplane ↥Aε p)) {H₂ : Hyperplane ↥Aε p} (hH₂ : H₂ ∉ I) {x : ↥Aε}
    (hx : ∀ H ∈ ({H₂} : Finset _), x ∉ H.1)
    (hx' : ∀ H'' : Hyperplane ↥Aε p, H'' ∉ ({H₂} : Finset _) →
      weightSpace (glRep Aε) H''.1 ≠ ⊥ → x ∈ H''.1)
    (hq : CFSG.Open.IsQuasisimple ↥(blkI β (wtU Aε (insert H₂ I)) (wtW Aε (insert H₂ I))))
    (hpJ : p ∣ Nat.card ↥(blkI β (wtU Aε (insert H₂ I)) (wtW Aε (insert H₂ I)))) :
    GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓ Subgroup.centralizer {(x : GL ι K)}) ≠ ⊥ := by
  set U := wtU Aε I with hUdef
  set W := wtW Aε I with hWdef
  set U' := wtU Aε (insert H₂ I) with hU'def
  set W' := wtW Aε (insert H₂ I) with hW'def
  set J' := blkI β U' W' with hJ'def
  set C := blkI β U W ⊓ Subgroup.centralizer {(x : GL ι K)} with hCdef
  have hU'W' : IsCompl U' W' := isCompl_ker_range_projI (glRep Aε) hp hA hpK (insert H₂ I)
  obtain ⟨hWW', hW₂W', hdecW'⟩ := wtW_insert hp hA hpK hH₂
  have hU'U : ∀ u ∈ U', u ∈ U := fun u hu => ((mem_wtU_insert hp hA hpK hH₂ u).mp hu).1
  have hU'₂ : ∀ u ∈ U', u ∈ wtU Aε {H₂} := fun u hu => ((mem_wtU_insert hp hA hpK hH₂ u).mp hu).2
  have hxfix : ∀ v ∈ wtU Aε {H₂}, glEquiv (x : GL ι K) v = v := fun v hv => by
    rw [← glRep_apply_eq_glEquiv]
    exact (apply_eq_self_iff_projI (glRep Aε) hp hA hpK hx hx' v).mpr hv
  have hxW' : ∀ w ∈ W', glEquiv (x : GL ι K) w ∈ W' := fun w hw => by
    have := (preserves_wtU_wtW hp hA hpK (insert H₂ I) _ (glRep_preserves_weightFamily x)).2 w hw
    simpa only [LinearMap.toAddMonoidHom_coe, glRep_apply_eq_glEquiv] using this
  have hsub : blkSub β U' W' ≤ blkSub β U W := by
    rintro g ⟨hgβ, hgU, hgW⟩
    refine ⟨hgβ, fun u hu => ?_, fun w hw => hgW w (hWW' hw)⟩
    obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.1
      (show u ∈ U' ⊔ W' by rw [hU'W'.sup_eq_top]; trivial)
    have hw'U : w' ∈ U := by
      have h1 : u' + w' - u' = w' := by abel
      rw [← h1]
      exact U.sub_mem hu (hU'U u' hu')
    rw [map_add, hgW w' hw']
    exact U.add_mem (hU'U _ (hgU u' hu')) hw'U
  have hcent : blkSub β U' W' ≤ Subgroup.centralizer {(x : GL ι K)} := by
    rintro g ⟨-, hgU, hgW⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply glEquiv.injective
    refine linearEquiv_ext_of_isCompl hU'W' (fun u hu => ?_) fun w hw => ?_
    · rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxfix u (hU'₂ u hu),
        hxfix _ (hU'₂ _ (hgU u hu))]
    · rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgW w hw,
        hgW _ (hxW' w hw)]
  have hJ'C : J' ≤ C := by
    refine le_inf ?_ ((blkI_le_blkSub β U' W').trans hcent)
    exact Subgroup.commutator_mono hsub hsub
  have hnorm : ∀ g ∈ C, ∀ f ∈ J', g * f * g⁻¹ ∈ J' := by
    rintro g ⟨hgI, hgx⟩ f hf
    obtain ⟨hgβ, hgU, hgW⟩ := blkI_le_blkSub β U W hgI
    have hgx' : ∀ v, (glEquiv g : (ι → K) →ₗ[K] (ι → K)) (glRep Aε x v) =
        glRep Aε x (glEquiv g v) := by
      intro v
      have hgx2 : g * (x : GL ι K) = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
      simp only [glRep_apply_eq_glEquiv, LinearEquiv.coe_coe]
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hgx2]
    obtain ⟨hg₂U, hg₂W⟩ := preserves_of_comm_supported (glRep Aε) hp hA hpK hx hx' _ hgx'
    refine conj_mem_blkI hgβ (fun u hu => ?_) (fun w hw => ?_) hf
    · exact (mem_wtU_insert hp hA hpK hH₂ _).mpr ⟨hgU u (hU'U u hu), hg₂U u (hU'₂ u hu)⟩
    · rw [hdecW' w hw, map_add, hgW _ ⟨w, rfl⟩]
      exact W'.add_mem (hWW' ⟨w, rfl⟩) (hW₂W' (hg₂W _ ⟨w, rfl⟩))
  have hn : (J'.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hcomp := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hq hpJ hJ'C hn
  intro hbot
  have hle : J' ≤ GLAPLayer p C := le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hpJ
  exact hp.one_lt.ne' (Nat.dvd_one.mp hpJ)

end Blocks

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
