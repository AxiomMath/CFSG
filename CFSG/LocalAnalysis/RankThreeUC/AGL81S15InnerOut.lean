module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerDef
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBQSylowActionInnerTools
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped MatrixGroups

namespace InnerOut

variable {K : Type*} [Group K]

theorem conj_mem {L : Subgroup K} {b : K} (hb : b ∈ Subgroup.normalizer (L : Set K)) {k : K}
    (hk : k ∈ L) : b * k * b⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp hb k).mp hk

theorem conj_inv_mem {L : Subgroup K} {b : K} (hb : b ∈ Subgroup.normalizer (L : Set K)) {k : K}
    (hk : k ∈ L) : b⁻¹ * k * b ∈ L := by
  simpa using conj_mem (inv_mem hb) hk

@[expose] def conjAut (L : Subgroup K) (b : K) (hb : b ∈ Subgroup.normalizer (L : Set K)) :
    MulAut ↥L where
  toFun k := ⟨b * k * b⁻¹, conj_mem hb k.2⟩
  invFun k := ⟨b⁻¹ * k * b, conj_inv_mem hb k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[expose] def conjHom (L B : Subgroup K) (hBN : B ≤ Subgroup.normalizer (L : Set K)) :
    ↥B →* MulAut ↥L where
  toFun b := conjAut L b (hBN b.2)
  map_one' := by
    ext k
    simp [conjAut]
  map_mul' b c := by
    ext k
    simp [conjAut, mul_assoc]

theorem coe_conjHom_apply (L B : Subgroup K) (hBN : B ≤ Subgroup.normalizer (L : Set K))
    (b : ↥B) (k : ↥L) : ((conjHom L B hBN b k : ↥L) : K) = (b : K) * (k : K) * (b : K)⁻¹ :=
  rfl

theorem exists_conjAgree_of_mem_range (L B : Subgroup K)
    (hBN : B ≤ Subgroup.normalizer (L : Set K)) (b : ↥B)
    (h : conjHom L B hBN b ∈ (MulAut.conj : ↥L →* MulAut ↥L).range) :
    ∃ l ∈ L, ConjAgree L (b : K) l := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l, l.2, fun k hk => ?_⟩
  have h1 := congrArg (fun a : MulAut ↥L => ((a ⟨k, hk⟩ : ↥L) : K)) hl
  simpa [MulAut.conj_apply, coe_conjHom_apply] using h1.symm

section Model

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

@[expose] noncomputable def centerQuotientEquiv {L : Type*} [Group L] (e : L ≃* SL(3, F)) :
    L ⧸ Subgroup.center L ≃* projectiveSL 3 F :=
  QuotientGroup.congr (Subgroup.center L) (scalars 3 F) e
    (by rw [scalars_eq_center]; exact Subgroup.map_center_eq e)

open CFSG.QuasithinUnique.Fin257.L3 in
theorem relIndex_inf_inner_le [Finite F] [CharP F 2]
    (E : Subgroup (MulAut (projectiveSL 3 F))) (h2 : ∀ a ∈ E, a * a = 1) :
    (E ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range).relIndex E ≤ 4 := by
  have hIs : (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ≤
      semilinearAutGroup 3 F :=
    (standard_outer_quotients (K := F) (n := 3)).1.trans linearAutGroup_le_semilinearAutGroup
  have hle : E ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ≤
      E ⊓ semilinearAutGroup 3 F := inf_le_inf_left _ hIs
  rw [← Subgroup.relIndex_mul_relIndex _ (E ⊓ semilinearAutGroup 3 F) E hle inf_le_left]
  exact (Nat.mul_le_mul (relIndex_inner_le E h2) (relIndex_inf_semilinear_le E)).trans
    (by norm_num)

end Model

end InnerOut

theorem relIndex_innerPart_le {K : Type} [Group K] [Finite K] (L B : Subgroup K)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* SL(3, F)) (hperf : commutator ↥L = ⊤)
    (hBN : B ≤ Subgroup.normalizer (L : Set K)) (hB2 : ∀ b ∈ B, b * b = 1) :
    (innerPart L B).relIndex B ≤ 4 := by
  open InnerOut CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.QuasithinUnique.SteinbergBQ.SylowActionInner in
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  haveI : Group.IsPerfect ↥L := ⟨hperf⟩
  set η := centerQuotientEquiv e
  set ψ : ↥B →* MulAut (projectiveSL 3 F) := (modelAut η).comp (conjHom L B hBN)
  set I : Subgroup (MulAut (projectiveSL 3 F)) :=
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range
  have h2 : ∀ a ∈ ψ.range, a * a = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_mul]
    have hbb : b * b = 1 := Subtype.ext (hB2 b b.2)
    rw [hbb, map_one]
  have hle : I.comap ψ ≤ (innerPart L B).subgroupOf B := by
    intro b hb
    obtain ⟨l, hl, hlA⟩ := exists_conjAgree_of_mem_range L B hBN b
      (mem_range_conj_of_modelAut η (α := conjHom L B hBN b) (Subgroup.mem_comap.mp hb))
    rw [Subgroup.mem_subgroupOf, mem_innerPart]
    exact ⟨b.2, l, hl, hlA⟩
  have hidx : (I.comap ψ).index ≤ 4 := by
    rw [Subgroup.index_comap, ← Subgroup.inf_relIndex_right I ψ.range, inf_comm]
    exact relIndex_inf_inner_le ψ.range h2
  have hpos : (I.comap ψ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) (Subgroup.index_dvd_of_le hle)).trans hidx

end CFSG.LocalAnalysis.RankThreeUC.S15
