module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Model8Torus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentSylow
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6ThreeCentral
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

section Toral


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem Std8.Γ_le_model (D : Std8 L) : D.S.Γ ≤ D.S.D.model :=
  commutator_le_self_of_subgroup D.S.D.model

theorem Std8.finite_Γ (D : Std8 L) : Finite ↥D.S.Γ := by
  haveI : Finite ↥D.S.D.model := D.S.finite
  exact Finite.of_injective (Subgroup.inclusion D.Γ_le_model) (Subgroup.inclusion_injective _)

theorem Std8.exists_lift_list (D : Std8 L) (l : List (Fin Tag.E6.rank)) :
    ∃ n : ↥D.S.Γ, ∀ {ω : Lˣ}, ω ^ 3 = 1 → ∀ x : Fin Tag.E6.rank → ZMod 3,
      (n : ModGL Tag.E6 L) * dV ω x * (n : ModGL Tag.E6 L)⁻¹ = dV ω (l.foldr reflV x) := by
  induction l with
  | nil =>
    refine ⟨1, fun {ω} _ x => ?_⟩
    simp
  | cons a l ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨ν, hνΓ, hν⟩ := D.exists_lift a
    refine ⟨⟨ν, hνΓ⟩ * n, fun {ω} hω x => ?_⟩
    have h1 : ((⟨ν, hνΓ⟩ * n : ↥D.S.Γ) : ModGL Tag.E6 L) * dV ω x *
        ((⟨ν, hνΓ⟩ * n : ↥D.S.Γ) : ModGL Tag.E6 L)⁻¹ =
          ν * ((n : ModGL Tag.E6 L) * dV ω x * (n : ModGL Tag.E6 L)⁻¹) * ν⁻¹ := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    rw [h1, hn hω x, hν hω]
    rfl


noncomputable def Std8.E (D : Std8 L) {ω : Lˣ} (hω : ω ^ 3 = 1) : Subgroup ↥D.S.Γ :=
  (dVHom (τ := Tag.E6) hω).range.subgroupOf D.S.Γ

theorem Std8.mem_E (D : Std8 L) {ω : Lˣ} (hω : ω ^ 3 = 1) {g : ↥D.S.Γ} :
    g ∈ D.E hω ↔ ∃ x : Fin Tag.E6.rank → ZMod 3, (g : ModGL Tag.E6 L) = dV ω x := by
  rw [Std8.E, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.toAdd, hy.symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨Multiplicative.ofAdd x, hx.symm⟩

theorem Std8.isPGroup_E (D : Std8 L) {ω : Lˣ} (hω : ω ^ 3 = 1) : IsPGroup 3 (D.E hω) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨x, hx⟩ := (D.mem_E hω).1 g.2
  apply Subtype.ext
  apply Subtype.ext
  change ((g : ↥D.S.Γ) : ModGL Tag.E6 L) ^ 3 ^ 1 = 1
  rw [hx, pow_one]
  exact dV_pow_three hω x

theorem Std8.conj_pow_dV (D : Std8 L) {ω : Lˣ} {n : ↥D.S.Γ}
    (hn : ∀ x : Fin Tag.E6.rank → ZMod 3, (n : ModGL Tag.E6 L) * dV ω x *
      (n : ModGL Tag.E6 L)⁻¹ = dV ω (gAct x)) (k : ℕ) (x : Fin Tag.E6.rank → ZMod 3) :
    ((n ^ k : ↥D.S.Γ) : ModGL Tag.E6 L) * dV ω x * ((n ^ k : ↥D.S.Γ) : ModGL Tag.E6 L)⁻¹ =
      dV ω (gAct^[k] x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h1 : ((n ^ (k + 1) : ↥D.S.Γ) : ModGL Tag.E6 L) * dV ω x *
        ((n ^ (k + 1) : ↥D.S.Γ) : ModGL Tag.E6 L)⁻¹ =
          (n : ModGL Tag.E6 L) * (((n ^ k : ↥D.S.Γ) : ModGL Tag.E6 L) * dV ω x *
            ((n ^ k : ↥D.S.Γ) : ModGL Tag.E6 L)⁻¹) * (n : ModGL Tag.E6 L)⁻¹ := by
      rw [pow_succ']
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    rw [h1, ih, hn, Function.iterate_succ_apply']


theorem Std8.exists_conj_dV_of_threeCentral (D : Std8 L)
    {ω : Lˣ} (hω : orderOf ω = 3) {z : ↥D.S.Γ} (hz : IsThreeCentral ↥D.S.Γ z) :
    ∃ (g : ↥D.S.Γ) (c : ZMod 3), c ≠ 0 ∧
      ((g * z * g⁻¹ : ↥D.S.Γ) : ModGL Tag.E6 L) = dV ω (c • x0) := by
  haveI := D.finite_Γ
  have hω3 : ω ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω
    rwa [hω] at this
  obtain ⟨n, hn⟩ := D.exists_lift_list gWord
  have hnG : ∀ x : Fin Tag.E6.rank → ZMod 3, (n : ModGL Tag.E6 L) * dV ω x *
      (n : ModGL Tag.E6 L)⁻¹ = dV ω (gAct x) := fun x => hn hω3 x
  have hn9 : (n ^ 9 : ↥D.S.Γ) ^ 9 = 1 := by
    have hmM : ((n ^ 9 : ↥D.S.Γ) : ModGL Tag.E6 L) ∈ D.S.D.model := D.Γ_le_model (n ^ 9).2
    have hcomm : ∀ x : Fin Tag.E6.rank → ZMod 3,
        Commute (dV ω x) ((n ^ 9 : ↥D.S.Γ) : ModGL Tag.E6 L) := fun x => by
      have h := D.conj_pow_dV hnG 9 x
      rw [gAct_pow_nine] at h
      exact ((mul_inv_eq_iff_eq_mul.1 h).symm : _)
    have hT := mem_torusGroup_of_commute_dV hω ((D.mem_model_iff.1 hmM).1) hcomm
    have hmT : ((n ^ 9 : ↥D.S.Γ) : ModGL Tag.E6 L) ∈ D.S.D.torus :=
      D.mem_torus_iff.2 ⟨hT, (D.mem_model_iff.1 hmM).2⟩
    apply Subtype.ext
    simpa using D.pow_nine_of_mem_torus hmT
  have hHp : IsPGroup 3 (Subgroup.zpowers n) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨4, ?_⟩
    apply Subtype.ext
    change (n ^ j) ^ 3 ^ 4 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have h81 : n ^ 3 ^ 4 = 1 := by
      rw [show (3 : ℕ) ^ 4 = 9 * 9 by norm_num, pow_mul]
      exact hn9
    rw [h81, one_zpow]
  have hnN : n ∈ Subgroup.normalizer ((D.E hω3 : Subgroup ↥D.S.Γ) : Set ↥D.S.Γ) := by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    obtain ⟨x, hx⟩ := (D.mem_E hω3).1 he
    refine (D.mem_E hω3).2 ⟨gAct x, ?_⟩
    change (n : ModGL Tag.E6 L) * (e : ModGL Tag.E6 L) * (n : ModGL Tag.E6 L)⁻¹ = _
    rw [hx]
    exact hnG x
  have hHN : Subgroup.zpowers n ≤ Subgroup.normalizer ((D.E hω3 : Subgroup ↥D.S.Γ) : Set ↥D.S.Γ) :=
    Subgroup.zpowers_le.2 hnN
  obtain ⟨g, hgE, hgH⟩ := exists_conj_mem_centralizer_of_threeCentral (D.isPGroup_E hω3) hHp hHN
    hz.2
  set z' : ↥D.S.Γ := g * z * g⁻¹ with hz'
  have hz'ord : orderOf z' = 3 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z).trans hz.1
  have hz'M : (z' : ModGL Tag.E6 L) ∈ D.S.D.model := D.Γ_le_model z'.2
  have hcomm : ∀ x : Fin Tag.E6.rank → ZMod 3, Commute (dV ω x) (z' : ModGL Tag.E6 L) := fun x => by
    have hxE : (⟨dV ω x, D.dV_mem_Γ hω3 x⟩ : ↥D.S.Γ) ∈ D.E hω3 := (D.mem_E hω3).2 ⟨x, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hgE _ hxE
    exact congrArg Subtype.val this
  have hT := mem_torusGroup_of_commute_dV hω ((D.mem_model_iff.1 hz'M).1) hcomm
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hz'3 : (z' : ModGL Tag.E6 L) ^ 3 = 1 := by
    have := pow_orderOf_eq_one z'
    rw [hz'ord] at this
    simpa using congrArg Subtype.val this
  have ha3 : a ^ 3 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← rootDiagUnit_pow, rootDiagUnit_one, ← ha]
    exact hz'3
  have hai : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun ha3 i
  choose y hy using fun i => CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hω (hai i)
  have hzy : (z' : ModGL Tag.E6 L) = dV ω y := by
    rw [ha]
    unfold dV
    congr 1
    funext i
    exact (hy i).symm
  have hnz : (n : ModGL Tag.E6 L) * (z' : ModGL Tag.E6 L) * (n : ModGL Tag.E6 L)⁻¹ =
      (z' : ModGL Tag.E6 L) := by
    have := Subgroup.mem_centralizer_iff.1 hgH n (Subgroup.mem_zpowers n)
    have h2 : (n : ModGL Tag.E6 L) * (z' : ModGL Tag.E6 L) =
        (z' : ModGL Tag.E6 L) * (n : ModGL Tag.E6 L) := congrArg Subtype.val this
    rw [h2, mul_inv_cancel_right]
  have hfix : gAct y = y := by
    apply dV_injective hω
    rw [← hnG y, ← hzy]
    exact hnz
  obtain ⟨c, hc⟩ := (gAct_eq_self_iff y).1 hfix
  refine ⟨g, c, ?_, by rw [← hz', hzy, hc]⟩
  rintro rfl
  have : (z' : ModGL Tag.E6 L) = 1 := by
    rw [hzy, hc, zero_smul, dV_zero]
  have hz1 : z' = 1 := Subtype.ext this
  rw [hz1, orderOf_one] at hz'ord
  exact absurd hz'ord (by norm_num)

end Toral

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
