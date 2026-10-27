module

public import CFSG.LargeExtraspecial.S45QSylow
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Module QuadraticMap Subgroup CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem finrank_le_finrank_inf_perp_add_two {W : Submodule (ZMod 2) V} (P : HypPair Q)
    (he : P.e ∈ W) (hf : P.f ∈ W) :
    finrank (ZMod 2) W ≤ finrank (ZMod 2) ↥(W ⊓ P.perp) + 2 := by
  classical
  have hle : W ≤ (W ⊓ P.perp) ⊔ Submodule.span (ZMod 2) ({P.e, P.f} : Set V) := by
    intro x hx
    rw [P.eq_add_proj x]
    have hp : P.proj x ∈ W ⊓ P.perp := by
      refine ⟨?_, P.proj_mem_perp x⟩
      rw [HypPair.proj]
      exact W.sub_mem (W.sub_mem hx (W.smul_mem _ he)) (W.smul_mem _ hf)
    refine Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))) (Submodule.mem_sup_left hp)
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ P.perp)
    (Submodule.span (ZMod 2) ({P.e, P.f} : Set V))
  have h3 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({P.e, P.f} : Set V)) ≤ 2 := by
    have := finrank_span_finset_le_card (R := ZMod 2) ({P.e, P.f} : Finset V)
    rw [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans ((Finset.card_insert_le _ _).trans (by simp))
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_singular_mem {W : Submodule (ZMod 2) V} [FiniteDimensional (ZMod 2) W]
    (h3 : 3 ≤ finrank (ZMod 2) W) : ∃ x ∈ W, x ≠ 0 ∧ Q x = 0 := by
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_map_eq_zero (Q := Q.comp W.subtype) h3
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), hx⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_hypPair_mem {W : Submodule (ZMod 2) V} (hW : PolarNondegOn Q W) {b : V}
    (hbW : b ∈ W) (hb0 : b ≠ 0) (hb : Q b = 0) : ∃ P : HypPair Q, P.e = b ∧ P.f ∈ W := by
  obtain ⟨y, hyW, hy⟩ := hW.exists_polar_ne_zero hbW hb0
  have hy1 : polar Q b y = 1 := CFSG.RankThree.Literature.FSmith.zmod2_eq_one_of_ne_zero hy
  refine ⟨HypPair.ofPolarEqOne hb hy1, rfl, ?_⟩
  rw [HypPair.ofPolarEqOne_f]
  exact W.sub_mem hyW (W.smul_mem _ hbW)

theorem exists_two_hypPairs (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V) :
    ∃ P₁ P₂ : HypPair Q, P₁.Orth P₂ ∧ PolarNondegOn Q (P₁.perp ⊓ P₂.perp) ∧
      finrank (ZMod 2) V ≤ finrank (ZMod 2) ↥(P₁.perp ⊓ P₂.perp) + 4 := by
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_map_eq_zero (Q := Q) (by omega)
  obtain ⟨P₁, rfl⟩ := exists_hypPair hQ ha ha0
  have hW₁ := HypPair.polarNondegOn_perp hQ P₁
  have hd₁ := finrank_le_finrank_inf_perp_add_two (W := ⊤) P₁ trivial trivial
  rw [top_inf_eq, finrank_top] at hd₁
  obtain ⟨b, hbW, hb0, hb⟩ := exists_singular_mem (Q := Q) (W := P₁.perp) (by omega)
  obtain ⟨P₂, rfl, hf₂⟩ := exists_hypPair_mem hW₁ hbW hb0 hb
  have hW₂ := hW₁.inf_perp P₂ hbW hf₂
  have hd₂ := finrank_le_finrank_inf_perp_add_two (W := P₁.perp) P₂ hbW hf₂
  exact ⟨P₁, P₂, ⟨(HypPair.mem_perp.mp hbW).1, (HypPair.mem_perp.mp hf₂).1,
    (HypPair.mem_perp.mp hbW).2, (HypPair.mem_perp.mp hf₂).2⟩, hW₂, by omega⟩

theorem exists_third_hypPair {P₁ P₂ : HypPair Q} (hW : PolarNondegOn Q (P₁.perp ⊓ P₂.perp))
    (h3 : 3 ≤ finrank (ZMod 2) ↥(P₁.perp ⊓ P₂.perp)) :
    ∃ P₃ : HypPair Q, P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  obtain ⟨c, hcW, hc0, hc⟩ := exists_singular_mem (Q := Q) h3
  obtain ⟨P₃, rfl, hf₃⟩ := exists_hypPair_mem hW hcW hc0 hc
  exact ⟨P₃, ⟨(HypPair.mem_perp.mp hcW.1).1, (HypPair.mem_perp.mp hf₃.1).1,
      (HypPair.mem_perp.mp hcW.1).2, (HypPair.mem_perp.mp hf₃.1).2⟩,
    ⟨(HypPair.mem_perp.mp hcW.2).1, (HypPair.mem_perp.mp hf₃.2).1,
      (HypPair.mem_perp.mp hcW.2).2, (HypPair.mem_perp.mp hf₃.2).2⟩⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem scalars_subgroupOf_eq_bot [Nontrivial V] (H : Subgroup (V ≃ₗ[ZMod 2] V)) :
    (scalars (ZMod 2) V).subgroupOf H = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := mem_scalars.mp (mem_subgroupOf.mp hg)
  rw [mem_bot]
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one c with rfl | rfl
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 := hc ((g : V ≃ₗ[ZMod 2] V).symm v)
    rw [LinearEquiv.apply_symm_apply, zero_smul] at h1
    exact absurd h1 hv
  · exact Subtype.ext (LinearEquiv.ext fun v => by rw [hc v, one_smul]; rfl)

theorem isSimpleGroup_omegaGroup_of_hypPairs (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) : IsSimpleGroup (omegaGroup Q hQ) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hgen := orthogonalGroup_eq_closure_reflect hQ (by omega) (Or.inl (by omega))
  have hE := commutator_orthogonalGroup_eq_of_le_closure hQ h₁₂ h₁₃ h₂₃
    (hgen.le.trans (closure_mono Set.subset_union_left))
  have hΩ := CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6
  have := isSimpleGroup_projElementary_of_hypPairs hQ h₁₂ h₁₃ h₂₃
  let e : elementaryGroup Q ≃* ProjElementary Q :=
    ((QuotientGroup.quotientMulEquivOfEq (scalars_subgroupOf_eq_bot _)).trans
      QuotientGroup.quotientBot).symm
  exact ((MulEquiv.subgroupCongr (hΩ.symm.trans hE)).trans e).isSimpleGroup

section Eichler

variable {a b u w : V} (ha : Q a = 0) (hb : Q b = 0) (hab : polar Q a b = 0)
  (hau : polar Q a u = 0) (haw : polar Q a w = 0) (hbu : polar Q b u = 0)
  (hbw : polar Q b w = 0) (huw : polar Q u w = 1)
include ha hb hab hau haw hbu hbw huw

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_pair_sq_apply (v : V) :
    ((eichler Q a u * eichler Q b w) ^ 2) v = v + polar Q v b • a + polar Q v a • b := by
  have hba : polar Q b a = 0 := by rw [polar_comm, hab]
  have hua : polar Q u a = 0 := by rw [polar_comm, hau]
  have hwa : polar Q w a = 0 := by rw [polar_comm, haw]
  have hub : polar Q u b = 0 := by rw [polar_comm, hbu]
  have hwb : polar Q w b = 0 := by rw [polar_comm, hbw]
  have hwu : polar Q w u = 1 := by rw [polar_comm, huw]
  have haa := CFSG.RankThree.Literature.FSmith.polar_self_zmod2 (Q := Q) a
  have hbb := CFSG.RankThree.Literature.FSmith.polar_self_zmod2 (Q := Q) b
  have huu := CFSG.RankThree.Literature.FSmith.polar_self_zmod2 (Q := Q) u
  have hww := CFSG.RankThree.Literature.FSmith.polar_self_zmod2 (Q := Q) w
  simp only [_root_.sq, LinearEquiv.mul_apply, CFSG.LargeExtraspecial.eichler_apply_zmod2 ha hau,
    CFSG.LargeExtraspecial.eichler_apply_zmod2 hb hbw, polar_add_left, polar_smul_left,
    smul_eq_mul, hba, hua, hwa, hub, hwb, hwu, haa, hbb, huu, hww, hab, hau, haw, hbu, hbw, huw]
  match_scalars <;> ring_nf <;> reduce_mod_char

end Eichler

theorem nonabelianSylowTwo_omegaGroup (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) : S5.NonabelianSylowTwo (omegaGroup Q hQ) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨P₁, P₂, h₁₂, hW, hd⟩ := exists_two_hypPairs hQ (by omega)
  have hWne : P₁.perp ⊓ P₂.perp ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd
    omega
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  obtain ⟨w, hwW, hw⟩ := hW.exists_polar_ne_zero huW hu0
  have huw : polar Q u w = 1 := CFSG.RankThree.Literature.FSmith.zmod2_eq_one_of_ne_zero hw
  have hau := (HypPair.mem_perp.mp huW.1).1
  have hbu := (HypPair.mem_perp.mp huW.2).1
  have haw := (HypPair.mem_perp.mp hwW.1).1
  have hbw := (HypPair.mem_perp.mp hwW.2).1
  have hab := h₁₂.ee
  have hsq := eichler_pair_sq_apply P₁.Q_e P₂.Q_e hab hau haw hbu hbw huw
  set x := eichler Q P₁.e u
  set y := eichler Q P₂.e w
  have hxx : x * x = 1 := CFSG.LargeExtraspecial.eichler_mul_self hau
  have hyy : y * y = 1 := CFSG.LargeExtraspecial.eichler_mul_self hbw
  have hT2 : (x * y) ^ 2 ≠ 1 := by
    intro h
    have h1 := hsq P₁.f
    rw [h, h₁₂.fe, P₁.polar_fe, zero_smul, add_zero, one_smul] at h1
    change P₁.f = P₁.f + P₂.e at h1
    rw [left_eq_add] at h1
    exact P₂.e_ne_zero h1
  refine nonabelianSylowTwo_of_mem (S2.eichler_mem_omegaGroup hQ _ _)
    (S2.eichler_mem_omegaGroup hQ _ _) hxx hyy (k := 2) ?_ ?_
  · rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul]
    ext v
    rw [_root_.sq ((x * y) ^ 2), LinearEquiv.mul_apply, hsq, hsq]
    have hba : polar Q P₂.e P₁.e = 0 := by rw [polar_comm, hab]
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, hab, hba,
      CFSG.RankThree.Literature.FSmith.polar_self_zmod2]
    change _ = v
    match_scalars <;> ring_nf <;> reduce_mod_char
  · intro h
    apply hT2
    rw [_root_.sq, show x * y * (x * y) = x * (y * x) * y by group, ← h,
      show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, one_mul]

end CFSG.LargeExtraspecial.S45Q
