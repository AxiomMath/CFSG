module

public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap LinearMap.BilinForm CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

@[expose] def IsMbarInvariant (W : Submodule (ZMod 2) S.Qt) : Prop :=
  ∀ m : S.M, ∀ v ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W

@[expose] def IsMinimalInvariant (W : Submodule (ZMod 2) S.Qt) : Prop :=
  W ≠ ⊥ ∧ IsMbarInvariant S W ∧
    ∀ U : Submodule (ZMod 2) S.Qt, U ≤ W → IsMbarInvariant S U → U = ⊥ ∨ U = W

@[expose] noncomputable def perp (W : Submodule (ZMod 2) S.Qt) : Submodule (ZMod 2) S.Qt :=
  LinearMap.BilinForm.orthogonal S.q.polarBilin W

variable {S}

theorem mem_perp {W : Submodule (ZMod 2) S.Qt} {v : S.Qt} :
    v ∈ perp S W ↔ ∀ w ∈ W, polar S.q w v = 0 := by
  simp only [perp, LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply]

theorem polar_ρ_apply (m : S.M) (v w : S.Qt) :
    polar S.q ((S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ((S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      polar S.q v w :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m).2 v w

theorem q_ρ_apply (m : S.M) (v : S.Qt) : S.q ((S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (S.ρ m).2 v

theorem ρ_inv_apply_apply (m : S.M) (v : S.Qt) :
    (S.ρ m⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem IsMbarInvariant.perp {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W) :
    IsMbarInvariant S (perp S W) := by
  intro m v hv
  rw [mem_perp] at hv ⊢
  intro w hw
  have h := hv _ (hW m⁻¹ w hw)
  rwa [← polar_ρ_apply m, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← map_mul,
    mul_inv_cancel, map_one] at h

theorem IsMbarInvariant.inf {W U : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
    (hU : IsMbarInvariant S U) : IsMbarInvariant S (W ⊓ U) :=
  fun m v hv => ⟨hW m v hv.1, hU m v hv.2⟩

theorem isTotallyIsotropic_or_isCompl {W : Submodule (ZMod 2) S.Qt}
    (hW : IsMinimalInvariant S W) : W ≤ perp S W ∨ IsCompl W (perp S W) := by
  rcases hW.2.2 (W ⊓ perp S W) (inf_le_left : W ⊓ perp S W ≤ W) (hW.2.1.inf hW.2.1.perp)
    with h | h
  · right
    rw [perp, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint S.polarBilin_isRefl,
      disjoint_iff]
    exact h
  · left
    intro v hv
    rw [← h] at hv
    exact hv.2

theorem restrict_nondegenerate_iff_isCompl {W : Submodule (ZMod 2) S.Qt} :
    (LinearMap.BilinForm.restrict S.q.polarBilin W).Nondegenerate ↔ IsCompl W (perp S W) :=
  LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal S.polarBilin_isRefl

theorem conj_mem_clPre {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W) {m x : G}
    (hm : m ∈ S.M) (hx : x ∈ S.clPre W) : m * x * m⁻¹ ∈ S.clPre W := by
  refine ⟨S.conj_mem_QG hm hx.1, ?_⟩
  rw [← S.ρ_cl ⟨m, hm⟩ hx.1]
  exact hW ⟨m, hm⟩ _ hx.2

theorem commute_of_mem_clPre {W : Submodule (ZMod 2) S.Qt} (hW : W ≤ perp S W) {x y : G}
    (hx : x ∈ S.clPre W) (hy : y ∈ S.clPre W) : x * y = y * x :=
  (S.polar_cl_eq_zero_iff hx.1 hy.1).mp (mem_perp.mp (hW hy.2) _ hx.2)

theorem q_add_of_le_perp {W : Submodule (ZMod 2) S.Qt} (hW : W ≤ perp S W) {v w : S.Qt}
    (hv : v ∈ W) (hw : w ∈ W) : S.q (v + w) = S.q v + S.q w := by
  have h := mem_perp.mp (hW hw) v hv
  rw [polar] at h
  linear_combination h

@[expose] noncomputable def singularPart (W : Submodule (ZMod 2) S.Qt) (hW : W ≤ perp S W) :
    Submodule (ZMod 2) S.Qt where
  carrier := {v | v ∈ W ∧ S.q v = 0}
  add_mem' := fun {v w} hv hw => ⟨W.add_mem hv.1 hw.1, by
    rw [q_add_of_le_perp hW hv.1 hw.1, hv.2, hw.2, add_zero]⟩
  zero_mem' := ⟨W.zero_mem, QuadraticMap.map_zero _⟩
  smul_mem' := fun c v hv => ⟨W.smul_mem c hv.1, by
    rw [QuadraticMap.map_smul, hv.2, smul_zero]⟩

theorem IsMbarInvariant.singularPart {W : Submodule (ZMod 2) S.Qt} (hW : W ≤ DW.perp S W)
    (hinv : IsMbarInvariant S W) : IsMbarInvariant S (DW.singularPart W hW) :=
  fun m v hv => ⟨hinv m v hv.1, by rw [q_ρ_apply, hv.2]⟩

theorem totallySingular_or_line {W : Submodule (ZMod 2) S.Qt} (hW : IsMinimalInvariant S W)
    (hiso : W ≤ perp S W) :
    (∀ v ∈ W, S.q v = 0) ∨ ∃ v : S.Qt, S.q v = 1 ∧ W = ZMod 2 ∙ v := by
  rcases hW.2.2 (singularPart W hiso) (fun v hv => hv.1) (hW.2.1.singularPart hiso) with h | h
  · right
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
    have hq : ∀ w ∈ W, w ≠ 0 → S.q w = 1 := by
      intro w hw hw0
      rcases zmod2_cases (S.q w) with h0 | h1
      · have : w ∈ singularPart W hiso := ⟨hw, h0⟩
        rw [h, Submodule.mem_bot] at this
        exact absurd this hw0
      · exact h1
    refine ⟨v, hq v hvW hv0, le_antisymm (fun w hw => ?_) ?_⟩
    · by_cases hw0 : w = 0
      · rw [hw0]
        exact Submodule.zero_mem _
      · have hs : v + w ∈ singularPart W hiso := by
          refine ⟨W.add_mem hvW hw, ?_⟩
          rw [q_add_of_le_perp hiso hvW hw, hq v hvW hv0, hq w hw hw0]
          decide
        rw [h, Submodule.mem_bot] at hs
        have hwv : w = v := by
          have := congrArg (· + w) hs
          simp only [zero_add] at this
          rw [add_assoc, CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2), add_zero]
            at this
          exact this.symm
        rw [hwv]
        exact Submodule.mem_span_singleton_self v
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hvW
  · left
    intro v hv
    rw [← h] at hv
    exact hv.2

theorem sq_eq_one_of_mem_clPre {W : Submodule (ZMod 2) S.Qt} (hW : ∀ v ∈ W, S.q v = 0) {x : G}
    (hx : x ∈ S.clPre W) : x ^ 2 = 1 :=
  (S.q_cl_eq_zero_iff hx.1).mp (hW _ hx.2)

theorem isElementaryAbelian_clPre {W : Submodule (ZMod 2) S.Qt} (hiso : W ≤ perp S W)
    (hW : ∀ v ∈ W, S.q v = 0) : CFSG.IsElementaryAbelian 2 (S.clPre W) where
  is_comm := ⟨fun x y => Subtype.ext (commute_of_mem_clPre hiso x.2 y.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using sq_eq_one_of_mem_clPre hW x.2)

theorem card_clPre_span_singleton {v : S.Qt} (hv : S.q v = 1) :
    Nat.card (S.clPre (ZMod 2 ∙ v)) = 4 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact absurd hv (by decide)
  rw [S.card_clPre, S.card_submodule, finrank_span_singleton hv0]
  rfl

theorem apply_eq_of_invariant_span {v : S.Qt} (hv0 : v ≠ 0)
    (hinv : IsMbarInvariant S (ZMod 2 ∙ v)) (m : S.M) :
    (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hinv m v (Submodule.mem_span_singleton_self v))
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, eq_comm, LinearEquiv.map_eq_zero_iff] at hc
    exact absurd hc hv0
  · rw [one_smul] at hc
    exact hc.symm

theorem exists_isMinimalInvariant_le {W₀ : Submodule (ZMod 2) S.Qt} (h0 : W₀ ≠ ⊥)
    (hinv : IsMbarInvariant S W₀) : ∃ W ≤ W₀, IsMinimalInvariant S W := by
  have hfin : {U : Submodule (ZMod 2) S.Qt | U ≠ ⊥ ∧ IsMbarInvariant S U}.Finite :=
    Set.toFinite _
  obtain ⟨W, hWle, hWmin⟩ := hfin.exists_le_minimal (a := W₀) ⟨h0, hinv⟩
  refine ⟨W, hWle, hWmin.prop.1, hWmin.prop.2, fun U hUW hU => ?_⟩
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  · exact Or.inr (hWmin.eq_of_le ⟨hU0, hU⟩ hUW)

theorem exists_isMinimalInvariant (hred : S.IsReducible) :
    ∃ W : Submodule (ZMod 2) S.Qt, IsMinimalInvariant S W ∧ W ≠ ⊤ := by
  obtain ⟨W₀, h0, htop, hinv⟩ := hred
  obtain ⟨W, hWle, hW⟩ := exists_isMinimalInvariant_le h0 hinv
  exact ⟨W, hW, fun h => htop (top_le_iff.mp (h ▸ hWle))⟩

theorem reduction (hred : S.IsReducible) :
    ∃ W : Submodule (ZMod 2) S.Qt, IsMinimalInvariant S W ∧ W ≠ ⊤ ∧
      (∀ m ∈ S.M, ∀ x ∈ S.clPre W, m * x * m⁻¹ ∈ S.clPre W) ∧
      (IsCompl W (perp S W) ∨
        (W ≤ perp S W ∧ ∀ x ∈ S.clPre W, x ^ 2 = 1) ∨
        ∃ v : S.Qt, S.q v = 1 ∧ W = ZMod 2 ∙ v) := by
  obtain ⟨W, hW, htop⟩ := exists_isMinimalInvariant hred
  refine ⟨W, hW, htop, fun m hm x hx => conj_mem_clPre hW.2.1 hm hx, ?_⟩
  rcases isTotallyIsotropic_or_isCompl hW with hiso | hc
  · rcases totallySingular_or_line hW hiso with hs | hl
    · exact Or.inr (Or.inl ⟨hiso, fun x hx => sq_eq_one_of_mem_clPre hs hx⟩)
    · exact Or.inr (Or.inr hl)
  · exact Or.inl hc

end CFSG.LargeExtraspecial.DW
