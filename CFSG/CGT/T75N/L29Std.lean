module

public import CFSG.CGT.T75N.L29Rad
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.T75N.L29Dual

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75

variable {F : Type} [Field F] {n : ℕ}

theorem exists_scalar_of_mem_transvImage {U : Subgroup (GL (Fin n) F)}
    {g : SpecialLinearGroup (Fin n) F}
    (h : (QuotientGroup.mk (specialLinearGroupEquivStatedSL n F g) :
      StatedProj (StatedSL n F)) ∈ transvImage n F U) :
    ∃ u : GL (Fin n) F, u ∈ U ∧ ∃ r : Fˣ,
      (g : Matrix (Fin n) (Fin n) F) = (r : F) • (u : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨u', hu', hu'g⟩ := h
  have hmem := QuotientGroup.eq.1 hu'g
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨((u' : StatedSL n F) : GL (Fin n) F), hu', r, ?_⟩
  have h1 : (((specialLinearGroupEquivStatedSL n F g : StatedSL n F) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = g := rfl
  have h2 : ((specialLinearGroupEquivStatedSL n F g : StatedSL n F) : GL (Fin n) F) =
      ((u' : StatedSL n F) : GL (Fin n) F) * Matrix.GeneralLinearGroup.scalar (Fin n) r := by
    have := congrArg (fun x : GL (Fin n) F => ((u' : StatedSL n F) : GL (Fin n) F) * x) hr
    simpa using this.symm
  rw [← h1, h2, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

section Involution

variable [CharP F 2] [NeZero n]

theorem scalar_eq_one_of_involution {M : Matrix (Fin n) (Fin n) F} (r : F) (hMM : M * M = 0)
    (hsq : (r • (1 + M)) * (r • (1 + M)) = 1) : r = 1 := by
  have hM2 : M + M = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  have h1 : (r • (1 + M)) * (r • (1 + M)) = (r * r) • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [smul_mul_smul_comm]
    have : (1 + M) * (1 + M) = 1 + (M + M) + M * M := by noncomm_ring
    rw [this, hM2, hMM]
    simp
  rw [h1] at hsq
  have h2 : r * r = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa using this
  have h3 : (r - 1) * (r + 1) = 0 := by ring_nf; linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · exact sub_eq_zero.1 h
  · have : r = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq]

theorem eq_transvection_of_involution {g : SpecialLinearGroup (Fin n) F} (hg : g * g = 1)
    {r : F} {x y : Fin n → F} (hxy : y ⬝ᵥ x = 0)
    (hgu : (g : Matrix (Fin n) (Fin n) F) = r • (1 + vecMulVec x y)) :
    (g : Matrix (Fin n) (Fin n) F) = 1 + vecMulVec x y := by
  have hsq : (g : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
    have := congrArg (fun z : SpecialLinearGroup (Fin n) F => (z : Matrix (Fin n) (Fin n) F)) hg
    simpa using this
  have hMM : vecMulVec x y * vecMulVec x y = 0 := by
    rw [vecMulVec_mul_vecMulVec, hxy, zero_smul, vecMulVec_zero]
  rw [hgu] at hsq
  have hr : r = 1 := scalar_eq_one_of_involution r hMM hsq
  rw [hgu, hr, one_smul]

theorem std_center_of_involution {Y : Type} [Group Y]
    (e₀ : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL n F))
    (π : Y →* SpecialLinearGroup (Fin n) F)
    (compat : ∀ y : Y, projectiveSpecialLinearGroupEquivStatedProj n F (QuotientGroup.mk (π y)) =
      e₀ (QuotientGroup.mk y))
    {E : Subgroup Y} (hE2 : ∀ x ∈ E, x * x = 1) {c : Fin n → F}
    (hc : (E.map (QuotientGroup.mk' (Subgroup.center Y))).map e₀.toMonoidHom =
      transvImage n F (transvCenter n F c)) :
    ∀ y ∈ E, ∃ a : Fin n → F, a ⬝ᵥ c = 0 ∧
      ((π y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + vecMulVec c a := by
  intro y hy
  have h1 : e₀ (QuotientGroup.mk y) ∈ transvImage n F (transvCenter n F c) := by
    rw [← hc]
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [← compat y] at h1
  have h2 : projectiveSpecialLinearGroupEquivStatedProj n F (QuotientGroup.mk (π y)) =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL n F (π y)) := rfl
  rw [h2] at h1
  obtain ⟨u, hu, r, hr⟩ := exists_scalar_of_mem_transvImage h1
  obtain ⟨a, ha, hau⟩ := hu
  have hg : π y * π y = 1 := by rw [← map_mul, hE2 y hy, map_one]
  exact ⟨a, ha, eq_transvection_of_involution hg ha (by rw [hr, hau])⟩

theorem std_axis_of_involution {Y : Type} [Group Y]
    (e₀ : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL n F))
    (π : Y →* SpecialLinearGroup (Fin n) F)
    (compat : ∀ y : Y, projectiveSpecialLinearGroupEquivStatedProj n F (QuotientGroup.mk (π y)) =
      e₀ (QuotientGroup.mk y))
    {E : Subgroup Y} (hE2 : ∀ x ∈ E, x * x = 1) {a : Fin n → F}
    (hc : (E.map (QuotientGroup.mk' (Subgroup.center Y))).map e₀.toMonoidHom =
      transvImage n F (transvAxis n F a)) :
    ∀ y ∈ E, ∃ v : Fin n → F, a ⬝ᵥ v = 0 ∧
      ((π y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + vecMulVec v a := by
  intro y hy
  have h1 : e₀ (QuotientGroup.mk y) ∈ transvImage n F (transvAxis n F a) := by
    rw [← hc]
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [← compat y] at h1
  have h2 : projectiveSpecialLinearGroupEquivStatedProj n F (QuotientGroup.mk (π y)) =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL n F (π y)) := rfl
  rw [h2] at h1
  obtain ⟨u, hu, r, hr⟩ := exists_scalar_of_mem_transvImage h1
  obtain ⟨v, hv, hvu⟩ := hu
  have hg : π y * π y = 1 := by rw [← map_mul, hE2 y hy, map_one]
  exact ⟨v, hv, eq_transvection_of_involution hg hv (by rw [hr, hvu])⟩

end Involution

section Normalize

variable [Finite F] [CharP F 2] [NeZero n]

omit [CharP F 2] in
theorem exists_std_surjection_center {Y : Type} [Group Y]
    (π : Y →* SpecialLinearGroup (Fin n) F) (hπ : Function.Surjective π) {E : Subgroup Y}
    (hEK : E ⊓ π.ker = ⊥) (hEcard : Nat.card E = Nat.card F ^ (n - 1)) {c : Fin n → F}
    (hc0 : c ≠ 0)
    (hE : ∀ y ∈ E, ∃ a : Fin n → F, a ⬝ᵥ c = 0 ∧
      ((π y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + vecMulVec c a) :
    ∃ π' : Y →* SpecialLinearGroup (Fin n) F, Function.Surjective π' ∧ π'.ker = π.ker ∧
      E.map π' = radRow n F 0 := by
  classical
  have he0 : (Pi.single 0 1 : Fin n → F) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  have h1 : Module.finrank F (Submodule.span F {c}) =
      Module.finrank F (Submodule.span F {(Pi.single 0 1 : Fin n → F)}) := by
    rw [finrank_span_singleton hc0, finrank_span_singleton he0]
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_map_eq_of_finrank_eq h1
  have hgc : (g : Matrix (Fin n) (Fin n) F) *ᵥ c ∈
      Submodule.span F {(Pi.single 0 1 : Fin n → F)} := by
    rw [← hg]
    exact ⟨c, Submodule.mem_span_singleton_self c, rfl⟩
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hgc
  have hginv : ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
      ((g : Matrix (Fin n) (Fin n) F) *ᵥ c) = c := by
    rw [mulVec_mulVec, sl_coe_inv_mul, one_mulVec]
  let π' : Y →* SpecialLinearGroup (Fin n) F := (MulAut.conj g).toMonoidHom.comp π
  have hπ'ker : π'.ker = π.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff (MulAut.conj g)
  have hle : E.map π' ≤ radRow n F 0 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hya⟩ := hE y hy
    refine ⟨r • (a ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)), ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := le_antisymm hi (Fin.zero_le i)
      subst hi0
      rw [Pi.smul_apply, vecMul_apply_eq, smul_eq_mul]
      have h2 : a ⬝ᵥ c = r * (a ⬝ᵥ (((g⁻¹ : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single 0 1 : Fin n → F))) := by
        conv_lhs => rw [← hginv, ← hr]
        rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
      rw [← h2, ha]
    · have key : ((g * π y * g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          rowMat 0 (r • (a ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) F) :
            Matrix (Fin n) (Fin n) F))) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hya]
        unfold rowMat
        rw [conj_one_add_vecMulVec _ _ (sl_coe_mul_inv g), ← hr, smul_vecMulVec, vecMulVec_smul]
      exact key
  refine ⟨π', (MulAut.conj g).surjective.comp hπ, hπ'ker, ?_⟩
  have hinj : Function.Injective (π'.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : (x : Y) ∈ π.ker := by
      rw [← hπ'ker]
      exact hx
    have hx' : (x : Y) ∈ E ⊓ π.ker := ⟨x.2, hxK⟩
    rw [hEK, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hcard : Nat.card (E.map π') = Nat.card E := by
    have h2 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h2
    exact h2.symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, hEcard, card_radRow]
  simp

omit [Finite F] [CharP F 2] [NeZero n] in
theorem tau_center_of_axis {Y : Type} [Group Y] (π : Y →* SpecialLinearGroup (Fin n) F)
    {E : Subgroup Y} (hE2 : ∀ x ∈ E, x * x = 1) {a : Fin n → F}
    (hE : ∀ y ∈ E, ∃ v : Fin n → F, a ⬝ᵥ v = 0 ∧
      ((π y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + vecMulVec v a) :
    ∀ y ∈ E, ∃ a' : Fin n → F, a' ⬝ᵥ (fun i => a (Fin.rev i)) = 0 ∧
      (((tauHom n F).comp π) y : Matrix (Fin n) (Fin n) F) =
        1 + vecMulVec (fun i => a (Fin.rev i)) a' := by
  intro y hy
  obtain ⟨v, hva, hyv⟩ := hE y hy
  have hg : π y * π y = 1 := by rw [← map_mul, hE2 y hy, map_one]
  have hginv : (π y)⁻¹ = π y := inv_eq_of_mul_eq_one_right hg
  refine ⟨fun i => v (Fin.rev i), ?_, ?_⟩
  · have : (fun i => v (Fin.rev i)) ⬝ᵥ (fun i => a (Fin.rev i)) = v ⬝ᵥ a := by
      unfold dotProduct
      exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun i => v i * a i)
    rw [this, dotProduct_comm, hva]
  · ext i j
    rw [MonoidHom.comp_apply, tauHom_apply, hginv, hyv]
    simp [Matrix.one_apply, vecMulVec_apply, Fin.rev_inj, mul_comm, eq_comm]

theorem exists_std_surjection {Y : Type} [Group Y]
    (e₀ : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL n F))
    (π : Y →* SpecialLinearGroup (Fin n) F) (hπ : Function.Surjective π)
    (compat : ∀ y : Y, projectiveSpecialLinearGroupEquivStatedProj n F (QuotientGroup.mk (π y)) =
      e₀ (QuotientGroup.mk y))
    {E : Subgroup Y} (hE2 : ∀ x ∈ E, x * x = 1) (hEK : E ⊓ π.ker = ⊥)
    (hEcard : Nat.card E = Nat.card F ^ (n - 1))
    (hstd : (∃ c : Fin n → F, c ≠ 0 ∧ (E.map (QuotientGroup.mk' (Subgroup.center Y))).map
        e₀.toMonoidHom = transvImage n F (transvCenter n F c)) ∨
      (∃ a : Fin n → F, a ≠ 0 ∧ (E.map (QuotientGroup.mk' (Subgroup.center Y))).map
        e₀.toMonoidHom = transvImage n F (transvAxis n F a))) :
    ∃ π' : Y →* SpecialLinearGroup (Fin n) F, Function.Surjective π' ∧ π'.ker = π.ker ∧
      E.map π' = radRow n F 0 := by
  rcases hstd with ⟨c, hc0, hc⟩ | ⟨a, ha0, ha⟩
  · exact exists_std_surjection_center π hπ hEK hEcard hc0
      (std_center_of_involution e₀ π compat hE2 hc)
  · have hax := std_axis_of_involution e₀ π compat hE2 ha
    have hτ := tau_center_of_axis π hE2 hax
    have hπ₁ : Function.Surjective ((tauHom n F).comp π) :=
      (tauHom_bijective (F := F) n).2.comp hπ
    have hker₁ : ((tauHom n F).comp π).ker = π.ker := by
      ext y
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
      constructor
      · intro h
        exact (tauHom_bijective (F := F) n).1 (h.trans (map_one (tauHom n F)).symm)
      · intro h
        rw [h, map_one]
    have hEK₁ : E ⊓ ((tauHom n F).comp π).ker = ⊥ := by rw [hker₁]; exact hEK
    have hrev : (fun i => a (Fin.rev i)) ≠ 0 := by
      intro h
      apply ha0
      funext i
      simpa using congrFun h (Fin.rev i)
    obtain ⟨π', h1, h2, h3⟩ := exists_std_surjection_center ((tauHom n F).comp π) hπ₁ hEK₁ hEcard
      hrev hτ
    exact ⟨π', h1, h2.trans hker₁, h3⟩

end Normalize

end CFSG.CGT.T75N
