module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem exists_conj_mem_innAutDerived_CQ (σ : L ≃+* L) {Q : ℕ} (hσ : ∀ c, σ c = c ^ Q)
    (i : KernelComponent χ) {g : ModGL τ L}
    (hg : g ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hgc : ∀ x ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)),
      x * (frobGL σ g * g⁻¹) = frobGL σ g * g⁻¹ * x) :
    ∃ hgC : MulAut.conj g ∈ CFSG.GroupActions.subgroupStabAut (CQ σ i),
      CFSG.GroupActions.subgroupStabRestrict (CQ σ i) ⟨MulAut.conj g, hgC⟩ ∈
        innAutDerived ↥(CQ σ i) := by
  classical
  obtain ⟨σ₂, hσ₂⟩ := exists_ringEquiv_frob (L := L) 2 1
  have hσ₂' : ∀ c : L, σ₂ c = c ^ 2 := by
    intro c
    have h := RingHom.congr_fun hσ₂ c
    rw [iterateFrobenius_def] at h
    simpa using h
  have hcomm : ∀ c : L, σ (σ₂ c) = σ₂ (σ c) := by
    intro c
    rw [hσ₂' c, hσ₂' (σ c), hσ (c ^ 2), hσ c, ← pow_mul c 2 Q, ← pow_mul c Q 2,
      Nat.mul_comm]
  have hex : ∃ s : Lˣ, s ^ 2 ≠ 1 := by
    classical
    obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hu0 : u ≠ 0 := fun h => hu (by simp [h])
    refine ⟨Units.mk0 u hu0, fun h => hu ?_⟩
    have h2 : u ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (u - 1) * (u + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  obtain ⟨s, hs⟩ := hex
  set c : ModGL τ L := frobGL σ g * g⁻¹ with hcdef
  have hcS : c ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    rw [hcdef]
    exact mul_mem (frobGL_mem_rootSpan σ hg) (inv_mem hg)
  have hcT : c ∈ unionTorus L χ ({i} : Set (KernelComponent χ)) :=
    central_mem_unionTorus (i := i) (c := c) ⟨s, hs⟩ hcS hgc
  have hyc : frobGL σ g = c * g := by
    rw [hcdef]
    group
  obtain ⟨t, ht, x, hx, hgtx, hφt⟩ :=
    exists_decomp (σ := σ) (i := i) (c := c) hg hcT hyc
  obtain ⟨htm, hti⟩ := torus_normalizes_CQ (i := i) ht hgc hφt
  have hxm : ∀ y ∈ CQ σ i, x * y * x⁻¹ ∈ CQ σ i :=
    fun y hy => mul_mem (mul_mem hx hy) (inv_mem hx)
  have hxi : ∀ y ∈ CQ σ i, x⁻¹ * y * x ∈ CQ σ i :=
    fun y hy => mul_mem (mul_mem (inv_mem hx) hy) hx
  have hgm : ∀ y ∈ CQ σ i, g * y * g⁻¹ ∈ CQ σ i := by
    intro y hy
    rw [show g * y * g⁻¹ = t * (x * y * x⁻¹) * t⁻¹ by rw [hgtx]; group]
    exact htm _ (hxm y hy)
  have hgi : ∀ y ∈ CQ σ i, g⁻¹ * y * g ∈ CQ σ i := by
    intro y hy
    rw [show g⁻¹ * y * g = x⁻¹ * (t⁻¹ * y * t) * x by rw [hgtx]; group]
    exact hxi _ (hti y hy)
  have hgC : MulAut.conj g ∈ CFSG.GroupActions.subgroupStabAut (CQ σ i) := by
    change (CQ σ i).map (MulAut.conj g).toMonoidHom = CQ σ i
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      simpa [MulAut.conj_apply] using hgm y hy
    · intro y hy
      exact ⟨g⁻¹ * y * g, hgi y hy, by
        change g * (g⁻¹ * y * g) * g⁻¹ = y
        group⟩
  have htC : MulAut.conj t ∈ CFSG.GroupActions.subgroupStabAut (CQ σ i) := by
    change (CQ σ i).map (MulAut.conj t).toMonoidHom = CQ σ i
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      simpa [MulAut.conj_apply] using htm y hy
    · intro y hy
      exact ⟨t⁻¹ * y * t, hti y hy, by
        change t * (t⁻¹ * y * t) * t⁻¹ = y
        group⟩
  have hxC : MulAut.conj x ∈ CFSG.GroupActions.subgroupStabAut (CQ σ i) := by
    change (CQ σ i).map (MulAut.conj x).toMonoidHom = CQ σ i
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      simpa [MulAut.conj_apply] using hxm y hy
    · intro y hy
      exact ⟨x⁻¹ * y * x, hxi y hy, by
        change x * (x⁻¹ * y * x) * x⁻¹ = y
        group⟩
  have hcancel : ∀ z : ModGL τ L, frobGL σ₂ (frobGL σ₂.symm z) = z := by
    intro z
    have hσ₂inv : σ₂ * σ₂.symm = 1 := mul_inv_cancel σ₂
    have h := units_map_entrywiseHom_mul_ringEquiv σ₂ σ₂.symm z
    rw [hσ₂inv, units_map_entrywiseHom_one_ringEquiv] at h
    exact h.symm
  have hcancel' : ∀ z : ModGL τ L, frobGL σ₂.symm (frobGL σ₂ z) = z := by
    intro z
    have hσ₂inv : σ₂.symm * σ₂ = 1 := inv_mul_cancel σ₂
    have h := units_map_entrywiseHom_mul_ringEquiv σ₂.symm σ₂ z
    rw [hσ₂inv, units_map_entrywiseHom_one_ringEquiv] at h
    exact h.symm
  have hCQmap : (CQ σ i).map (frobGL σ₂) = CQ σ i := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      change frobGL σ₂ y ∈ CQ σ i
      unfold CQ at hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
          obtain ⟨γ, hγ, d, hd, rfl⟩ := hz
          rw [frobGL_pinnedX]
          exact pinnedX_mem_CQ hγ (by rw [hcomm, hd])
      | one => rw [map_one]; exact one_mem _
      | mul a b _ _ iha ihb => rw [map_mul]; exact mul_mem iha ihb
      | inv a _ iha => rw [map_inv]; exact inv_mem iha
    · intro y hy
      unfold CQ at hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
          obtain ⟨γ, hγ, d, hd, rfl⟩ := hz
          exact ⟨pinnedX τ L γ (σ₂.symm d), pinnedX_mem_CQ hγ (by
            apply σ₂.injective
            rw [← hcomm, RingEquiv.apply_symm_apply, hd]),
            by rw [frobGL_pinnedX, RingEquiv.apply_symm_apply]⟩
      | one => exact ⟨1, one_mem _, map_one _⟩
      | mul a b _ _ iha ihb =>
          obtain ⟨a', ha', rfl⟩ := iha
          obtain ⟨b', hb', rfl⟩ := ihb
          exact ⟨a' * b', mul_mem ha' hb', by rw [map_mul]⟩
      | inv a _ iha =>
          obtain ⟨a', ha', rfl⟩ := iha
          exact ⟨a'⁻¹, inv_mem ha', by rw [map_inv]⟩
  let frob₂ : MulAut (ModGL τ L) :=
    { toFun := frobGL σ₂
      invFun := frobGL σ₂.symm
      left_inv := hcancel'
      right_inv := hcancel
      map_mul' := map_mul (frobGL σ₂) }
  have frob₂_mem : frob₂ ∈ CFSG.GroupActions.subgroupStabAut (CQ σ i) := by
    change (CQ σ i).map frob₂.toMonoidHom = CQ σ i
    exact hCQmap
  have hφ₂t : frobGL σ₂ t = t * t := by
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
    rw [hl, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit,
      ← rootDiagUnit_mul]
    congr 1
    funext j
    exact Units.ext (by simp [hσ₂', pow_two])
  have hconj_comm : MulAut.conj t = ⁅frob₂, MulAut.conj t⁆ := by
    refine MulEquiv.ext fun y => ?_
    simp only [commutatorElement_def, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply]
    change t * y * t⁻¹ = frobGL σ₂ (t * frobGL σ₂.symm (t⁻¹ * y * t) * t⁻¹)
    rw [map_mul, map_mul, map_inv, hφ₂t, hcancel]
    group
  let φ₂ : MulAut ↥(CQ σ i) :=
    CFSG.GroupActions.subgroupStabRestrict (CQ σ i) ⟨frob₂, frob₂_mem⟩
  let φt : MulAut ↥(CQ σ i) :=
    CFSG.GroupActions.subgroupStabRestrict (CQ σ i) ⟨MulAut.conj t, htC⟩
  let φx : MulAut ↥(CQ σ i) :=
    CFSG.GroupActions.subgroupStabRestrict (CQ σ i) ⟨MulAut.conj x, hxC⟩
  have hφt_comm : φt = ⁅φ₂, φt⁆ := by
    have hsub : (⟨MulAut.conj t, htC⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i)) =
        ⁅(⟨frob₂, frob₂_mem⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i)),
          (⟨MulAut.conj t, htC⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i))⁆ := by
      apply Subtype.ext
      exact hconj_comm
    calc φt = CFSG.GroupActions.subgroupStabRestrict (CQ σ i)
          (⟨MulAut.conj t, htC⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i)) := rfl
      _ = CFSG.GroupActions.subgroupStabRestrict (CQ σ i)
            ⁅(⟨frob₂, frob₂_mem⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i)),
              (⟨MulAut.conj t, htC⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i))⁆ :=
            congrArg (CFSG.GroupActions.subgroupStabRestrict (CQ σ i)) hsub
      _ = ⁅φ₂, φt⁆ := by rw [map_commutatorElement]
  have hφt_derived : φt ∈ commutator (MulAut ↥(CQ σ i)) := by
    rw [hφt_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hφx_eq : φx = MulAut.conj (⟨x, hx⟩ : ↥(CQ σ i)) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.subgroupStabRestrict_conj_of_mem_kd264alg hx hxC
  have hφx_inner : φx ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(CQ σ i) := by
    rw [hφx_eq]
    exact ⟨⟨x, hx⟩, rfl⟩
  have hconj_mul : MulAut.conj g = MulAut.conj t * MulAut.conj x := by
    rw [hgtx]
    exact map_mul MulAut.conj t x
  have hsub_g : (⟨MulAut.conj g, hgC⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i)) =
      (⟨MulAut.conj t, htC⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i)) *
        (⟨MulAut.conj x, hxC⟩ : CFSG.GroupActions.subgroupStabAut (CQ σ i)) := by
    apply Subtype.ext
    exact hconj_mul
  have hφg_eq : CFSG.GroupActions.subgroupStabRestrict (CQ σ i) ⟨MulAut.conj g, hgC⟩ =
      φt * φx := by
    rw [hsub_g, map_mul]
  refine ⟨hgC, ?_⟩
  rw [hφg_eq]
  exact mul_mem (commutator_le_innAutDerived _ hφt_derived)
    (inner_le_innAutDerived _ hφx_inner)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
