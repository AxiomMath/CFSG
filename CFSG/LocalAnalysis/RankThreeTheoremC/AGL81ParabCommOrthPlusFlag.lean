module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelMaximal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix QuadraticMap CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (native_partialBorel_eq_fullBorel)

variable {r : ℕ} {K : Type} [Field K]

section Basic

variable [Finite K] [CharP K 2]

theorem posUnip_le_plusFlagStab (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) :
    posUnip r K ≤ plusFlagStab K r D := by
  intro g hg
  have hb : g ∈ OrthogonalSplit.borel r K := by
    rw [← native_partialBorel_eq_fullBorel r K hr]
    exact posUnip_le_flagStab hg
  exact mem_plusFlagStab.2 ⟨OrthogonalSplit.borel_le hb, fun d hd =>
    MulAction.mem_stabilizer_iff.1 (borel_le_stabilizer_flag (hD d hd).1 (hD d hd).2 hb)⟩

theorem fieldConj_mem_plusFlagStab (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r)
    (σ : K ≃+* K) {x : GLV r K} (hx : x ∈ plusFlagStab K r D) :
    fieldConj r K σ x ∈ plusFlagStab K r D := by
  obtain ⟨hxE, hxF⟩ := mem_plusFlagStab.1 hx
  exact mem_plusFlagStab.2 ⟨fieldConj_mem_orthElementaryGroup hr σ hxE,
    fun d hd => smul_flag_fieldConj σ (hD d hd) (hxF d hd)⟩


@[expose] def Normalizes (D : Finset ℕ) (h : GLV r K) (σ : K ≃+* K) : Prop :=
  ∀ q ∈ plusFlagStab K r D, ∃ x ∈ plusFlagStab K r D, h * fieldConj r K σ x * h⁻¹ = q

theorem smul_invariant (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {h : GLV r K}
    {σ : K ≃+* K} (hN : Normalizes D h σ) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ q ∈ plusFlagStab K r D, q • W = W) :
    ∀ q ∈ plusFlagStab K r D, q • (h • W) = h • W := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := hN q hq
  have hxσ := hW _ (fieldConj_mem_plusFlagStab hr hD σ hx)
  have hmul : h * fieldConj r K σ x * h⁻¹ * h = h * fieldConj r K σ x := by group
  rw [← mul_smul, hmul, mul_smul, hxσ]

theorem finrank_Xstar (hr : 3 ≤ r) :
    Module.finrank K ↥(Xstar r K (by omega : 0 < r)) = r := by
  have h := (swapPair_smul_flag_top (K := K) hr).1
  have h2 := LinearEquiv.finrank_map_eq (swapPair K (⟨r - 1, by omega⟩ : Fin r))
    (flag r K r)
  rw [finrank_flag_of_le le_rfl] at h2
  rw [← h]
  exact h2

theorem classify_invariant (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : ∀ q ∈ plusFlagStab K r D, q • W = W)
    (hs : ∀ x ∈ W, quadPlus r K x = 0) (h1 : 1 ≤ Module.finrank K ↥W) :
    (Module.finrank K ↥W ≤ r - 1 ∧ W = flag r K (Module.finrank K ↥W)) ∨
      (Module.finrank K ↥W = r ∧ (W = flag r K r ∨ W = Xstar r K (by omega : 0 < r))) := by
  have hne : W ≠ ⊥ := by
    rintro rfl
    simp at h1
  have hinv : ∀ g ∈ posUnip r K, W.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = W :=
    fun g hg => hW g (posUnip_le_plusFlagStab hr hD hg)
  rcases ((orthogonal_geometry_split_unipotent_invariant_singular_subspaces (K := K)
    (by omega)).2.1 W hne hs).1 hinv with ⟨i, hi1, hi2, hWi⟩ | hWX | hWX
  · have hf : Module.finrank K ↥W = i := by rw [hWi, finrank_flag_of_le (by omega)]
    rw [hf]
    exact Or.inl ⟨hi2, hWi⟩
  · have hf : Module.finrank K ↥W = r := by rw [hWX, finrank_flag_of_le le_rfl]
    exact Or.inr ⟨hf, Or.inl hWX⟩
  · have hf : Module.finrank K ↥W = r := by rw [hWX, finrank_Xstar hr]
    exact Or.inr ⟨hf, Or.inr hWX⟩

theorem smul_flag_mem (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) {h : GLV r K}
    {σ : K ≃+* K} (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
    (hN : Normalizes D h σ) {d : ℕ} (hd : d ∈ D) :
    (d < r ∧ h • flag r K d = flag r K d) ∨
      (d = r ∧ (h • flag r K r = flag r K r ∨
        h • flag r K r = Xstar r K (by omega : 0 < r))) := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hinv := smul_invariant hr hD' hN
    (W := flag r K d) fun q hq => (mem_plusFlagStab.1 hq).2 d hd
  have hfr : Module.finrank K ↥(h • flag r K d) = d := by
    have := LinearEquiv.finrank_map_eq h (flag r K d)
    rw [finrank_flag_of_le (hD d hd).2] at this
    exact this
  have hs : ∀ x ∈ h • flag r K d, quadPlus r K x = 0 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    change quadPlus r K (h v) = 0
    rw [map_of_mem hO]
    exact flag_singular d v hv
  rcases classify_invariant hr hD hinv hs (by rw [hfr]; exact (hD d hd).1) with
    ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
  · rw [hfr] at h1 h2
    exact Or.inl ⟨by have := (hD d hd).1; omega, h2⟩
  · rw [hfr] at h1
    rw [h1] at h2
    exact Or.inr ⟨h1, Or.inl h2⟩
  · rw [hfr] at h1
    rw [h1] at h2
    exact Or.inr ⟨h1, Or.inr h2⟩


theorem sCoord_mem_Xstar (σ : K ≃+* K) (hr : 0 < r) {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ Xstar r K hr) : sCoord σ v ∈ Xstar r K hr := by
  obtain ⟨h1, h2⟩ := (mem_Xstar hr).1 hv
  exact (mem_Xstar hr).2 ⟨by simp [h1], fun k hk => by simp [h2 k hk]⟩

theorem smul_Xstar_fieldConj (σ : K ≃+* K) (hr : 0 < r) {x : GLV r K}
    (hx : x • Xstar r K hr = Xstar r K hr) :
    fieldConj r K σ x • Xstar r K hr = Xstar r K hr := by
  have hmem : ∀ y : GLV r K, y • Xstar r K hr = Xstar r K hr →
      ∀ v ∈ Xstar r K hr, y v ∈ Xstar r K hr := by
    intro y hy v hv
    have := Submodule.smul_mem_pointwise_smul v y _ hv
    rw [hy] at this
    exact this
  have hle : ∀ y : GLV r K, y • Xstar r K hr = Xstar r K hr →
      ∀ v ∈ Xstar r K hr, fieldConj r K σ y v ∈ Xstar r K hr := by
    intro y hy v hv
    rw [fieldConj_apply]
    exact sCoord_mem_Xstar σ hr (hmem y hy _ (sCoord_mem_Xstar σ.symm hr hv))
  have hx' : x⁻¹ • Xstar r K hr = Xstar r K hr := by
    rw [inv_smul_eq_iff]
    exact hx.symm
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
    exact hle x hx w hw
  · intro hv
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨fieldConj r K σ x⁻¹ v,
      hle x⁻¹ hx' v hv, ?_⟩
    change fieldConj r K σ x (fieldConj r K σ x⁻¹ v) = v
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem exists_stab_X_not_stab_Xstar (hr : 3 ≤ r) :
    ∃ g ∈ orthElementaryGroup (quadPlus r K), g • flag r K r = flag r K r ∧
      g • Xstar r K (by omega : 0 < r) ≠ Xstar r K (by omega : 0 < r) := by
  let i₀ : Fin r := ⟨r - 1, by omega⟩
  let j₀ : Fin r := ⟨0, by omega⟩
  have hij : coordIdx (Sum.inl i₀ : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inl j₀) := by
    simp only [coordIdx_inl, i₀, j₀, ne_eq, Fin.mk.injEq]
    omega
  refine ⟨rpElt (Sum.inl i₀) (Sum.inl j₀) (1 : K), eichler_mem_elementaryGroup _ _ _, ?_, ?_⟩
  · have hle : ∀ v ∈ flag r K r, rpElt (Sum.inl i₀) (Sum.inl j₀) (1 : K) v ∈ flag r K r := by
      intro v hv
      obtain ⟨hv1, -⟩ := mem_flag_iff_coord.1 hv
      rw [rpElt_apply hij]
      refine mem_flag_iff_coord.2 ⟨fun k => ?_, fun k hk => absurd k.2 (by omega)⟩
      simp [hv1 k, hv1 i₀, Pi.single_apply]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hle v hv
    · exact LinearEquiv.finrank_map_eq _ _
  · intro hX
    have hf : (Pi.single (Sum.inr i₀) (1 : K) : Fin r ⊕ Fin r → K) ∈ Xstar r K (by omega) := by
      refine (mem_Xstar (by omega)).2 ⟨by simp, fun k hk => ?_⟩
      have : (Sum.inr k : Fin r ⊕ Fin r) ≠ Sum.inr i₀ := by simpa [i₀] using hk
      simp [Pi.single_eq_of_ne this]
    have hg := Submodule.smul_mem_pointwise_smul _ (rpElt (Sum.inl i₀) (Sum.inl j₀) (1 : K)) _ hf
    rw [hX] at hg
    have h2 := ((mem_Xstar (by omega)).1 hg).2 j₀ (by simp [i₀, j₀, Fin.ext_iff]; omega)
    have hji : (Sum.inr j₀ : Fin r ⊕ Fin r) ≠ Sum.inr i₀ := by
      simp only [ne_eq, Sum.inr.injEq, i₀, j₀, Fin.mk.injEq]
      omega
    change rpElt (Sum.inl i₀) (Sum.inl j₀) (1 : K) (Pi.single (Sum.inr i₀) 1) (Sum.inr j₀) = 0
      at h2
    rw [rpElt_apply hij] at h2
    simp [Pi.single_apply, hji] at h2

theorem mem_of_pow_eq_one {G : Type*} [Group G] (α : MulAut G) {T₁ T₂ : Set G}
    (h12 : ∀ x ∈ T₁, α x ∈ T₂) (h21 : ∀ x ∈ T₂, α x ∈ T₁) {n : ℕ} (hn : Odd n)
    (hα : α ^ n = 1) : ∀ x ∈ T₁, x ∈ T₂ := by
  have key : ∀ j : ℕ, (∀ x ∈ T₁, (α ^ j) x ∈ (if Even j then T₁ else T₂)) ∧
      (∀ x ∈ T₂, (α ^ j) x ∈ (if Even j then T₂ else T₁)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hpar : Even (j + 1) ↔ ¬ Even j := by rw [Nat.even_add_one]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [pow_succ', MulAut.mul_apply]
        have := ih.1 x hx
        by_cases hj : Even j
        · rw [if_pos hj] at this
          rw [if_neg (hpar.not.2 (not_not.2 hj))]
          exact h12 _ this
        · rw [if_neg hj] at this
          rw [if_pos (hpar.2 hj)]
          exact h21 _ this
      · rw [pow_succ', MulAut.mul_apply]
        have := ih.2 x hx
        by_cases hj : Even j
        · rw [if_pos hj] at this
          rw [if_neg (hpar.not.2 (not_not.2 hj))]
          exact h21 _ this
        · rw [if_neg hj] at this
          rw [if_pos (hpar.2 hj)]
          exact h12 _ this
  intro x hx
  have := (key n).1 x hx
  rw [hα, if_neg (Nat.not_even_iff_odd.2 hn)] at this
  exact this

theorem flag_top_ne_Xstar (hr : 3 ≤ r) :
    flag r K r ≠ Xstar r K (by omega : 0 < r) := by
  intro h
  have hf : (Pi.single (Sum.inr (⟨r - 1, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) ∈
      Xstar r K (by omega) := by
    refine (mem_Xstar (by omega)).2 ⟨by simp, fun k hk => ?_⟩
    have : (Sum.inr k : Fin r ⊕ Fin r) ≠ Sum.inr (⟨r - 1, by omega⟩ : Fin r) := by simpa using hk
    simp [Pi.single_eq_of_ne this]
  rw [← h] at hf
  have := (mem_flag_iff_coord.1 hf).1 ⟨r - 1, by omega⟩
  simp at this

theorem smul_flag_eq (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r)
    {α : MulAut ↥(orthElementaryGroup (quadPlus r K))} {h : GLV r K} {σ : K ≃+* K}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
    (hα : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
      ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) = h * fieldConj r K σ x * h⁻¹)
    (hN : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
      (x : GLV r K) ∈ plusFlagStab K r D ↔
        ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) ∈ plusFlagStab K r D)
    (hodd : Odd (orderOf α)) {d : ℕ} (hd : d ∈ D) : h • flag r K d = flag r K d := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hNorm : Normalizes D h σ := by
    intro q hq
    have hqE := (mem_plusFlagStab.1 hq).1
    refine ⟨((α.symm ⟨q, hqE⟩ : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K), ?_, ?_⟩
    · rw [hN]
      simpa using hq
    · rw [← hα]
      simp
  rcases smul_flag_mem hr hD hO hNorm hd with ⟨-, h1⟩ | ⟨hdr, h1 | h1⟩
  · exact h1
  · rw [hdr]
    exact h1
  · exfalso
    rw [hdr] at hd
    have hX : ∀ q ∈ plusFlagStab K r D, q • flag r K r = flag r K r :=
      fun q hq => (mem_plusFlagStab.1 hq).2 r hd
    have hXs : ∀ q ∈ plusFlagStab K r D, q • Xstar r K (by omega : 0 < r) =
        Xstar r K (by omega : 0 < r) := by
      rw [← h1]
      exact smul_invariant hr hD' hNorm hX
    have hXs' : h • Xstar r K (by omega : 0 < r) = flag r K r := by
      have hinv := smul_invariant hr hD' hNorm hXs
      have hfr : Module.finrank K ↥(h • Xstar r K (by omega : 0 < r)) = r := by
        have := LinearEquiv.finrank_map_eq h (Xstar r K (by omega : 0 < r))
        rw [finrank_Xstar hr] at this
        exact this
      have hs : ∀ x ∈ h • Xstar r K (by omega : 0 < r), quadPlus r K x = 0 := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
        change quadPlus r K (h v) = 0
        rw [map_of_mem hO]
        have : v ∈ h • flag r K r := by rw [h1]; exact hv
        obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        change quadPlus r K (h u) = 0
        rw [map_of_mem hO]
        exact flag_singular r u hu
      rcases classify_invariant hr hD hinv hs (by rw [hfr]; omega) with ⟨h3, -⟩ | ⟨-, h3 | h3⟩
      · rw [hfr] at h3
        omega
      · exact h3
      · exfalso
        have h4 : h • Xstar r K (by omega : 0 < r) = h • flag r K r := by rw [h3, h1]
        exact flag_top_ne_Xstar hr (smul_left_cancel h h4).symm
    obtain ⟨g, hgE, hg1, hg2⟩ := exists_stab_X_not_stab_Xstar (K := K) hr
    have hmain := mem_of_pow_eq_one α
      (T₁ := {x : ↥(orthElementaryGroup (quadPlus r K)) | (x : GLV r K) • flag r K r = flag r K r})
      (T₂ := {x : ↥(orthElementaryGroup (quadPlus r K)) |
        (x : GLV r K) • Xstar r K (by omega : 0 < r) = Xstar r K (by omega : 0 < r)})
      (fun x hx => by
        change ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) • Xstar r K _ = _
        rw [hα, mul_smul, mul_smul, inv_smul_eq_iff.2 h1.symm]
        change h • (fieldConj r K σ x • flag r K r) = _
        rw [smul_flag_fieldConj σ le_rfl hx, h1])
      (fun x hx => by
        change ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) • flag r K r = _
        rw [hα, mul_smul, mul_smul, inv_smul_eq_iff.2 hXs'.symm]
        change h • (fieldConj r K σ x • Xstar r K _) = _
        rw [smul_Xstar_fieldConj σ _ hx, hXs'])
      hodd (pow_orderOf_eq_one α) ⟨g, hgE⟩ hg1
    exact hg2 hmain

end Basic

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
