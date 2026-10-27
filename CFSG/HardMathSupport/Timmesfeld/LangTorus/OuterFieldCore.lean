module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidPinned
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

set_option linter.unusedSectionVars false


section Elementary

theorem finset_noncommProd_eq_list_prod {G ι : Type*} [Group G] [DecidableEq ι] (s : Finset ι)
    (f : ι → G) (comm : (s : Set ι).Pairwise (Function.onFun Commute f)) :
    s.noncommProd f comm = (s.toList.map f).prod := by
  have h := Finset.noncommProd_toFinset s.toList f (by simpa using comm) (Finset.nodup_toList s)
  simpa using h

theorem units_coe_list_prod {A ι : Type*} [Monoid A] (l : List ι) (g : ι → Aˣ) :
    (((l.map g).prod : Aˣ) : A) = (l.map fun x => (g x : A)).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem norm_eq_list_prod {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (y : P.S 0) :
    (P.norm y : G) = ((Finset.univ : Finset (ZMod s)).toList.map
      fun k => iterHom F k.val (y : G)).prod := by
  unfold CycFamily.norm CycFamily.mu
  rw [MonoidHom.comp_apply, Subgroup.noncommPiCoprod_apply]
  exact (finset_noncommProd_eq_list_prod _ _ _).trans rfl

variable {τ : Tag} {L : Type} [Field L]

theorem entrywise_pinnedX_units (ψ : L →+* L) (γ : Fin τ.rank → ℤ) (c : L) :
    Units.map (entrywiseHom ψ) (pinnedX τ L γ c) = pinnedX τ L γ (ψ c) :=
  Units.ext (by
    rw [Units.coe_map]
    exact entrywise_pinnedX ψ γ c)

theorem conj_map_pinnedX_expand (hτ : τ ≠ .G2) (ψ : L →+* L) (g : ModGL τ L) {μ : L}
    (hμ : μ ≠ 0) (α : Fin τ.rank → ℤ) :
    ∃ a b : Module.End L (RootModule τ L), a ≠ 0 ∧
      (SimplyLacedTag τ → 2 ≤ Module.finrank L (LinearMap.range a) ∧
        Module.finrank L (LinearMap.range b) ≤ 1) ∧ ∀ c : L,
      ((Units.map (entrywiseHom ψ) (g * pinnedX τ L α (μ * c) * g⁻¹) : ModGL τ L) :
        Module.End L (RootModule τ L)) = 1 + (ψ c) • a + (ψ c) ^ 2 • b := by
  obtain ⟨A, B, hA, hrk, hAB⟩ := pinnedX_expand (L := L) hτ α
  set g' : ModGL τ L := Units.map (entrywiseHom ψ) g with hg'
  have hgg : (g' : Module.End L (RootModule τ L)) * ((g'⁻¹ : ModGL τ L) :
      Module.End L (RootModule τ L)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hψμ : ψ μ ≠ 0 := fun h => hμ ((map_eq_zero ψ).1 h)
  refine ⟨ψ μ • ((g' : Module.End L (RootModule τ L)) * A *
      ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))),
    (ψ μ) ^ 2 • ((g' : Module.End L (RootModule τ L)) * B *
      ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))), ?_, ?_, fun c => ?_⟩
  · intro h0
    rcases smul_eq_zero.1 h0 with h | h
    · exact hψμ h
    · apply hA
      have := congrArg (fun m => ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) * m *
        (g' : Module.End L (RootModule τ L))) h
      simpa [mul_assoc] using this
  · intro hsl
    obtain ⟨h1, h2⟩ := hrk hsl
    constructor
    · rw [finrank_range_smul_eq hψμ, finrank_range_conj_eq]
      exact h1
    · refine (finrank_range_smul_le _ _).trans ?_
      refine (finrank_range_conj_le g' _).trans ?_
      exact h2
  · rw [map_mul, map_mul, map_inv, entrywise_pinnedX_units, ← hg']
    rw [Units.val_mul, Units.val_mul, hAB, map_mul]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul, mul_one, hgg]
    congr 2 <;> congr 1 <;> ring

end Elementary

section Factor

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem exists_factor_data (hτ : τ ≠ .G2) (ψ : L →+* L) (zu : ModGL τ L) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (k : ℕ) :
    ∃ a b a' b' : Module.End L (RootModule τ L), a ≠ 0 ∧ a' ≠ 0 ∧
      (SimplyLacedTag τ → 2 ≤ Module.finrank L (LinearMap.range a') ∧
        Module.finrank L (LinearMap.range b) ≤ 1) ∧
      (∀ t : L, ((iterHom S.D.step k (zu * pinnedX τ L γ t * zu⁻¹) : ModGL τ L) :
        Module.End L (RootModule τ L)) = 1 + (t ^ (S.D.q ^ k)) • a +
          (t ^ (S.D.q ^ k)) ^ 2 • b) ∧
      (∀ t : L, ((Units.map (entrywiseHom ψ) (iterHom S.D.step k
        (zu * pinnedX τ L γ t * zu⁻¹)) : ModGL τ L) : Module.End L (RootModule τ L)) =
          1 + (ψ (t ^ (S.D.q ^ k))) • a' + (ψ (t ^ (S.D.q ^ k))) ^ 2 • b') := by
  obtain ⟨μ, hμ, hμe⟩ := iter_step_pinnedX S k hγ
  have hit : ∀ t : L, iterHom S.D.step k (zu * pinnedX τ L γ t * zu⁻¹) =
      iterHom S.D.step k zu * pinnedX τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ)
        (μ * t ^ (S.D.q ^ k)) * (iterHom S.D.step k zu)⁻¹ := by
    intro t
    rw [map_mul, map_mul, map_inv, iterHom_eq_iterate, iterHom_eq_iterate, hμe]
  obtain ⟨a, b, ha, hrk, hab⟩ := conj_map_pinnedX_expand hτ (RingHom.id L)
    (iterHom S.D.step k zu) hμ ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ)
  obtain ⟨a', b', ha', hrk', hab'⟩ := conj_map_pinnedX_expand hτ ψ (iterHom S.D.step k zu) hμ
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ)
  refine ⟨a, b, a', b', ha, ha', fun hsl => ⟨(hrk' hsl).1, (hrk hsl).2⟩, fun t => ?_,
    fun t => ?_⟩
  · rw [hit]
    have h1 := hab (t ^ (S.D.q ^ k))
    have e : ∀ x : ModGL τ L, Units.map (entrywiseHom (RingHom.id L)) x = x :=
      fun x => Units.ext (entrywise_id _)
    rw [e] at h1
    simpa using h1
  · rw [hit, hab' (t ^ (S.D.q ^ k))]

end Factor

section Weyl

variable {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}

theorem outer_smul_mem_iff (hΨ : IsRootComponent Ψ) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    ∀ x : Fin τ.rank → ℤ, w • x ∈ Ψ ↔ x ∈ Ψ := by
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    intro x
    refine ⟨fun h => ?_, fun h => hΨ.reflection_mem x h γ hγ⟩
    have h2 := hΨ.reflection_mem _ h γ hγ
    rwa [smul_smul, rootReflection_mul_self (hΨ.isRoot γ hγ), one_smul] at h2
  | one => exact fun x => by rw [one_smul]
  | mul u v _ _ hu hv => exact fun x => by rw [mul_smul, hu, hv]
  | inv u _ hu => exact fun x => by rw [← hu (u⁻¹ • x), smul_inv_smul]

theorem outer_exists_smul_iform_ne_zero (hΨ : IsRootComponent Ψ) {α β : Fin τ.rank → ℤ}
    (hα : α ∈ Ψ) (hβ : β ∈ Ψ) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ},
      iform (w • α) β ≠ 0 := by
  classical
  set W := Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} with hW
  set A : Set (Fin τ.rank → ℤ) := {γ | γ ∈ Ψ ∧ ∃ w ∈ W, iform (w • α) γ ≠ 0} with hA
  have horth : ∀ γ ∈ A, ∀ δ ∈ Ψ, δ ∉ A → iform γ δ = 0 := by
    rintro γ ⟨hγΨ, w, hw, hne⟩ δ hδΨ hδA
    have hδ : ∀ w' ∈ W, iform (w' • α) δ = 0 := fun w' hw' => by
      by_contra h
      exact hδA ⟨hδΨ, w', hw', h⟩
    have hγr : IsRoot τ γ := hΨ.isRoot γ hγΨ
    have h2 := hδ (rootReflection γ * w) (mul_mem (Subgroup.subset_closure ⟨γ, hγΨ, rfl⟩) hw)
    rw [mul_smul, rootReflection_smul hγr, iform_sub_left, hδ w hw, iform_smul_left] at h2
    have hc : corootPair γ (w • α) ≠ 0 := by
      intro h0
      have h3 := corootPair_mul hγr (w • α)
      rw [h0, zero_mul, iform_comm] at h3
      exact hne (by omega)
    have h4 : corootPair γ (w • α) * iform γ δ = 0 := by linarith
    exact (mul_eq_zero.1 h4).resolve_left hc
  have hAΨ : A ⊆ Ψ := by
    intro γ hγ
    exact hγ.1
  rcases hΨ.irreducible A hAΨ horth with h | h
  · have hαA : α ∈ A := ⟨hα, 1, one_mem _, by
      rw [one_smul]
      exact (iform_self_pos_of_isRoot (hΨ.isRoot α hα)).ne'⟩
    rw [h] at hαA
    simp at hαA
  · have hβA : β ∈ A := by
      rw [h]
      exact hβ
    exact hβA.2

theorem outer_exists_smul_eq (hΨ : IsRootComponent Ψ) {α β : Fin τ.rank → ℤ} (hα : α ∈ Ψ)
    (hβ : β ∈ Ψ) (hlen : iform α α = iform β β) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}, w • α = β := by
  obtain ⟨w, hw, hne⟩ := outer_exists_smul_iform_ne_zero hΨ hα hβ
  have hvΨ : w • α ∈ Ψ := (outer_smul_mem_iff hΨ hw α).2 hα
  have hrβ : rootReflection β ∈
      Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    Subgroup.subset_closure ⟨β, hβ, rfl⟩
  have hrv : rootReflection (w • α) ∈
      Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    Subgroup.subset_closure ⟨_, hvΨ, rfl⟩
  have hvlen : iform (w • α) (w • α) = iform β β := by rw [iform_smul, hlen]
  set v := w • α with hv
  have hvr : IsRoot τ v := hΨ.isRoot v hvΨ
  have hβr : IsRoot τ β := hΨ.isRoot β hβ
  by_cases h1 : v = β
  · exact ⟨w, hw, h1⟩
  by_cases h2 : v = -β
  · refine ⟨rootReflection β * w, mul_mem hrβ hw, ?_⟩
    rw [mul_smul, ← hv, h2, smul_neg, rootReflection_smul_self hβr, neg_neg]
  have hlt := iform_sq_lt hvr hβr h1 h2
  rw [hvlen] at hlt
  have hpos := iform_self_pos_of_isRoot hβr
  have hc := corootPair_mul hβr v
  have hx : iform β v = iform v β := iform_comm β v
  have hcc : corootPair β v = 1 ∨ corootPair β v = -1 := by
    have hsq : (corootPair β v) ^ 2 < 4 := by
      by_contra hcon'
      have hcon : 4 ≤ (corootPair β v) ^ 2 := not_lt.1 hcon'
      have e1 : (corootPair β v * iform β β) ^ 2 = 4 * iform v β ^ 2 := by
        rw [hc, hx]
        ring
      nlinarith [mul_le_mul_of_nonneg_right hcon (sq_nonneg (iform β β))]
    have hne0 : corootPair β v ≠ 0 := by
      intro h0
      rw [h0, zero_mul, hx] at hc
      exact hne (by omega)
    have hlo : -2 < corootPair β v := by nlinarith
    have hhi : corootPair β v < 2 := by nlinarith
    omega
  rcases hcc with hc1 | hc1
  ·
    have hd : corootPair v (v - β) = 1 := by
      have h3 := corootPair_mul hvr (v - β)
      rw [iform_sub_right, hvlen] at h3
      have h2x : 2 * iform v β = iform β β := by rw [← hx, ← hc, hc1, one_mul]
      have h4 : corootPair v (v - β) * iform β β = 1 * iform β β := by linarith
      exact mul_right_cancel₀ hpos.ne' h4
    have hs1 : rootReflection β • v = v - β := by
      rw [rootReflection_smul hβr, hc1, one_smul]
    have hs2 : rootReflection v • (v - β) = -β := by
      rw [rootReflection_smul hvr, hd, one_smul, sub_sub_cancel_left]
    refine ⟨rootReflection β * rootReflection v * rootReflection β * w,
      mul_mem (mul_mem (mul_mem hrβ hrv) hrβ) hw, ?_⟩
    rw [mul_smul, mul_smul, mul_smul, ← hv, hs1, hs2, smul_neg, rootReflection_smul_self hβr,
      neg_neg]
  ·
    have hd : corootPair v (v + β) = 1 := by
      have h3 := corootPair_mul hvr (v + β)
      rw [iform_add_right, hvlen] at h3
      have h2x : 2 * iform v β = -iform β β := by rw [← hx, ← hc, hc1, neg_one_mul]
      have h4 : corootPair v (v + β) * iform β β = 1 * iform β β := by linarith
      exact mul_right_cancel₀ hpos.ne' h4
    have hs1 : rootReflection β • v = v + β := by
      rw [rootReflection_smul hβr, hc1, neg_one_smul, sub_neg_eq_add]
    have hs2 : rootReflection v • (v + β) = β := by
      rw [rootReflection_smul hvr, hd, one_smul, add_sub_cancel_left]
    refine ⟨rootReflection v * rootReflection β * w, mul_mem (mul_mem hrv hrβ) hw, ?_⟩
    rw [mul_smul, mul_smul, ← hv, hs1, hs2]

end Weyl

section Pin

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem outer_exists_pin_root (σ : L ≃+* L) (φ : ModGL τ L →* ModGL τ L)
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) {w : WeylGroup τ} {h : ModGL τ L}
    (hhM : h ∈ monomialSubgroup τ L) (hπ : weylQuotientHom τ L ⟨h, hhM⟩ = w⁻¹)
    {m m' : L} (hm0 : m ≠ 0)
    (hmφ : ∀ c : L, φ (pinnedX τ L θ c) = pinnedX τ L (w • θ) (m * σ c))
    (hm'φ : ∀ c : L, φ (pinnedX τ L (-θ) c) = pinnedX τ L (w • -θ) (m' * σ c)) :
    ∃ cT : Fin τ.rank → Lˣ, ∀ A : SL2 L,
      (rootDiagUnit τ cT * h) * φ (rootSL2 τ L θ A) * (rootDiagUnit τ cT * h)⁻¹ =
        rootSL2 τ L θ (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  classical
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hhM (IsRoot.smul hθ w)
  obtain ⟨μ', hμ'⟩ := monomial_conj_pinnedX hhM (IsRoot.smul (IsRoot.neg hθ) w)
  rw [hπ, inv_smul_smul] at hμ hμ'
  obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := L) hθ
  have hση : σ η = η := sq_eq_one_fixed σ hη
  have hu : ∀ c, h * φ (rootSL2 τ L θ (uSL c)) * h⁻¹ =
      rootSL2 τ L θ (uSL (((μ : L) * m) * σ c)) := by
    intro c
    rw [rootSL2_uSL_eq, hmφ, hμ, rootSL2_uSL_eq, map_zsmul]
    congr 1
    simp only [zsmul_eq_mul]
    ring
  have hv' : ∀ c, h * φ (rootSL2 τ L θ (vSL c)) * h⁻¹ =
      rootSL2 τ L θ (vSL (((μ' : L) * m') * σ c)) := by
    intro c
    rw [hv, hm'φ, hμ', hv, map_mul, hση]
    congr 1
    ring
  have ha0 : (μ : L) * m ≠ 0 := mul_ne_zero μ.ne_zero hm0
  have hab : ((μ : L) * m) * ((μ' : L) * m') = 1 := by
    refine rank_one_scalar_compat hθ ((MulAut.conj h).toMonoidHom.comp φ) σ.toRingHom ha0
      (fun c => ?_) (fun c => ?_)
    · simpa [MulAut.conj_apply] using hu c
    · simpa [MulAut.conj_apply] using hv' c
  have hθ0 : (fun j => (θ j : ℚ)) ≠ 0 := by
    intro h0
    apply hθ.ne_zero
    funext j
    have := congrFun h0 j
    simpa using this
  obtain ⟨cT, hcT⟩ := algebraically_closed_lattice_character_interpolation L τ.rank 1
    (fun _ => θ) (linearIndependent_unique_iff.2 hθ0) fun _ => (Units.mk0 _ ha0)⁻¹
  have hχ : (rootChar cT θ : L) = ((μ : L) * m)⁻¹ := by
    have hk : ∏ j, cT j ^ θ j = (Units.mk0 _ ha0)⁻¹ := hcT 0
    have hk' : ((∏ j, cT j ^ θ j : Lˣ) : L) = ((μ : L) * m)⁻¹ := by
      rw [hk]
      simp
    exact hk'
  refine ⟨cT, fun A => ?_⟩
  set y : ModGL τ L := rootDiagUnit τ cT * h with hy
  have heq := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L))
    (f := ((MulAut.conj y).toMonoidHom.comp φ).comp (rootSL2 τ L θ))
    (g := (rootSL2 τ L θ).comp (Matrix.SpecialLinearGroup.map σ.toRingHom)) ?_
  · exact DFunLike.congr_fun heq A
  have hyφ : ∀ x : ModGL τ L, y * φ x * y⁻¹ =
      rootDiagUnit τ cT * (h * φ x * h⁻¹) * (rootDiagUnit τ cT)⁻¹ := by
    intro x
    rw [hy]
    group
  rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
  · change y * φ (rootSL2 τ L θ (uSL z)) * y⁻¹ =
      rootSL2 τ L θ (Matrix.SpecialLinearGroup.map σ.toRingHom (uSL z))
    rw [hyφ, hu z, (CFSG.LieType.AlgebraicGroups.rootDiagUnit_conj_rootSL2 cT hθ _).1, map_uSL, hχ,
      ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    rfl
  · change y * φ (rootSL2 τ L θ (vSL z)) * y⁻¹ =
      rootSL2 τ L θ (Matrix.SpecialLinearGroup.map σ.toRingHom (vSL z))
    rw [hyφ, hv' z, (CFSG.LieType.AlgebraicGroups.rootDiagUnit_conj_rootSL2 cT hθ _).2, map_vSL]
    have hχ' : (((rootChar cT θ)⁻¹ : Lˣ) : L) = (μ : L) * m := by
      rw [Units.val_inv_eq_inv_val, hχ, inv_inv]
    rw [hχ', ← mul_assoc, hab, one_mul]
    rfl

end Pin

section Untwist

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_iterate_neg (n : ℕ) (γ : Fin τ.rank → ℤ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ :=
  rho_iterate_neg S n γ

theorem outer_iterate_iform (n : ℕ) (γ δ : Fin τ.rank → ℤ) :
    iform ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ) ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ) =
      iform γ δ :=
  iform_rho_iterate S n γ δ

theorem outer_exists_untwist_root {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hs : 0 < s) {θ : Fin τ.rank → ℤ}
    (hθ : θ ∈ componentRoots (rootCharHom a) i) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure
      {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ})
    (hwθ : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] θ = w • θ) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ A : SL2 L, iterHom S.D.step s (z * rootSL2 τ L θ A * z⁻¹) =
        z * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s hθr
  obtain ⟨μ', -, hμ'⟩ := iter_step_pinnedX S s (IsRoot.neg hθr)
  have hφθ : ∀ c, iterHom S.D.step s (pinnedX τ L θ c) = pinnedX τ L (w • θ) (μ * σ c) := by
    intro c
    rw [iterHom_eq_iterate, hμ, hwθ, hσc]
  have hφθ' : ∀ c, iterHom S.D.step s (pinnedX τ L (-θ) c) =
      pinnedX τ L (w • -θ) (μ' * σ c) := by
    intro c
    rw [iterHom_eq_iterate, hμ', outer_iterate_neg S, hwθ, smul_neg, hσc]
  obtain ⟨gw, hgwS, hgwM, hgwmaps⟩ := exists_lift_mem_closure_reflections (L := L) i hw
  have hhM : gw⁻¹ ∈ monomialSubgroup τ L := inv_mem hgwM
  have hπ : weylQuotientHom τ L ⟨gw⁻¹, hhM⟩ = w⁻¹ := weylQuotientHom_eq hgwmaps.inv
  obtain ⟨cT, hpin⟩ := outer_exists_pin_root σ (iterHom S.D.step s) hθr hhM hπ hμ0 hφθ hφθ'
  have hy₁ : rootDiagUnit τ cT * gw⁻¹ ∈
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup cT))
      (Subgroup.mem_sup_right (inv_mem ((rootSpan_mono fun γ hγ => hγ.1) hgwS)))
  obtain ⟨z, hφz, hnorm⟩ := outer_exists_lang S hT hs hy₁
  refine ⟨σ, z, hσc, hnorm, fun A => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz, ← hpin A]
  group

end Untwist

section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_fixSubfield_card {r n : ℕ} [Fact r.Prime] [CharP L r] (hn : 0 < n)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ (r ^ n)) :
    Finite (fixSubfield σ) ∧ Nat.card (fixSubfield σ) = r ^ n := by
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r n hn
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ n) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ]
    rfl
  refine ⟨?_, ?_⟩
  · have h1 : (fixSubfield σ : Set L).Finite := by
      rw [hset]
      exact hfinset
    exact h1.to_subtype
  · have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]

theorem outer_false_of_norm_fixed (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {θ : Fin τ.rank → ℤ} (hθr : IsRoot τ θ) (zu : ModGL τ L)
    (hy : ∀ t : L, zu * pinnedX τ L θ t * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0)
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f) (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (r ^ (f * s)))
    (hrt : ∀ t : L, σ t = t → (outerOrbitFamily S hT i hs hmin).norm ⟨_, hy t⟩ ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ) (hj0 : 0 < j) (hjf : j < f) (z' : ModGL τ L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := (expChar_prime_iff L hr).1 inferInstance
  have hr2 := hr.two_le
  have hf2 : 2 ≤ f := by omega
  have hfs : 0 < f * s := Nat.mul_pos (by omega) hs0
  have hrf4 : 4 ≤ r ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
      _ ≤ r ^ f := Nat.pow_le_pow_right (by omega) hf2
  obtain ⟨hfinK, hKcard⟩ := outer_fixSubfield_card (L := L) hfs σ hσ
  let : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hKcard' : Fintype.card (fixSubfield σ) = (r ^ f) ^ s := by
    rw [← Nat.card_eq_fintype_card, hKcard, pow_mul]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : L →+* L, ψ = iterateFrobenius L r j := ⟨_, rfl⟩
  rw [← hψ] at hfix
  have hψpow : ∀ x : L, ψ x = x ^ (r ^ j) := fun x => by rw [hψ, iterateFrobenius_def]
  have hdata := fun κ : ZMod s => exists_factor_data S hτ ψ zu hθr κ.val
  choose aZ bZ aZ' bZ' haZ haZ' hrkZ hE1 hE2 using hdata
  have hcast : ∀ κ : ZMod s, ((κ.val : ℕ) : ZMod s) = κ := ZMod.natCast_zmod_val
  obtain ⟨aN, haN⟩ : ∃ aN : ℕ → Module.End L (RootModule τ L),
      ∀ κ : ZMod s, aN κ.val = aZ κ := ⟨fun n => aZ (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨bN, hbN⟩ : ∃ bN : ℕ → Module.End L (RootModule τ L),
      ∀ κ : ZMod s, bN κ.val = bZ κ := ⟨fun n => bZ (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨aN', haN'⟩ : ∃ aN' : ℕ → Module.End L (RootModule τ L),
      ∀ κ : ZMod s, aN' κ.val = aZ' κ := ⟨fun n => aZ' (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨bN', hbN'⟩ : ∃ bN' : ℕ → Module.End L (RootModule τ L),
      ∀ κ : ZMod s, bN' κ.val = bZ' κ := ⟨fun n => bZ' (n : ZMod s), fun κ => by simp [hcast]⟩
  obtain ⟨ks, hks⟩ : ∃ ks : List ℕ,
      ks = (Finset.univ : Finset (ZMod s)).toList.map ZMod.val := ⟨_, rfl⟩
  have hnd : ks.Nodup := by
    rw [hks]
    exact List.Nodup.map (ZMod.val_injective s) (Finset.nodup_toList _)
  have h0 : 0 ∈ ks := by
    rw [hks]
    exact List.mem_map.2 ⟨0, Finset.mem_toList.2 (Finset.mem_univ _), ZMod.val_zero⟩
  have hksl : ∀ k ∈ ks, k < s := fun k hk => by
    rw [hks] at hk
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hk
    exact ZMod.val_lt κ
  have hsq : ∀ (x : L) (m : ℕ), x ^ (2 * m) = (x ^ m) ^ 2 := fun x m => by
    rw [← pow_mul, mul_comm]
  have hmain : ∀ t : fixSubfield σ,
      (z' : Module.End L (RootModule τ L)) *
        evAt (((t : L)) ^ (r ^ j)) (prodList (r ^ f) aN' bN' ks) *
          (↑z'⁻¹ : Module.End L (RootModule τ L)) =
        evAt (t : L) (prodList (r ^ f) aN bN ks) := by
    intro t
    have hc : σ (t : L) = t := t.2
    have hf := hfix _ (hrt (t : L) hc)
    have hnormeq := norm_eq_list_prod P ⟨_, hy (t : L)⟩
    have hnormA : ((P.norm ⟨_, hy (t : L)⟩ : ModGL τ L) : Module.End L (RootModule τ L)) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + ((t : L) ^ (r ^ f) ^ κ.val) • aZ κ +
            ((t : L) ^ (r ^ f) ^ κ.val) ^ 2 • bZ κ).prod := by
      rw [hnormeq, units_coe_list_prod]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      have e := hE1 κ (t : L)
      rw [hq] at e
      exact e
    have hnormA' : ((Units.map (entrywiseHom ψ) (P.norm ⟨_, hy (t : L)⟩) : ModGL τ L) :
        Module.End L (RootModule τ L)) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + (ψ ((t : L) ^ (r ^ f) ^ κ.val)) • aZ' κ +
            (ψ ((t : L) ^ (r ^ f) ^ κ.val)) ^ 2 • bZ' κ).prod := by
      rw [hnormeq, map_list_prod, List.map_map, units_coe_list_prod]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      have e := hE2 κ (t : L)
      rw [hq] at e
      exact e
    have hfA := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L))) hf
    simp only [Units.val_mul] at hfA
    rw [hnormA, hnormA'] at hfA
    have hR : evAt (t : L) (prodList (r ^ f) aN bN ks) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + ((t : L) ^ (r ^ f) ^ κ.val) • aZ κ +
            ((t : L) ^ (r ^ f) ^ κ.val) ^ 2 • bZ κ).prod := by
      rw [evAt_prodList, hks, List.map_map]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      simp only [Function.comp, haN, hbN, hsq]
    have hL : evAt ((t : L) ^ (r ^ j)) (prodList (r ^ f) aN' bN' ks) =
        ((Finset.univ : Finset (ZMod s)).toList.map fun κ =>
          1 + (ψ ((t : L) ^ (r ^ f) ^ κ.val)) • aZ' κ +
            (ψ ((t : L) ^ (r ^ f) ^ κ.val)) ^ 2 • bZ' κ).prod := by
      rw [evAt_prodList, hks, List.map_map]
      congr 1
      refine List.map_congr_left fun κ _ => ?_
      simp only [Function.comp, haN', hbN', hsq, hψpow]
      rw [pow_right_comm ((t : L)) ((r ^ f) ^ κ.val) (r ^ j)]
    rw [hR, hL]
    exact hfA
  by_cases hex : r ^ j = 2 ∧ r ^ f = 4
  ·
    obtain ⟨hrj, hrf⟩ := hex
    have hsl : SimplyLacedTag τ := by
      rcases hq4 with h | h
      · exact absurd (by rw [hq, hrf]) h
      · exact h
    have hm4 := twisted_conj_q4 (fixSubfield σ).subtype hs0 (by rw [hKcard', hrf]) ks hnd h0
      hksl aN bN aN' bN' z' (fun t => by
        have := hmain t
        rwa [hrf, hrj] at this)
    obtain ⟨hr2, hr1⟩ := hrkZ 0 hsl
    have haN0 : aN' 0 = aZ' 0 := by
      have := haN' 0
      rwa [ZMod.val_zero] at this
    have hbN0 : bN 0 = bZ 0 := by
      have := hbN 0
      rwa [ZMod.val_zero] at this
    rw [haN0, hbN0] at hm4
    have h3 := finrank_range_conj_eq z' (aZ' 0)
    rw [hm4] at h3
    omega
  · refine no_twisted_conj (fixSubfield σ).subtype hr hj0 hjf hs0 hKcard' hrf4 ?_ ks hnd h0 hksl
      aN bN aN' bN' ?_ ?_ z' hmain
    · intro hc2
      have hr2' : r = 2 := by
        have : r ∣ 2 := by
          rw [← hc2]
          exact dvd_pow_self r hj0.ne'
        exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this
      subst hr2'
      have hf3 : f ≠ 2 := fun hf2' => hex ⟨hc2, by rw [hf2']; norm_num⟩
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) (by omega)
    · have := haZ 0
      rwa [← haN 0, ZMod.val_zero] at this
    · have := haZ' 0
      rwa [← haN' 0, ZMod.val_zero] at this

theorem outer_false_of_component_fixed_by_twist (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f)
    (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ) (hj0 : 0 < j) (hjf : j < f) (z' : ModGL τ L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := (expChar_prime_iff L hr).1 inferInstance
  obtain ⟨⟨θ, hθk⟩, hθi⟩ := Quotient.exists_rep i
  have hθ : θ ∈ componentRoots (rootCharHom a) i := ⟨hθk, hθi⟩
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  have hθs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] θ ∈ componentRoots (rootCharHom a) i := by
    rw [← hs]
    exact Set.mem_image_of_mem _ hθ
  obtain ⟨w, hw, hwθ⟩ := outer_exists_smul_eq (isRootComponent_componentRoots i) hθ hθs
    (outer_iterate_iform S s θ θ).symm
  obtain ⟨σ, zu, hσ, hnorm, hz⟩ := outer_exists_untwist_root S hT i hs0 hθ hw hwθ.symm
  have hσ' : ∀ c, σ c = c ^ (r ^ (f * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hfs : 0 < f * s := Nat.mul_pos (by omega) hs0
  obtain ⟨hfinK, hKcard⟩ := outer_fixSubfield_card (L := L) hfs σ hσ'
  have hQ4 : 4 ≤ r ^ (f * s) := by
    have hr2 := hr.two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
      _ ≤ r ^ (f * s) :=
        Nat.pow_le_pow_right (by omega) (le_trans (by omega) (Nat.le_mul_of_pos_right f hs0))
  have hperf : Group.IsPerfect (SL2 (fixSubfield σ)) := by
    let : Fintype (fixSubfield σ) := Fintype.ofFinite _
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset (fixSubfield σ)).card by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hKcard]
        exact hQ4)
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hneg : -θ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem θ hθ
  have hmemS : ∀ A : SL2 L, zu * rootSL2 τ L θ A * zu⁻¹ ∈ P.S 0 := by
    intro A
    rw [hP0]
    refine (hnorm i _).1 ?_
    have h1 : rootSL2 τ L θ A ∈ rootRankOneGroup τ L θ := ⟨A, rfl⟩
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hθr).1] at h1
    exact sup_le (rootSubgroup_le_rootSpan hθ) (rootSubgroup_le_rootSpan hneg) h1
  let θ₀ : SL2 (fixSubfield σ) →* P.S 0 :=
    ((MulAut.conj zu).toMonoidHom.comp ((rootSL2 τ L θ).comp
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype))).codRestrict (P.S 0)
      fun A => hmemS _
  have hθ₀ : ∀ A, ((θ₀ A : P.S 0) : ModGL τ L) =
      zu * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) * zu⁻¹ :=
    fun A => rfl
  have hσι : ∀ A : SL2 (fixSubfield σ), Matrix.SpecialLinearGroup.map σ.toRingHom
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) =
        Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A := by
    intro A
    ext k l
    exact ((A : Matrix (Fin 2) (Fin 2) (fixSubfield σ)) k l).2
  have hθfix : ∀ A, iterHom S.D.step s ((θ₀ A : P.S 0) : ModGL τ L) = θ₀ A := by
    intro A
    rw [hθ₀, hz, hσι]
  have hy : ∀ t : L, zu * pinnedX τ L θ t * zu⁻¹ ∈ P.S 0 := by
    intro t
    rw [hP0]
    exact (hnorm i _).1 (pinnedX_mem_rootSpan hθ _)
  refine outer_false_of_norm_fixed S hτ hT i hs hmin hθr zu hy hr hq σ hσ' (fun t ht => ?_)
    hq4 hj0 hjf z' hfix
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = (pinnedData τ θ).2.2 := ⟨_, rfl⟩
  have hε2 : ε • ε • t = t := by
    rcases pinnedSign_eq τ θ with h | h <;> rw [hε, h] <;> simp
  have hA : ((θ₀ (uSL (ε • (⟨t, ht⟩ : fixSubfield σ))) : P.S 0) : ModGL τ L) =
      zu * pinnedX τ L θ t * zu⁻¹ := by
    rw [hθ₀, map_uSL, rootSL2_uSL_eq, map_zsmul, ← hε]
    have e : ε • ε • (fixSubfield σ).subtype (⟨t, ht⟩ : fixSubfield σ) = t := hε2
    rw [e]
  have h1 := outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hθfix
    (uSL (ε • (⟨t, ht⟩ : fixSubfield σ)))
  have h2 : θ₀ (uSL (ε • (⟨t, ht⟩ : fixSubfield σ))) = ⟨_, hy t⟩ := Subtype.ext hA
  rw [h2] at h1
  exact h1

theorem outer_false_of_component_fixed_by_twist_of_E (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hE : rootDiagUnit τ a ∈ S.E) (i : KernelComponent (rootCharHom a))
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f)
    (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ) (hj0 : 0 < j) (hjf : j < f) (z' : ModGL τ L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False :=
  outer_false_of_component_fixed_by_twist S hτ (Subgroup.mem_inf.1 (S.E_le hE)).1 i hr hq hq4
    hj0 hjf z' hfix

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus
