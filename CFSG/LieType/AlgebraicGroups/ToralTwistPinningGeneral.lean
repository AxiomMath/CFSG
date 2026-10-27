module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.ConvolutionPoints

theorem exists_iterate_eq_of_mapsTo {α : Type*} {f : α → α} {s : Set α} (hs : s.Finite)
    (hf : Set.MapsTo f s s) (hinj : Set.InjOn f s) : ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ s, f^[d] x = x := by
  have : Finite s := hs.to_subtype
  have hg : Function.Injective (hf.restrict f s s) := (Set.MapsTo.restrict_inj hf).2 hinj
  let σ : Equiv.Perm s := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hg)
  refine ⟨orderOf σ, orderOf_pos σ, fun x hx => ?_⟩
  have h1 : (σ ^ orderOf σ) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [pow_orderOf_eq_one]
    rfl
  rw [Equiv.Perm.coe_pow] at h1
  have h2 := hf.coe_iterate_restrict ⟨x, hx⟩ (orderOf σ)
  change ((⇑σ)^[orderOf σ] ⟨x, hx⟩ : α) = _ at h2
  rw [h1] at h2
  exact h2.symm

section General

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [CharP k p]

theorem exists_frobTwistGL_pinnedX_of_conj
    (e : ℕ) {Q : ModGL τ k}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hQ : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (μ * c))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : kˣ, ∀ c : k, frobTwistGL τ k p e Q (pinnedX τ k γ c) =
      pinnedX τ k (θ γ) (μ * iterateFrobenius k p e c) := by
  obtain ⟨μ, hμ⟩ := hQ γ hγ
  exact ⟨μ, fun c => by rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, hμ]⟩

variable [PerfectRing k p]

theorem map_frobTwistGL_rootSubgroup_of_conj
    (e : ℕ) {Q : ModGL τ k}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hQ : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (μ * c))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (rootSubgroup τ k γ).map (frobTwistGL τ k p e Q) = rootSubgroup τ k (θ γ) := by
  obtain ⟨μ, hμ⟩ := exists_frobTwistGL_pinnedX_of_conj p e hQ hγ
  refine map_rootSubgroup_eq_of_forall (g := fun c => (μ : k) * iterateFrobenius k p e c)
    (fun c => ?_) hμ
  obtain ⟨d, hd⟩ := (iterateFrobeniusEquiv k p e).surjective (((μ⁻¹ : kˣ) : k) * c)
  refine ⟨d, ?_⟩
  change (μ : k) * (iterateFrobeniusEquiv k p e) d = c
  rw [hd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem map_frobTwistGL_rootSpan_of_conj
    (e : ℕ) {Q : ModGL τ k}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hQ : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (μ * c))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    (rootSpan τ k S).map (frobTwistGL τ k p e Q) = rootSpan τ k (θ '' S) := by
  simp only [rootSpan, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun α hα => ?_
    rw [map_frobTwistGL_rootSubgroup_of_conj p e hQ (hS α hα)]
    exact le_iSup₂_of_le (f := fun β (_ : β ∈ θ '' S) => rootSubgroup τ k β) _ ⟨α, hα, rfl⟩
      le_rfl
  · refine iSup₂_le ?_
    rintro _ ⟨α, hα, rfl⟩
    rw [← map_frobTwistGL_rootSubgroup_of_conj p e hQ (hS α hα)]
    exact le_iSup₂_of_le (f := fun β (_ : β ∈ S) =>
      (rootSubgroup τ k β).map (frobTwistGL τ k p e Q)) α hα le_rfl

theorem exists_frobTwistGL_rootSL2_of_conj
    (hp : p ≠ 2) (e : ℕ) {Q : ModGL τ k}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hQ : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (μ * c))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hθβ : IsRoot τ (θ β)) (hθneg : θ (-β) = -θ β) :
    ∃ a : kˣ, ∀ c : k,
      frobTwistGL τ k p e Q (rootSL2 τ k β (uSL c)) =
          rootSL2 τ k (θ β)
            (uSL ((a : k) * iterateFrobenius k p e c)) ∧
        frobTwistGL τ k p e Q (rootSL2 τ k β (vSL c)) =
          rootSL2 τ k (θ β)
            (vSL (((a⁻¹ : kˣ) : k) * iterateFrobenius k p e c)) := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  have hwβ : IsRoot τ (θ β) := hθβ
  obtain ⟨μ, hμ⟩ := exists_frobTwistGL_pinnedX_of_conj p e hQ hβ
  have hε := pinnedSign_eq τ β
  have hε' := pinnedSign_eq τ (θ β)
  set ε := (pinnedData τ β).2.2
  set ε' := (pinnedData τ (θ β)).2.2
  set a : kˣ := Units.mk0 ((ε' : k) * ε * μ)
    (mul_ne_zero (mul_ne_zero (intCast_ne_zero_of_sign hε') (intCast_ne_zero_of_sign hε))
      μ.ne_zero) with ha
  have hu : ∀ c, frobTwistGL τ k p e Q (rootSL2 τ k β (uSL c)) =
      rootSL2 τ k (θ β) (uSL ((a : k) * iterateFrobenius k p e c)) := by
    intro c
    rw [rootSL2_uSL_eq, hμ, rootSL2_uSL_eq, map_zsmul, zsmul_eq_mul, zsmul_eq_mul, ha,
      Units.val_mk0]
    congr 1
    linear_combination -((μ : k) * (ε : k) * iterateFrobenius k p e c) *
      intCast_mul_self_of_sign (k := k) hε'
  obtain ⟨μ', hμ'⟩ := exists_frobTwistGL_pinnedX_of_conj p e hQ (IsRoot.neg hβ)
  obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := k) hβ
  obtain ⟨η', hη', hv'⟩ := exists_rootSL2_vSL_eq (K := k) hwβ
  have hη0 : η ≠ 0 := fun h => by rw [h, zero_mul] at hη; exact zero_ne_one hη
  have hη'0 : η' ≠ 0 := fun h => by rw [h, zero_mul] at hη'; exact zero_ne_one hη'
  have hση : iterateFrobenius k p e η = η := by
    rcases mul_self_eq_one_iff.1 hη with h | h <;> rw [h]
    · exact map_one _
    · rw [map_neg, map_one]
  set b : kˣ := Units.mk0 (η' * μ' * η) (mul_ne_zero (mul_ne_zero hη'0 μ'.ne_zero) hη0) with hb
  have hl : ∀ c, frobTwistGL τ k p e Q (rootSL2 τ k β (vSL c)) =
      rootSL2 τ k (θ β) (vSL ((b : k) * iterateFrobenius k p e c)) := by
    intro c
    rw [hv, hμ', hθneg, hv', map_mul, hση, hb, Units.val_mk0]
    congr 1
    linear_combination -((μ' : k) * η * iterateFrobenius k p e c) * hη'
  obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ :=
    exceptional_Lang_root_rank_one_data τ k (θ β)
  obtain ⟨hρinj, e', he'⟩ := hinj hk
  obtain ⟨-, -, -, -, -, -, -, hinjβ, -⟩ := exceptional_Lang_root_rank_one_data τ k β
  have hmem : ∀ A, frobTwistGL τ k p e Q (rootSL2 τ k β A) ∈
      rootRankOneGroup τ k (θ β) := by
    intro A
    have htop : (rootRankOneGroup τ k (θ β)).comap
        ((frobTwistGL τ k p e Q).comp (rootSL2 τ k β)) = ⊤ := by
      rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨uSL _, (hu c).symm⟩
      · exact ⟨vSL _, (hl c).symm⟩
    have hA : A ∈ (rootRankOneGroup τ k (θ β)).comap
        ((frobTwistGL τ k p e Q).comp (rootSL2 τ k β)) := by
      rw [htop]
      exact Subgroup.mem_top A
    exact hA
  let T : SL2 k →* SL2 k := e'.symm.toMonoidHom.comp
    (((frobTwistGL τ k p e Q).comp (rootSL2 τ k β)).codRestrict _ hmem)
  have hT : ∀ A, rootSL2 τ k (θ β) (T A) =
      frobTwistGL τ k p e Q (rootSL2 τ k β A) := by
    intro A
    rw [← he']
    simp [T]
  have hTinj : Function.Injective T := fun A B h => by
    have h' := congrArg (rootSL2 τ k (θ β)) h
    rw [hT, hT] at h'
    exact (hinjβ hk).1 (frobTwistGL_injective p e Q h')
  have hTu : ∀ c, T (uSL c) = uSL ((a : k) * (iterateFrobeniusEquiv k p e) c) := fun c =>
    hρinj (by rw [hT, hu]; rfl)
  have hTl : ∀ c, T (vSL c) = vSL ((b : k) * (iterateFrobeniusEquiv k p e) c) := fun c =>
    hρinj (by rw [hT, hl]; rfl)
  obtain ⟨hab, -⟩ := SL2_opposite_root_scalar_compatibility hk (iterateFrobeniusEquiv k p e) a b T
    hTu hTl (map_neg_one_of_injective hk hTinj)
  have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  refine ⟨a, fun c => ⟨hu c, ?_⟩⟩
  rw [hl, hb']


end General

section Main

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

omit [IsAlgClosed k] in
theorem iterate_frobTwistGL_rootSL2_of_map
    (e : ℕ) {Q : ModGL τ k}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {Δ : Set (Fin τ.rank → ℤ)}
    (hΔ : Set.MapsTo θ Δ Δ)
    (hpin : ∀ β ∈ Δ, ∀ A : SL2 k, frobTwistGL τ k p e Q (rootSL2 τ k β A) =
      rootSL2 τ k (θ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A)) (m : ℕ) :
    ∀ β ∈ Δ, ∀ A : SL2 k, (frobTwistGL τ k p e Q)^[m] (rootSL2 τ k β A) =
      rootSL2 τ k (θ^[m] β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p (e * m)) A) := by
  induction m with
  | zero =>
    intro β _ A
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply, mul_zero,
      iterateFrobenius_zero]
    congr 1
  | succ m ih =>
    intro β hβ A
    rw [Function.iterate_succ_apply', ih β hβ A, hpin _ (hΔ.iterate m hβ),
      Function.iterate_succ_apply', show e * (m + 1) = e * m + e by ring,
      ← iterateFrobenius_comp_iterateFrobenius]
    congr 1

variable (τ k) in
@[expose] def IsTwistPinningNormalization
    (p e : ℕ) [Fact p.Prime] [CharP k p]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (Q₀ : ModGL τ k) : Prop :=
  ∃ h ∈ torusGroup τ k,
    (∀ β ∈ unionSimpleRoots χ Set.univ, ∀ A : SL2 k,
      frobTwistGL τ k p e (h * Q₀) (rootSL2 τ k β A) =
        rootSL2 τ k (θ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A)) ∧
    (rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e (h * Q₀)) =
      rootSpan τ k (kernelRoots χ) ∧
    (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e (h * Q₀)) =
      torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) ∧
    (∀ d : ℕ, 1 ≤ d → (∀ β ∈ unionSimpleRoots χ Set.univ, θ^[d] β = β) →
      ∀ s ∈ rootSpan τ k (kernelRoots χ),
        (frobTwistGL τ k p e (h * Q₀))^[d] s = entrywiseFrobGL τ k p (e * d) s) ∧
    Finite (fixedPointsIn (rootSpan τ k (kernelRoots χ)) (frobTwistGL τ k p e (h * Q₀))) ∧
    ∃ u ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ),
      (fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ))
          (frobTwistGL τ k p e (h * Q₀))).map (MulAut.conj u).toMonoidHom =
        fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) (frobTwistGL τ k p e Q₀)

theorem isTwistPinningNormalization_of_conj
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) {Q₀ : ModGL τ k}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hQ₀ : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      Q₀ * pinnedX τ k γ c * Q₀⁻¹ = pinnedX τ k (θ γ) (μ * c))
    (hQ₀T : Q₀ ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hθroot : ∀ γ, IsRoot τ γ → IsRoot τ (θ γ)) (hθneg : ∀ v, θ (-v) = -θ v)
    (hθinj : Function.Injective θ) (hθS : θ '' kernelRoots χ = kernelRoots χ)
    (hθΔ : θ '' unionSimpleRoots χ Set.univ = unionSimpleRoots χ Set.univ) :
    IsTwistPinningNormalization τ k p e χ θ Q₀ := by
  classical
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set Δ := simpleRoots (kernelRoots χ) with hΔ_def
  have hΔeq : unionSimpleRoots χ Set.univ = (Δ : Set (Fin τ.rank → ℤ)) :=
    unionSimpleRoots_univ_eq
  rw [hΔeq] at hθΔ
  have hθΔ' : Set.MapsTo θ (Δ : Set (Fin τ.rank → ℤ)) Δ := fun β hβ => by
    have h1 : θ β ∈ θ '' (Δ : Set (Fin τ.rank → ℤ)) := ⟨β, hβ, rfl⟩
    rwa [hθΔ] at h1
  have hsign : ∀ β : Fin τ.rank → ℤ, ∃ a : kˣ, β ∈ Δ → ∀ c : k,
      frobTwistGL τ k p e Q₀ (rootSL2 τ k β (uSL c)) =
          rootSL2 τ k (θ β) (uSL ((a : k) * iterateFrobenius k p e c)) ∧
        frobTwistGL τ k p e Q₀ (rootSL2 τ k β (vSL c)) =
          rootSL2 τ k (θ β) (vSL (((a⁻¹ : kˣ) : k) * iterateFrobenius k p e c)) := by
    intro β
    by_cases hβ : β ∈ Δ
    · obtain ⟨a, ha⟩ := exists_frobTwistGL_rootSL2_of_conj p hp e hQ₀ (simpleRoots_isRoot hβ)
        (hθroot β (simpleRoots_isRoot hβ)) (hθneg β)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨1, fun h => absurd h hβ⟩
  choose a ha using hsign
  have hpre : ∀ β ∈ Δ, Function.invFunOn θ (Δ : Set (Fin τ.rank → ℤ)) (θ β) = β :=
    fun β hβ => hθinj.injOn.leftInvOn_invFunOn hβ
  let ν : Fin Δ.card → Fin τ.rank → ℤ := fun i => (Δ.equivFin.symm i : Fin τ.rank → ℤ)
  have hνinj : Function.Injective ν := Subtype.val_injective.comp Δ.equivFin.symm.injective
  have hνΔ : ∀ i, ν i ∈ Δ := fun i => (Δ.equivFin.symm i).2
  obtain ⟨c, hc⟩ := algebraically_closed_lattice_character_interpolation k τ.rank Δ.card ν
    (linearIndependent_simpleRoots_kernelRoots hνinj hνΔ)
    fun i => (a (Function.invFunOn θ (Δ : Set (Fin τ.rank → ℤ)) (ν i)))⁻¹
  have hχc : ∀ β ∈ Δ, rootChar c (θ β) = (a β)⁻¹ := by
    intro β hβ
    have hi := hc (Δ.equivFin ⟨θ β, hθΔ' hβ⟩)
    have hν : ν (Δ.equivFin ⟨θ β, hθΔ' hβ⟩) = θ β := by
      simp only [ν, Equiv.symm_apply_apply]
    rw [hν, hpre β hβ] at hi
    exact hi
  set h := rootDiagUnit τ c with hh_def
  have hhT : h ∈ torusGroup τ k := rootDiagUnit_mem_torusGroup c
  have hFh : ∀ y, frobTwistGL τ k p e (h * Q₀) y = h * frobTwistGL τ k p e Q₀ y * h⁻¹ := by
    intro y
    simp only [frobTwistGL_apply]
    group
  have hpin : ∀ β ∈ Δ, ∀ A : SL2 k, frobTwistGL τ k p e (h * Q₀) (rootSL2 τ k β A) =
      rootSL2 τ k (θ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A) := by
    intro β hβ A
    have hθβ : IsRoot τ (θ β) := hθroot β (simpleRoots_isRoot hβ)
    have heq := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := k))
      (f := (frobTwistGL τ k p e (h * Q₀)).comp (rootSL2 τ k β))
      (g := (rootSL2 τ k (θ β)).comp
        (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e))) ?_
    · exact DFunLike.congr_fun heq A
    rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · change frobTwistGL τ k p e (h * Q₀) (rootSL2 τ k β (uSL z)) =
        rootSL2 τ k (θ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) (uSL z))
      rw [hFh, (ha β hβ z).1, (rootDiagUnit_conj_rootSL2 c hθβ _).1, map_uSL, hχc β hβ,
        ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · change frobTwistGL τ k p e (h * Q₀) (rootSL2 τ k β (vSL z)) =
        rootSL2 τ k (θ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) (vSL z))
      rw [hFh, (ha β hβ z).2, (rootDiagUnit_conj_rootSL2 c hθβ _).2, map_vSL, hχc β hβ,
        inv_inv, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hhQ₀ : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c' : k,
      (h * Q₀) * pinnedX τ k γ c' * (h * Q₀)⁻¹ = pinnedX τ k (θ γ) (μ * c') := by
    intro γ hγ
    obtain ⟨μ, hμ⟩ := hQ₀ γ hγ
    refine ⟨rootChar c (θ γ) * μ, fun c' => ?_⟩
    calc (h * Q₀) * pinnedX τ k γ c' * (h * Q₀)⁻¹ =
        h * (Q₀ * pinnedX τ k γ c' * Q₀⁻¹) * h⁻¹ := by group
      _ = _ := by
        rw [hμ, rootDiagUnit_conj_pinnedX c (hθroot γ hγ), Units.val_mul, mul_assoc]
  have hhQ₀T : h * Q₀ ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    mul_mem (Subgroup.le_normalizer hhT) hQ₀T
  have hSmap : ∀ {Q : ModGL τ k}, (∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c' : k,
      Q * pinnedX τ k γ c' * Q⁻¹ = pinnedX τ k (θ γ) (μ * c')) →
      (rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q) =
        rootSpan τ k (kernelRoots χ) := fun hQ => by
    rw [map_frobTwistGL_rootSpan_of_conj p e hQ fun α hα => hα.1, hθS]
  have hS := hSmap hhQ₀
  have hM : (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map
      (frobTwistGL τ k p e (h * Q₀)) = torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
    rw [Subgroup.map_sup, map_frobTwistGL_torusGroup p e hhQ₀T, hS]
  have hiter : ∀ d : ℕ, (∀ β ∈ Δ, θ^[d] β = β) → ∀ s ∈ rootSpan τ k (kernelRoots χ),
      (frobTwistGL τ k p e (h * Q₀))^[d] s = entrywiseFrobGL τ k p (e * d) s := by
    intro d hd s hs
    let Fd : Monoid.End (ModGL τ k) := frobTwistGL τ k p e (h * Q₀)
    have hFd : ⇑(Fd ^ d) = (⇑(frobTwistGL τ k p e (h * Q₀)))^[d] := Monoid.End.coe_pow _ Fd d
    have hle : rootSpan τ k (kernelRoots χ) ≤
        MonoidHom.eqLocus (M := ModGL τ k) (Fd ^ d) (entrywiseFrobGL τ k p (e * d)) := by
      rw [rootSpan_kernelRoots_eq_iSup_rootRankOneGroup]
      refine iSup₂_le fun β hβ => ?_
      rintro _ ⟨A, rfl⟩
      change (Fd ^ d) (rootSL2 τ k β A) = entrywiseFrobGL τ k p (e * d) (rootSL2 τ k β A)
      rw [hFd, iterate_frobTwistGL_rootSL2_of_map p e hθΔ' hpin d β hβ A, hd β hβ,
        entrywiseFrobGL_rootSL2 p (e * d) (simpleRoots_isRoot hβ)]
    have h1 := hle hs
    change (Fd ^ d) s = _ at h1
    rwa [hFd] at h1
  have hfin : Finite (fixedPointsIn (rootSpan τ k (kernelRoots χ))
      (frobTwistGL τ k p e (h * Q₀))) := by
    obtain ⟨d, hd, hdΔ⟩ := exists_iterate_eq_of_mapsTo Δ.finite_toSet hθΔ' hθinj.injOn
    have hsub : (fixedPointsIn (rootSpan τ k (kernelRoots χ)) (frobTwistGL τ k p e (h * Q₀)) :
        Set (ModGL τ k)) ⊆ {g | entrywiseFrobGL τ k p (e * d) g = g} := by
      intro s hs
      obtain ⟨hsS, hsF⟩ := mem_fixedPointsIn.1 hs
      have h1 := hiter d hdΔ s hsS
      rw [Function.iterate_fixed hsF] at h1
      exact h1.symm
    exact ((finite_setOf_entrywiseFrobGL_eq p (Nat.mul_le_mul he hd)).subset hsub).to_subtype
  have hker := rootCharKernel_signCharTuple (k := k) hk χ
  obtain ⟨-, ⟨hMc, -, hMsm, -, -⟩, -⟩ := exceptional_toral_centralizer_identity_component τ k hk
    (signCharTuple χ) (signCharTuple_sign χ)
  rw [toralRootPointSubgroup, toralRootGroup, hker] at hMc hMsm
  have hF₀M : ∀ g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ),
      frobTwistGL τ k p e Q₀ g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
    intro g hg
    have hM₀ : (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q₀) =
        torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
      rw [Subgroup.map_sup, map_frobTwistGL_torusGroup p e hQ₀T, hSmap hQ₀]
    rw [← hM₀]
    exact ⟨g, hg, rfl⟩
  obtain ⟨u, huM, hu⟩ := exists_eq_inv_mul_frobTwistGL p he Q₀ hMc hMsm hF₀M
    (Subgroup.mem_sup_left hhT)
  have hF₀u : frobTwistGL τ k p e Q₀ u = u * h := by
    rw [hu]
    group
  have hconj : ∀ y, frobTwistGL τ k p e Q₀ (u * y * u⁻¹) =
      u * frobTwistGL τ k p e (h * Q₀) y * u⁻¹ := by
    intro y
    rw [map_mul, map_mul, map_inv, hF₀u, hFh]
    group
  have hΔ' : ∀ β ∈ unionSimpleRoots χ Set.univ, β ∈ Δ := fun β hβ => by
    rw [← Finset.mem_coe, ← hΔeq]
    exact hβ
  refine ⟨h, hhT, fun β hβ A => hpin β (hΔ' β hβ) A, hS, hM,
    fun d _ hd => hiter d fun β hβ => hd β (by rw [hΔeq]; exact hβ), hfin, u, huM, ?_⟩
  ext z
  rw [Subgroup.mem_map, mem_fixedPointsIn]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyM, hyF⟩ := mem_fixedPointsIn.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨mul_mem (mul_mem huM hyM) (inv_mem huM), by rw [hconj, hyF]⟩
  · rintro ⟨hzM, hzF⟩
    refine ⟨u⁻¹ * z * u, mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem huM) hzM) huM, ?_⟩, ?_⟩
    · have h1 := hconj (u⁻¹ * z * u)
      rw [show u * (u⁻¹ * z * u) * u⁻¹ = z by group, hzF] at h1
      calc frobTwistGL τ k p e (h * Q₀) (u⁻¹ * z * u) =
          u⁻¹ * (u * frobTwistGL τ k p e (h * Q₀) (u⁻¹ * z * u) * u⁻¹) * u := by group
        _ = u⁻¹ * z * u := by rw [← h1]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end Main

end CFSG.LieType.AlgebraicGroups
