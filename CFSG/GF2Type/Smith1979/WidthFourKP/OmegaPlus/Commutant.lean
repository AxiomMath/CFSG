module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.OmegaFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial

@[expose] def ωM : S10.M2 := !![0, 1; 1, 1]

@[expose] def sM : S10.M2 := !![0, 1; 1, 0]

@[expose] def gab (ab : S10.M2 × S10.M2) (m : S10.M2) : S10.M2 :=
  (m 0 0 + m 0 1 + m 1 0) • ab.1 + (m 0 0 + m 1 1) • (ωM * ab.1) +
    (m 0 0 + m 0 1 + m 1 1) • ab.2 + (m 0 1 + m 1 0) • (ωM * ab.2)

private theorem M2_coords : ∀ m : S10.M2,
    m = (m 0 0 + m 0 1 + m 1 0) • (1 : S10.M2) +
      (m 0 0 + m 1 1) • ωM + (m 0 0 + m 0 1 + m 1 1) • sM +
        (m 0 1 + m 1 0) • (ωM * sM) := by
  decide +kernel

theorem eq_gab {f : S10.M2 →ₗ[ZMod 2] S10.M2} (hf : ∀ m, f (ωM * m) = ωM * f m) :
    ∀ m, f m = gab (f 1, f sM) m := by
  intro m
  conv_lhs => rw [M2_coords m]
  have h1 : f ωM = ωM * f 1 := by rw [← hf, mul_one]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, hf sM]
  rfl

private theorem gab_one (m : S10.M2) : gab ((1 : S10.M2), sM) m = m := by
  simp only [gab, mul_one]
  exact (M2_coords m).symm

set_option maxRecDepth 100000 in
theorem card_gab_alt : (Finset.univ.filter fun ab : S10.M2 × S10.M2 =>
    (∀ m, gab ab (m * ωM) = gab ab m * ωM) ∧ ∀ m, S10.pf (gab ab m) m = 0).card = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gab_cube : ∀ ab : S10.M2 × S10.M2, (∀ m, gab ab (m * ωM) = gab ab m * ωM) →
    Function.Injective (gab ab) → ∀ m, gab ab (gab ab (gab ab m)) = m := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gab_eq_id : ∀ ab : S10.M2 × S10.M2, (∀ m, gab ab (m * ωM) = gab ab m * ωM) →
    (∀ m, S10.pf (gab ab m) m = 0) → Function.Injective (gab ab) → ab = (1, sM) := by
  decide +kernel

theorem exists_act_left : ∃ γ : S10.Gm, γ ^ 3 = 1 ∧ ∀ m, S10.act γ m = ωM * m :=
  ⟨(⟨ωM, by decide +kernel⟩, 1), by decide +kernel, fun m => by simp [S10.act]⟩

theorem exists_act_right : ∃ γ : S10.Gm, γ ^ 3 = 1 ∧ ∀ m, S10.act γ m = m * ωM :=
  ⟨(1, ⟨ωM, by decide +kernel⟩), by decide +kernel, fun m => by
    have hT : ωM.transpose = ωM := by decide +kernel
    simp [S10.act, hT]⟩

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {Q : QuadraticForm (ZMod 2) W}

theorem exists_isometry_M2 (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ e : W ≃ₗ[ZMod 2] S10.M2, ∀ w, S10.q₀ (e w) = Q w := by
  obtain ⟨e₁⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ (n := 2)
    (by rw [h4]) hplus
  refine ⟨e₁.toLinearEquiv.trans S10.plusEquiv, fun w => ?_⟩
  change S10.q₀ (S10.plusEquiv (e₁ w)) = Q w
  rw [S10.q₀_plusEquiv, e₁.map_app]

private theorem polar_eq_of_isometry (e : W ≃ₗ[ZMod 2] S10.M2)
    (he : ∀ w, S10.q₀ (e w) = Q w) (x y : W) :
    Q.polarBilin x y = S10.pf (e x) (e y) := by
  rw [QuadraticMap.polarBilin_apply_apply, ← S10.polar_q₀]
  simp only [QuadraticMap.polar, he, map_add]
  rw [← he (x + y), map_add]

private theorem conjEquiv_mem_omegaGroup_iff (hQ : Q.polarBilin.Nondegenerate)
    (e : W ≃ₗ[ZMod 2] S10.M2) (he : ∀ w, S10.q₀ (e w) = Q w)
    {f : W ≃ₗ[ZMod 2] W} :
    conjEquiv e f ∈ omegaGroup S10.q₀ S10.q₀_nondegenerate ↔ f ∈ omegaGroup Q hQ := by
  constructor
  · intro h
    have h' : conjEquiv e.symm (conjEquiv e f) ∈ omegaGroup Q hQ :=
      conjEquiv_mem_omegaGroup S10.q₀_nondegenerate hQ e.symm
        (fun m => by rw [← he (e.symm m), LinearEquiv.apply_symm_apply]) h
    have hsymm : conjEquiv e.symm (conjEquiv e f) = f := by
      ext w
      rw [conjEquiv_apply, conjEquiv_apply]
      simp
    rwa [hsymm] at h'
  · intro h
    exact conjEquiv_mem_omegaGroup hQ S10.q₀_nondegenerate e he h

theorem pow_three_of_pow_nine_omega (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) W = 4) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {f : W ≃ₗ[ZMod 2] W} (hf : f ∈ omegaGroup Q hQ) (h9 : f ^ 9 = 1) : f ^ 3 = 1 := by
  obtain ⟨e, he⟩ := exists_isometry_M2 hQ h4 hplus
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp (by
    rw [S10.range_ρ₀]
    exact (conjEquiv_mem_omegaGroup_iff hQ e he).mpr hf)
  have hγ9 : γ ^ 9 = 1 := by
    apply S10.ρ₀_injective
    rw [map_pow, map_one, hγ]
    calc (conjEquiv e f) ^ 9 = conjEquiv e (f ^ 9) := (map_pow (conjEquiv e) f 9).symm
      _ = 1 := by rw [h9, map_one]
  have hγ3 := gm_pow_three_of_pow_nine γ hγ9
  apply (conjEquiv e).injective
  rw [map_pow, map_one, ← hγ, ← map_pow, hγ3, map_one]

private theorem eq_set_of_le_omegaGroup (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) W = 4) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {P : Subgroup (W ≃ₗ[ZMod 2] W)} (hP : P ≤ omegaGroup Q hQ) (hP9 : Nat.card P = 9) :
    (P : Set (W ≃ₗ[ZMod 2] W)) = {f | f ∈ omegaGroup Q hQ ∧ f ^ 3 = 1} := by
  classical
  obtain ⟨e, he⟩ := exists_isometry_M2 hQ h4 hplus
  let P' : Subgroup S10.Gm := (P.map (conjEquiv e).toMonoidHom).comap S10.ρ₀
  have hcube : ∀ f ∈ P, f ^ 3 = 1 := by
    intro f hf
    refine pow_three_of_pow_nine_omega hQ h4 hplus (hP hf) ?_
    have h := pow_card_eq_one' (G := P) (x := ⟨f, hf⟩)
    rw [hP9] at h
    exact congrArg Subtype.val h
  have hP'card : Nat.card P' = 9 := by
    have hle : P.map (conjEquiv e).toMonoidHom ≤ S10.ρ₀.range := by
      rintro _ ⟨f, hf, rfl⟩
      rw [S10.range_ρ₀]
      exact (conjEquiv_mem_omegaGroup_iff hQ e he).mpr (hP hf)
    have h1 : Nat.card (P.map (conjEquiv e).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (conjEquiv e).injective, hP9]
    have h2 := Subgroup.map_comap_eq_self hle
    rw [← h1, ← h2, Subgroup.card_map_of_injective S10.ρ₀_injective]
  have hsubF : (P' : Set S10.Gm).toFinset ⊆
      Finset.univ.filter (fun δ : S10.Gm => δ ^ 3 = 1) := by
    intro δ hδ
    simp only [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_comap] at hδ
    obtain ⟨f, hf, hfe⟩ := Subgroup.mem_map.mp hδ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply S10.ρ₀_injective
    rw [map_pow, map_one, ← hfe, ← map_pow, hcube f hf, map_one]
  have hcardP' : (P' : Set S10.Gm).toFinset.card = 9 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hP'card
  have heqF : (P' : Set S10.Gm).toFinset =
      Finset.univ.filter (fun δ : S10.Gm => δ ^ 3 = 1) :=
    Finset.eq_of_subset_of_card_le hsubF (by rw [gm_card_pow_three, hcardP'])
  have hmemP' : ∀ δ : S10.Gm, δ ∈ P' ↔ δ ^ 3 = 1 := by
    intro δ
    have h1 : δ ∈ (P' : Set S10.Gm).toFinset ↔
        δ ∈ Finset.univ.filter (fun δ : S10.Gm => δ ^ 3 = 1) := by
      rw [heqF]
    simpa using h1
  ext f
  constructor
  · intro hf
    exact ⟨hP hf, hcube f hf⟩
  · rintro ⟨hfΩ, hf3⟩
    have hrange : conjEquiv e f ∈ S10.ρ₀.range := by
      rw [S10.range_ρ₀]
      exact (conjEquiv_mem_omegaGroup_iff hQ e he).mpr hfΩ
    obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.mp hrange
    have hδ3 : δ ^ 3 = 1 := by
      apply S10.ρ₀_injective
      rw [map_pow, map_one, hδ, ← map_pow, hf3, map_one]
    have hδP' : δ ∈ P' := (hmemP' δ).mpr hδ3
    rw [Subgroup.mem_comap] at hδP'
    obtain ⟨g, hg, hgδ⟩ := Subgroup.mem_map.mp hδP'
    have hgf : g = f := by
      apply (conjEquiv e).injective
      have hgg : conjEquiv e g = S10.ρ₀ δ := hgδ
      rw [hgg, hδ]
    rwa [← hgf]

theorem eq_of_card_nine_omega (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {P P' : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hP : P ≤ omegaGroup Q hQ) (hP9 : Nat.card P = 9) (hP' : P' ≤ omegaGroup Q hQ)
    (hP'9 : Nat.card P' = 9) : P' = P := by
  have hP := eq_set_of_le_omegaGroup hQ h4 hplus hP hP9
  have hP' := eq_set_of_le_omegaGroup hQ h4 hplus hP' hP'9
  exact SetLike.ext' (hP'.trans hP.symm)

private theorem mem_P_of_mem_omegaGroup_cube (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) W = 4) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {P : Subgroup (W ≃ₗ[ZMod 2] W)} (hP : P ≤ omegaGroup Q hQ) (hP9 : Nat.card P = 9)
    {e : W ≃ₗ[ZMod 2] S10.M2} (he : ∀ w, S10.q₀ (e w) = Q w) {γ : S10.Gm}
    (hγ3 : γ ^ 3 = 1) :
    conjEquiv e.symm (S10.ρ₀ γ) ∈ P := by
  have hΩ : conjEquiv e.symm (S10.ρ₀ γ) ∈ omegaGroup Q hQ :=
    conjEquiv_mem_omegaGroup S10.q₀_nondegenerate hQ e.symm
      (fun m => by rw [← he (e.symm m), LinearEquiv.apply_symm_apply])
      (by rw [← S10.range_ρ₀]; exact ⟨γ, rfl⟩)
  have hcube : (conjEquiv e.symm (S10.ρ₀ γ)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hγ3, map_one, map_one]
  have heq := eq_set_of_le_omegaGroup hQ h4 hplus hP hP9
  have hmem : conjEquiv e.symm (S10.ρ₀ γ) ∈ (P : Set (W ≃ₗ[ZMod 2] W)) := by
    rw [heq]
    exact ⟨hΩ, hcube⟩
  exact hmem


private theorem comp_commute_left {e : W ≃ₗ[ZMod 2] S10.M2} {γ : S10.Gm}
    (hγ : ∀ m, S10.act γ m = ωM * m) {f : W →ₗ[ZMod 2] W}
    (hf : ∀ w, f (conjEquiv e.symm (S10.ρ₀ γ) w) = conjEquiv e.symm (S10.ρ₀ γ) (f w))
    (m : S10.M2) :
    (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) (ωM * m) =
      ωM * (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) m := by
  have h1 : e.symm (ωM * m) = conjEquiv e.symm (S10.ρ₀ γ) (e.symm m) := by
    rw [conjEquiv_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply, S10.ρ₀_apply]
    rw [hγ]
  calc (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) (ωM * m)
      = e (f (e.symm (ωM * m))) := rfl
    _ = e (f (conjEquiv e.symm (S10.ρ₀ γ) (e.symm m))) := by rw [h1]
    _ = e (conjEquiv e.symm (S10.ρ₀ γ) (f (e.symm m))) := by rw [hf]
    _ = S10.ρ₀ γ (e (f (e.symm m))) := by
          rw [conjEquiv_apply]
          simp only [LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply,
            LinearEquiv.apply_symm_apply]
    _ = ωM * e (f (e.symm m)) := by rw [S10.ρ₀_apply]; exact hγ _
    _ = ωM * (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) m := rfl

private theorem comp_commute_right {e : W ≃ₗ[ZMod 2] S10.M2} {γ : S10.Gm}
    (hγ : ∀ m, S10.act γ m = m * ωM) {f : W →ₗ[ZMod 2] W}
    (hf : ∀ w, f (conjEquiv e.symm (S10.ρ₀ γ) w) = conjEquiv e.symm (S10.ρ₀ γ) (f w))
    (m : S10.M2) :
    (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) (m * ωM) =
      (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) m * ωM := by
  have h1 : e.symm (m * ωM) = conjEquiv e.symm (S10.ρ₀ γ) (e.symm m) := by
    rw [conjEquiv_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply, S10.ρ₀_apply]
    rw [hγ]
  calc (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) (m * ωM)
      = e (f (e.symm (m * ωM))) := rfl
    _ = e (f (conjEquiv e.symm (S10.ρ₀ γ) (e.symm m))) := by rw [h1]
    _ = e (conjEquiv e.symm (S10.ρ₀ γ) (f (e.symm m))) := by rw [hf]
    _ = S10.ρ₀ γ (e (f (e.symm m))) := by
          rw [conjEquiv_apply]
          simp only [LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply,
            LinearEquiv.apply_symm_apply]
    _ = e (f (e.symm m)) * ωM := by rw [S10.ρ₀_apply]; exact hγ _
    _ = (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) m * ωM := rfl

theorem card_commutant_alt_le (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {P : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hP : P ≤ omegaGroup Q hQ) (hP9 : Nat.card P = 9) :
    Nat.card {f : W →ₗ[ZMod 2] W //
      (∀ p ∈ P, ∀ w, f (p w) = p (f w)) ∧ ∀ w, Q.polarBilin (f w) w = 0} ≤ 4 := by
  classical
  obtain ⟨e, he⟩ := exists_isometry_M2 hQ h4 hplus
  obtain ⟨γl, hγl3, hγl⟩ := exists_act_left
  obtain ⟨γr, hγr3, hγr⟩ := exists_act_right
  have hflP : conjEquiv e.symm (S10.ρ₀ γl) ∈ P :=
    mem_P_of_mem_omegaGroup_cube hQ h4 hplus hP hP9 he hγl3
  have hfrP : conjEquiv e.symm (S10.ρ₀ γr) ∈ P :=
    mem_P_of_mem_omegaGroup_cube hQ h4 hplus hP hP9 he hγr3
  let F : (W →ₗ[ZMod 2] W) → (S10.M2 →ₗ[ZMod 2] S10.M2) :=
    fun f => e.toLinearMap.comp (f.comp e.symm.toLinearMap)
  have hFl : ∀ (f : W →ₗ[ZMod 2] W), (∀ p ∈ P, ∀ w, f (p w) = p (f w)) →
      ∀ m, F f (ωM * m) = ωM * F f m := by
    intro f hf m
    exact comp_commute_left hγl (hf _ hflP) m
  have hFr : ∀ (f : W →ₗ[ZMod 2] W), (∀ p ∈ P, ∀ w, f (p w) = p (f w)) →
      ∀ m, F f (m * ωM) = F f m * ωM := by
    intro f hf m
    exact comp_commute_right hγr (hf _ hfrP) m
  have hFa : ∀ (f : W →ₗ[ZMod 2] W), (∀ w, Q.polarBilin (f w) w = 0) →
      ∀ m, S10.pf (F f m) m = 0 := by
    intro f hf m
    have h := hf (e.symm m)
    rw [polar_eq_of_isometry e he] at h
    simpa [F] using h
  have key : ∀ (f : W →ₗ[ZMod 2] W), (∀ p ∈ P, ∀ w, f (p w) = p (f w)) →
      (∀ w, Q.polarBilin (f w) w = 0) →
      (F f 1, F f sM) ∈ Finset.univ.filter (fun ab : S10.M2 × S10.M2 =>
        (∀ m, gab ab (m * ωM) = gab ab m * ωM) ∧ ∀ m, S10.pf (gab ab m) m = 0) := by
    intro f hf hfalt
    have hgab : ∀ m, F f m = gab (F f 1, F f sM) m := eq_gab (hFl f hf)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun m => ?_, fun m => ?_⟩
    · rw [← hgab (m * ωM), ← hgab m]
      exact hFr f hf m
    · rw [← hgab m]
      exact hFa f hfalt m
  let Φ : {f : W →ₗ[ZMod 2] W //
      (∀ p ∈ P, ∀ w, f (p w) = p (f w)) ∧ ∀ w, Q.polarBilin (f w) w = 0} →
      {ab : S10.M2 × S10.M2 // ab ∈ Finset.univ.filter (fun ab : S10.M2 × S10.M2 =>
        (∀ m, gab ab (m * ωM) = gab ab m * ωM) ∧ ∀ m, S10.pf (gab ab m) m = 0)} :=
    fun f => ⟨(F f.1 1, F f.1 sM), key f.1 f.2.1 f.2.2⟩
  have hΦinj : Function.Injective Φ := by
    rintro ⟨f, hfP, hfalt⟩ ⟨g', hgP, hgalt⟩ hfg
    have hpair : (F f 1, F f sM) = (F g' 1, F g' sM) := congrArg Subtype.val hfg
    have hFf : ∀ m, F f m = gab (F f 1, F f sM) m := eq_gab (hFl f hfP)
    have hFg : ∀ m, F g' m = gab (F g' 1, F g' sM) m := eq_gab (hFl g' hgP)
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    have hm : F f (e w) = F g' (e w) := by rw [hFf, hFg, hpair]
    have := congrArg e.symm hm
    simpa [F] using this
  calc Nat.card {f : W →ₗ[ZMod 2] W //
        (∀ p ∈ P, ∀ w, f (p w) = p (f w)) ∧ ∀ w, Q.polarBilin (f w) w = 0}
      ≤ Nat.card {ab : S10.M2 × S10.M2 // ab ∈ Finset.univ.filter
          (fun ab : S10.M2 × S10.M2 =>
            (∀ m, gab ab (m * ωM) = gab ab m * ωM) ∧
              ∀ m, S10.pf (gab ab m) m = 0)} :=
        Nat.card_le_card_of_injective Φ hΦinj
    _ = 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_gab_alt]

theorem eq_id_of_commute_alt (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {P : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hP : P ≤ omegaGroup Q hQ) (hP9 : Nat.card P = 9) {f : W →ₗ[ZMod 2] W}
    (hfP : ∀ p ∈ P, ∀ w, f (p w) = p (f w)) (halt : ∀ w, Q.polarBilin (f w) w = 0)
    (hinj : Function.Injective f) : f = LinearMap.id := by
  classical
  obtain ⟨e, he⟩ := exists_isometry_M2 hQ h4 hplus
  obtain ⟨γl, hγl3, hγl⟩ := exists_act_left
  obtain ⟨γr, hγr3, hγr⟩ := exists_act_right
  have hflP : conjEquiv e.symm (S10.ρ₀ γl) ∈ P :=
    mem_P_of_mem_omegaGroup_cube hQ h4 hplus hP hP9 he hγl3
  have hfrP : conjEquiv e.symm (S10.ρ₀ γr) ∈ P :=
    mem_P_of_mem_omegaGroup_cube hQ h4 hplus hP hP9 he hγr3
  let F : S10.M2 →ₗ[ZMod 2] S10.M2 := e.toLinearMap.comp (f.comp e.symm.toLinearMap)
  have hFl : ∀ m, F (ωM * m) = ωM * F m := by
    intro m
    exact comp_commute_left hγl (hfP _ hflP) m
  have hFr : ∀ m, F (m * ωM) = F m * ωM := by
    intro m
    exact comp_commute_right hγr (hfP _ hfrP) m
  have hFa : ∀ m, S10.pf (F m) m = 0 := by
    intro m
    have h := halt (e.symm m)
    rw [polar_eq_of_isometry e he] at h
    simpa [F] using h
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : f (e.symm x) = f (e.symm y) := e.injective hxy
    exact e.symm.injective (hinj h1)
  have hgab : ∀ m, F m = gab (F 1, F sM) m := eq_gab hFl
  have hid : (F 1, F sM) = ((1 : S10.M2), sM) := by
    refine gab_eq_id (F 1, F sM) (fun m => ?_) (fun m => ?_) (fun x y hxy => ?_)
    · rw [← hgab (m * ωM), ← hgab m]
      exact hFr m
    · rw [← hgab m]
      exact hFa m
    · exact hFinj (by rw [hgab x, hgab y]; exact hxy)
  have hFid : F = LinearMap.id := by
    apply LinearMap.ext
    intro m
    rw [hgab, hid]
    exact gab_one m
  apply LinearMap.ext
  intro w
  have h := congrArg e.symm (congrArg (fun g => g (e w)) hFid)
  simpa [F] using h

theorem pow_three_of_commute (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {P : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hP : P ≤ omegaGroup Q hQ) (hP9 : Nat.card P = 9) {f : W ≃ₗ[ZMod 2] W}
    (hfP : ∀ p ∈ P, f * p = p * f) : f ^ 3 = 1 := by
  classical
  obtain ⟨e, he⟩ := exists_isometry_M2 hQ h4 hplus
  obtain ⟨γl, hγl3, hγl⟩ := exists_act_left
  obtain ⟨γr, hγr3, hγr⟩ := exists_act_right
  have hflP : conjEquiv e.symm (S10.ρ₀ γl) ∈ P :=
    mem_P_of_mem_omegaGroup_cube hQ h4 hplus hP hP9 he hγl3
  have hfrP : conjEquiv e.symm (S10.ρ₀ γr) ∈ P :=
    mem_P_of_mem_omegaGroup_cube hQ h4 hplus hP hP9 he hγr3
  let F : S10.M2 →ₗ[ZMod 2] S10.M2 := e.toLinearMap.comp (f.toLinearMap.comp e.symm.toLinearMap)
  have hpoint : ∀ p ∈ P, ∀ w, f (p w) = p (f w) := by
    intro p hp w
    have h := congrArg (fun g : W ≃ₗ[ZMod 2] W => g w) (hfP p hp)
    simpa using h
  have hFl : ∀ m, F (ωM * m) = ωM * F m := by
    intro m
    exact comp_commute_left hγl (hpoint _ hflP) m
  have hFr : ∀ m, F (m * ωM) = F m * ωM := by
    intro m
    exact comp_commute_right hγr (hpoint _ hfrP) m
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : f (e.symm x) = f (e.symm y) := e.injective hxy
    exact e.symm.injective (f.injective h1)
  have hgab : ∀ m, F m = gab (F 1, F sM) m := eq_gab hFl
  have hgabinj : Function.Injective (gab (F 1, F sM)) := by
    intro x y hxy
    exact hFinj (by rw [hgab x, hgab y]; exact hxy)
  have hFrgab : ∀ m, gab (F 1, F sM) (m * ωM) = gab (F 1, F sM) m * ωM := by
    intro m
    rw [← hgab (m * ωM), ← hgab m]
    exact hFr m
  have hcube := gab_cube (F 1, F sM) hFrgab hgabinj
  have hF3 : ∀ m, F (F (F m)) = m := by
    intro m
    rw [hgab (F (F m)), hgab (F m), hgab m]
    exact hcube m
  apply LinearEquiv.ext
  intro w
  show (f ^ 3) w = (1 : W ≃ₗ[ZMod 2] W) w
  have h3 : (f ^ 3) w = f (f (f w)) := by
    simp [pow_succ, LinearEquiv.mul_apply]
  rw [h3]
  exact e.injective (by simpa [F, LinearEquiv.symm_apply_apply] using hF3 (e w))

end CFSG.GF2Type.Smith1979.OmegaPlus
