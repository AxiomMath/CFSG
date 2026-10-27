module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddYCase
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddGsub

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Fischer CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec11
  CFSG.RankThree.PartTwo.Sec19

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_tauPow_apply_fix (n : ℕ) {g : C0 σ} (hg : tauAut σ g = g) :
    (tauAut σ ^ n) g = g := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hg]

theorem triOdd_mul_normal_form {α β : MulAut (C0 σ)} {g g' : C0 σ} {δ δ' : X ≃+* X}
    (hα : α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ)
    (hβ : β = MulAut.conj g' * fieldActor (t := TwistTag.D4) σ δ') (hδ : ∃ k : ℕ, δ = σ ^ k)
    (hg' : tauAut σ g' = g') :
    α * β = MulAut.conj (g * g') * fieldActor (t := TwistTag.D4) σ (δ * δ') := by
  obtain ⟨k, rfl⟩ := hδ
  have hfix : fieldActor (t := TwistTag.D4) σ (σ ^ k) g' = g' := by
    rw [triOdd_fieldActor_pow]
    exact triOdd_tauPow_apply_fix σ k hg'
  have hc := aut_conj_conj (fieldActor (t := TwistTag.D4) σ (σ ^ k)) g'
  rw [hfix] at hc
  have hcomm : fieldActor (t := TwistTag.D4) σ (σ ^ k) * MulAut.conj g' =
      MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ k) :=
    mul_inv_eq_iff_eq_mul.mp hc
  rw [hα, hβ, map_mul, fieldActor_mul σ (σ ^ k) δ']
  calc MulAut.conj g * fieldActor (t := TwistTag.D4) σ (σ ^ k) *
        (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ δ')
      = MulAut.conj g * (fieldActor (t := TwistTag.D4) σ (σ ^ k) * MulAut.conj g') *
          fieldActor (t := TwistTag.D4) σ δ' := by group
    _ = MulAut.conj g * (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ k)) *
          fieldActor (t := TwistTag.D4) σ δ' := by rw [hcomm]
    _ = MulAut.conj g * MulAut.conj g' *
          (fieldActor (t := TwistTag.D4) σ (σ ^ k) * fieldActor (t := TwistTag.D4) σ δ') := by
        group

theorem triOdd_closure_fixUnion_eq_top_of_central_tau {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ))
    (hcomm : ∀ α ∈ E, α * tauAut σ = tauAut σ * α) (hτE : tauAut σ ∉ E) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ1 : σ ≠ 1 := triOdd_sigma_ne_one σ (ℓ ^ f) hq2 hX hσ
  have hσ2 : σ ^ 2 ≠ 1 := nf1_sq_ne_one σ hσ3 hσ1
  obtain ⟨-, hdec, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcard3, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  haveI : Finite (X ≃+* X) := Nat.finite_of_card_ne_zero (by rw [hcard3]; omega)
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  have hτ3 : tauAut σ ^ 3 = 1 := triOdd_tauAut_pow_three σ hσ3
  obtain ⟨nf, hnf, huniq⟩ : ∃ nf : MulAut (C0 σ) → C0 σ × (X ≃+* X),
      (∀ α, α = MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (nf α).2) ∧
      ∀ α (y : C0 σ × (X ≃+* X)),
        α = MulAut.conj y.1 * fieldActor (t := TwistTag.D4) σ y.2 → y = nf α :=
    ⟨fun α => Classical.choose (hdec α), fun α => (Classical.choose_spec (hdec α)).1,
      fun α y h => (Classical.choose_spec (hdec α)).2 y h⟩
  have hΘnf : ∀ α, Θ α = (nf α).2 := fun α => hΘ α _ _ (hnf α)
  have hEcube : ∀ α ∈ E, α ^ 3 = 1 := fun α hα =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) α hα
  have hδ : ∀ α ∈ E, ∃ k : ℕ, k < 3 ∧ (nf α).2 = σ ^ k := by
    intro α hα
    have hψ : (nf α).2 ^ 3 = 1 := by rw [← hΘnf, ← map_pow, hEcube α hα, map_one]
    rcases mem_of_cube_eq_one_cyclic σ hσ3 hσ1 hσ2 _ hψ with h | h | h
    · exact ⟨0, by norm_num, by rw [h]; simp⟩
    · exact ⟨1, by norm_num, by rw [h]; simp⟩
    · exact ⟨2, by norm_num, h⟩
  have hcommσ : ∀ k : ℕ, σ * σ ^ k = σ ^ k * σ := fun k => (pow_mul_comm' σ k).symm
  have hgJ : ∀ α ∈ E, tauAut σ (nf α).1 = (nf α).1 := by
    intro α hα
    obtain ⟨k, -, hk⟩ := hδ α hα
    have h1 := hcomm α hα
    rw [hnf α, hk] at h1
    have e1 : MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k) * tauAut σ =
        MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k * σ) := by
      rw [fieldActor_mul]; rfl
    have e2 : tauAut σ * (MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k)) =
        MulAut.conj (tauAut σ (nf α).1) * fieldActor (t := TwistTag.D4) σ (σ * σ ^ k) := by
      have hc := aut_conj_conj (tauAut σ) (nf α).1
      calc tauAut σ * (MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k))
          = (tauAut σ * MulAut.conj (nf α).1 * (tauAut σ)⁻¹) *
              (tauAut σ * fieldActor (t := TwistTag.D4) σ (σ ^ k)) := by group
        _ = _ := by rw [hc, fieldActor_mul]
    rw [e1, e2, ← hcommσ k] at h1
    have h2 : MulAut.conj (nf α).1 = MulAut.conj (tauAut σ (nf α).1) := mul_right_cancel h1
    exact (hinj h2).symm
  have hπmul : ∀ α ∈ E, ∀ β ∈ E, (nf (α * β)).1 = (nf α).1 * (nf β).1 := by
    intro α hα β hβ
    obtain ⟨k, -, hk⟩ := hδ α hα
    have hmul := triOdd_mul_normal_form σ (hnf α) (hnf β) ⟨k, hk⟩ (hgJ β hβ)
    have h := huniq (α * β) ((nf α).1 * (nf β).1, (nf α).2 * (nf β).2) hmul
    exact congrArg Prod.fst h.symm
  let π : E →* C0 σ := MonoidHom.mk' (fun α => (nf α.1).1) (fun α β => hπmul α.1 α.2 β.1 β.2)
  have hπ : ∀ α : E, π α = (nf α.1).1 := fun α => rfl
  have hπker : ∀ α : E, π α = 1 → α = 1 := by
    intro α hα
    have hg1 : (nf α.1).1 = 1 := hα
    obtain ⟨k, hk3, hk⟩ := hδ α.1 α.2
    have hαeq : (α : MulAut (C0 σ)) = tauAut σ ^ k := by
      have h := hnf α.1
      rwa [hg1, hk, map_one, one_mul, triOdd_fieldActor_pow] at h
    interval_cases k
    · exact Subtype.ext (by rw [hαeq]; simp)
    · exact absurd (by simpa [hαeq] using α.2) hτE
    · refine absurd ?_ hτE
      have h2 : tauAut σ ^ 2 ∈ E := hαeq ▸ α.2
      have h4 : tauAut σ = (tauAut σ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hτ3, one_mul]
      rw [h4]
      exact E.pow_mem h2 2
  have hπinj : Function.Injective π := (injective_iff_map_eq_one π).2 hπker
  have hFG : π.range ≤ Gsub σ := by
    rintro _ ⟨α, rfl⟩
    exact hgJ α.1 α.2
  have hFab : ∀ a ∈ π.range, ∀ b ∈ π.range, a * b = b * a := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (elemAb_comm hE α.1 α.2 β.1 β.2))
  have hF3 : ∀ a ∈ π.range, a ^ 3 = 1 := by
    rintro _ ⟨α, rfl⟩
    rw [← map_pow]
    have : α ^ 3 = 1 := Subtype.ext (hEcube α.1 α.2)
    rw [this, map_one]
  have hcardF : Nat.card π.range = 3 ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv).symm.trans hcard
  have hgen := triOdd_gsub_plane_gen σ hℓ hℓ2 hℓ3 hf hX hσ π.range hFG hFab hF3 hcardF
  have hGsub : Gsub σ ≤ Subgroup.closure (fixUnion E) := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro j ⟨hjG, _, ⟨α, rfl⟩, hf1, hjf⟩
    have hα1 : (α : MulAut (C0 σ)) ≠ 1 := fun h => hf1 (by
      have : α = 1 := Subtype.ext h
      rw [this, map_one])
    obtain ⟨k, -, hk⟩ := hδ α.1 α.2
    have hjτ : tauAut σ j = j := hjG
    have hfix : (α : MulAut (C0 σ)) j = j := by
      have h1 : (α : MulAut (C0 σ)) = MulAut.conj (nf α.1).1 * tauAut σ ^ k := by
        have h := hnf α.1
        rwa [hk, triOdd_fieldActor_pow] at h
      have hjf' : j * (nf α.1).1 = (nf α.1).1 * j := hjf
      rw [h1, MulAut.mul_apply, triOdd_tauPow_apply_fix σ k hjτ, MulAut.conj_apply, ← hjf',
        mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.subset_closure (fixedSubgroup_subset_fixUnion α.2 hα1 hfix)
  obtain ⟨x, hx3, hx1, _g, _e, -, -, -, hEeq⟩ :=
    triOdd_plane_shape σ hℓ hℓ2 hf hX hσ E hE hcard hout
  have hcx : MulAut.conj x ∈ E := by rw [hEeq]; exact Subgroup.subset_closure (by simp)
  have hcx1 : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (h.trans (map_one MulAut.conj).symm))
  have hτx : tauAut σ x = x := by
    have h1 := hcomm _ hcx
    have h2 := aut_conj_conj (tauAut σ) x
    apply hinj
    rw [← h2, ← h1, mul_inv_cancel_right]
  have hW := triOdd_fixedSubgroup_sup_tau hℓ hℓ2 hℓ3 hf hX σ hσ x hx3 hx1 hτx
  have hxle : fixedSubgroup (MulAut.conj x) ≤ Subgroup.closure (fixUnion E) := fun y hy =>
    Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hcx hcx1 hy)
  have hτle : fixedSubgroup (tauAut σ) ≤ Subgroup.closure (fixUnion E) := by
    rw [← triOdd_gsub_eq_fixedSubgroup σ]
    exact hGsub
  rw [eq_top_iff, ← hW]
  exact sup_le hxle hτle

theorem triOdd_map_congr_plane (φ : MulAut (C0 σ)) (E : Subgroup (MulAut (C0 σ)))
    (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hout : ¬ E ≤ innerAut (C0 σ)) :
    CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr φ).toMonoidHom) ∧
      Nat.card (E.map (MulAut.congr φ).toMonoidHom) = 3 ^ 2 ∧
      ¬ E.map (MulAut.congr φ).toMonoidHom ≤ innerAut (C0 σ) := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨isElementaryAbelian_map_three hE (MulAut.congr φ), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
  · intro hle
    apply hout
    intro ψ hψ
    have hmem : (MulAut.congr φ).toMonoidHom ψ ∈ innerAut (C0 σ) := hle ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg⟩ := hmem
    refine ⟨φ⁻¹ g, ?_⟩
    have h1 : φ * ψ * φ⁻¹ = MulAut.conj g := (congr_apply_eq φ ψ).symm.trans hg.symm
    have h2 : ψ = φ⁻¹ * MulAut.conj g * φ := by
      rw [← h1]; group
    rw [h2, show φ⁻¹ * MulAut.conj g * φ = MulAut.conj (φ⁻¹ g) by
      have := aut_conj_conj φ⁻¹ g
      rwa [inv_inv] at this]

theorem triOdd_closure_fixUnion_eq_top_of_central_gline {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) (β : MulAut (C0 σ))
    (hβ : TriOddIsGLine σ β) (hcomm : ∀ α ∈ E, α * β = β * α) (hβE : β ∉ E) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  obtain ⟨φ, hφ⟩ := hβ
  obtain ⟨hE', hcard', hout'⟩ := triOdd_map_congr_plane σ φ E hE hcard hout
  rw [← triOdd_closure_fixUnion_conj_iff σ φ E]
  have hcommE' : ∀ α' ∈ E.map (MulAut.congr φ).toMonoidHom,
      α' * tauAut σ = tauAut σ * α' := by
    rintro _ ⟨α, hα, rfl⟩
    have h1 : (φ * α * φ⁻¹) * (φ * β * φ⁻¹) = (φ * β * φ⁻¹) * (φ * α * φ⁻¹) := by
      calc (φ * α * φ⁻¹) * (φ * β * φ⁻¹) = φ * (α * β) * φ⁻¹ := by group
        _ = φ * (β * α) * φ⁻¹ := by rw [hcomm α hα]
        _ = (φ * β * φ⁻¹) * (φ * α * φ⁻¹) := by group
    show (MulAut.congr φ) α * tauAut σ = tauAut σ * (MulAut.congr φ) α
    rw [congr_apply_eq]
    rcases hφ with h | h
    · rw [h] at h1
      exact h1
    · rw [h] at h1
      have h3 : Commute (φ * α * φ⁻¹) (tauAut σ)⁻¹ := h1
      simpa using (Commute.inv_right h3).eq
  have hτE' : tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom := by
    intro hτ
    apply hβE
    have hiff : (MulAut.congr φ).toMonoidHom β ∈ E.map (MulAut.congr φ).toMonoidHom ↔ β ∈ E :=
      Subgroup.mem_map_iff_mem (MulAut.congr φ).injective
    rw [← hiff]
    show (MulAut.congr φ) β ∈ _
    rw [congr_apply_eq]
    rcases hφ with h | h
    · rw [h]
      exact hτ
    · rw [h]
      exact Subgroup.inv_mem _ hτ
  exact triOdd_closure_fixUnion_eq_top_of_central_tau σ hℓ hℓ2 hℓ3 hf hX hσ _ hE' hcard' hout'
    hcommE' hτE'

end Model

section Statements


@[expose] def TriOddXNoGCent : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (E : Subgroup (MulAut (C0 σ))) (x : C0 σ), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (C0 σ) → ¬ TriOddHasGLine σ E →
      (∀ β : MulAut (C0 σ), TriOddIsGLine σ β → ¬ ∀ α ∈ E, α * β = β * α) →
      x ^ 3 = 1 → x ≠ 1 → MulAut.conj x ∈ E → TriOddIsClassX σ x →
      Subgroup.closure (fixUnion E) = ⊤

theorem triOddXNoG_of_cent (h : TriOddXNoGCent) : TriOddXNoG := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ E x hE hcard hout hng hx3 hx1 hcx hX
  by_cases hc : ∃ β : MulAut (C0 σ), TriOddIsGLine σ β ∧ ∀ α ∈ E, α * β = β * α
  · obtain ⟨β, hβ, hβc⟩ := hc
    exact triOdd_closure_fixUnion_eq_top_of_central_gline σ hℓ hℓ2 hℓ3 hf hK hσ E hE hcard hout β
      hβ hβc (fun hβE => hng ⟨β, hβE, hβ⟩)
  · exact h ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ E x hE hcard hout hng
      (fun β hβ hall => hc ⟨β, hβ, hall⟩) hx3 hx1 hcx hX

theorem trialityThreePlanesOdd_of_cent (h : TriOddXNoGCent) : TrialityThreePlanesOdd :=
  trialityThreePlanesOdd_of_X (triOddXNoG_of_cent h)

end Statements

end CFSG.LieType.SeitzGeneration.ExcWideThree
