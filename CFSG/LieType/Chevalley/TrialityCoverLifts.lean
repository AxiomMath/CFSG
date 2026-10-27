module

public import CFSG.LieType.Chevalley.TrialityCoverForms
public import CFSG.LieType.Chevalley.ExceptionalFieldFourCoverLifts

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Chevalley.TwistedE6Cover
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem map_conj_self_of_mem {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hg hy) (inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, mul_mem (mul_mem (inv_mem hg) hx) hg, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_orbitGroup
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α) :
    (orbitGroup σ α).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)).toMonoidHom =
      orbitGroup σ (w • α) := by
  rw [orbitGroup, orbitGroup, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport TwistTag.D4.tag K).1 w _
      fun β hβ => TwistTag.D4.isRoot_of_mem_diagramOrbit hα hβ,
    TwistTag.D4.diagramOrbit_smul hw, Finset.coe_image,
    map_conj_self_of_mem (canonicalRep_mem_twistedFixedGroup TwistTag.D4 K σ.toRingHom
      ((mem_relWeylTwist TwistTag.D4).1 hw))]

theorem trialityGroup_le_graphFixedRootGroup
    (j : Fin 6) :
    trialityGroup σ j ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  (rootSpan_trialityOrbit_le j).trans (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)

theorem orbitGroup_trialityRoot
    (j : Fin 6) :
    orbitGroup σ (trialityRoot j) = trialityGroup σ j :=
  rfl

variable
    [Finite K] [CharP K 2] {E : Type*} [Group E]
  {η : E →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom}

omit [Finite K] [CharP K 2] in
theorem coe_map_conj' (a b : E) :
    ((η (a * b * a⁻¹) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) =
      (η a : ModGL TwistTag.D4.tag K) * (η b : ModGL TwistTag.D4.tag K) *
        (η a : ModGL TwistTag.D4.tag K)⁻¹ := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

variable (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
include hη hC

omit [Finite K] [CharP K 2] hC in
theorem lift_commute_of_map_conj
    {A B : Subgroup (ModGL TwistTag.D4.tag K)}
    {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hAB : A.map (MulAut.conj g).toMonoidHom = B)
    (hA : ∀ y y' : E, (η y : ModGL TwistTag.D4.tag K) ∈ A → (η y' : ModGL TwistTag.D4.tag K) ∈ A →
      y * y' = y' * y)
    (y y' : E) (hy : (η y : ModGL TwistTag.D4.tag K) ∈ B)
    (hy' : (η y' : ModGL TwistTag.D4.tag K) ∈ B) : y * y' = y' * y := by
  obtain ⟨m, hm⟩ := hη ⟨g, hg⟩
  have hmM : (η m : ModGL TwistTag.D4.tag K) = g := by rw [hm]
  have hconj : ∀ z : E, (η z : ModGL TwistTag.D4.tag K) ∈ B →
      (η (m⁻¹ * z * m⁻¹⁻¹) : ModGL TwistTag.D4.tag K) ∈ A := fun z hz => by
    rw [← hAB] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    rw [coe_map_conj', map_inv, Subgroup.coe_inv, hmM, ← hxz]
    simpa [MulAut.conj_apply, mul_assoc] using hx
  have h := hA _ _ (hconj y hy) (hconj y' hy')
  have h' := congrArg (fun z => m * z * m⁻¹) h
  simp only [inv_inv, mul_assoc, mul_inv_cancel_left] at h'
  simpa [mul_assoc] using h'

theorem lift_commute_zero
    (hσ : σ ^ 3 = 1) {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n)
    (y y' : E) (hy : (η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 0)
    (hy' : (η y' : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 0) : y * y' = y' * y := by
  let Γ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set P : K → ModGL TwistTag.D4.tag K := fun c =>
    (trialityOrbitProd K σ.toRingHom (trialityRoot 0) c : ModGL TwistTag.D4.tag K)
  have hPmem : ∀ c, P c ∈ trialityGroup σ 0 := fun c =>
    trialityOrbitProd_mem (Or.inl rfl) (toRingHom_pow_three σ hσ) c
  have hPadd : ∀ c c', P (c + c') = P c * P c' := fun c c' => by
    simp only [P, trialityOrbitProd_add' (Or.inl rfl), Subgroup.coe_mul]
  have hPΓ : ∀ c, P c ∈ Γ := fun c => trialityGroup_le_graphFixedRootGroup σ 0 (hPmem c)
  let PC : K → Γ := fun c => ⟨P c, hPΓ c⟩
  have hPC : ∀ g : Γ, g ∈ (trialityGroup σ 0).subgroupOf Γ ↔ ∃ c, g = PC c := fun g => by
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := exists_trialityOrbitProd_eq' (Or.inl rfl) hg
      exact ⟨c, Subtype.ext hc.symm⟩
    · rintro ⟨c, rfl⟩
      exact hPmem c
  have hPCadd : ∀ c c', PC (c + c') = PC c * PC c' := fun c c' => Subtype.ext (hPadd c c')
  let τΓ : Kˣ × (trialityFixedField K σ.toRingHom)ˣ → Γ := fun p =>
    ⟨trialityTorus σ p, trialityTorus_mem_graphFixedRootGroup σ hσ p⟩
  have hτ : ∀ p c, τΓ p * PC c * (τΓ p)⁻¹ =
      PC ((rootChar K (trialityRoot 0) (torusParam σ p) : K) * c) := fun p c =>
    Subtype.ext (trialityTorus_conj_orbitProd σ hσ (isRoot_trialityRoot 0) p c)
  refine lift_commute_of_form_eq_zero η hη hC τΓ ((trialityGroup σ 0).subgroupOf Γ)
    ((trialityGroup σ 0).subgroupOf Γ) (fun g hg g' hg' => ?_) (fun g hg => ?_)
    (fun b hb₁ hb₂ hbT g hg g' hg' => ?_) y y' (Subgroup.mem_subgroupOf.2 hy)
    (Subgroup.mem_subgroupOf.2 hy')
  · obtain ⟨c, rfl⟩ := (hPC g).1 hg
    obtain ⟨d, rfl⟩ := (hPC g').1 hg'
    rw [← hPCadd, ← hPCadd, add_comm]
  · obtain ⟨c, rfl⟩ := (hPC g).1 hg
    have hP0 : P 0 = 1 := by
      have h0 := hPadd 0 0
      rw [add_zero] at h0
      exact left_eq_mul.1 h0
    rw [sq, ← hPCadd, CharTwo.add_self_eq_zero]
    exact Subtype.ext hP0
  · obtain ⟨c, rfl⟩ := (hPC g).1 hg
    obtain ⟨d, rfl⟩ := (hPC g').1 hg'
    have hF := form_eq_zero_of_chars (k := K) (by omega) hK
      (fun p => rootChar K (trialityRoot 0) (torusParam σ p))
      (fun p => rootChar K (trialityRoot 0) (torusParam σ p))
      (exists_weight_zero_pow_ne_one σ hn hK) (fun c d => b (PC c) (PC d))
      (fun c₁ c₂ d => by
        rw [hPCadd]
        exact hb₁ _ ((hPC _).2 ⟨c₁, rfl⟩) _ ((hPC _).2 ⟨c₂, rfl⟩) _ ((hPC _).2 ⟨d, rfl⟩))
      (fun c d₁ d₂ => by
        rw [hPCadd]
        exact hb₂ _ ((hPC _).2 ⟨c, rfl⟩) _ ((hPC _).2 ⟨d₁, rfl⟩) _ ((hPC _).2 ⟨d₂, rfl⟩))
      (fun t c d => by
        rw [← hτ t c, ← hτ t d]
        exact hbT t _ ((hPC _).2 ⟨c, rfl⟩) _ ((hPC _).2 ⟨d, rfl⟩))
    exact hF c d

omit [Finite K] hη hC in
theorem paramX_sq
    (j : Fin 6) (c : paramField σ j) : paramX σ j c ^ 2 = 1 := by
  have h0 : paramX σ j 0 = 1 := by
    have h := paramX_add σ j 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  rw [sq, ← paramX_add, CharTwo.add_self_eq_zero, h0]

theorem lift_commute_of_separated
    (hσ : σ ^ 3 = 1) {i j : Fin 6} (hsep : Separated σ i j)
    (hcomm : ∀ c d, Commute (paramX σ i c) (paramX σ j d)) (y y' : E)
    (hy : (η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ i)
    (hy' : (η y' : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ j) : y * y' = y' * y := by
  let Γ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hPΓ : ∀ (l : Fin 6) (c : paramField σ l), paramX σ l c ∈ Γ := fun l c =>
    trialityGroup_le_graphFixedRootGroup σ l (paramX_mem σ hσ l c)
  let PC : (l : Fin 6) → paramField σ l → Γ := fun l c => ⟨paramX σ l c, hPΓ l c⟩
  have hPC : ∀ (l : Fin 6) (g : Γ), g ∈ (trialityGroup σ l).subgroupOf Γ ↔ ∃ c, g = PC l c :=
    fun l g => by
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hg
        obtain ⟨c, hc⟩ := exists_paramX_eq σ l hg
        exact ⟨c, Subtype.ext hc.symm⟩
      · rintro ⟨c, rfl⟩
        exact paramX_mem σ hσ l c
  have hPCadd : ∀ (l : Fin 6) (c c' : paramField σ l), PC l (c + c') = PC l c * PC l c' :=
    fun l c c' => Subtype.ext (paramX_add σ l c c')
  let τΓ : Kˣ × (trialityFixedField K σ.toRingHom)ˣ → Γ := fun p =>
    ⟨trialityTorus σ p, trialityTorus_mem_graphFixedRootGroup σ hσ p⟩
  have hτ : ∀ (l : Fin 6) p (c : paramField σ l),
      τΓ p * PC l c * (τΓ p)⁻¹ = PC l (paramWeight σ hσ l p * c) := fun l p c =>
    Subtype.ext (trialityTorus_conj_paramX σ hσ l p c)
  obtain ⟨p, hp⟩ := hsep
  refine lift_commute_of_form_eq_zero η hη hC τΓ ((trialityGroup σ i).subgroupOf Γ)
    ((trialityGroup σ j).subgroupOf Γ) (fun g hg g' hg' => ?_) (fun g hg => ?_)
    (fun b hb₁ hb₂ hbT g hg g' hg' => ?_) y y' (Subgroup.mem_subgroupOf.2 hy)
    (Subgroup.mem_subgroupOf.2 hy')
  · obtain ⟨c, rfl⟩ := (hPC i g).1 hg
    obtain ⟨d, rfl⟩ := (hPC j g').1 hg'
    exact Subtype.ext (hcomm c d).eq
  · obtain ⟨c, rfl⟩ := (hPC i g).1 hg
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact paramX_sq σ i c)
  · obtain ⟨c, rfl⟩ := (hPC i g).1 hg
    obtain ⟨d, rfl⟩ := (hPC j g').1 hg'
    exact form_param_eq_zero τΓ (PC i) (PC j) (hPCadd i) (hPCadd j) (paramWeight σ hσ i)
      (paramWeight σ hσ j) (hτ i) (hτ j) p
      (by simpa only [paramWeight_eq_one_iff, ne_eq] using hp) b
      (fun s₁ s₂ s' => hb₁ _ ((hPC i _).2 ⟨s₁, rfl⟩) _ ((hPC i _).2 ⟨s₂, rfl⟩) _
        ((hPC j _).2 ⟨s', rfl⟩))
      (fun s s₁' s₂' => hb₂ _ ((hPC i _).2 ⟨s, rfl⟩) _ ((hPC j _).2 ⟨s₁', rfl⟩) _
        ((hPC j _).2 ⟨s₂', rfl⟩))
      (fun s s' => hbT p _ ((hPC i _).2 ⟨s, rfl⟩) _ ((hPC j _).2 ⟨s', rfl⟩)) c d

omit [Finite K] [CharP K 2] hη hC in
theorem paramX_of_long
    {j : Fin 6} (hj : ¬ (j = 0 ∨ j = 2 ∨ j = 3)) (c : paramField σ j) :
    paramX σ j c = pinnedX TwistTag.D4.tag K (trialityRoot j) c := by
  unfold paramX
  rw [ite_eq_right hj]

omit [Finite K] [CharP K 2] hη hC in
theorem mem_fixed_of_paramField {j : Fin 6} (hj : ¬ (j = 0 ∨ j = 2 ∨ j = 3))
    (c : paramField σ j) : (c : K) ∈ trialityFixedField K σ.toRingHom :=
  (SetLike.ext_iff.1 (ite_eq_right hj : paramField σ j = trialityFixedField K σ.toRingHom)
    (c : K)).1 c.2

omit [Finite K] hη hC in
theorem commute_paramX_four_five
    (hσ : σ ^ 3 = 1) (c : paramField σ 4) (d : paramField σ 5) :
    Commute (paramX σ 4 c) (paramX σ 5 d) := by
  rw [paramX_of_long σ (by decide), paramX_of_long σ (by decide)]
  have h := (even_triality_trace_commutators K σ.toRingHom
    (toRingHom_pow_three σ hσ)).2.2.2.2.2.2.2.2.2.2.2.2.1
    ⟨c, mem_fixed_of_paramField σ (by decide) c⟩ ⟨d, mem_fixed_of_paramField σ (by decide) d⟩
  exact h.map (adjointGroup TwistTag.D4.tag K).subtype

theorem lift_commute_five_six
    (hσ : σ ^ 3 = 1) (hsep : Separated σ 4 5) (y y' : E)
    (hy : (η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 4)
    (hy' : (η y' : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 5) : y * y' = y' * y :=
  lift_commute_of_separated σ hη hC hσ hsep (commute_paramX_four_five σ hσ) y y' hy hy'

theorem lift_commute_six
    (hσ : σ ^ 3 = 1) (hsep : Separated σ 4 5) (z z' : E)
    (hz : (η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 5)
    (hz' : (η z' : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 5) : z * z' = z' * z := by
  have hσ' := toRingHom_pow_three σ hσ
  have hTC := even_triality_trace_commutators K σ.toRingHom hσ'
  obtain ⟨c, hc⟩ := exists_pinnedX_trialityRoot_eq (Or.inr (Or.inr rfl)) hz
  obtain ⟨c', hc'⟩ := exists_pinnedX_trialityRoot_eq (Or.inr (Or.inr rfl)) hz'
  have hcen : ∀ g ∈ η.ker, ∀ h : E, Commute g h := fun g hg h =>
    ((Subgroup.mem_center_iff.1 (hC hg)) h).symm
  have hker : ∀ g : E, ((η g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = 1 → g ∈ η.ker := fun g hg => (MonoidHom.mem_ker).2 (Subtype.ext hg)
  have hmem : ∀ (j : Fin 6), (j = 1 ∨ j = 4 ∨ j = 5) → ∀ e : trialityFixedField K σ.toRingHom,
      pinnedX TwistTag.D4.tag K (trialityRoot j) e ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun j hj e =>
    trialityGroup_le_graphFixedRootGroup σ j (pinnedX_trialityRoot_mem hj e)
  obtain ⟨x, hx⟩ := hη ⟨_, hmem 4 (Or.inr (Or.inl rfl)) c⟩
  obtain ⟨x', hx'⟩ := hη ⟨_, hmem 4 (Or.inr (Or.inl rfl)) c'⟩
  obtain ⟨n, hn⟩ := hη ⟨_, hmem 1 (Or.inl rfl) 1⟩
  have hxM : (η x : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K (trialityRoot 4) c := by
    rw [hx]
  have hx'M : (η x' : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 4) c' := by rw [hx']
  have hnM : (η n : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 1) ((1 : trialityFixedField K σ.toRingHom) : K) := by
    rw [hn]
  have hshear : ∀ e : trialityFixedField K σ.toRingHom,
      pinnedX TwistTag.D4.tag K (trialityRoot 1) ((1 : trialityFixedField K σ.toRingHom) : K) *
        pinnedX TwistTag.D4.tag K (trialityRoot 4) e *
        (pinnedX TwistTag.D4.tag K (trialityRoot 1)
          ((1 : trialityFixedField K σ.toRingHom) : K))⁻¹ *
        (pinnedX TwistTag.D4.tag K (trialityRoot 4) e)⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) e := fun e => by
    have h := congrArg Subtype.val (hTC.2.2.1 1 e)
    rw [coe_commutatorElement_adjoint, one_mul, commutatorElement_def] at h
    exact h
  set z₀ := n * x * n⁻¹ * x⁻¹ with hz₀
  set z₀' := n * x' * n⁻¹ * x'⁻¹ with hz₀'
  have hz₀M : (η z₀ : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K (trialityRoot 5) c := by
    rw [hz₀, map_mul, Subgroup.coe_mul, coe_map_conj', hnM, hxM, map_inv, Subgroup.coe_inv, hxM,
      hshear]
  have hz₀'M : (η z₀' : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) c' := by
    rw [hz₀', map_mul, Subgroup.coe_mul, coe_map_conj', hnM, hx'M, map_inv, Subgroup.coe_inv, hx'M,
      hshear]
  have hlift : ∀ a b : E, (η a : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 4 →
      (η b : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 5 → Commute a b := fun a b ha hb =>
    lift_commute_five_six σ hη hC hσ hsep a b ha hb
  have hm4 : ∀ e : trialityFixedField K σ.toRingHom,
      pinnedX TwistTag.D4.tag K (trialityRoot 4) e ∈ trialityGroup σ 4 := fun e =>
    pinnedX_trialityRoot_mem (Or.inr (Or.inl rfl)) e
  have hm5 : ∀ e : trialityFixedField K σ.toRingHom,
      pinnedX TwistTag.D4.tag K (trialityRoot 5) e ∈ trialityGroup σ 5 := fun e =>
    pinnedX_trialityRoot_mem (Or.inr (Or.inr rfl)) e
  have hcommX : pinnedX TwistTag.D4.tag K (trialityRoot 4) c *
      pinnedX TwistTag.D4.tag K (trialityRoot 4) c' =
      pinnedX TwistTag.D4.tag K (trialityRoot 4) c' *
        pinnedX TwistTag.D4.tag K (trialityRoot 4) c := by
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  have hc₀ : ⁅x, x'⁆ ∈ η.ker := hker _ (by
    simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hxM,
      hx'M]
    rw [hcommX]
    group)
  have key : ⁅x, x'⁆ = ⁅x, x'⁆ * ⁅z₀, z₀'⁆ := by
    have e1 : n * ⁅x, x'⁆ * n⁻¹ = ⁅x, x'⁆ := by
      rw [(hcen _ hc₀ n).eq.symm, mul_inv_cancel_right]
    have e2 : n * ⁅x, x'⁆ * n⁻¹ = ⁅z₀ * x, z₀' * x'⁆ := by
      rw [hz₀, hz₀']
      simp only [commutatorElement_def]
      group
    calc ⁅x, x'⁆ = n * ⁅x, x'⁆ * n⁻¹ := e1.symm
      _ = ⁅z₀ * x, z₀' * x'⁆ := e2
      _ = ⁅x, x'⁆ * ⁅z₀, z₀'⁆ := commutator_shear
          (hlift x z₀' (by rw [hxM]; exact hm4 c) (by rw [hz₀'M]; exact hm5 c'))
          (hlift x' z₀ (by rw [hx'M]; exact hm4 c') (by rw [hz₀M]; exact hm5 c)) (hcen _ hc₀)
  have hz₀z₀' : Commute z₀ z₀' := by
    have h1 : ⁅z₀, z₀'⁆ = 1 := by
      have := key
      rwa [left_eq_mul] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hu : z₀⁻¹ * z ∈ η.ker := hker _ (by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hz₀M, hc, inv_mul_cancel])
  have hu' : z₀'⁻¹ * z' ∈ η.ker := hker _ (by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hz₀'M, hc', inv_mul_cancel])
  have h := commute_mul_central hz₀z₀' (hcen _ hu) (hcen _ hu')
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h
  exact h.eq

omit [Finite K] [CharP K 2] hη hC in
theorem orbitReflection_smul_trialityRoot :
    TwistTag.D4.orbitReflection ⟨1, by decide⟩ •
      (TwistTag.D4.orbitReflection ⟨0, by decide⟩ • trialityRoot 1) = trialityRoot 5 := by
  rw [TwistTag.orbitReflection_smul, TwistTag.orbitReflection_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem lift_commute_two
    (hσ : σ ^ 3 = 1) (hsep : Separated σ 4 5) (y y' : E)
    (hy : (η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 1)
    (hy' : (η y' : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ 1) : y * y' = y' * y := by
  set w := TwistTag.D4.orbitReflection ⟨1, by decide⟩ * TwistTag.D4.orbitReflection ⟨0, by decide⟩
  have hw : w ∈ relWeylTwist TwistTag.D4 :=
    mul_mem (TwistTag.D4.orbitReflection_mem _) (TwistTag.D4.orbitReflection_mem _)
  have hwinv : w⁻¹ ∈ relWeylTwist TwistTag.D4 := inv_mem hw
  have hmap := map_conj_orbitGroup σ hwinv (isRoot_trialityRoot' 5)
  have hα : w⁻¹ • trialityRoot 5 = trialityRoot 1 := by
    rw [inv_smul_eq_iff, mul_smul, orbitReflection_smul_trialityRoot]
  rw [hα] at hmap
  exact lift_commute_of_map_conj σ hη (canonicalRep_mem_graphFixedRootGroup hwinv) hmap
    (fun z z' hz hz' => lift_commute_six σ hη hC hσ hsep z z' hz hz') y y' hy hy'

omit [Finite K] [CharP K 2] hη hC in
theorem single_orbitMin_zero :
    (Pi.single (TwistTag.D4.orbitMin ⟨0, by decide⟩) 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      trialityRoot 0 :=
  List.ofFn_injective (by decide +kernel)

omit [Finite K] [CharP K 2] hη hC in
theorem single_orbitMin_one :
    (Pi.single (TwistTag.D4.orbitMin ⟨1, by decide⟩) 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      trialityRoot 1 :=
  List.ofFn_injective (by decide +kernel)

theorem lift_commute_orbitGroup
    (hσ : σ ^ 3 = 1) {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hsep : Separated σ 4 5) {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α)
    (y y' : E) (hy : (η y : ModGL TwistTag.D4.tag K) ∈ orbitGroup σ α)
    (hy' : (η y' : ModGL TwistTag.D4.tag K) ∈ orbitGroup σ α) : y * y' = y' * y := by
  obtain ⟨w, hw, a, h⟩ := TwistTag.D4.exists_diagramOrbit_eq hα
  have hβ : TwistTag.D4.diagramOrbit (w • Pi.single (TwistTag.D4.orbitMin a) 1) =
      TwistTag.D4.diagramOrbit α := by
    rw [TwistTag.D4.diagramOrbit_smul_single hw, TwistTag.D4.orbitIndex_orbitMin, h]
  have hO : (orbitGroup σ (Pi.single (TwistTag.D4.orbitMin a) 1)).map
      (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)).toMonoidHom =
        orbitGroup σ α := by
    rw [map_conj_orbitGroup σ hw (isRoot_single _ _), orbitGroup, orbitGroup, hβ]
  refine lift_commute_of_map_conj σ hη (canonicalRep_mem_graphFixedRootGroup hw) hO ?_ y y' hy hy'
  fin_cases a
  · rw [show (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) = ⟨0, by decide⟩ from rfl,
      single_orbitMin_zero, orbitGroup_trialityRoot]
    exact lift_commute_zero σ hη hC hσ hn hK
  · rw [show (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) = ⟨1, by decide⟩ from rfl,
      single_orbitMin_one, orbitGroup_trialityRoot]
    exact lift_commute_two σ hη hC hσ hsep

end CFSG.LieType.Chevalley.TrialityCover
