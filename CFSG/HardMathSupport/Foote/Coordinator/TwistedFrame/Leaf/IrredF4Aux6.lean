module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux0
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux1
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Lemma3

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


@[expose] def OnDeg1 {R : Type} [Zero R] (u : (Fin Tag.F4.rank → ℤ) → R) : Prop :=
  ∀ β, β ∉ Deg1 Tag.F4 → u β = 0

@[expose] def emb {K L : Type} [Field K] [Field L] [Algebra K L]
    (v : (Fin Tag.F4.rank → ℤ) → K) : (Fin Tag.F4.rank → ℤ) → L :=
  fun β => algebraMap K L (v β)

theorem actFun_smul {L : Type} [Field L]
    (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) (γ : Fin Tag.F4.rank → ℤ)
    (t s : L) (c : (Fin Tag.F4.rank → ℤ) → L) :
    actFun a1 a2 γ t (s • c) = s • actFun a1 a2 γ t c := by
  funext ν
  simp only [actFun, Pi.smul_apply, smul_eq_mul]
  ring

theorem actFun_zero_param {L : Type} [Field L]
    (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) (γ : Fin Tag.F4.rank → ℤ)
    (c : (Fin Tag.F4.rank → ℤ) → L) : actFun a1 a2 γ 0 c = c := by
  funext ν
  simp [actFun]

theorem actFun_param_add {L : Type} [Field L]
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}
    (hact : ∀ γ ∈ rootFinset Tag.F4, γ 0 = 0 → ∀ t : L, ∀ q ∈ Qθ Tag.F4 L,
      heisCoord Tag.F4 L (pinnedX Tag.F4 L γ t * q * (pinnedX Tag.F4 L γ t)⁻¹) =
        actFun a1 a2 γ t (heisCoord Tag.F4 L q))
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList) (s t : L)
    {u : (Fin Tag.F4.rank → ℤ) → L} (hu : OnDeg1 u) :
    actFun a1 a2 γ s (actFun a1 a2 γ t u) = actFun a1 a2 γ (s + t) u := by
  obtain ⟨q, hq, rfl⟩ := (heisCoord_spec Tag.F4 L).surj u hu
  obtain ⟨hγr, hγ0⟩ := f4ShortList_deg0 γ hγ
  have hq1 : pinnedX Tag.F4 L γ t * q * (pinnedX Tag.F4 L γ t)⁻¹ ∈ Qθ Tag.F4 L :=
    Lθ_conj_mem_Qθ (pinnedX_mem_Lθ_S2 L hγ t) hq
  have h1 := hact γ hγr hγ0 t q hq
  have h2 := hact γ hγr hγ0 s _ hq1
  have h3 := hact γ hγr hγ0 (s + t) q hq
  have e : pinnedX Tag.F4 L γ s * (pinnedX Tag.F4 L γ t * q * (pinnedX Tag.F4 L γ t)⁻¹) *
      (pinnedX Tag.F4 L γ s)⁻¹ = pinnedX Tag.F4 L γ (s + t) * q * (pinnedX Tag.F4 L γ (s + t))⁻¹ := by
    rw [pinnedX_add]
    group
  rw [← h1, ← h2, e, h3]

theorem Phi_inj {L : Type} [Field L] {g : ModGL Tag.F4 L} (hg : g ∈ Lθ Tag.F4 L)
    {Φ : ((Fin Tag.F4.rank → ℤ) → L) →ₗ[L] ((Fin Tag.F4.rank → ℤ) → L)}
    (hΦ : ∀ q ∈ Qθ Tag.F4 L, g⁻¹ * q * g ∈ Qθ Tag.F4 L ∧
      heisCoord Tag.F4 L (g⁻¹ * q * g) = Φ (heisCoord Tag.F4 L q))
    {u : (Fin Tag.F4.rank → ℤ) → L} (hu : OnDeg1 u) (h0 : Φ u = 0) : u = 0 := by
  obtain ⟨q, hq, rfl⟩ := (heisCoord_spec Tag.F4 L).surj u hu
  obtain ⟨hq', hc⟩ := hΦ q hq
  rw [← hc] at h0
  have h1 : g⁻¹ * q * g ∈ Uθ Tag.F4 L := ((heisCoord_spec Tag.F4 L).eq_zero_iff _ hq').1 h0
  have h2 : g * (g⁻¹ * q * g) * g⁻¹ ∈ Uθ Tag.F4 L := Lθ_conj_mem_Uθ hg h1
  have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
  rw [e] at h2
  exact ((heisCoord_spec Tag.F4 L).eq_zero_iff q hq).2 h2

theorem conj_assoc3 {G : Type*} [Group G] (a b c q : G) :
    a * (b * (c * q * c⁻¹) * b⁻¹) * a⁻¹ = a * b * c * q * (a * b * c)⁻¹ := by group

theorem stab_span {L : Type} [Field L]
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}
    (hact : ∀ γ ∈ rootFinset Tag.F4, γ 0 = 0 → ∀ t : L, ∀ q ∈ Qθ Tag.F4 L,
      heisCoord Tag.F4 L (pinnedX Tag.F4 L γ t * q * (pinnedX Tag.F4 L γ t)⁻¹) =
        actFun a1 a2 γ t (heisCoord Tag.F4 L q))
    (G : Set ((Fin Tag.F4.rank → ℤ) → L)) {γ₁ γ₂ γ₃ : Fin Tag.F4.rank → ℤ}
    (h₁ : γ₁ ∈ f4ShortList) (h₂ : γ₂ ∈ f4ShortList) (h₃ : γ₃ ∈ f4ShortList) (t₁ t₂ t₃ : L)
    (hG : ∀ v ∈ G, ∃ q ∈ Qθ Tag.F4 L, heisCoord Tag.F4 L q = v ∧
      heisCoord Tag.F4 L (pinnedX Tag.F4 L γ₁ t₁ * pinnedX Tag.F4 L γ₂ t₂ * pinnedX Tag.F4 L γ₃ t₃ * q *
        (pinnedX Tag.F4 L γ₁ t₁ * pinnedX Tag.F4 L γ₂ t₂ * pinnedX Tag.F4 L γ₃ t₃)⁻¹) ∈ G) :
    ∀ v ∈ Submodule.span L G,
      actFun a1 a2 γ₁ t₁ (actFun a1 a2 γ₂ t₂ (actFun a1 a2 γ₃ t₃ v)) ∈ Submodule.span L G := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q, hq, rfl, hqG⟩ := hG v hv
    obtain ⟨r₁, r₁0⟩ := f4ShortList_deg0 γ₁ h₁
    obtain ⟨r₂, r₂0⟩ := f4ShortList_deg0 γ₂ h₂
    obtain ⟨r₃, r₃0⟩ := f4ShortList_deg0 γ₃ h₃
    have hq₃ : pinnedX Tag.F4 L γ₃ t₃ * q * (pinnedX Tag.F4 L γ₃ t₃)⁻¹ ∈ Qθ Tag.F4 L :=
      Lθ_conj_mem_Qθ (pinnedX_mem_Lθ_S2 L h₃ t₃) hq
    have hq₂ : pinnedX Tag.F4 L γ₂ t₂ * (pinnedX Tag.F4 L γ₃ t₃ * q * (pinnedX Tag.F4 L γ₃ t₃)⁻¹) *
        (pinnedX Tag.F4 L γ₂ t₂)⁻¹ ∈ Qθ Tag.F4 L :=
      Lθ_conj_mem_Qθ (pinnedX_mem_Lθ_S2 L h₂ t₂) hq₃
    have e3 := hact γ₃ r₃ r₃0 t₃ q hq
    have e2 := hact γ₂ r₂ r₂0 t₂ (pinnedX Tag.F4 L γ₃ t₃ * q * (pinnedX Tag.F4 L γ₃ t₃)⁻¹) hq₃
    have e1 := hact γ₁ r₁ r₁0 t₁ (pinnedX Tag.F4 L γ₂ t₂ * (pinnedX Tag.F4 L γ₃ t₃ * q *
      (pinnedX Tag.F4 L γ₃ t₃)⁻¹) * (pinnedX Tag.F4 L γ₂ t₂)⁻¹) hq₂
    have key : actFun a1 a2 γ₁ t₁ (actFun a1 a2 γ₂ t₂ (actFun a1 a2 γ₃ t₃ (heisCoord Tag.F4 L q))) =
        heisCoord Tag.F4 L (pinnedX Tag.F4 L γ₁ t₁ * pinnedX Tag.F4 L γ₂ t₂ *
          pinnedX Tag.F4 L γ₃ t₃ * q *
          (pinnedX Tag.F4 L γ₁ t₁ * pinnedX Tag.F4 L γ₂ t₂ * pinnedX Tag.F4 L γ₃ t₃)⁻¹) := by
      rw [← e3, ← e2, ← e1, conj_assoc3]
    rw [key]
    exact Submodule.subset_span hqG
  | zero =>
    rw [ActionAux.actFun_zero, ActionAux.actFun_zero, ActionAux.actFun_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [ActionAux.actFun_add, ActionAux.actFun_add, ActionAux.actFun_add]
    exact add_mem hx hy
  | smul s x _ hx =>
    rw [actFun_smul, actFun_smul, actFun_smul]
    exact Submodule.smul_mem _ s hx

open Classical in
@[expose] def Sfun {L : Type} [Field L] (Fr : L →+* L) (ε : (Fin Tag.F4.rank → ℤ) → L)
    (v : (Fin Tag.F4.rank → ℤ) → L) : (Fin Tag.F4.rank → ℤ) → L :=
  fun μ => if μ ∈ Deg1 Tag.F4 then ε (wF • μ) * Fr (v (wF • μ)) else 0

theorem Sfun_add {L : Type} [Field L] (Fr : L →+* L) (ε : (Fin Tag.F4.rank → ℤ) → L)
    (u v : (Fin Tag.F4.rank → ℤ) → L) : Sfun Fr ε (u + v) = Sfun Fr ε u + Sfun Fr ε v := by
  classical
  funext μ
  simp only [Sfun, Pi.add_apply]
  split_ifs
  · simp [mul_add]
  · simp

theorem Sfun_smul {L : Type} [Field L] (Fr : L →+* L) (ε : (Fin Tag.F4.rank → ℤ) → L)
    (c : L) (v : (Fin Tag.F4.rank → ℤ) → L) : Sfun Fr ε (c • v) = Fr c • Sfun Fr ε v := by
  classical
  funext μ
  simp only [Sfun, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · simp only [map_mul]
    ring
  · simp

theorem stab_span_semilinear {L : Type} [Field L] (Fr : L →+* L)
    (S : ((Fin Tag.F4.rank → ℤ) → L) → ((Fin Tag.F4.rank → ℤ) → L))
    (hadd : ∀ u v, S (u + v) = S u + S v) (hsmul : ∀ (c : L) u, S (c • u) = Fr c • S u)
    (G : Set ((Fin Tag.F4.rank → ℤ) → L)) (hG : ∀ v ∈ G, S v ∈ Submodule.span L G) :
    ∀ v ∈ Submodule.span L G, S v ∈ Submodule.span L G := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => exact hG v hv
  | zero =>
    have h := hsmul 0 0
    rw [zero_smul, map_zero, zero_smul] at h
    rw [h]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [hadd]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [hsmul]
    exact Submodule.smul_mem _ _ hx

theorem VM_onDeg1 {K : Type} [Field K] (X : Subgroup (ModGL Tag.F4 K)) :
    ∀ v ∈ VM X, OnDeg1 v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q, hq, rfl⟩ := hv
    exact fun β hβ => (heisCoord_spec Tag.F4 K).support q hq.1 β hβ
  | zero => exact fun β _ => rfl
  | add x y _ _ hx hy => exact fun β hβ => by simp [hx β hβ, hy β hβ]
  | smul c x _ hx => exact fun β hβ => by simp [hx β hβ]

theorem wF_mem_Deg1 {μ : Fin Tag.F4.rank → ℤ} (h : μ ∈ Deg1 Tag.F4) : wF • μ ∈ Deg1 Tag.F4 := by
  obtain ⟨hr, hd⟩ := h
  refine ⟨IsRoot.smul hr wF, ?_⟩
  have h1 : (wF • μ) 0 = μ 0 := wF_deg μ (mem_rootFinset.2 hr)
  exact h1.trans hd

theorem Sfun_single {L : Type} [Field L] (Fr : L →+* L) (ε : (Fin Tag.F4.rank → ℤ) → L)
    {ν : Fin Tag.F4.rank → ℤ} (hν : ν ∈ Deg1 Tag.F4) (c : L) :
    Sfun Fr ε (Pi.single ν c) = Pi.single (wF • ν) (ε ν * Fr c) := by
  classical
  funext μ
  simp only [Sfun]
  by_cases hμ : μ ∈ Deg1 Tag.F4
  · rw [if_pos hμ]
    by_cases h : μ = wF • ν
    · subst h
      rw [wF_invol, Pi.single_eq_same, Pi.single_eq_same]
    · have h' : wF • μ ≠ ν := fun e => h (by rw [← e, wF_invol])
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
      simp
  · rw [if_neg hμ]
    have h : μ ≠ wF • ν := fun e => hμ (e ▸ wF_mem_Deg1 hν)
    rw [Pi.single_eq_of_ne h]

open Classical in
theorem Sfun_fixed {L : Type} [Field L] (Fr : L →+* L) {ε : (Fin Tag.F4.rank → ℤ) → L}
    (hε : ∀ α, IsRoot Tag.F4 α → ε α * ε α = 1) {q : ModGL Tag.F4 L} (hq : q ∈ Qθ Tag.F4 L)
    (hn : ∀ α, heisCoord Tag.F4 L ((canonicalRep (coxeterSystem Tag.F4) L wF)⁻¹ * q *
        canonicalRep (coxeterSystem Tag.F4) L wF) α =
      if α ∈ Deg1 Tag.F4 then ε α * heisCoord Tag.F4 L q (wF • α) else 0)
    (hF : Units.map (entrywiseHom Fr) q = (canonicalRep (coxeterSystem Tag.F4) L wF)⁻¹ * q *
        canonicalRep (coxeterSystem Tag.F4) L wF) :
    Sfun Fr ε (heisCoord Tag.F4 L q) = heisCoord Tag.F4 L q := by
  classical
  funext μ
  simp only [Sfun]
  by_cases hμ : μ ∈ Deg1 Tag.F4
  · rw [if_pos hμ]
    have hα := wF_mem_Deg1 hμ
    have h1 : heisCoord Tag.F4 L (Units.map (entrywiseHom Fr) q) (wF • μ) =
        Fr (heisCoord Tag.F4 L q (wF • μ)) := congrFun (coord_frob Fr hq).2 (wF • μ)
    have h2 := hn (wF • μ)
    rw [← hF, h1, if_pos hα, wF_invol] at h2
    rw [h2, ← mul_assoc, hε (wF • μ) hα.1, one_mul]
  · rw [if_neg hμ]
    exact ((heisCoord_spec Tag.F4 L).support q hq μ hμ).symm

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
