module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthInner
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped commutatorElement

@[expose] def OrthRealized (lab : LargeEvenLabel) {G₀ : Type} [Group G₀] (J₀ : Subgroup G₀) : Prop :=
  CFSG.Assembly.LargeEvenRawDatum lab fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
    ∃ Θ₁ : ↥J₀ →* R, Function.Surjective Θ₁ ∧ Θ₁.ker ≤ Subgroup.center ↥J₀ ∧
      ∀ φ ∈ I, ∃ L : G₀, ∃ hL : ∀ ω ∈ J₀, L * ω * L⁻¹ ∈ J₀,
        ∀ ω : ↥J₀, φ (Θ₁ ω) = Θ₁ ⟨L * ω * L⁻¹, hL ω ω.2⟩

@[expose] def OrthBlockMark (p : ℕ) {G₀ : Type} [Group G₀] (J₀ : Subgroup G₀) : Prop :=
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.tag ≠ .triD4 ∧
    ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) ∧ OrthRealized lab J₀

@[expose] def OrthBlockMarkW {G₀ : Type} [Group G₀] (J₀ : Subgroup G₀) : Prop :=
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.tag ≠ .triD4 ∧ OrthRealized lab J₀

theorem orthBlockMarkW_of_orthBlockMark {p : ℕ} {G₀ : Type} [Group G₀] {J₀ : Subgroup G₀}
    (h : OrthBlockMark p J₀) : OrthBlockMarkW J₀ := by
  obtain ⟨lab, hlab, htri, -, hraw⟩ := h
  exact ⟨lab, hlab, htri, hraw⟩

theorem orth_commutator_eq_top_of_surjective {A B : Type*} [Group A] [Group B]
    (hA : commutator A = ⊤) (f : A →* B) (hf : Function.Surjective f) : commutator B = ⊤ := by
  have h := Subgroup.map_commutator (⊤ : Subgroup A) ⊤ f
  rw [Subgroup.map_top_of_surjective f hf] at h
  rw [commutator_def, ← h, ← commutator_def, hA, Subgroup.map_top_of_surjective f hf]

theorem orth_commutator_eq_top_of_glaPComponent {G : Type} [Group G] {p : ℕ} {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : commutator ↥J = ⊤ := by
  have h1 := Subgroup.map_subtype_commutator J
  rw [CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ] at h1
  have h2 : (⊤ : Subgroup ↥J).map J.subtype = J := by rw [Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective J.subtype_injective (h1.trans h2.symm)

section Certs

theorem orth_marking_notInner {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup Ω} (hJ : GLAPComponent p X J) {y : Ω}
    (hy : y ∈ Subgroup.normalizer (J : Set Ω)) {G₀ : Type} [Group G₀]
    {J₀ : Subgroup G₀} (ρ : ↥J →* ↥J₀) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥J) (Γ : ↥J₀ →* ↥J₀)
    (hΓ : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J), ρ ⟨_, hl⟩ = Γ (ρ l))
    (hno : ∀ L : G₀, ¬ ∀ ω : ↥J₀, ((Γ ω : ↥J₀) : G₀) = L * ω * L⁻¹)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hraw : OrthRealized lab J₀) :
    CFSG.Assembly.LargeEvenMarking (PQuot p J) fun lab' R _ I _ θ =>
      lab' = lab ∧ MulAut.congr θ (MI.indAut p J y hy) ∉ I := by
  have hperfJ : commutator ↥J = ⊤ := orth_commutator_eq_top_of_glaPComponent hJ
  have hperf0 : commutator ↥J₀ = ⊤ := orth_commutator_eq_top_of_surjective hperfJ ρ hρs
  have hperfQ : commutator (PQuot p J) = ⊤ :=
    (isQuasisimple_pQuot_of_glaPComponent hp hJ).1
  refine ⟨hperfQ, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, Θ₁, hΘs, hΘk, hreal⟩
  set Θ : ↥J →* R := Θ₁.comp ρ with hΘdef
  have hΘsurj : Function.Surjective Θ := hΘs.comp hρs
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    have h1 : ρ l ∈ Subgroup.center ↥J₀ := hΘk hl
    refine Y10GInnLin.mem_center_of_commutator_mem_center hperfJ fun j => hρk ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 h1 (ρ j)).symm
  obtain ⟨e, he⟩ := l154_exists_pSimple_equiv hp hJ hs Θ hΘsurj hΘker
  refine ⟨hs, hna, e, rfl, fun hφ => ?_⟩
  obtain ⟨L, hL, hLeq⟩ := hreal _ hφ
  apply hno L
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hy
  have hmemJ : ∀ l : ↥J, y⁻¹ * (l : Ω) * y ∈ J := fun l => by
    have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
    simpa using this
  have hdisp : ∀ ω : ↥J₀, Γ ω * (⟨L * ω * L⁻¹, hL ω ω.2⟩ : ↥J₀)⁻¹ ∈ Subgroup.center ↥J₀ := by
    intro ω
    obtain ⟨l, rfl⟩ := hρs ω
    apply hΘk
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hLeq, mul_inv_eq_one, ← hΓ l (hmemJ l)]
    have e1 : Θ₁ (ρ ⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩) = e (QuotientGroup.mk (QuotientGroup.mk
        (⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩ : ↥J))) := (he _).symm
    have e2 : Θ₁ (ρ l) = e (QuotientGroup.mk (QuotientGroup.mk l)) := (he l).symm
    have e3 : MI.indAut p J y hy (QuotientGroup.mk (QuotientGroup.mk l)) =
        QuotientGroup.mk (QuotientGroup.mk (⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩ : ↥J)) :=
      MI.indAut_apply_mk hy ⟨l, ⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩, rfl, rfl, rfl⟩
    rw [e1, e2, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, e3]
  intro ω
  have key := K155X.hom_of_displacement hperf0 (J₀.subtype.comp Γ)
    ((MulAut.conj L).toMonoidHom.comp J₀.subtype)
    (fun v => v ∈ (Subgroup.center ↥J₀).map J₀.subtype)
    (by
      rintro v v' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hb a))
    (by
      rintro v ⟨a, ha, rfl⟩ g
      have h1 := Subgroup.mem_center_iff.1 ha ⟨L * g * L⁻¹, hL g g.2⟩
      exact (congrArg Subtype.val h1).symm)
    (fun g => ⟨_, hdisp g, rfl⟩) ω
  simpa [MulAut.conj_apply] using key

theorem fieldOn_of_blockMark {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X J : Subgroup Ω} (hJ : GLAPComponent p X J) {y : Ω}
    (hy : y ∈ Subgroup.normalizer (J : Set Ω)) (hyp : y ^ p = 1) {G₀ : Type} [Group G₀]
    {J₀ : Subgroup G₀} (ρ : ↥J →* ↥J₀) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥J) (Γ : ↥J₀ →* ↥J₀)
    (hΓ : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J), ρ ⟨_, hl⟩ = Γ (ρ l))
    (hno : ∀ L : G₀, ¬ ∀ ω : ↥J₀, ((Γ ω : ↥J₀) : G₀) = L * ω * L⁻¹)
    (hM : OrthBlockMark p J₀) : FieldOn p y J := by
  obtain ⟨lab, hlab, htri, hD4, hraw⟩ := hM
  refine fieldOn_of_notInner hp hp2 hy hyp (Canonical.largeEvenMarking_mono ?_
    (orth_marking_notInner hp hJ hy ρ hρs hρk Γ hΓ hno hlab hraw))
  rintro lab' R _ I F θ ⟨rfl, hnot⟩
  exact ⟨Or.inl htri, hD4, hnot⟩

end Certs

section CertsTD4

theorem nidTd4_of_blockMarkW {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup Ω} (hJ : GLAPComponent p X J) {y : Ω}
    (hy : y ∈ Subgroup.normalizer (J : Set Ω)) {G₀ : Type} [Group G₀]
    {J₀ : Subgroup G₀} (ρ : ↥J →* ↥J₀) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥J) (Γ : ↥J₀ →* ↥J₀)
    (hΓ : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J), ρ ⟨_, hl⟩ = Γ (ρ l))
    (hno : ∀ L : G₀, ¬ ∀ ω : ↥J₀, ((Γ ω : ↥J₀) : G₀) = L * ω * L⁻¹)
    (hM : OrthBlockMarkW J₀) : NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J) := by
  obtain ⟨lab, hlab, htri, hraw⟩ := hM
  have hmark := orth_marking_notInner hp hJ hy ρ hρs hρk Γ hΓ hno hlab hraw
  refine ⟨⟨hy, fun hD => ?_⟩, ?_⟩
  · have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p J)
        fun _ _ _ I _ θ => ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ (indRel p J y) φ :=
      Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh y (Subgroup.mem_zpowers y)) hD.2
    obtain ⟨-, -, -, R, _, I, F, θ, -, -, ⟨-, hnot⟩, φ, hφ, hind⟩ :=
      Canonical.largeEvenMarking_exists (MI.marking_transport (indRel p J y) hdiag hmark)
    rw [(MI.induces_indRel_iff hy θ).1 hind] at hφ
    exact hnot hφ
  · rintro ⟨rfl, hT⟩
    obtain ⟨lab', -, R, _, I, F, θ, -, -, ⟨rfl, -⟩, hMM⟩ :=
      Canonical.largeEvenMarking_exists_markedModel hmark
    exact htri (MI.tag_triD4_of_isTD4 hMM hT θ)

end CertsTD4

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

section Obstructions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem orth_kline_no_real {σ : K ≃+* K} (hσ : σ ≠ 1) (Φ : V ≃+ V)
    (hΦ : ∀ (c : K) (v : V), Φ (c • v) = σ c • Φ v) {J₀ : Subgroup (V ≃ₗ[K] V)}
    (Γ : ↥J₀ →* ↥J₀)
    (hΓ : ∀ (ω : ↥J₀) (v : V), ((Γ ω : ↥J₀) : V ≃ₗ[K] V) (Φ v) = Φ ((ω : V ≃ₗ[K] V) v))
    (N : V →ₗ[K] V) (hN : N ≠ 0)
    (hline : ∀ c : K, ∃ ω ∈ J₀, ∀ v, (ω : V ≃ₗ[K] V) v = v + c • N v) (L : V ≃ₗ[K] V) :
    ¬ ∀ ω : ↥J₀, ((Γ ω : ↥J₀) : V ≃ₗ[K] V) = L * ω * L⁻¹ := by
  intro h
  have key : ∀ (c : K) (v : V), c • N (L.symm (Φ v)) = σ c • L.symm (Φ (N v)) := by
    intro c v
    obtain ⟨ω, hω, hωv⟩ := hline c
    have h1 : L (ω (L.symm (Φ v))) = Φ (ω v) := by
      have h0 := hΓ ⟨ω, hω⟩ v
      rw [h ⟨ω, hω⟩] at h0
      exact h0
    rw [hωv, hωv, LinearEquiv.map_add, LinearEquiv.apply_symm_apply, LinearEquiv.map_smul,
      AddEquiv.map_add, hΦ] at h1
    have h3 := congrArg L.symm (add_left_cancel h1)
    rwa [LinearEquiv.map_smul, LinearEquiv.symm_apply_apply, LinearEquiv.map_smul] at h3
  have key1 : ∀ v, N (L.symm (Φ v)) = L.symm (Φ (N v)) := by
    intro v
    have := key 1 v
    rwa [one_smul, map_one, one_smul] at this
  apply hσ
  ext c
  obtain ⟨w, hw⟩ : ∃ w, N w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN (LinearMap.ext hcon)
  obtain ⟨v, rfl⟩ : ∃ v, L.symm (Φ v) = w := ⟨Φ.symm (L w), by simp⟩
  have h1 := key c v
  rw [← key1 v] at h1
  have h2 : (c - σ c) • N (L.symm (Φ v)) = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact (sub_eq_zero.1 h3).symm
  · exact absurd h3 hw

theorem orth_trace_no_real [FiniteDimensional K V] {J₀ : Subgroup (V ≃ₗ[K] V)} (Γ : ↥J₀ →* ↥J₀) (ω : ↥J₀)
    (hω : LinearMap.trace K V (((Γ ω : ↥J₀) : V ≃ₗ[K] V) : V →ₗ[K] V) ≠
      LinearMap.trace K V (((ω : ↥J₀) : V ≃ₗ[K] V) : V →ₗ[K] V)) (L : V ≃ₗ[K] V) :
    ¬ ∀ ω' : ↥J₀, ((Γ ω' : ↥J₀) : V ≃ₗ[K] V) = L * ω' * L⁻¹ := by
  intro h
  apply hω
  rw [h ω]
  have e : (((L * (ω : V ≃ₗ[K] V) * L⁻¹ : V ≃ₗ[K] V)) : V →ₗ[K] V) =
      ((L : V →ₗ[K] V) ∘ₗ ((ω : V ≃ₗ[K] V) : V →ₗ[K] V)) ∘ₗ (L.symm : V →ₗ[K] V) := rfl
  rw [e, ← LinearEquiv.conj_apply, LinearMap.trace_conj']

end Obstructions

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open scoped commutatorElement

theorem orth_lab_eq_of_canon_D {lab : LargeEvenLabel} {m f : ℕ} (hm3 : m ≠ 3)
    (h : canonLabel lab = ⟨.D, m, f⟩) : lab = ⟨.D, m, f⟩ := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [canonLabel, LargeEvenLabel.mk.injEq] at h ⊢
  all_goals first
    | (exact absurd h.1 (by decide))
    | skip
  · by_cases h3 : rank = 3
    · simp [h3] at h
    · simp only [h3, ↓reduceIte, LargeEvenLabel.mk.injEq] at h
      exact ⟨trivial, h.2⟩
  · by_cases h3 : rank = 3
    · simp [h3] at h
    · by_cases h2 : rank = 2
      · simp [h3, h2] at h
      · simp [h3, h2] at h

theorem orth_lab_eq_of_canon_twD {lab : LargeEvenLabel} {m f : ℕ} (hm2 : m ≠ 2) (hm3 : m ≠ 3)
    (h : canonLabel lab = ⟨.twD, m, f⟩) : lab = ⟨.twD, m, f⟩ := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [canonLabel, LargeEvenLabel.mk.injEq] at h ⊢
  all_goals first
    | (exact absurd h.1 (by decide))
    | skip
  · by_cases h3 : rank = 3
    · simp [h3] at h
    · simp [h3] at h
  · by_cases h3 : rank = 3
    · simp [h3] at h
    · by_cases h2 : rank = 2
      · simp [h3, h2] at h
      · simp only [h3, h2, ↓reduceIte, LargeEvenLabel.mk.injEq] at h
        exact ⟨trivial, h.2⟩

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X

theorem orth_model_of_l154Orth {T : Type} [Group T] (h : catalogIs T l154Orth) :
    ∃ m f : ℕ, StatedClassicalModel T .POmegaPlus m 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [l154Orth, onLie] at hi
  | alternating n hn => simp [l154Orth, onLie] at hi
  | sporadic s => simp [l154Orth, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | D r q =>
      have hq : q.p = 2 := by simpa [l154Orth, onLie] using hi
      have h1 := CFSG.Models.lieModel_D r q hv e
      rw [hq] at h1
      rcases h1.2 with h2 | ⟨-, ⟨⟨t', hv'⟩, hd, -⟩⟩
      · exact ⟨r, q.exponent, h2⟩
      · cases t' <;> simp [CFSG.Models.NamesTag] at hd
    | _ => simp [l154Orth, onLie] at hi

theorem orth_model_of_l154TwOrth {T : Type} [Group T] (h : catalogIs T l154TwOrth) :
    ∃ m f : ℕ, StatedClassicalModel T .POmegaMinus m 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [l154TwOrth, onLie] at hi
  | alternating n hn => simp [l154TwOrth, onLie] at hi
  | sporadic s => simp [l154TwOrth, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | twistedD r q =>
      have hq : q.p = 2 := by simpa [l154TwOrth, onLie] using hi
      have h1 := CFSG.Models.lieModel_twistedD r q hv e
      rw [hq] at h1
      rcases h1.2 with h2 | ⟨-, ⟨⟨t', hv'⟩, hd, -⟩⟩
      · exact ⟨r, q.exponent, h2⟩
      · cases t' <;> simp [CFSG.Models.NamesTag] at hd
    | _ => simp [l154TwOrth, onLie] at hi

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.RankThree.PartOne.AUTSL (conjAct)

open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldPair fieldPair_left fieldPair_right)

theorem orth_conjAct_inclusion {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) : conjAct Q (matrixDerivedInclusion Q A) = MulAut.conj A := by
  refine MulEquiv.ext fun X => Subtype.ext ?_
  change (matrixDerivedConjugation Q (matrixDerivedInclusion Q A) X).val = (A * X * A⁻¹).val
  rw [matrixDerivedConjugation_val, matrixDerivedInclusion_val]
  simp

theorem orth_congr_conj {R Γ : Type*} [Group R] [Group Γ] (e : R ≃* Γ) (r : R) :
    MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) :=
  MulEquiv.ext fun z => by simp [MulAut.congr_apply, MulAut.conj_apply]

section Certs

theorem orth_plus_marking_data (hOD : Y10GFldOrth.OrthLabelDict) {p : ℕ} (hp : p.Prime)
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    (hQ : catalogIs (PSimple p S) l154Orth)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (e : PSimple p S ≃* matrixDerived (coordinateQuadPlus m K))
      (A : matrixDerived (coordinateQuadPlus m K)) (g : similarityPairs (coordinateQuadPlus m K)),
      4 ≤ m ∧ (∃ f : ℕ, StatedClassicalModel (PSimple p S) .POmegaPlus m 2 f) ∧
      IsSimpleGroup (PSimple p S) ∧ (∃ a b : PSimple p S, a * b ≠ b * a) ∧
      (g : coordinateSemilinearGroup (2 * m) K).right ≠ 1 ∧
      (g : coordinateSemilinearGroup (2 * m) K).right ^ p = 1 ∧
      (∀ q q' : PQuot p S, indRel p S x q q' → e (q' : PSimple p S) = A * e q * A⁻¹) ∧
      (∀ q q' : PQuot p S, indRel p S y q q' →
        e (q' : PSimple p S) = conjAct (coordinateQuadPlus m K) g (e q)) := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := MI.marking_transport (indRel p S x) hdiag hF.2
  have hlab : HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨m, f, hmodel⟩ := orth_model_of_l154Orth hQ
  have hcanon := (hOD (PQuot p S) lab m f hlab).1 hmodel
  have hm4 : 4 ≤ m := hmodel.1.2.2
  have hlabeq := orth_lab_eq_of_canon_D (by omega) hcanon
  subst hlabeq
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  simp only [show m ≠ 3 by omega, ↓reduceIte] at hraw
  unfold LargeEvenRecipeOmegaPlus at hraw
  obtain ⟨K, hKf, hKfin, hcard, hs, hna, θ, ⟨-, f₀, hf₀, u, hu, hord, hindy⟩, φx, hφx, hindx⟩ := hraw
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hcard
  have hm1 : 1 ≤ m := by omega
  set Θ := RecipeFieldOmega.plusEquiv (K := K) hm1 with hΘ
  obtain ⟨ru, rfl⟩ := hu
  obtain ⟨r, rfl⟩ := hφx
  obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm1 hf₀
  set gu := matrixDerivedInclusion (coordinateQuadPlus m K) (Θ ru) with hgu
  set gf := fieldPair (coordinateQuadPlus m K) σ
    (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap m σ) with hgf
  have hright : ((gu * gf * gu⁻¹ : similarityPairs (coordinateQuadPlus m K)) :
      coordinateSemilinearGroup (2 * m) K).right = σ := by
    change gu.val.right * gf.val.right * gu.val.right⁻¹ = σ
    rw [hgu, matrixDerivedInclusion_val, hgf, fieldPair_right]
    simp
  have hf1 : f₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hfp : f₀ ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one f₀
  haveI := hs
  have hsS : IsSimpleGroup (PSimple p S) := θ.isSimpleGroup
  have hnaS : ∃ a b : PSimple p S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨θ.symm a, θ.symm b, fun h => hab (θ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  refine ⟨m, K, hKf, hKfin, inferInstance, θ.trans Θ, Θ r, gu * gf * gu⁻¹, hm4, ⟨f, hmodel⟩, hsS,
    hnaS, ?_, ?_, ?_, ?_⟩
  · rw [hright]
    rintro rfl
    apply hf1
    apply (MulAut.congr Θ).injective
    rw [hσ, map_one, map_one]
  · rw [hright]
    have h1 : AutOm.fieldAutP m (σ ^ p) = 1 := by
      rw [map_pow, ← hσ, ← map_pow, hfp, map_one]
    refine AutOm.eq_one_of_mem_inner_plusCompl (n := m) (by omega) (Or.inl rfl) ?_
    rw [h1]
    exact one_mem _
  · intro q q' hqq'
    have h1 : MulAut.conj r (θ q) = θ q' := hindx _ _ hqq'
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← h1, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · intro q q' hqq'
    have h1 : (MulAut.conj ru * f₀ * (MulAut.conj ru)⁻¹) (θ q) = θ q' := hindy _ _ hqq'
    have key : conjAct (coordinateQuadPlus m K) (gu * gf * gu⁻¹) =
        MulAut.congr Θ (MulAut.conj ru * f₀ * (MulAut.conj ru)⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, orth_congr_conj, hσ, hgu,
        orth_conjAct_inclusion, hgf, ← AutOm.fieldAutP_apply]
    rw [key, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1]

theorem orth_orderOf_frobenius {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) : orderOf (frobeniusEquiv K 2) = f := by
  obtain ⟨σ, hσ, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf1 hf
  have hσφ : σ = frobeniusEquiv K 2 := RingEquiv.ext fun a => by
    rw [hσ, frobeniusEquiv_apply, frobenius_def]
  rw [← hσφ, hord]

theorem orth_minus_marking_data (hOD : Y10GFldOrth.OrthLabelDict) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    (hQ : catalogIs (PSimple p S) l154TwOrth)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (hm4 : 4 ≤ m) (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (e : PSimple p S ≃* matrixDerived (CFSG.RankThree.PartOne.AUTSL.Qm m hm4 b c))
      (A : matrixDerived (CFSG.RankThree.PartOne.AUTSL.Qm m hm4 b c))
      (g : similarityPairs (CFSG.RankThree.PartOne.AUTSL.Qm m hm4 b c)),
      (∃ f : ℕ, StatedClassicalModel (PSimple p S) .POmegaMinus m 2 f) ∧
      IsSimpleGroup (PSimple p S) ∧ (∃ a b : PSimple p S, a * b ≠ b * a) ∧
      (g : coordinateSemilinearGroup (2 * m) K).right ≠ 1 ∧
      (g : coordinateSemilinearGroup (2 * m) K).right ^ p = 1 ∧
      (∀ q q' : PQuot p S, indRel p S x q q' → e (q' : PSimple p S) = A * e q * A⁻¹) ∧
      (∀ q q' : PQuot p S, indRel p S y q q' →
        e (q' : PSimple p S) = conjAct (CFSG.RankThree.PartOne.AUTSL.Qm m hm4 b c) g (e q)) := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := MI.marking_transport (indRel p S x) hdiag hF.2
  have hlab : HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨m, f, hmodel⟩ := orth_model_of_l154TwOrth hQ
  have hcanon := (hOD (PQuot p S) lab m f hlab).2 hmodel
  have hm4 : 4 ≤ m := hmodel.1.2.2
  have hf1 : 1 ≤ f := hmodel.1.2.1
  have hlabeq := orth_lab_eq_of_canon_twD (by omega) (by omega) hcanon
  subst hlabeq
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  simp only [show m ≠ 3 by omega, show m ≠ 2 by omega, ↓reduceIte] at hraw
  unfold LargeEvenRecipeOmegaMinus at hraw
  obtain ⟨K, hKf, hKfin, hcard, b, c, hirr, hs, hna, θ, ⟨-, f₀, hf₀, u, hu, hord, hindy⟩, φx, hφx,
    hindx⟩ := hraw
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hcard
  obtain ⟨ru, rfl⟩ := hu
  obtain ⟨r, rfl⟩ := hφx
  obtain ⟨k, hk⟩ := RecipeFieldOmega.congr_minusEquiv_of_mem_phi hm4 hirr hf₀
  have hb : b ≠ 0 := CFSG.RankThree.PartOne.AUTSL.ne_zero_of_irreducible_tail b c hirr
  set Qm := CFSG.RankThree.PartOne.AUTSL.Qm m hm4 b c with hQm
  set Θ := RecipeFieldOmega.minusEquiv (K := K) (n := m) hm4 b c with hΘ
  set gu := matrixDerivedInclusion Qm (Θ ru) with hgu
  set gf := (CFSG.RankThree.PartOne.AUTSL.frobPair m (by omega) b c hb : similarityPairs Qm) ^ k
    with hgf
  have hτ : AutOm.frobAut hm4 hirr ^ k = conjAct Qm gf := by
    rw [hgf, map_pow]
    rfl
  have hgfr : ((gf : similarityPairs Qm) : coordinateSemilinearGroup (2 * m) K).right =
      frobeniusEquiv K 2 ^ k :=
    RecipeFieldOmega.frobPair_pow_right (by omega) hb k
  have hright : ((gu * gf * gu⁻¹ : similarityPairs Qm) : coordinateSemilinearGroup (2 * m) K).right =
      frobeniusEquiv K 2 ^ k := by
    change gu.val.right * gf.val.right * gu.val.right⁻¹ = _
    rw [hgu, matrixDerivedInclusion_val, hgfr]
    simp
  have hfp : f₀ ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one f₀
  have hFord := orth_orderOf_frobenius hcard hf1
  haveI := hs
  have hsS : IsSimpleGroup (PSimple p S) := θ.isSimpleGroup
  have hnaS : ∃ a b : PSimple p S, a * b ≠ b * a := by
    obtain ⟨a, b', hab⟩ := hna
    exact ⟨θ.symm a, θ.symm b', fun h => hab (θ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  refine ⟨m, K, hKf, hKfin, inferInstance, hm4, b, c, hirr, θ.trans Θ, Θ r, gu * gf * gu⁻¹,
    ⟨f, hmodel⟩, hsS, hnaS, ?_, ?_, ?_, ?_⟩
  · rw [hright]
    intro h1
    have hdvd : f ∣ k := hFord ▸ orderOf_dvd_of_pow_eq_one h1
    obtain ⟨j, rfl⟩ := hdvd
    have h2 : MulAut.congr Θ (f₀ ^ 2) = 1 := by
      rw [map_pow, hk, ← pow_mul, show f * j * 2 = 2 * f * j by ring, pow_mul,
        AutOm.frobAut_pow_two_mul hm4 hirr hcard, one_pow]
    have h3 : f₀ ^ 2 = 1 := (MulAut.congr Θ).injective (by rw [h2, map_one])
    have h4 : p ∣ 2 := hord ▸ orderOf_dvd_of_pow_eq_one h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)
  · rw [hright, ← pow_mul]
    have h1 : AutOm.frobAut hm4 hirr ^ (k * p) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived Qm) := by
      rw [pow_mul, ← hk, ← map_pow, hfp, map_one]
      exact one_mem _
    have h2 := AutOm.dvd_of_frobAut_pow_mem_inner hm4 hirr hcard hf1 h1
    rw [← hFord] at h2
    exact orderOf_dvd_iff_pow_eq_one.1 h2
  · intro q q' hqq'
    have h1 : MulAut.conj r (θ q) = θ q' := hindx _ _ hqq'
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← h1, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · intro q q' hqq'
    have h1 : (MulAut.conj ru * f₀ * (MulAut.conj ru)⁻¹) (θ q) = θ q' := hindy _ _ hqq'
    have key : conjAct Qm (gu * gf * gu⁻¹) =
        MulAut.congr Θ (MulAut.conj ru * f₀ * (MulAut.conj ru)⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, orth_congr_conj, hk, hgu,
        orth_conjAct_inclusion, hτ]
    rw [key, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1]

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.AUTSL (conjAct)

open scoped commutatorElement

theorem orth_eq_or_eq_inv_of_add_inv {K : Type*} [Field K] {s μ : K} (hs : s ≠ 0) (hμ : μ ≠ 0)
    (h : s + s⁻¹ = μ + μ⁻¹) : s = μ ∨ s = μ⁻¹ := by
  have h1 : (s - μ) * (s * μ - 1) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact Or.inl (sub_eq_zero.1 h2)
  · right
    exact eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h2)

theorem orth_exists_add_inv_moved {K : Type*} [Field K] [CharP K 2] {σ : K ≃+* K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hσ : σ ≠ 1) (hσp : σ ^ p = 1) :
    ∃ μ : K, μ ≠ 0 ∧ σ (μ + μ⁻¹) ≠ μ + μ⁻¹ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_contra hcon
  push Not at hcon
  have hdich : ∀ μ : K, μ ≠ 0 → σ μ = μ ∨ σ μ = μ⁻¹ := fun μ hμ =>
    orth_eq_or_eq_inv_of_add_inv ((map_ne_zero σ).2 hμ) hμ (by rw [← map_inv₀, ← map_add]; exact hcon μ hμ)
  obtain ⟨l, hl⟩ : ∃ l : K, σ l ≠ l := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have hl0 : l ≠ 0 := by rintro rfl; exact hl (map_zero σ)
  have hl1 : l ≠ 1 := by rintro rfl; exact hl (map_one σ)
  have hσl : σ l = l⁻¹ := (hdich l hl0).resolve_left hl
  have hl10 : l + 1 ≠ 0 := by
    intro h
    apply hl1
    linear_combination h - h2
  have hσl1 : σ (l + 1) = (l + 1)⁻¹ := by
    rcases hdich (l + 1) hl10 with h | h
    · exfalso
      rw [map_add, map_one, hσl] at h
      have h3 : l⁻¹ = l := by linear_combination h
      have h4 : l * l = 1 := by
        calc l * l = l * l⁻¹ := by rw [h3]
          _ = 1 := mul_inv_cancel₀ hl0
      have h5 : (l + 1) * (l + 1) = 0 := by linear_combination h4 + (l + 1) * h2
      exact hl10 (mul_self_eq_zero.1 h5)
    · exact h
  have hq : l ^ 2 + l + 1 = 0 := by
    rw [map_add, map_one, hσl] at hσl1
    have h3 : (l⁻¹ + 1) * (l + 1) = 1 := by rw [hσl1, inv_mul_cancel₀ hl10]
    have h4 : l⁻¹ * l = 1 := inv_mul_cancel₀ hl0
    have h5 : l + l⁻¹ = 1 := by linear_combination h3 - h4 - h2
    have h6 : l * (l + l⁻¹) = l * 1 := by rw [h5]
    rw [mul_add, mul_inv_cancel₀ hl0, mul_one] at h6
    linear_combination h6 + h2 * l
  have hl3 : l ^ 3 = 1 := by linear_combination (l - 1) * hq
  have hσl' : σ l = l ^ 2 := by
    rw [hσl, eq_comm, ← mul_eq_one_iff_eq_inv₀ hl0, ← pow_succ, hl3]
  have hσ2 : (σ ^ 2) l = l := by
    rw [pow_two]
    change σ (σ l) = l
    rw [hσl', map_pow, hσl', ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, hl3,
      one_mul]
  have hev : ∀ k : ℕ, (σ ^ (2 * k)) l = l := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [mul_add, mul_one, pow_add,
        show (σ ^ (2 * k) * σ ^ 2) l = (σ ^ (2 * k)) ((σ ^ 2) l) from rfl, hσ2, ih]
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hσpl : (σ ^ p) l = σ l := by
    rw [hk, pow_succ, show (σ ^ (2 * k) * σ) l = (σ ^ (2 * k)) (σ l) from rfl, hσl', map_pow, hev]
  rw [hσp] at hσpl
  exact hl hσpl.symm

section Semi

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def orthSemiConj (g : coordinateSemilinearGroup d K) :
    MulAut ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  MulAut.congr (matrixLinearIso (d := d) (K := K)) (matrixConjugation g)

theorem orthSemiConj_apply (g : coordinateSemilinearGroup d K)
    (ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) (v : Fin d → K) :
    orthSemiConj g ω v = coordinateSemilinearMap g (ω ((coordinateSemilinearMap g).symm v)) := by
  obtain ⟨A, rfl⟩ := (matrixLinearIso (d := d) (K := K)).surjective ω
  rw [orthSemiConj, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  exact matrixConjugation_vector g A v

theorem orthSemiConj_apply_map (g : coordinateSemilinearGroup d K)
    (ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) (v : Fin d → K) :
    orthSemiConj g ω (coordinateSemilinearMap g v) = coordinateSemilinearMap g (ω v) := by
  rw [orthSemiConj_apply, AddEquiv.symm_apply_apply]

theorem orth_matrixLinearIso_toLinearMap (A : GL (Fin d) K) :
    ((matrixLinearIso A : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) =
      Matrix.toLin' (A : Matrix (Fin d) (Fin d) K) :=
  LinearMap.ext fun _ => rfl

theorem orth_trace_matrixLinearIso (A : GL (Fin d) K) :
    LinearMap.trace K (Fin d → K)
      ((matrixLinearIso A : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) =
      Matrix.trace (A : Matrix (Fin d) (Fin d) K) := by
  rw [orth_matrixLinearIso_toLinearMap, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin d)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem orth_trace_semiConj (g : coordinateSemilinearGroup d K)
    (ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
    LinearMap.trace K (Fin d → K)
      ((orthSemiConj g ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) =
      g.right (LinearMap.trace K (Fin d → K) ((ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
        (Fin d → K) →ₗ[K] (Fin d → K))) := by
  obtain ⟨A, rfl⟩ := (matrixLinearIso (d := d) (K := K)).surjective ω
  rw [orthSemiConj, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, orth_trace_matrixLinearIso, orth_trace_matrixLinearIso]
  change Matrix.trace ((g.left * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut
    (Fin d) K g.right A * g.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, map_sum]
  rfl

end Semi

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
open CFSG.ClassicalGroups.Orthogonal (scalars mem_scalars)

open CFSG.RankThree.PartOne.AUTSL (conjAct)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open scoped commutatorElement

section Scalars

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

theorem orth_scalars_subgroupOf_eq_bot {Q : QuadraticForm K V} (hQ : ∃ v, Q v ≠ 0) :
    (scalars K V).subgroupOf (orthDerived Q) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hgΩ⟩ hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := mem_scalars.1 hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ hgΩ
  obtain ⟨v, hv⟩ := hQ
  have h1 : Q (g v) = Q v := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hgO) v
  rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h1
  have h2 : c * c = 1 := by
    have : (c * c - 1) * Q v = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)
  have h3 : c = 1 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (c - 1) * (c - 1) = 0 := by linear_combination h2 - c * h22 + h22
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [Subgroup.mem_bot]
  refine Subtype.ext (LinearEquiv.ext fun w => ?_)
  rw [hc, h3, one_smul]
  rfl

@[expose] noncomputable def orthProjEquiv {Q : QuadraticForm K V} (hQ : ∃ v, Q v ≠ 0) :
    ProjOrthDerived Q ≃* orthDerived Q :=
  (QuotientGroup.quotientMulEquivOfEq (orth_scalars_subgroupOf_eq_bot hQ)).trans
    QuotientGroup.quotientBot

theorem orthProjEquiv_mk {Q : QuadraticForm K V} (hQ : ∃ v, Q v ≠ 0) (ω : orthDerived Q) :
    orthProjEquiv hQ (QuotientGroup.mk ω) = ω := rfl

theorem orth_mk'_injective {Q : QuadraticForm K V} (hQ : ∃ v, Q v ≠ 0) :
    Function.Injective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  intro a b h
  have := congrArg (orthProjEquiv hQ) h
  exact this

end Scalars

@[expose] def OrthObstruction {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (J₀ : Subgroup (V ≃ₗ[K] V)) : Prop :=
  (∃ N : V →ₗ[K] V, N ≠ 0 ∧ ∀ c : K, ∃ ω ∈ J₀, ∀ v, (ω : V ≃ₗ[K] V) v = v + c • N v) ∨
    ∀ μ : K, μ ≠ 0 → ∃ ω ∈ J₀, LinearMap.trace K V ((ω : V ≃ₗ[K] V) : V →ₗ[K] V) = μ + μ⁻¹

@[expose] def OrthBlockData (p : ℕ) {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (J₀ : Subgroup (V ≃ₗ[K] V)) : Prop :=
  OrthBlockMark p J₀ ∧ OrthObstruction J₀

@[expose] def OrthBlockDataW {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (J₀ : Subgroup (V ≃ₗ[K] V)) : Prop :=
  OrthBlockMarkW J₀ ∧ OrthObstruction J₀

theorem orthBlockDataW_of_orthBlockData {p : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {J₀ : Subgroup (V ≃ₗ[K] V)} (h : OrthBlockData p J₀) : OrthBlockDataW J₀ :=
  ⟨orthBlockMarkW_of_orthBlockMark h.1, h.2⟩

@[expose] def OrthBlockClass (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (d : ℕ) (Q : QuadraticForm K (Fin d → K)),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ x : (Fin d → K) ≃ₗ[K] (Fin d → K), OddOrderIsometry Q p x →
      (∀ h ∈ primaryFactors x.toLinearMap, h ≠ Polynomial.X - 1 →
        CFSG.IsQuasisimple ↥(specialBlock Q x h) → OrthBlockData p (specialBlock Q x h)) ∧
      (FixedLayerListed Q x → ∀ F : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)), CFSG.IsQuasisimple ↥F →
        F ≤ supportedFixedDerived Q x → (F.subgroupOf (supportedFixedDerived Q x)).Normal →
        OrthBlockDataW F ∧ (OrthBlockData p F ∨
          (p = 3 ∧ F = supportedFixedDerived Q x ∧
            Nonempty ((Q.comp (fixedSpace x).subtype).IsometryEquiv
              (CFSG.LieType.Universal.Spin.quadPlus 4 K)))))

theorem orth_no_real_of_obstruction {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [CharP K 2]
    {d : ℕ} {J₀ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))} (g : coordinateSemilinearGroup d K)
    (hσ : g.right ≠ 1) (hσp : g.right ^ p = 1) (Γ : ↥J₀ →* ↥J₀)
    (hΓv : ∀ ω : ↥J₀, ((Γ ω : ↥J₀) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orthSemiConj g ω)
    (hW : OrthObstruction J₀) (L : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
    ¬ ∀ ω : ↥J₀, ((Γ ω : ↥J₀) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = L * ω * L⁻¹ := by
  rcases hW with ⟨N, hN, hline⟩ | htr
  · exact orth_kline_no_real hσ (coordinateSemilinearMap g) (coordinateSemilinearMap_smul g) Γ
      (fun ω v => by rw [hΓv]; exact orthSemiConj_apply_map g ω v) N hN hline L
  · obtain ⟨μ, hμ, hmove⟩ := orth_exists_add_inv_moved hp hp2 hσ hσp
    obtain ⟨ω, hω, htrω⟩ := htr μ hμ
    refine orth_trace_no_real Γ ⟨ω, hω⟩ ?_ L
    rw [hΓv, orth_trace_semiConj]
    change g.right (LinearMap.trace K (Fin d → K) ((ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
      (Fin d → K) →ₗ[K] (Fin d → K))) ≠ _
    rw [htrω]
    exact hmove

theorem orth_exists_action {Ω : Type} [Group Ω] {J : Subgroup Ω} {y : Ω}
    (hy : y ∈ Subgroup.normalizer (J : Set Ω)) {K : Type} [Field K] {d : ℕ}
    {J₀ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))} (ρ : ↥J →* ↥J₀) (hρs : Function.Surjective ρ)
    (g : coordinateSemilinearGroup d K)
    (hΓ : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J),
      ((ρ ⟨_, hl⟩ : ↥J₀) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orthSemiConj g (ρ l)) :
    ∃ Γ : ↥J₀ →* ↥J₀, (∀ ω : ↥J₀, ((Γ ω : ↥J₀) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orthSemiConj g ω) ∧
      ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J), ρ ⟨_, hl⟩ = Γ (ρ l) := by
  have hstab : ∀ ω ∈ J₀, orthSemiConj g ω ∈ J₀ := by
    intro ω hω
    obtain ⟨l, hl⟩ := hρs ⟨ω, hω⟩
    have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hy
    have hmem : y⁻¹ * (l : Ω) * y ∈ J := by
      have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
      simpa using this
    have h1 := hΓ l hmem
    rw [hl] at h1
    rw [← h1]
    exact (ρ _).2
  refine ⟨((orthSemiConj g).toMonoidHom.comp J₀.subtype).codRestrict J₀ fun ω => hstab ω ω.2,
    fun _ => rfl, fun l hl => Subtype.ext ?_⟩
  exact hΓ l hl

section Certs

theorem fieldOn_of_blockData {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [CharP K 2]
    {d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {X J : Subgroup Ω} (hJ : GLAPComponent p X J) {y : Ω}
    (hy : y ∈ Subgroup.normalizer (J : Set Ω)) (hyp : y ^ p = 1)
    {J₀ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))} (ρ : ↥J →* ↥J₀) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥J) (g : coordinateSemilinearGroup d K) (hσ : g.right ≠ 1)
    (hσp : g.right ^ p = 1)
    (hΓ : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J),
      ((ρ ⟨_, hl⟩ : ↥J₀) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orthSemiConj g (ρ l))
    (hB : OrthBlockData p J₀) : FieldOn p y J := by
  obtain ⟨Γ, hΓv, hΓρ⟩ := orth_exists_action hy ρ hρs g hΓ
  exact fieldOn_of_blockMark hp hp2 hJ hy hyp ρ hρs hρk Γ hΓρ
    (orth_no_real_of_obstruction hp hp2 g hσ hσp Γ hΓv hB.2) hB.1

end Certs

section CertsTD4

theorem nidTd4_of_blockDataW {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [CharP K 2]
    {d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {X J : Subgroup Ω} (hJ : GLAPComponent p X J) {y : Ω}
    (hy : y ∈ Subgroup.normalizer (J : Set Ω))
    {J₀ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))} (ρ : ↥J →* ↥J₀) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥J) (g : coordinateSemilinearGroup d K) (hσ : g.right ≠ 1)
    (hσp : g.right ^ p = 1)
    (hΓ : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J),
      ((ρ ⟨_, hl⟩ : ↥J₀) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orthSemiConj g (ρ l))
    (hB : OrthBlockDataW J₀) : NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J) := by
  obtain ⟨Γ, hΓv, hΓρ⟩ := orth_exists_action hy ρ hρs g hΓ
  exact nidTd4_of_blockMarkW hp hJ hy ρ hρs hρk Γ hΓρ
    (orth_no_real_of_obstruction hp hp2 g hσ hσp Γ hΓv hB.2) hB.1

end CertsTD4

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

open CFSG.ClassicalGroups.Orthogonal (scalars mem_scalars)

open CFSG.RankThree.PartOne.AUTSL (conjAct)

open CFSG.RankThree.PartOne.KCOrthComm (matrixDerivedEquiv coe_matrixDerivedEquiv)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open scoped commutatorElement

section Pipeline

variable {Ω : Type} [Group Ω] {p : ℕ} {S : Subgroup Ω}

theorem orth_indAut_eq_conj {G : Type} [Group G] {x : Ω} (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (e : PSimple p S ≃* G) (A : G)
    (hAx : ∀ q q' : PQuot p S, indRel p S x q q' → e (q' : PSimple p S) = A * e q * A⁻¹) :
    MI.indAut p S x hxN = MulAut.conj (e.symm A) := by
  refine MulEquiv.ext fun s => ?_
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hl' : x⁻¹ * (l : Ω) * x ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 hxinv (l : Ω)).1 l.2
    simpa using this
  have hrel : indRel p S x (QuotientGroup.mk l) (QuotientGroup.mk ⟨_, hl'⟩) :=
    ⟨l, ⟨_, hl'⟩, rfl, rfl, rfl⟩
  rw [MI.indAut_apply_mk hxN hrel]
  apply e.injective
  rw [hAx _ _ hrel, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem orth_fixSubgroup_conj {G : Type*} [Group G] (a : G) :
    fixSubgroup (MulAut.conj a) = Subgroup.centralizer ({a} : Set G) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem orth_fixSubgroup_congr {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (β : MulAut G) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : G →* G') := by
  ext z
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (β (e.symm z)) = z ↔ β (e.symm z) = e.symm z
  exact e.eq_symm_apply.symm

end Pipeline

@[expose] def OrthD4Fact : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (d : ℕ) (Q : QuadraticForm K (Fin d → K)),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ x : (Fin d → K) ≃ₗ[K] (Fin d → K), OddOrderIsometry Q 3 x →
    Nonempty ((Q.comp (fixedSpace x).subtype).IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus 4 K)) →
    ∀ g : coordinateSemilinearGroup d K, g ∈ similarityPairs Q → g.right ≠ 1 → g.right ^ 3 = 1 →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (X J : Subgroup Ω), GLAPComponent 3 X J →
    ∀ y : Ω, y ∈ Subgroup.normalizer (J : Set Ω) → y ^ 3 = 1 →
    ∀ ρ : ↥J →* ↥(supportedFixedDerived Q x), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center ↥J →
      (∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J),
        ((ρ ⟨_, hl⟩ : ↥(supportedFixedDerived Q x)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
          orthSemiConj g (ρ l)) →
      FieldOn 3 y J

section Core

variable {K : Type} [Field K] {d : ℕ}

theorem orth_matrixDerivedEquiv_conjAct (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q)
    (X : matrixDerived Q) :
    ((matrixDerivedEquiv Q (conjAct Q g X) : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      orthSemiConj (g : coordinateSemilinearGroup d K)
        ((matrixDerivedEquiv Q X : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
  rw [coe_matrixDerivedEquiv, coe_matrixDerivedEquiv, orthSemiConj, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.trans_apply]
  change matrixLinearIso (matrixDerivedConjugation Q g X).val = matrixLinearIso
    (matrixConjugation (g : coordinateSemilinearGroup d K) (matrixLinearIso.symm (matrixLinearIso X.val)))
  rw [MulEquiv.symm_apply_apply, matrixDerivedConjugation_val]
  rfl

end Core

theorem orth_core_block {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ}
    (hmodel : StatedClassicalModel (PSimple p S) t m 2 f)
    (hsS : IsSimpleGroup (PSimple p S)) (hnaS : ∃ a b : PSimple p S, a * b ≠ b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : PSimple p S ≃* matrixDerived Q) (A : matrixDerived Q) (g : similarityPairs Q)
    (hAx : ∀ q q' : PQuot p S, indRel p S x q q' → e (q' : PSimple p S) = A * e q * A⁻¹)
    (hgy : ∀ q q' : PQuot p S, indRel p S y q q' → e (q' : PSimple p S) = conjAct Q g (e q)) :
    ∃ (x' : (Fin d → K) ≃ₗ[K] (Fin d → K)) (_ : OddOrderIsometry Q p x')
      (B : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))) (ρ : ↥J →* ↥B),
      Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center ↥J ∧
      (∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J),
        ((ρ ⟨_, hl⟩ : ↥B) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
          orthSemiConj (g : coordinateSemilinearGroup d K) (ρ l)) ∧
      ((∃ h ∈ primaryFactors x'.toLinearMap, h ≠ Polynomial.X - 1 ∧
          CFSG.IsQuasisimple ↥(specialBlock Q x' h) ∧ B = specialBlock Q x' h) ∨
        (FixedLayerListed Q x' ∧ CFSG.IsQuasisimple ↥B ∧ B ≤ supportedFixedDerived Q x' ∧
          (B.subgroupOf (supportedFixedDerived Q x')).Normal)) := by
  classical
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hJ' : GLAPComponent p (S ⊓ Subgroup.centralizer ({x⁻¹} : Set Ω)) J := by
    rw [l154_centralizer_inv_singleton]; exact hJ
  have hTc := glaPComponent_chevTransfer hp hxN'
    (l154_isPGroup_zpowers_of_pow_eq_one (by simp [inv_pow, hxp])) hJ'
  have hconj := orth_indAut_eq_conj hxN e A hAx
  set a : PSimple p S := e.symm A with ha_def
  have hTc' : GLAPComponent p (fixSubgroup (MulAut.conj a)) (chevTransfer p S J) := by
    rw [← hconj]; exact hTc
  have hcen : Subgroup.center (PSimple p S) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hsS hnaS
  have hap : a ^ p = 1 := by
    have h1 : MulAut.conj (a ^ p) = 1 := by
      rw [map_pow, ← hconj]; exact l154_indAut_pow_eq_one hxN hxp
    have h2 : a ^ p ∈ Subgroup.center (PSimple p S) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h3 := DFunLike.congr_fun h1 z
      rw [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    rw [hcen, Subgroup.mem_bot] at h2
    exact h2
  have hPIL := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_omega
    (by rcases ht with rfl | rfl <;> simp) hmodel hp hp2 hp2 a hap
  have hcomp : CFSG.Open.IsComponentOf (chevTransfer p S J) (fixSubgroup (MulAut.conj a)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hTc'
      (hPIL _ hTc'.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hTc'))).1
  have hQne : ∃ v, Q v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨U, hU3, -⟩ := hT
    have hd : 0 < d := by
      have h1 := Submodule.finrank_le U
      rw [hU3, Module.finrank_fin_fun] at h1
      omega
    have hv := hQ.1 (Pi.single ⟨0, hd⟩ 1) fun w => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hcon, hcon, hcon]
      simp
    have := congrFun hv ⟨0, hd⟩
    simp at this
  set eT : PSimple p S ≃* ProjOrthDerived Q :=
    (e.trans (matrixDerivedEquiv Q)).trans (orthProjEquiv hQne).symm with heT
  have hcompT : CFSG.Open.IsComponentOf ((chevTransfer p S J).map (eT : PSimple p S →* _))
      (Subgroup.centralizer ({eT a} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eT hcomp
    rwa [← orth_fixSubgroup_congr, orth_congr_conj, orth_fixSubgroup_conj] at h1
  have haT : (eT a) ^ p = 1 := by rw [← map_pow, hap, map_one]
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K 2]; exact hp2
  obtain ⟨x', hx', hcase⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S2019.exists_lift_component_cases hp hp2 hQ hT hpK (eT a) haT _ hcompT
  set ρS : ↥S →* ↥(orthDerived Q) :=
    (matrixDerivedEquiv Q).toMonoidHom.comp (e.toMonoidHom.comp (chevQuotHom p S)) with hρS
  set J₀ : Subgroup ↥(orthDerived Q) := (J.subgroupOf S).map ρS with hJ₀
  have hJT : (chevTransfer p S J).map (eT : PSimple p S →* _) =
      J₀.map (QuotientGroup.mk' ((scalars K (Fin d → K)).subgroupOf (orthDerived Q))) := by
    rw [chevTransfer, Subgroup.map_map, hJ₀, Subgroup.map_map]
    congr 1
  have hmkinj := orth_mk'_injective hQne (Q := Q)
  have hρJker : ∀ l : ↥J, ρS ⟨l, hJS l.2⟩ = 1 → l ∈ Subgroup.center ↥J := by
    intro l hl
    have h1 : chevQuotHom p S ⟨l.1, hJS l.2⟩ = 1 := by
      have h0 : (e.trans (matrixDerivedEquiv Q)) (chevQuotHom p S ⟨l.1, hJS l.2⟩) = 1 := hl
      exact (map_eq_one_iff _ (e.trans (matrixDerivedEquiv Q)).injective).1 h0
    have h2 : (QuotientGroup.mk (⟨l.1, hJS l.2⟩ : ↥S) : PQuot p S) ∈
        Subgroup.center (PQuot p S) := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : ∀ s : ↥S, s * ⟨l.1, hJS l.2⟩ = ⟨l.1, hJS l.2⟩ * s := by
      intro s
      have h4 := Subgroup.mem_center_iff.1 h2 (QuotientGroup.mk s)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hSp,
        Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.1 h4
    refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
    have h5 := h3 ⟨j.1, hJS j.2⟩
    show (j : Ω) * (l : Ω) = (l : Ω) * (j : Ω)
    exact congrArg Subtype.val h5
  have hρy : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J),
      ((ρS ⟨_, hJS hl⟩ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
        orthSemiConj (g : coordinateSemilinearGroup d K) (ρS ⟨l, hJS l.2⟩) := by
    intro l hl
    have hrel : indRel p S y (QuotientGroup.mk ⟨l.1, hJS l.2⟩) (QuotientGroup.mk ⟨_, hJS hl⟩) :=
      ⟨⟨l.1, hJS l.2⟩, ⟨_, hJS hl⟩, rfl, rfl, rfl⟩
    have h1 := hgy _ _ hrel
    change ((matrixDerivedEquiv Q (e (QuotientGroup.mk (QuotientGroup.mk ⟨_, hJS hl⟩))) :
      orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orthSemiConj (g : coordinateSemilinearGroup d K)
        ((matrixDerivedEquiv Q (e (QuotientGroup.mk (QuotientGroup.mk ⟨l.1, hJS l.2⟩))) :
          orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))
    rw [h1, orth_matrixDerivedEquiv_conjAct]
  have key : ∀ B : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)), B ≤ orthDerived Q →
      J₀ = B.subgroupOf (orthDerived Q) →
      ∃ ρ : ↥J →* ↥B, Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center ↥J ∧
        ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J),
          ((ρ ⟨_, hl⟩ : ↥B) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
            orthSemiConj (g : coordinateSemilinearGroup d K) (ρ l) := by
    intro B hBle hJ₀B
    have hmemB : ∀ l : ↥J, ((ρS ⟨l, hJS l.2⟩ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ B := by
      intro l
      have h1 : ρS ⟨l, hJS l.2⟩ ∈ J₀ :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 l.2)
      rw [hJ₀B, Subgroup.mem_subgroupOf] at h1
      exact h1
    let ρ' : ↥J →* ↥B :=
      MonoidHom.codRestrict (((orthDerived Q).subtype.comp ρS).comp (Subgroup.inclusion hJS)) B
        hmemB
    have hρ'v : ∀ l : ↥J, ((ρ' l : ↥B) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = ρS ⟨l, hJS l.2⟩ :=
      fun _ => rfl
    refine ⟨ρ', ?_, ?_, ?_⟩
    · rintro ⟨ω, hω⟩
      have h1 : (⟨ω, hBle hω⟩ : ↥(orthDerived Q)) ∈ J₀ := by
        rw [hJ₀B, Subgroup.mem_subgroupOf]
        exact hω
      obtain ⟨s, hs, hsω⟩ := Subgroup.mem_map.1 h1
      refine ⟨⟨s, Subgroup.mem_subgroupOf.1 hs⟩, Subtype.ext ?_⟩
      rw [hρ'v]
      exact congrArg Subtype.val hsω
    · intro l hl
      refine hρJker l (Subtype.ext ?_)
      have h1 : ((ρ' l : ↥B) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = 1 := congrArg Subtype.val hl
      rw [hρ'v] at h1
      exact h1
    · intro l hl
      rw [hρ'v, hρ'v]
      exact hρy l hl
  rcases hcase with ⟨h, hh, hne1, hq, hJTc⟩ | ⟨hlist, F, hFq, hFle, hFn, hJTc⟩
  · have hBle : specialBlock Q x' h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer h).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
    have hJ₀ : J₀ = (specialBlock Q x' h).subgroupOf (orthDerived Q) := by
      rw [hJT] at hJTc
      exact Subgroup.map_injective hmkinj hJTc
    obtain ⟨ρ, hρs, hρk, hρy'⟩ := key _ hBle hJ₀
    exact ⟨x', hx', _, ρ, hρs, hρk, hρy', Or.inl ⟨h, hh, hne1, hq, rfl⟩⟩
  · have hFΩ : F ≤ orthDerived Q := hFle.trans hx'.supportedFixedDerived_le_orthDerived
    have hJ₀ : J₀ = F.subgroupOf (orthDerived Q) := by
      rw [hJT] at hJTc
      exact Subgroup.map_injective hmkinj hJTc
    obtain ⟨ρ, hρs, hρk, hρy'⟩ := key F hFΩ hJ₀
    exact ⟨x', hx', F, ρ, hρs, hρk, hρy', Or.inr ⟨hlist, hFq, hFle, hFn⟩⟩

section CoreCerts

theorem orth_core_fieldOn {p : ℕ} (hBC : OrthBlockClass p) (hD4 : OrthD4Fact) (hp : p.Prime)
    (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ}
    (hmodel : StatedClassicalModel (PSimple p S) t m 2 f)
    (hsS : IsSimpleGroup (PSimple p S)) (hnaS : ∃ a b : PSimple p S, a * b ≠ b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : PSimple p S ≃* matrixDerived Q) (A : matrixDerived Q) (g : similarityPairs Q)
    (hσ : (g : coordinateSemilinearGroup d K).right ≠ 1)
    (hσp : (g : coordinateSemilinearGroup d K).right ^ p = 1)
    (hAx : ∀ q q' : PQuot p S, indRel p S x q q' → e (q' : PSimple p S) = A * e q * A⁻¹)
    (hgy : ∀ q q' : PQuot p S, indRel p S y q q' → e (q' : PSimple p S) = conjAct Q g (e q)) :
    FieldOn p y J := by
  obtain ⟨x', hx', B, ρ, hρs, hρk, hρy, hcase⟩ :=
    orth_core_block hp hp2 hSp hxp hxN hJ ht hmodel hsS hnaS hQ hT e A g hAx hgy
  rcases hcase with ⟨h, hh, hne1, hq, rfl⟩ | ⟨hlist, hBq, hBle, hBn⟩
  · exact fieldOn_of_blockData hp hp2 hJ hJy hyp ρ hρs hρk (g : coordinateSemilinearGroup d K) hσ hσp
      hρy ((hBC hp hp2 K d Q hQ x' hx').1 h hh hne1 hq)
  · rcases ((hBC hp hp2 K d Q hQ x' hx').2 hlist B hBq hBle hBn).2 with hB | ⟨rfl, rfl, hψ⟩
    · exact fieldOn_of_blockData hp hp2 hJ hJy hyp ρ hρs hρk (g : coordinateSemilinearGroup d K) hσ
        hσp hρy hB
    · exact hD4 K d Q hQ x' hx' hψ (g : coordinateSemilinearGroup d K) g.2 hσ hσp Ω _ J hJ y hJy
        hyp ρ hρs hρk hρy

theorem l154OmegaFld_orth_of (hOD : Y10GFldOrth.OrthLabelDict) (hBC : ∀ p, OrthBlockClass p)
    (hD4 : OrthD4Fact) : L154OmegaFld l154Orth := by
  intro p hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ hInn hF hJ hJy
  obtain ⟨m, K, _, _, _, e, A, g, hm4, ⟨f, hmodel⟩, hsS, hnaS, hσ, hσp, hAx, hgy⟩ :=
    orth_plus_marking_data hOD hp hQ hInn hF
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus m K (by omega)
  exact orth_core_fieldOn (hBC p) hD4 hp hp2 hSp hxp hyp (hInn.1 (Subgroup.mem_zpowers x)) hJ hJy
    (Or.inl rfl) hmodel hsS hnaS hnd hT e A g hσ hσp hAx hgy

theorem l154OmegaFld_twOrth_of (hOD : Y10GFldOrth.OrthLabelDict) (hBC : ∀ p, OrthBlockClass p)
    (hD4 : OrthD4Fact) : L154OmegaFld l154TwOrth := by
  intro p hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ hInn hF hJ hJy
  obtain ⟨m, K, _, _, _, hm4, b, c, hirr, e, A, g, ⟨f, hmodel⟩, hsS, hnaS, hσ, hσp, hAx, hgy⟩ :=
    orth_minus_marking_data hOD hp hp2 hQ hInn hF
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus m K b c hm4 hirr
  exact orth_core_fieldOn (hBC p) hD4 hp hp2 hSp hxp hyp (hInn.1 (Subgroup.mem_zpowers x)) hJ hJy
    (Or.inr rfl) hmodel hsS hnaS hnd hT e A g hσ hσp hAx hgy

end CoreCerts

@[expose] def L154OmegaNT (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω) (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (PSimple p S) →
    catalogIs (PSimple p S) Q → x ^ p = 1 → y ^ p = 1 → x * y = y * x →
    InnDiagOn p (Subgroup.zpowers x) S → FieldOn p y S →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J → y ∈ Subgroup.normalizer (J : Set Ω) →
    NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J)

section Transfer

open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.T156 CFSG.LocalAnalysis.GLTheoremA.S267
  CFSG.LocalAnalysis.GLTheoremA.T158

theorem l154NIDOn_and_TD4On_of_omegaNT {Q : TauCeti.CFSGIndex → Prop} (hΩ : L154OmegaNT Q) :
    L154NIDOn Q ∧ L154TD4On Q := by
  have key : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (X K J : Subgroup Γ) (x y : Γ),
      CFSG.Open.IsKGroup ↥X → GLAPComponent p X K → IsChevSimple 2 (PSimple p K) →
      catalogIs (PSimple p K) Q → x ∈ X → x ^ p = 1 → y ^ p = 1 → x * y = y * x → y ∉ Subgroup.zpowers x →
      x ∈ Subgroup.normalizer (K : Set Γ) → y ∈ Subgroup.normalizer (K : Set Γ) → ¬ CentMod p K x →
      InnDiagOn p (Subgroup.zpowers x) K → FieldOn p y K →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
      y ∈ Subgroup.normalizer (J : Set Γ) → NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J) := by
    intro p hp hp2 Γ _ _ X K J x y hXk hK hc hQ hxX hxp hyp hxy hynx hN1 hN2 hcm hInn hF hJ hJy
    set H : Subgroup Γ := K ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y with hHdef
    have hK1H : K ⊔ Subgroup.zpowers x ≤ H := le_sup_left
    have hKH : K ≤ H := le_sup_left.trans hK1H
    have hxH : x ∈ H := hK1H (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hHN : H ≤ Subgroup.normalizer (K : Set Γ) :=
      sup_le (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hN1)) (Subgroup.zpowers_le.2 hN2)
    set M : Subgroup ↥H := K.subgroupOf H with hMdef
    have hMn : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
    have hN0n : (GLAPPrimeCoreOf p M).Normal := by
      have h := normalizer_le_normalizer_glaPPrimeCoreOf p M
      rw [Subgroup.normalizer_eq_top_iff.2 hMn, top_le_iff] at h
      exact Subgroup.normalizer_eq_top_iff.1 h
    haveI := hN0n
    set N0 : Subgroup ↥H := GLAPPrimeCoreOf p M with hN0def
    set π : ↥H →* ↥H ⧸ N0 := QuotientGroup.mk' N0 with hπdef
    have hN : ¬ p ∣ Nat.card π.ker := by
      rw [hπdef, QuotientGroup.ker_mk']
      exact not_dvd_card_glaPPrimeCoreOf hp _
    have hMK : M.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
    set S : Subgroup (↥H ⧸ N0) := M.map π with hSdef
    have hSn : S.Normal := hMn.map π (QuotientGroup.mk'_surjective N0)
    set eK : PQuot p K ≃* PQuot p S := compIso hp hMK π hN with heKdef
    have hqPS : CFSG.Open.IsQuasisimple (PQuot p S) :=
      (isQuasisimple_pQuot_of_glaPComponent hp hK).of_mulEquiv eK.symm
    have hSp : GLAPPrimeCore p ↥S = ⊥ := by
      have h1 : (GLAPPrimeCoreOf p M).map π = GLAPPrimeCoreOf p S := map_glaPPrimeCoreOf hp π hN M
      have h2 : (GLAPPrimeCoreOf p M).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
      have h3 : GLAPPrimeCoreOf p S = ⊥ := by rw [← h1, h2]
      exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h3
    have eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
    have hqS : CFSG.Open.IsQuasisimple ↥S := hqPS.of_mulEquiv eS.symm
    have hcS : IsChevSimple 2 (PSimple p S) := isChevSimple_congr (psimpleIso eK) hc
    have hQS : catalogIs (PSimple p S) Q := catalog_forth hp hKH hN hQ
    have hxp' : (⟨x, hxH⟩ : ↥H) ^ p = 1 := Subtype.ext hxp
    have hyp' : (⟨y, hyH⟩ : ↥H) ^ p = 1 := Subtype.ext hyp
    have hxpΩ : (π ⟨x, hxH⟩) ^ p = 1 := by rw [← map_pow, hxp', map_one]
    have hypΩ : (π ⟨y, hyH⟩) ^ p = 1 := by rw [← map_pow, hyp', map_one]
    have hcommΩ : π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext hxy)
    have hJH : J ≤ H := hJ.1.trans (inf_le_left.trans hKH)
    have hInnΩ := innDiagOn_forth hp hKH hN hxH hInn
    have hFΩ := fieldOn_forth hp hKH hN hyH hN2 hF
    have hJΩ := glaPComponent_forth hp hKH hxH hN1 hxp hN hJ
    have hJyΩ : π ⟨y, hyH⟩ ∈ Subgroup.normalizer (((J.subgroupOf H).map π : Subgroup _) : Set _) :=
      map_normalizer_mem π (mem_normalizer_subgroupOf' hyH hJy)
    obtain ⟨hNID, hTD4⟩ := hΩ p hp hp2 (↥H ⧸ N0) S (π ⟨x, hxH⟩) (π ⟨y, hyH⟩) ((J.subgroupOf H).map π) hSn
      hqS hSp hcS hQS hxpΩ hypΩ hcommΩ hInnΩ hFΩ hJΩ hJyΩ
    refine ⟨nonInnDiag_back hp hJH hN hyH hJy hNID, ?_⟩
    rintro ⟨rfl, hT⟩
    exact hTD4 ⟨rfl, catalog_forth hp hJH hN hT⟩
  exact ⟨fun p hp hp2 Γ _ _ X K J x y hXk hK hc hQ hxX hxp hyp hxy hynx hN1 hN2 hcm hInn hF hJ hJy =>
      (key p hp hp2 Γ X K J x y hXk hK hc hQ hxX hxp hyp hxy hynx hN1 hN2 hcm hInn hF hJ hJy).1,
    fun p hp hp2 Γ _ _ X K J x y hXk hK hc hQ hxX hxp hyp hxy hynx hN1 hN2 hcm hInn hF hJ hJy =>
      (key p hp hp2 Γ X K J x y hXk hK hc hQ hxX hxp hyp hxy hynx hN1 hN2 hcm hInn hF hJ hJy).2⟩

end Transfer

section CoreCertsTD4

theorem orth_core_nidTd4 {p : ℕ} (hBC : OrthBlockClass p) (hp : p.Prime)
    (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ}
    (hmodel : StatedClassicalModel (PSimple p S) t m 2 f)
    (hsS : IsSimpleGroup (PSimple p S)) (hnaS : ∃ a b : PSimple p S, a * b ≠ b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : PSimple p S ≃* matrixDerived Q) (A : matrixDerived Q) (g : similarityPairs Q)
    (hσ : (g : coordinateSemilinearGroup d K).right ≠ 1)
    (hσp : (g : coordinateSemilinearGroup d K).right ^ p = 1)
    (hAx : ∀ q q' : PQuot p S, indRel p S x q q' → e (q' : PSimple p S) = A * e q * A⁻¹)
    (hgy : ∀ q q' : PQuot p S, indRel p S y q q' → e (q' : PSimple p S) = conjAct Q g (e q)) :
    NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J) := by
  obtain ⟨x', hx', B, ρ, hρs, hρk, hρy, hcase⟩ :=
    orth_core_block hp hp2 hSp hxp hxN hJ ht hmodel hsS hnaS hQ hT e A g hAx hgy
  rcases hcase with ⟨h, hh, hne1, hq, rfl⟩ | ⟨hlist, hBq, hBle, hBn⟩
  · exact nidTd4_of_blockDataW hp hp2 hJ hJy ρ hρs hρk (g : coordinateSemilinearGroup d K) hσ hσp hρy
      (orthBlockDataW_of_orthBlockData ((hBC hp hp2 K d Q hQ x' hx').1 h hh hne1 hq))
  · exact nidTd4_of_blockDataW hp hp2 hJ hJy ρ hρs hρk (g : coordinateSemilinearGroup d K) hσ hσp hρy
      ((hBC hp hp2 K d Q hQ x' hx').2 hlist B hBq hBle hBn).1

theorem l154OmegaNT_orth_of (hOD : Y10GFldOrth.OrthLabelDict) (hBC : ∀ p, OrthBlockClass p) :
    L154OmegaNT l154Orth := by
  intro p hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ hInn hF hJ hJy
  obtain ⟨m, K, _, _, _, e, A, g, hm4, ⟨f, hmodel⟩, hsS, hnaS, hσ, hσp, hAx, hgy⟩ :=
    orth_plus_marking_data hOD hp hQ hInn hF
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus m K (by omega)
  exact orth_core_nidTd4 (hBC p) hp hp2 hSp hxp (hInn.1 (Subgroup.mem_zpowers x)) hJ hJy
    (Or.inl rfl) hmodel hsS hnaS hnd hT e A g hσ hσp hAx hgy

theorem l154OmegaNT_twOrth_of (hOD : Y10GFldOrth.OrthLabelDict) (hBC : ∀ p, OrthBlockClass p) :
    L154OmegaNT l154TwOrth := by
  intro p hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ hInn hF hJ hJy
  obtain ⟨m, K, _, _, _, hm4, b, c, hirr, e, A, g, ⟨f, hmodel⟩, hsS, hnaS, hσ, hσp, hAx, hgy⟩ :=
    orth_minus_marking_data hOD hp hp2 hQ hInn hF
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus m K b c hm4 hirr
  exact orth_core_nidTd4 (hBC p) hp hp2 hSp hxp (hInn.1 (Subgroup.mem_zpowers x)) hJ hJy
    (Or.inr rfl) hmodel hsS hnaS hnd hT e A g hσ hσp hAx hgy

end CoreCertsTD4

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped commutatorElement

theorem orthRealized_of_centerQuot {G₀ : Type} [Group G₀] {J₀ : Subgroup G₀}
    (hq : CFSG.IsQuasisimple ↥J₀) {lab : LargeEvenLabel}
    (hraw : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I _ =>
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃* R) ∧ I ⊆ LargeEvenInnSet R) :
    OrthRealized lab J₀ := by
  refine Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨⟨eR⟩, hI⟩
  obtain ⟨-, hs, a, b, hab⟩ := hq
  haveI := hs
  refine ⟨eR.symm.isSimpleGroup, ⟨eR a, eR b, fun h => hab (eR.injective (by rw [map_mul, map_mul, h]))⟩,
    eR.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J₀)), ?_, ?_, ?_⟩
  · exact eR.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro ω hω
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eR.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hω
    exact hω
  · intro φ hφ
    obtain ⟨r, rfl⟩ := hI hφ
    obtain ⟨z, hz⟩ := eR.surjective r
    obtain ⟨ω₀, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨(ω₀ : G₀), fun ω hω => J₀.mul_mem (J₀.mul_mem ω₀.2 hω) (J₀.inv_mem ω₀.2), fun ω => ?_⟩
    have e1 : (⟨(ω₀ : G₀) * ω * (ω₀ : G₀)⁻¹, J₀.mul_mem (J₀.mul_mem ω₀.2 ω.2) (J₀.inv_mem ω₀.2)⟩ :
        ↥J₀) = ω₀ * ω * ω₀⁻¹ := rfl
    rw [e1, MulAut.conj_apply, ← hz]
    simp [map_mul, map_inv]

theorem orthRealized_of_inn {G₀ : Type} [Group G₀] {J₀ : Subgroup G₀} {lab : LargeEvenLabel}
    (hraw : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ I ⊆ LargeEvenInnSet R ∧
      ∃ Θ₁ : ↥J₀ →* R, Function.Surjective Θ₁ ∧ Θ₁.ker ≤ Subgroup.center ↥J₀) :
    OrthRealized lab J₀ := by
  refine Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, hI, Θ₁, hΘs, hΘk⟩
  refine ⟨hs, hna, Θ₁, hΘs, hΘk, fun φ hφ => ?_⟩
  obtain ⟨r, rfl⟩ := hI hφ
  obtain ⟨ω₀, rfl⟩ := hΘs r
  refine ⟨(ω₀ : G₀), fun ω hω => J₀.mul_mem (J₀.mul_mem ω₀.2 hω) (J₀.inv_mem ω₀.2), fun ω => ?_⟩
  have e1 : (⟨(ω₀ : G₀) * ω * (ω₀ : G₀)⁻¹, J₀.mul_mem (J₀.mul_mem ω₀.2 ω.2) (J₀.inv_mem ω₀.2)⟩ :
      ↥J₀) = ω₀ * ω * ω₀⁻¹ := rfl
  rw [e1, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem orth_ker_mk'_comp_le_center {A B : Type*} [Group A] [Group B] (e : A ≃* B) (Z : Subgroup B)
    [Z.Normal] (hZ : Z ≤ Subgroup.center B) :
    ((QuotientGroup.mk' Z).comp e.toMonoidHom).ker ≤ Subgroup.center A := by
  intro a ha
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
  refine Subgroup.mem_center_iff.2 fun g => e.injective ?_
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 (hZ ha) (e g)

theorem orth_exists_noncomm_of_surjective {A B : Type*} [Group A] [Group B] [Nontrivial B]
    (hA : Group.IsPerfect A) (f : A →* B) (hf : Function.Surjective f) : ∃ a b : B, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hB : commutator B = ⊤ :=
    orth_commutator_eq_top_of_surjective (Group.isPerfect_def.mp hA) f hf
  have hbot : commutator B = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  obtain ⟨u, hu⟩ := exists_ne (1 : B)
  apply hu
  have : u ∈ commutator B := by rw [hB]; exact Subgroup.mem_top u
  rw [hbot, Subgroup.mem_bot] at this
  exact this

section Linear

variable {E : Type} [Field E] {d : ℕ}

theorem orth_matConj_SL_sub_inn (hpow : ∀ c : E, c ≠ 0 → ∃ c' : E, c' ≠ 0 ∧ c' ^ d = c) :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) E)) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin d) E)) := by
  rintro φ ⟨P, -, hP⟩
  have hdet : (P : Matrix (Fin d) (Fin d) E).det ≠ 0 := by
    have := P.isUnit.map Matrix.detMonoidHom
    exact this.ne_zero
  obtain ⟨c, hc0, hc⟩ := hpow _ hdet
  set s : GL (Fin d) E := Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)⁻¹ with hs
  set P' : GL (Fin d) E := s * P with hP'
  have hP'mem : P' ∈ LargeEvenSLGroup (Fin d) E := by
    rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff, hP', hs, Units.val_mul,
      Matrix.det_mul]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_smul, ← hc, hc0]
  refine ⟨LargeEvenProjMk _ ⟨P', hP'mem⟩, ?_⟩
  refine MulEquiv.ext fun z => ?_
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  have hnorm : (LargeEvenSLGroup (Fin d) E).Normal := by
    rw [largeEvenSLGroup_eq_statedSL]; infer_instance
  have hmem : P * (h : GL (Fin d) E) * P⁻¹ ∈ LargeEvenSLGroup (Fin d) E := hnorm.conj_mem _ h.2 P
  have h1 := hP h ⟨_, hmem⟩ rfl
  rw [MulAut.conj_apply]
  change _ = φ (LargeEvenProjMk _ h)
  rw [h1]
  change LargeEvenProjMk _ ⟨P', hP'mem⟩ * LargeEvenProjMk _ h *
    (LargeEvenProjMk _ ⟨P', hP'mem⟩)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show P' * (h : GL (Fin d) E) * P'⁻¹ = P * (h : GL (Fin d) E) * P⁻¹
  have hsc : ∀ X : GL (Fin d) E, s * X = X * s := fun X =>
    CFSG.LieType.SemisimpleCentralizers.HeldLang.scalar_mul_comm _ X
  rw [hP', mul_inv_rev]
  calc s * P * (h : GL (Fin d) E) * (P⁻¹ * s⁻¹) = s * (P * (h : GL (Fin d) E) * P⁻¹) * s⁻¹ := by
        group
    _ = (P * (h : GL (Fin d) E) * P⁻¹) * s * s⁻¹ := by rw [hsc]
    _ = P * (h : GL (Fin d) E) * P⁻¹ := by group

theorem orth_exists_pow_two_pow {E : Type*} [Field E] [Finite E] [CharP E 2] (j : ℕ) (c : E) (hc : c ≠ 0) :
    ∃ c' : E, c' ≠ 0 ∧ c' ^ 2 ^ j = c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := iterateFrobeniusEquiv_apply E 2 j ((iterateFrobeniusEquiv E 2 j).symm c)
  rw [RingEquiv.apply_symm_apply, iterateFrobenius_def] at h
  refine ⟨(iterateFrobeniusEquiv E 2 j).symm c, ?_, h.symm⟩
  intro h0
  rw [h0, zero_pow (pow_ne_zero _ two_ne_zero)] at h
  exact hc h

end Linear

section Unitary

variable {E : Type} [Field E] [Finite E]

theorem orth_exists_norm_eq {q : ℕ} (hq : 2 ≤ q) (hE : Nat.card E = q ^ 2) {μ : E} (hμ : μ ≠ 0)
    (hμq : μ ^ q = μ) : ∃ c : E, c ≠ 0 ∧ c ^ (q + 1) = μ := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hcard : Nat.card Eˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hE]
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 μ hμ)))
  have hk' : g ^ k = Units.mk0 μ hμ := hk
  have h1 : g ^ (k * (q - 1)) = 1 := by
    rw [pow_mul, hk']
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have : μ ^ (q - 1) * μ = μ := by rw [← pow_succ, Nat.sub_add_cancel (by omega), hμq]
    exact (mul_eq_right₀ hμ).1 this
  have h2 : (q + 1) * (q - 1) ∣ k * (q - 1) := by
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h3
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rwa [this] at h3
  obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_right (by omega) h2
  refine ⟨((g ^ j : Eˣ) : E), (g ^ j).ne_zero, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm j, ← hj, hk', Units.val_mk0]

theorem orth_pow_two_pow_injective [CharP E 2] (j : ℕ) {a b : E} (h : a ^ 2 ^ j = b ^ 2 ^ j) : a = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := iterateFrobeniusEquiv_apply E 2 j a
  have h2 := iterateFrobeniusEquiv_apply E 2 j b
  rw [iterateFrobenius_def] at h1 h2
  apply (iterateFrobeniusEquiv E 2 j).injective
  rw [h1, h2, h]

theorem orth_matConj_SU_sub_inn [CharP E 2] {q f : ℕ} (hqf : q = 2 ^ f) (hf : 1 ≤ f)
    (hE : Nat.card E = q ^ 2) :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) E q)) (LargeEvenGUSet (Fin 4) E q) ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSUGroup (Fin 4) E q)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro φ ⟨A, ⟨μ, hμ0, hμq, hAμ⟩, hφ⟩
  have hq2 : 2 ≤ q := by rw [hqf]; exact Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
  set δ := (A : Matrix (Fin 4) (Fin 4) E).det with hδ
  have hδ0 : δ ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
  have hfrob : ∀ x : E, iterateFrobenius E 2 f x = x ^ q := fun x => by
    rw [iterateFrobenius_def, hqf]
  have hdetq : ((A : Matrix (Fin 4) (Fin 4) E).map (· ^ q)).det = δ ^ q := by
    have hmap : (iterateFrobenius E 2 f).mapMatrix (A : Matrix (Fin 4) (Fin 4) E) =
        (A : Matrix (Fin 4) (Fin 4) E).map (· ^ q) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      exact hfrob _
    rw [← hmap, ← RingHom.map_det, hfrob]
  have hδμ : δ ^ (q + 1) = μ ^ 4 := by
    have h1 := congrArg Matrix.det hAμ
    rw [Matrix.det_mul, Matrix.det_transpose, hdetq, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    rw [pow_succ]
    exact h1
  obtain ⟨c₀, hc₀0, hc₀⟩ := orth_exists_norm_eq hq2 hE hμ0 hμq
  set ε := δ * (c₀ ^ 4)⁻¹ with hε
  have hε0 : ε ≠ 0 := mul_ne_zero hδ0 (inv_ne_zero (pow_ne_zero _ hc₀0))
  have hεq : ε ^ (q + 1) = 1 := by
    rw [hε, mul_pow, inv_pow, hδμ, ← pow_mul, mul_comm 4, pow_mul, hc₀, mul_inv_cancel₀ (pow_ne_zero _ hμ0)]
  obtain ⟨η, hη0, hη⟩ := orth_exists_pow_two_pow 2 ε hε0
  have hη4 : η ^ 4 = ε := by simpa using hη
  have hηq : η ^ (q + 1) = 1 := by
    apply orth_pow_two_pow_injective (E := E) 2
    rw [← pow_mul, mul_comm, pow_mul, hη, hεq, one_pow]
  set c := c₀ * η with hc
  have hc0 : c ≠ 0 := mul_ne_zero hc₀0 hη0
  have hcq : c ^ (q + 1) = μ := by rw [hc, mul_pow, hc₀, hηq, mul_one]
  have hc4 : c ^ 4 = δ := by
    rw [hc, mul_pow, hη4, hε, mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hc₀0), mul_one]
  set s : GL (Fin 4) E := Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c hc0)⁻¹ with hs
  set A' : GL (Fin 4) E := s * A with hA'
  have hA'val : (A' : Matrix (Fin 4) (Fin 4) E) = c⁻¹ • (A : Matrix (Fin 4) (Fin 4) E) := by
    rw [hA', hs, Units.val_mul]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_eq_diagonal_mul]
  have hA'mem : A' ∈ LargeEvenSUGroup (Fin 4) E q := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [hA'val, Matrix.det_smul, Fintype.card_fin, inv_pow, hc4, inv_mul_cancel₀ hδ0]
    · rw [hA'val]
      have hmap : ((c⁻¹ • (A : Matrix (Fin 4) (Fin 4) E)).map (· ^ q)) =
          (c⁻¹) ^ q • (A : Matrix (Fin 4) (Fin 4) E).map (· ^ q) := by
        ext i j
        simp [mul_pow]
      rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hAμ, smul_smul, smul_smul,
        ← pow_succ, inv_pow, hcq, inv_mul_cancel₀ hμ0, one_smul]
  refine ⟨LargeEvenProjMk _ ⟨A', hA'mem⟩, MulEquiv.ext fun z => ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  have hconj : A * (h : GL (Fin 4) E) * A⁻¹ = A' * (h : GL (Fin 4) E) * A'⁻¹ := by
    have hsc : ∀ X : GL (Fin 4) E, s * X = X * s := fun X =>
      CFSG.LieType.SemisimpleCentralizers.HeldLang.scalar_mul_comm _ X
    rw [hA', mul_inv_rev]
    calc A * (h : GL (Fin 4) E) * A⁻¹ = s * (A * (h : GL (Fin 4) E) * A⁻¹) * s⁻¹ := by
          rw [hsc (A * (h : GL (Fin 4) E) * A⁻¹), mul_inv_cancel_right]
      _ = s * A * (h : GL (Fin 4) E) * (A⁻¹ * s⁻¹) := by group
  have hmem : A * (h : GL (Fin 4) E) * A⁻¹ ∈ LargeEvenSUGroup (Fin 4) E q := by
    rw [hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA'mem h.2) (Subgroup.inv_mem _ hA'mem)
  have h1 := hφ h ⟨_, hmem⟩ rfl
  rw [MulAut.conj_apply]
  change _ = φ (LargeEvenProjMk _ h)
  rw [h1]
  change LargeEvenProjMk _ ⟨A', hA'mem⟩ * LargeEvenProjMk _ h * (LargeEvenProjMk _ ⟨A', hA'mem⟩)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact hconj.symm

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open QuadraticMap
open scoped commutatorElement

section Torus

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def orthTorusLin (Q : QuadraticForm K V) (e f : V) (t : K) : V →ₗ[K] V :=
  LinearMap.id + (t - 1) • ((polarBilin Q).flip f).smulRight e +
    (t⁻¹ - 1) • ((polarBilin Q).flip e).smulRight f

theorem orthTorusLin_apply (e f : V) (t : K) (v : V) :
    orthTorusLin Q e f t v = v + ((t - 1) * polar Q v f) • e + ((t⁻¹ - 1) * polar Q v e) • f := by
  simp [orthTorusLin, mul_smul]

variable {e f : V} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1)
include he hf hef

theorem orthTorusLin_polar_f (t : K) (v : V) : polar Q (orthTorusLin Q e f t v) f = t * polar Q v f := by
  rw [orthTorusLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hef,
    CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hf]
  ring

theorem orthTorusLin_polar_e (t : K) (v : V) (ht : t ≠ 0) :
    polar Q (orthTorusLin Q e f t v) e = t⁻¹ * polar Q v e := by
  rw [orthTorusLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_comm Q f e, hef, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero he]
  ring

theorem orthTorusLin_comp {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) (v : V) :
    orthTorusLin Q e f s (orthTorusLin Q e f t v) = orthTorusLin Q e f (s * t) v := by
  rw [orthTorusLin_apply e f s, orthTorusLin_polar_f he hf hef, orthTorusLin_polar_e he hf hef t v ht,
    orthTorusLin_apply, orthTorusLin_apply, mul_inv]
  have h1 : (s - 1) * (t * polar Q v f) = (s * t - 1 - (t - 1)) * polar Q v f := by ring
  have h2 : (s⁻¹ - 1) * (t⁻¹ * polar Q v e) = (t⁻¹ * s⁻¹ - 1 - (t⁻¹ - 1)) * polar Q v e := by ring
  rw [h1, h2]
  module

theorem orthTorusLin_one (v : V) : orthTorusLin Q e f 1 v = v := by
  rw [orthTorusLin_apply]
  simp

theorem orthTorusLin_isometry {t : K} (ht : t ≠ 0) (v : V) : Q (orthTorusLin Q e f t v) = Q v := by
  rw [orthTorusLin_apply, QuadraticMap.map_add (⇑Q), QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul,
    QuadraticMap.map_smul, he, hf, smul_zero, smul_zero, add_zero, add_zero, polar_add_left,
    polar_smul_right, polar_smul_right, polar_smul_left, polar_smul_right, hef]
  have key : (t - 1) + (t⁻¹ - 1) + (t - 1) * (t⁻¹ - 1) = 0 := by field_simp; ring
  linear_combination (polar Q v e * polar Q v f) * key

@[expose] noncomputable def orthTorus (t : Kˣ) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (orthTorusLin Q e f (t : K)) (orthTorusLin Q e f ((t⁻¹ : Kˣ) : K))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, orthTorusLin_comp he hf hef t.ne_zero (t⁻¹).ne_zero, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, orthTorusLin_one he hf hef]
      rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, orthTorusLin_comp he hf hef (t⁻¹).ne_zero t.ne_zero, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, orthTorusLin_one he hf hef]
      rfl)

theorem orthTorus_apply (t : Kˣ) (v : V) :
    orthTorus he hf hef t v = v + (((t : K) - 1) * polar Q v f) • e + (((t : K)⁻¹ - 1) * polar Q v e) • f :=
  orthTorusLin_apply (Q := Q) e f (t : K) v

theorem orthTorus_mul (s t : Kˣ) : orthTorus he hf hef s * orthTorus he hf hef t = orthTorus he hf hef (s * t) :=
  LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply]
    exact orthTorusLin_comp he hf hef s.ne_zero t.ne_zero v

theorem orth_Q_add_ef : Q (e + f) = 1 := by
  rw [QuadraticMap.map_add (⇑Q), he, hf, hef]
  ring

theorem orth_reflect_torus_reflect (t : Kˣ) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q (e + f) * orthTorus he hf hef t *
      CFSG.ClassicalGroups.Orthogonal.reflect Q (e + f) = orthTorus he hf hef t⁻¹ := by
  have hQ1 : Q (e + f) ≠ 0 := by rw [orth_Q_add_ef he hf hef]; exact one_ne_zero
  set r := CFSG.ClassicalGroups.Orthogonal.reflect Q (e + f) with hr
  have hrv : ∀ v, r v = v - (polar Q e v + polar Q f v) • (e + f) := by
    intro v
    rw [hr, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQ1, orth_Q_add_ef he hf hef, div_one,
      polar_add_left]
  have hre : r e = -f := by
    rw [hrv, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero he, polar_comm Q f e, hef]
    simp
  have hrf : r f = -e := by
    rw [hrv, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hf, hef]
    simp
  have hrr : ∀ v, r (r v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hr, CFSG.ClassicalGroups.Orthogonal.reflect_mul_self]
    rfl
  have hpe : ∀ v, polar Q (r v) e = -polar Q v f := by
    intro v
    rw [hrv, polar_sub_left, polar_smul_left, polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero he,
      polar_comm Q f e, hef, polar_comm Q e v, polar_comm Q f v]
    ring
  have hpf : ∀ v, polar Q (r v) f = -polar Q v e := by
    intro v
    rw [hrv, polar_sub_left, polar_smul_left, polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hf,
      hef, polar_comm Q e v, polar_comm Q f v]
    ring
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, orthTorus_apply, map_add, map_add, map_smul, map_smul,
    hrr, hre, hrf, hpe, hpf, orthTorus_apply, Units.val_inv_eq_inv_val, inv_inv]
  module

theorem orth_commutator_torus_reflect (μ : Kˣ) :
    ⁅orthTorus he hf hef μ, CFSG.ClassicalGroups.Orthogonal.reflect Q (e + f)⁆ = orthTorus he hf hef (μ * μ) := by
  have h1 : (orthTorus he hf hef μ)⁻¹ = orthTorus he hf hef μ⁻¹ := by
    rw [inv_eq_iff_mul_eq_one, orthTorus_mul, mul_inv_cancel]
    exact LinearEquiv.ext fun v => by rw [orthTorus_apply]; simp
  rw [commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv, h1, mul_assoc, mul_assoc,
    ← mul_assoc (CFSG.ClassicalGroups.Orthogonal.reflect Q (e + f)), orth_reflect_torus_reflect, inv_inv,
    orthTorus_mul]

theorem orthTorus_trace [FiniteDimensional K V] (t : Kˣ) :
    LinearMap.trace K V ((orthTorus he hf hef t : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (Module.finrank K V : K) + ((t : K) - 1) + ((t : K)⁻¹ - 1) := by
  change LinearMap.trace K V (orthTorusLin Q e f (t : K)) = _
  rw [orthTorusLin, map_add, map_add, map_smul, map_smul, LinearMap.trace_id, LinearMap.trace_smulRight,
    LinearMap.trace_smulRight, LinearMap.flip_apply, LinearMap.flip_apply, polarBilin_apply_apply,
    polarBilin_apply_apply, hef, polar_comm Q f e, hef, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

end Torus

section FixedTrace

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_polar_fixed_others (hx : OddOrderIsometry Q p x) {w r : V} (hw : w ∈ fixedSpace x)
    (hr : r ∈ othersSpace x.toLinearMap (Polynomial.X - 1)) : polar Q r w = 0 := by
  rw [polar_comm]
  exact hx.fixed_others.2 w hw r hr

theorem orthTorus_mem_supportedBlock (hx : OddOrderIsometry Q p x) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hef : polar Q e f = 1) (heW : e ∈ fixedSpace x) (hfW : f ∈ fixedSpace x)
    (t : Kˣ) : orthTorus he hf hef t ∈ supportedBlock Q x (Polynomial.X - 1) := by
  have hxe : x e = e := mem_fixedSpace.1 heW
  have hxf : x f = f := mem_fixedSpace.1 hfW
  refine mem_supportedBlock.2 ⟨mem_isometryCentralizer.2 ⟨fun v => orthTorusLin_isometry he hf hef t.ne_zero v,
    fun v => ?_⟩, fun r hr => ?_⟩
  · rw [orthTorus_apply, orthTorus_apply, map_add, map_add, map_smul, map_smul, hxe, hxf,
      hx.polar_apply v, hx.polar_apply v]
    have h1 : x.symm f = f := by rw [LinearEquiv.symm_apply_eq, hxf]
    have h2 : x.symm e = e := by rw [LinearEquiv.symm_apply_eq, hxe]
    rw [h1, h2]
  · rw [orthTorus_apply, orth_polar_fixed_others hx heW hr, orth_polar_fixed_others hx hfW hr]
    simp

theorem orth_reflect_mem_supportedBlock (hx : OddOrderIsometry Q p x) {u : V} (huW : u ∈ fixedSpace x) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q u ∈ supportedBlock Q x (Polynomial.X - 1) := by
  have hxu : x u = u := mem_fixedSpace.1 huW
  refine mem_supportedBlock.2 ⟨mem_isometryCentralizer.2
    ⟨fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q u)) v, fun v => ?_⟩, fun r hr => ?_⟩
  · have h1 := CFSG.ClassicalGroups.Orthogonal.reflect_conj hx.mem u
    rw [hxu] at h1
    have h2 : CFSG.ClassicalGroups.Orthogonal.reflect Q u * x = x * CFSG.ClassicalGroups.Orthogonal.reflect Q u :=
      (mul_inv_eq_iff_eq_mul.1 h1).symm
    exact congrArg (fun g : V ≃ₗ[K] V => g v) h2
  · exact CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      (by rw [polar_comm]; exact orth_polar_fixed_others hx huW hr)

theorem orthTorus_sq_mem_supportedFixedDerived (hx : OddOrderIsometry Q p x) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hef : polar Q e f = 1) (heW : e ∈ fixedSpace x) (hfW : f ∈ fixedSpace x)
    (μ : Kˣ) : orthTorus he hf hef (μ * μ) ∈ supportedFixedDerived Q x := by
  rw [hx.supportedFixedDerived_eq, ← orth_commutator_torus_reflect he hf hef μ]
  exact Subgroup.commutator_mem_commutator (orthTorus_mem_supportedBlock hx he hf hef heW hfW μ)
    (orth_reflect_mem_supportedBlock hx (Submodule.add_mem _ heW hfW))

theorem orth_trace_witness_fixed [Finite K] [CharP K 2] (hx : OddOrderIsometry Q p x) {e f : V}
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) (heW : e ∈ fixedSpace x)
    (hfW : f ∈ fixedSpace x) (hev : Even (Module.finrank K V)) (l : K) (hl : l ≠ 0) :
    ∃ ω ∈ supportedFixedDerived Q x,
      LinearMap.trace K V ((ω : V ≃ₗ[K] V) : V →ₗ[K] V) = l + l⁻¹ := by
  obtain ⟨μ, hμ0, hμ⟩ := orth_exists_pow_two_pow 1 l hl
  refine ⟨_, orthTorus_sq_mem_supportedFixedDerived hx he hf hef heW hfW (Units.mk0 μ hμ0), ?_⟩
  rw [orthTorus_trace]
  obtain ⟨k, hk⟩ := hev
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hl' : ((Units.mk0 μ hμ0 * Units.mk0 μ hμ0 : Kˣ) : K) = l := by
    rw [Units.val_mul, Units.val_mk0, ← _root_.sq]
    simpa using hμ
  rw [hl', hk]
  push_cast
  linear_combination (k : K) * h2 - h2

end FixedTrace

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)

open QuadraticMap

section StatedBridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def orthStatedOmegaEquiv {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) : StatedOmega Q₀ ≃* orthDerived Q :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ]
      exact Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _))

theorem orth_statedScalars_subgroupOf_le_center (H : Subgroup (GL ι K)) :
    (StatedScalars ι K).subgroupOf H ≤ Subgroup.center ↥H := by
  intro z hz
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
  show (g : GL ι K) * z = z * g
  rw [← hc]
  exact (CFSG.LieType.SemisimpleCentralizers.HeldLang.scalar_mul_comm c (g : GL ι K)).symm

end StatedBridge

section LargeFixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orthRealized_fixed_plus (hx : OddOrderIsometry Q p x) {s f : ℕ} (hs4 : 4 ≤ s)
    (hK : Nat.card K = 2 ^ f)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus s K))
    (hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x)) :
    OrthRealized ⟨.D, s, f⟩ (supportedFixedDerived Q x) := by
  set e : ↥(supportedFixedDerived Q x) ≃* StatedOmega (StatedQuadPlus s K) :=
    ((supportedFixedDerivedEquiv hx).trans (CFSG.RankThree.PartOne.orthDerivedEquiv ψ)).trans
      (orthStatedOmegaEquiv (coe_quadPlus s K)).symm with he
  refine orthRealized_of_inn ?_
  unfold CFSG.Assembly.LargeEvenRawDatum
  simp only [show s ≠ 3 by omega, ↓reduceIte]
  unfold LargeEvenRecipeOmegaPlus
  haveI hsimp : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K s))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
  set Θ₁ : ↥(supportedFixedDerived Q x) →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K s)) :=
    (QuotientGroup.mk' _).comp e.toMonoidHom with hΘ₁
  have hΘs : Function.Surjective Θ₁ := (QuotientGroup.mk'_surjective _).comp e.surjective
  exact ⟨K, inferInstance, inferInstance, hK, hsimp, orth_exists_noncomm_of_surjective hq.1 Θ₁ hΘs,
    subset_rfl, Θ₁, hΘs, orth_ker_mk'_comp_le_center e _ (orth_statedScalars_subgroupOf_le_center _)⟩

theorem orthRealized_fixed_minus (hx : OddOrderIsometry Q p x) {s f : ℕ} (hs4 : 4 ≤ s)
    (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadMinus s K b c))
    (hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x)) :
    OrthRealized ⟨.twD, s, f⟩ (supportedFixedDerived Q x) := by
  set e : ↥(supportedFixedDerived Q x) ≃* StatedOmega (StatedQuadMinus s K b c) :=
    ((supportedFixedDerivedEquiv hx).trans (CFSG.RankThree.PartOne.orthDerivedEquiv ψ)).trans
      (orthStatedOmegaEquiv (coe_quadMinus s K b c)).symm with he
  refine orthRealized_of_inn ?_
  unfold CFSG.Assembly.LargeEvenRawDatum
  simp only [show s ≠ 3 by omega, show s ≠ 2 by omega, ↓reduceIte]
  unfold LargeEvenRecipeOmegaMinus
  haveI hsimp' : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus s K b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hs4 hirr
  haveI hsimp : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (s - 1) b c))) :=
    (omegaMinusProjEquiv s b c).isSimpleGroup
  set Θ₁ : ↥(supportedFixedDerived Q x) →* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (s - 1) b c)) :=
    (omegaMinusProjEquiv s b c).symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp e.toMonoidHom) with hΘ₁
  have hΘs : Function.Surjective Θ₁ :=
    (omegaMinusProjEquiv s b c).symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.surjective)
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hirr, hsimp,
    orth_exists_noncomm_of_surjective hq.1 Θ₁ hΘs, subset_rfl, Θ₁, hΘs, ?_⟩
  intro ω hω
  apply orth_ker_mk'_comp_le_center e _ (orth_statedScalars_subgroupOf_le_center _)
  rw [MonoidHom.mem_ker] at hω ⊢
  exact (map_eq_one_iff _ (omegaMinusProjEquiv s b c).symm.injective).1 hω

end LargeFixed

end CFSG.LocalAnalysis.GLTheoremA.K155XOr
