module

public import CFSG.CGT.PushingUpLit.CGT6.Props
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoOff

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin
open scoped commutatorElement

theorem eq_bot_of_isPGroup_normal_sl2 {n : ℕ} (hn : 2 ≤ n)
    {N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Fq n))} [N.Normal] (hN : IsPGroup 2 ↥N) :
    N = ⊥ := by
  have := isSimpleGroup_sl2_gf hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hS : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) (Fq n)) := by
      intro g
      obtain ⟨k, hk⟩ := hN ⟨g, by rw [h]; trivial⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hc := hS.center_nontrivial
    have := (Subgroup.nontrivial_iff_ne_bot _).mp hc
    exact this (center_sl2_eq_bot (Fq n))

theorem isPGroup_map_two {A B : Type*} [Group A] [Group B] {N : Subgroup A} (hN : IsPGroup 2 ↥N)
    (f : A →* B) : IsPGroup 2 ↥(N.map f) := by
  rintro ⟨_, ⟨n, hn, rfl⟩⟩
  obtain ⟨k, hk⟩ := hN ⟨n, hn⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun z : ↥N => f (z : A)) hk
  simpa [← map_pow] using this

theorem eq_bot_of_isPGroup_normal_sl2_prod {n : ℕ} (hn : 2 ≤ n)
    {N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Fq n) ×
      Matrix.SpecialLinearGroup (Fin 2) (Fq n))} [hNn : N.Normal] (hN : IsPGroup 2 ↥N) : N = ⊥ := by
  have h1 : N.map (MonoidHom.fst _ _) = ⊥ := by
    have : (N.map (MonoidHom.fst _ _)).Normal := hNn.map _ Prod.fst_surjective
    exact eq_bot_of_isPGroup_normal_sl2 hn (isPGroup_map_two hN _)
  have h2 : N.map (MonoidHom.snd _ _) = ⊥ := by
    have : (N.map (MonoidHom.snd _ _)).Normal := hNn.map _ Prod.snd_surjective
    exact eq_bot_of_isPGroup_normal_sl2 hn (isPGroup_map_two hN _)
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hab
  have ha : a ∈ N.map (MonoidHom.fst _ _) := ⟨(a, b), hab, rfl⟩
  have hb : b ∈ N.map (MonoidHom.snd _ _) := ⟨(a, b), hab, rfl⟩
  rw [h1, Subgroup.mem_bot] at ha
  rw [h2, Subgroup.mem_bot] at hb
  rw [Subgroup.mem_bot, ha, hb]
  rfl

theorem pCore_le_ker_of_surjective {L S : Type} [Group L] [Finite L] [Group S] (φ : L →* S)
    (hφ : Function.Surjective φ)
    (hS : ∀ N : Subgroup S, N.Normal → IsPGroup 2 ↥N → N = ⊥) : pCore 2 L ≤ φ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pCore 2 L).Normal := pCore_normal
  have : ((pCore 2 L).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have h := hS _ inferInstance (isPGroup_map_two pCore_isPGroup φ)
  intro z hz
  have : φ z ∈ (pCore 2 L).map φ := ⟨z, hz, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact this

section Components

variable {Γ : Type*} [Group Γ]

theorem normal_range_inl (A B : Type*) [Group A] [Group B] : (MonoidHom.inl A B).range.Normal :=
  ⟨by
    rintro _ ⟨a, rfl⟩ g
    exact ⟨g.1 * a * g.1⁻¹, by ext <;> simp⟩⟩

theorem normal_range_inr (A B : Type*) [Group A] [Group B] : (MonoidHom.inr A B).range.Normal :=
  ⟨by
    rintro _ ⟨b, rfl⟩ g
    exact ⟨g.2 * b * g.2⁻¹, by ext <;> simp⟩⟩

theorem isComponentOf_map_range_inl {Gb E : Subgroup Γ} {A B : Type*} [Group A] [Group B]
    (hE : E ≤ Gb) (hsub : CFSG.Open.IsSubnormal E Gb) (θ : ↥E ≃* A × B)
    (hA : CFSG.Open.IsQuasisimple A) :
    CFSG.Open.IsComponentOf
      (((MonoidHom.inl A B).range.map θ.symm.toMonoidHom).map E.subtype) Gb := by
  have hn := normal_range_inl A B
  have hK₁n : ((MonoidHom.inl A B).range.map θ.symm.toMonoidHom).Normal :=
    hn.map _ θ.symm.surjective
  refine ⟨(Subgroup.map_subtype_le _).trans hE, ?_, ?_⟩
  · refine CFSG.Open.IsSubnormal.step (Subgroup.map_subtype_le _) ?_ hsub
    have : (((MonoidHom.inl A B).range.map θ.symm.toMonoidHom).map E.subtype).subgroupOf E =
        (MonoidHom.inl A B).range.map θ.symm.toMonoidHom :=
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
    rw [this]
    exact hK₁n
  · let e : A ≃* ↥(((MonoidHom.inl A B).range.map θ.symm.toMonoidHom).map E.subtype) :=
      (MonoidHom.ofInjective
        (fun a b h => congrArg Prod.fst h : Function.Injective (MonoidHom.inl A B))).trans
        ((MulEquiv.subgroupMap θ.symm (MonoidHom.inl A B).range).trans
          (Subgroup.equivMapOfInjective _ E.subtype E.subtype_injective))
    exact isQuasisimple_of_mulEquiv' e hA

theorem isComponentOf_map_range_inr {Gb E : Subgroup Γ} {A B : Type*} [Group A] [Group B]
    (hE : E ≤ Gb) (hsub : CFSG.Open.IsSubnormal E Gb) (θ : ↥E ≃* A × B)
    (hB : CFSG.Open.IsQuasisimple B) :
    CFSG.Open.IsComponentOf
      (((MonoidHom.inr A B).range.map θ.symm.toMonoidHom).map E.subtype) Gb := by
  have hn := normal_range_inr A B
  have hK₂n : ((MonoidHom.inr A B).range.map θ.symm.toMonoidHom).Normal :=
    hn.map _ θ.symm.surjective
  refine ⟨(Subgroup.map_subtype_le _).trans hE, ?_, ?_⟩
  · refine CFSG.Open.IsSubnormal.step (Subgroup.map_subtype_le _) ?_ hsub
    have : (((MonoidHom.inr A B).range.map θ.symm.toMonoidHom).map E.subtype).subgroupOf E =
        (MonoidHom.inr A B).range.map θ.symm.toMonoidHom :=
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
    rw [this]
    exact hK₂n
  · let e : B ≃* ↥(((MonoidHom.inr A B).range.map θ.symm.toMonoidHom).map E.subtype) :=
      (MonoidHom.ofInjective
        (fun a b h => congrArg Prod.snd h : Function.Injective (MonoidHom.inr A B))).trans
        ((MulEquiv.subgroupMap θ.symm (MonoidHom.inr A B).range).trans
          (Subgroup.equivMapOfInjective _ E.subtype E.subtype_injective))
    exact isQuasisimple_of_mulEquiv' e hB

theorem exists_mul_of_prod_equiv {E : Subgroup Γ} {A B : Type*} [Group A] [Group B]
    (θ : ↥E ≃* A × B) {e : Γ} (he : e ∈ E) :
    ∃ k₁ ∈ ((MonoidHom.inl A B).range.map θ.symm.toMonoidHom).map E.subtype,
      ∃ k₂ ∈ ((MonoidHom.inr A B).range.map θ.symm.toMonoidHom).map E.subtype, e = k₁ * k₂ := by
  set p := θ ⟨e, he⟩ with hp
  have h : (⟨e, he⟩ : ↥E) =
      θ.symm (MonoidHom.inl A B p.1) * θ.symm (MonoidHom.inr A B p.2) := by
    rw [← map_mul]
    have : MonoidHom.inl A B p.1 * MonoidHom.inr A B p.2 = p := by ext <;> simp
    rw [this, hp, MulEquiv.symm_apply_apply]
  refine ⟨(θ.symm (MonoidHom.inl A B p.1) : Γ),
    ⟨_, ⟨_, ⟨p.1, rfl⟩, rfl⟩, rfl⟩, (θ.symm (MonoidHom.inr A B p.2) : Γ),
    ⟨_, ⟨_, ⟨p.2, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  have := congrArg Subtype.val h
  simpa using this

theorem le_normalizer_of_components {E K₁ K₂ Ao : Subgroup Γ} (hK₁ : K₁ ≤ E) (hK₂ : K₂ ≤ E)
    (hdec : ∀ e ∈ E, ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, e = k₁ * k₂)
    (h₁ : Ao ≤ Subgroup.normalizer (K₁ : Set Γ)) (h₂ : Ao ≤ Subgroup.normalizer (K₂ : Set Γ)) :
    Ao ≤ Subgroup.normalizer (E : Set Γ) := by
  have key : ∀ g ∈ Ao, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hdec e he
    have e1 : g * (k₁ * k₂) * g⁻¹ = (g * k₁ * g⁻¹) * (g * k₂ * g⁻¹) := by group
    rw [e1]
    exact E.mul_mem (hK₁ ((Subgroup.mem_normalizer_iff.mp (h₁ hg) k₁).mp hk₁))
      (hK₂ ((Subgroup.mem_normalizer_iff.mp (h₂ hg) k₂).mp hk₂))
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => key g hg e he, fun hge => ?_⟩
  have := key g⁻¹ (Ao.inv_mem hg) _ hge
  simpa [mul_assoc] using this

end Components

section Data

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_autOn_equiv {V X W : Subgroup G} {S M : Type*} [Group S] [Group M]
    {act : S → M → M} (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hnat : IsNatBy act X W)
    (hker : X ⊓ Subgroup.centralizer (V : Set G) = X ⊓ Subgroup.centralizer (W : Set G)) :
    ∃ (φ : ↥X →* S) (θ : ↥(autOn X V) ≃* S), Function.Surjective φ ∧
      φ.ker = (X ⊓ Subgroup.centralizer (W : Set G)).subgroupOf X ∧
      ∀ g : ↥X, θ (actOnRange V X hXV g) = φ g := by
  obtain ⟨φ, ψ, hφs, hφk, -⟩ := hnat
  have hρs := actOnRange_surjective V X hXV
  have hkerEq : (actOnRange V X hXV).ker = φ.ker := by
    rw [ker_actOnRange, hφk, hker]
  let θ : ↥(autOn X V) ≃* S :=
    (QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφs))
  refine ⟨φ, θ, hφs, hφk, fun g => ?_⟩
  show (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
      ((QuotientGroup.quotientMulEquivOfEq hkerEq)
        ((QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm
          (actOnRange V X hXV g))) = φ g
  have : (QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm (actOnRange V X hXV g) =
      (QuotientGroup.mk g : ↥X ⧸ (actOnRange V X hXV).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

theorem exists_finset_card_four {n : ℕ} (hn : 2 ≤ n) : ∃ s : Finset (Fq n), s.card = 4 := by
  classical
  have : Fintype (Fq n) := Fintype.ofFinite _
  have hcard : 4 ≤ Fintype.card (Fq n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fq n)))
    (n := 4) (by simpa using hcard)
  exact ⟨s, hs⟩

theorem omega_data {V X : Subgroup G} [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V)
    (hXs : X.IsSubnormal) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNatBy (omegaPlusAct n) X ⁅X, V⁆ ∨ IsNatBy (omegaMinusAct n) X ⁅X, V⁆)
    (hker : X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G) ≤
      Subgroup.centralizer (V : Set G)) :
    oTwoIn X ≤ Subgroup.centralizer (V : Set G) ∧
      ∀ A : Subgroup G, IsOffG V A →
        autOn A V ≤ Subgroup.normalizer (autOn X V : Set (MulAut ↥V)) := by
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  have hWV : (⁅X, V⁆ : Subgroup G) ≤ V := Subgroup.commutator_le_right X V
  have hker' : X ⊓ Subgroup.centralizer (V : Set G) =
      X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G) :=
    le_antisymm (inf_le_inf_left X (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWV)))
      (le_inf inf_le_left hker)
  have hpc : ∀ {S : Type} [Group S] (φ : ↥X →* S),
      pCore 2 ↥X ≤ φ.ker →
      φ.ker = (X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G)).subgroupOf X →
      oTwoIn X ≤ Subgroup.centralizer (V : Set G) := by
    intro S _ φ hle hk z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have h1 := hle hz'
    rw [hk, Subgroup.mem_subgroupOf] at h1
    exact hker h1
  have hsub : CFSG.Open.IsSubnormal (autOn X V) (autOn ⊤ V) := autOn_isSubnormal hXs
  have hEG : autOn X V ≤ autOn ⊤ V := autOn_le_autOn V le_top
  refine ⟨?_, fun A hA => ?_⟩
  · rcases hnat with hplus | hminus
    · obtain ⟨φ, θ, hφs, hφk, -⟩ := exists_autOn_equiv hXV hplus hker'
      exact hpc φ (pCore_le_ker_of_surjective φ hφs (fun N hN hNp => by
        have := hN
        exact eq_bot_of_isPGroup_normal_sl2_prod hn hNp)) hφk
    · obtain ⟨φ, θ, hφs, hφk, -⟩ := exists_autOn_equiv hXV hminus hker'
      exact hpc φ (pCore_le_ker_of_surjective φ hφs (fun N hN hNp => by
        have := hN
        exact eq_bot_of_isPGroup_normal_sl2 (by omega) hNp)) hφk
  · have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1
    let _ : CommGroup ↥V := commGroupOfElemAbelian hV
    have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
    have hoff : IsOff (autOn A V) := (isOffG_iff_isOff_autOn hV hAN).mp hA
    have hAG : autOn A V ≤ autOn ⊤ V := autOn_le_autOn V le_top
    rcases hnat with hplus | hminus
    · obtain ⟨φ, θ, -⟩ := exists_autOn_equiv hXV hplus hker'
      have hq := isQuasisimple_special_linear_two (F := Fq n) (exists_finset_card_four hn)
      have h1 := offender_le_normalizer_of_isComponentOf hV2 hoff hAG
        (isComponentOf_map_range_inl hEG hsub θ hq)
      have h2 := offender_le_normalizer_of_isComponentOf hV2 hoff hAG
        (isComponentOf_map_range_inr hEG hsub θ hq)
      exact le_normalizer_of_components (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
        (fun e he => exists_mul_of_prod_equiv θ he) h1 h2
    · obtain ⟨φ, θ, -⟩ := exists_autOn_equiv hXV hminus hker'
      have hq := isQuasisimple_special_linear_two (F := Fq (2 * n))
        (exists_finset_card_four (by omega))
      exact offender_le_normalizer_of_isComponentOf hV2 hoff hAG
        ⟨hEG, hsub, isQuasisimple_of_mulEquiv' θ.symm hq⟩

end Data

theorem sixTwoOmegaInput_of_twoEight (h28 : AschbacherTwoEight) :
    ∀ (G : Type) [Group G] [Finite G] (V Y X : Subgroup G) [V.Normal],
      CFSG.Open.IsElemAbelian 2 V → OmegaFourOutcome V Y X → Y ≤ X → X.IsSubnormal →
        Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (X : Set G) →
        IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) →
        Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y → InClassX ↥Y →
        ¬ Y ≤ Subgroup.centralizer (V : Set G) →
          XCtx V Y X ∧ (∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G)) ∧
            ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X := by
  intro G _ _ V Y X _ hV hΩ hYX hXs hCX hN0 hCY hY _
  obtain ⟨hres, hperf, n, hn2, hnat, hC0, hker, -⟩ := hΩ
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  have hWV : (⁅X, V⁆ : Subgroup G) ≤ V := Subgroup.commutator_le_right X V
  have hker' : X ⊓ Subgroup.centralizer (V : Set G) =
      X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G) :=
    le_antisymm (inf_le_inf_left X (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWV)))
      (le_inf inf_le_left hker)
  obtain ⟨hO2, hcomp⟩ := omega_data hV hXs hn2 hnat hker
  have hNoY := SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq
  have hNoX := SubTwo.noTwoQuotient_of_oResidualTwo hres
  have hP : PerfCtx V Y X :=
    { hYX := hYX, hXs := hXs, hNoY := hNoY, hNoX := hNoX, hperf := hperf, hCX := hCX,
      hN0 := hN0, hOX := (blockU_le_oTwoIn X).trans hO2, hCY := hCY }
  have hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G) :=
    fun A hA => le_normalizer_of_autOn_le_normalizer hP hA.1 (hcomp A hA)
  refine ⟨hP.toXCtx, hP1, fun A hA => ?_⟩
  by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
  ·
    refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
    refine hP.inf_le_oTwoIn (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [commutatorElement_def]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCX (hAC ha)) x).mp hx) (X.inv_mem hx)
    · have hCn : (Subgroup.centralizer (V : Set G)).Normal := inferInstance
      have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (Subgroup.centralizer (V : Set G)).mul_mem (hAC ha)
        (hCn.conj_mem _ ((Subgroup.centralizer (V : Set G)).inv_mem (hAC ha)) x)
  · have hOff : IsOffG V A := isOffG_of_isMaxElemAbelian hV le_top (by
      rw [Subgroup.normalizer_eq_top V]) hA hAC
    have hAN : A ≤ Subgroup.normalizer (X : Set G) := hP1 A hOff
    let _ : CommGroup ↥V := commGroupOfElemAbelian hV
    have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
    have hoff : IsOff (autOn A V) := (isOffG_iff_isOff_autOn hV hOff.1).mp hOff
    have hfac : ∀ w ∈ (⁅X, V⁆ : Subgroup G), ∃ p ∈ (⁅X, V⁆ : Subgroup G),
        ∃ c ∈ (⁅X, V⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G), w = p * c :=
      fun w hw => ⟨w, hw, 1, one_mem _, (mul_one w).symm⟩
    have hZ : commV (autOn X V) ⊓ fixV (autOn X V) = ⊥ := by
      have h1 : commOn hV X ⊓ fixOn hV X =
          (⁅X, V⁆ ⊓ Subgroup.centralizer (X : Set G)).subgroupOf V := by
        rw [commOn_eq hV hXV, fixOn_eq hV hXV]
        exact (Subgroup.comap_inf _ _ _).symm
      rw [hC0, Subgroup.bot_subgroupOf] at h1
      exact h1
    have hbot : ⁅autOn X V, autOn A V⁆ = ⊥ := by
      rcases hnat with hplus | hminus
      · exact h28 ↥V hV2 (autOn X V) (autOn A V) n hn2 (hcomp A hOff) hoff
          (Or.inl (isNatSectionBy_autOn hV hXV hplus le_rfl hfac hker')) hZ
      · exact h28 ↥V hV2 (autOn X V) (autOn A V) n hn2 (hcomp A hOff) hoff
          (Or.inr (isNatSectionBy_autOn hV hXV hminus le_rfl hfac hker')) hZ
    refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
    refine hP.inf_le_oTwoIn (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [commutatorElement_def]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN ha) x).mp hx) (X.inv_mem hx)
    · have hAU : A ≤ Subgroup.normalizer (V : Set G) := hOff.1
      have h1 : conjAct V ⟨a, hAU ha⟩ ∈ autOn A V := mem_autOn_iff.mpr ⟨⟨a, hAU ha⟩, ha, rfl⟩
      have h2 : conjAct V ⟨x, hXV hx⟩ ∈ autOn X V := mem_autOn_iff.mpr ⟨⟨x, hXV hx⟩, hx, rfl⟩
      have h3 := Subgroup.commutator_mem_commutator h2 h1
      rw [hbot, Subgroup.mem_bot, ← map_commutatorElement] at h3
      have h4 := (conjAct_eq_one_iff V _).mp h3
      have h5 : ⁅a, x⁆ = ⁅x, a⁆⁻¹ := (commutatorElement_inv x a).symm
      rw [h5]
      exact (Subgroup.centralizer (V : Set G)).inv_mem h4

end CFSG.CGT.PushingUpLit.CGT6
