module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aSelfDual
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Overgroup
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aNodes

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.QuasithinUnique.K1

section CoverSec

variable {F : Type} [Field F] {Λ : Type} [Group Λ]

structure Cover (φ : SL(3, F) →* Λ) : Prop where
  surjective : Function.Surjective φ
  ker_le : ∀ x, φ x = 1 → x ∈ scalars 3 F
  map_scalars : (scalars 3 F).map φ = Subgroup.center Λ

namespace Cover

variable {φ : SL(3, F) →* Λ} (h : Cover φ)

include h

theorem mem_center_iff (x : SL(3, F)) : φ x ∈ Subgroup.center Λ ↔ x ∈ scalars 3 F := by
  constructor
  · intro hx
    rw [← h.map_scalars] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : x = z * (z⁻¹ * x) := by group
    rw [this]
    refine (scalars 3 F).mul_mem hz (h.ker_le _ ?_)
    rw [map_mul, map_inv, hzx, inv_mul_cancel]
  · intro hx
    rw [← h.map_scalars]
    exact ⟨x, hx, rfl⟩

@[expose] noncomputable def coverHom : projectiveSL 3 F →* Λ ⧸ Subgroup.center Λ :=
  QuotientGroup.lift (scalars 3 F) ((QuotientGroup.mk' (Subgroup.center Λ)).comp φ)
    (fun x hx => by
      show (QuotientGroup.mk' (Subgroup.center Λ)) (φ x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (h.mem_center_iff x).2 hx)

theorem coverHom_proj (x : SL(3, F)) :
    h.coverHom (proj 3 F x) = (QuotientGroup.mk (φ x) : Λ ⧸ Subgroup.center Λ) := rfl

theorem coverHom_bijective : Function.Bijective h.coverHom := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    obtain ⟨x, rfl⟩ := proj_surjective 3 F p
    rw [MonoidHom.mem_ker, coverHom_proj, QuotientGroup.eq_one_iff] at hp
    rw [Subgroup.mem_bot, proj_eq_one_iff]
    exact (h.mem_center_iff x).1 hp
  · intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := h.surjective l
    exact ⟨proj 3 F x, rfl⟩

@[expose] noncomputable def coverEquiv : projectiveSL 3 F ≃* Λ ⧸ Subgroup.center Λ :=
  MulEquiv.ofBijective h.coverHom h.coverHom_bijective

theorem coverEquiv_proj (x : SL(3, F)) :
    h.coverEquiv (proj 3 F x) = (QuotientGroup.mk (φ x) : Λ ⧸ Subgroup.center Λ) := rfl

@[expose] noncomputable def theta : MulAut Λ →* MulAut (projectiveSL 3 F) :=
  (MulAut.congr h.coverEquiv.symm).toMonoidHom.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Λ)

theorem coverEquiv_theta (α : MulAut Λ) (p : projectiveSL 3 F) :
    h.coverEquiv (h.theta α p) =
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Λ α (h.coverEquiv p) := by
  simp [theta, MulAut.congr_apply]

theorem theta_apply_proj (α : MulAut Λ) (x : SL(3, F)) :
    h.coverEquiv (h.theta α (proj 3 F x)) = (QuotientGroup.mk (α (φ x)) : Λ ⧸ Subgroup.center Λ) := by
  rw [coverEquiv_theta, coverEquiv_proj]
  exact CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk Λ α (φ x)

theorem theta_injective [Group.IsPerfect Λ] : Function.Injective h.theta := by
  intro α β hαβ
  apply CFSG.ComponentClassification.CentralCover.perfect_central_quotient_automorphism_faithful Λ
  apply (MulAut.congr h.coverEquiv.symm).injective
  exact hαβ

theorem theta_conj (y : SL(3, F)) :
    h.theta (MulAut.conj (φ y)) = MulAut.conj (proj 3 F y) := by
  apply MulEquiv.ext
  intro p
  obtain ⟨x, rfl⟩ := proj_surjective 3 F p
  apply h.coverEquiv.injective
  rw [theta_apply_proj]
  simp only [MulAut.conj_apply, map_mul, map_inv, coverEquiv_proj, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv]

omit h in
theorem hom_eq_of_inv_mul_mem_center {S : Type*} [Group S] [Group.IsPerfect S] (f₁ f₂ : S →* Λ)
    (hc : ∀ x, (f₁ x)⁻¹ * f₂ x ∈ Subgroup.center Λ) : f₁ = f₂ := by
  let d : S →* Subgroup.center Λ :=
    { toFun := fun x => ⟨(f₁ x)⁻¹ * f₂ x, hc x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (f₁ (x * y))⁻¹ * f₂ (x * y) = ((f₁ x)⁻¹ * f₂ x) * ((f₁ y)⁻¹ * f₂ y)
        have hcx := Subgroup.mem_center_iff.mp (hc x) (f₁ y)⁻¹
        calc (f₁ (x * y))⁻¹ * f₂ (x * y)
            = (f₁ y)⁻¹ * ((f₁ x)⁻¹ * f₂ x) * f₂ y := by rw [map_mul, map_mul]; group
          _ = ((f₁ x)⁻¹ * f₂ x) * (f₁ y)⁻¹ * f₂ y := by rw [hcx]
          _ = ((f₁ x)⁻¹ * f₂ x) * ((f₁ y)⁻¹ * f₂ y) := by rw [mul_assoc] }
  have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative d
  ext x
  have h2 : (f₁ x)⁻¹ * f₂ x = 1 := by
    have := congrArg (fun g : S →* Subgroup.center Λ => (g x : Λ)) h1
    simpa [d] using this
  exact inv_mul_eq_one.mp h2

variable [Finite F]

theorem exists_stdAut_lift (α : MulAut Λ) :
    ∃ (Ab : GL (Fin 3) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      h.theta α = conjAut 3 F Ab * fieldAut 3 F σ * dualAut 3 F ^ ε ∧
      ∀ x : SL(3, F), α (φ x) = φ (stdAut Ab σ ε x) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨Ab, σ, ε, hε, hθ⟩ := hgen (h.theta α)
  refine ⟨Ab, σ, ε, hε, hθ, ?_⟩
  have hperf : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3) le_rfl
  have h2 : h.theta α = descendAut 3 F (stdAut Ab σ ε) := by rw [hθ, descendAut_stdAut]
  have key : ∀ x : SL(3, F), (α (φ x))⁻¹ * φ (stdAut Ab σ ε x) ∈ Subgroup.center Λ := by
    intro x
    have h1 := h.theta_apply_proj α x
    rw [h2, descendAut_proj, coverEquiv_proj] at h1
    exact QuotientGroup.eq.mp h1.symm
  have := hom_eq_of_inv_mul_mem_center
    ((α : Λ →* Λ).comp φ) (φ.comp ((stdAut Ab σ ε : MulAut SL(3, F)) : SL(3, F) →* SL(3, F))) key
  intro x
  exact congrArg (fun g : SL(3, F) →* Λ => g x) this

end Cover

section Frob

open CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.QuasithinUnique.Setup.X7a (frobPow frobSL tauSL frobSL_iterate_coe tauSL_coe trInvMat)

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

omit [Fintype F] in
theorem frobPow_eq_iterate (j : ℕ) (g : SL(3, F)) : frobPow F j g = (frobSL F)^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

omit [Fintype F] in
theorem frobPow_coe (j : ℕ) (g : SL(3, F)) :
    ((frobPow F j g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F).map (fun x => x ^ 2 ^ j) := by
  rw [frobPow_eq_iterate]
  exact frobSL_iterate_coe j g

omit [CharP F 2] in
theorem exists_frob_eq {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (σ : F ≃+* F) :
    ∃ j : ℕ, ∀ x : F, σ x = x ^ 2 ^ j := by
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨σ₀, hσ₀, -, hzp, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hNat
  have hfin : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hmem : σ ∈ Subgroup.zpowers σ₀ := by rw [hzp]; exact Subgroup.mem_top σ
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
  have hj' : σ₀ ^ j = σ := hj
  have key : ∀ (m : ℕ) (x : F), (σ₀ ^ m) x = x ^ 2 ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, show (σ₀ ^ m * σ₀) x = (σ₀ ^ m) (σ₀ x) from rfl, hσ₀, ih, ← pow_mul,
        pow_succ 2 m, mul_comm]
  exact ⟨j, fun x => by rw [← hj']; exact key j x⟩

@[expose] noncomputable def graphFieldHom (A : GL (Fin 3) F) (j : ℕ) : SL(3, F) →* SL(3, F) :=
  ((slConjugation 3 F A).toMonoidHom.comp (tauSL F)).comp (frobPow F j)

theorem stdAut_one_apply {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (A : GL (Fin 3) F)
    (σ : F ≃+* F) : ∃ j : ℕ, ∀ x : SL(3, F), stdAut A σ 1 x = graphFieldHom A j x := by
  obtain ⟨j, hj⟩ := exists_frob_eq hF hf σ
  refine ⟨j, fun x => ?_⟩
  show slConjugation 3 F A (slFieldAut (Fin 3) F σ (slGraphAut 3 F x)) =
    slConjugation 3 F A (tauSL F (frobPow F j x))
  congr 1
  apply Subtype.ext
  have h1 : ((slFieldAut (Fin 3) F σ (slGraphAut 3 F x) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ).map σ) := rfl
  rw [h1, tauSL_coe, trInvMat, ← map_inv, frobPow_coe, Matrix.transpose_map]
  ext a b
  simp [Matrix.map_apply, hj]

end Frob

section Lift

open CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal inner_map_congr)

variable {X : Type} [Group X] [Finite X]

theorem lift_of_inf_eq_weak {p : ℕ} [Fact p.Prime]
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {U Q₁ Q₂ : Subgroup X}
    (hn₁ : ¬ Q₁.Normal) (hn₂ : ¬ Q₂.Normal) (hgen : Q₁ ⊔ Q₂ = ⊤)
    {D : Subgroup (MulAut X)} (hD : inner X ≤ D)
    (hinv : ∀ α ∈ D, U.map α.toMonoidHom = U →
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂)
    (hU : IsSylowOf p (U.map (MulAut.conj : X →* MulAut X)) (inner X))
    {R : Subgroup (MulAut X)}
    (hRD : R ≤ D) (hRU : R ⊓ inner X = U.map (MulAut.conj : X →* MulAut X)) :
    HasTwoGeneratingOvergroups D R := by
  classical
  set ι : X →* MulAut X := MulAut.conj with hι
  let Y : Subgroup X → Subgroup (MulAut X) := fun Q =>
    D ⊓ Subgroup.normalizer ((Q.map ι : Subgroup (MulAut X)) : Set (MulAut X))
  have hYle : ∀ Q, Y Q ≤ D := fun Q => inf_le_left
  have hY : ∀ α ∈ D, α ∈ Subgroup.normalizer
      ((U.map ι : Subgroup (MulAut X)) : Set (MulAut X)) → α ∈ Y Q₁ ∧ α ∈ Y Q₂ := by
    intro α hα hαn
    rw [mem_normalizer_map_conj_iff hinj] at hαn
    obtain ⟨h1, h2⟩ := hinv α hα hαn
    exact ⟨⟨hα, (mem_normalizer_map_conj_iff hinj _ _).2 h1⟩,
      ⟨hα, (mem_normalizer_map_conj_iff hinj _ _).2 h2⟩⟩
  have hRn : ∀ r ∈ R, r ∈ Subgroup.normalizer
      ((U.map ι : Subgroup (MulAut X)) : Set (MulAut X)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [← hRU]
    constructor
    · intro hh
      exact ⟨R.mul_mem (R.mul_mem hr hh.1) (R.inv_mem hr),
        (inner_normal X).conj_mem _ hh.2 r⟩
    · intro hh
      have h1 : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ ∈ inner X := (inner_normal X).conj_mem _ hh.2 r⁻¹
      have h2 : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ ∈ R :=
        R.mul_mem (R.mul_mem (R.inv_mem hr) hh.1) (by simpa using hr)
      have h3 : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
      rw [h3] at h1 h2
      exact ⟨h2, h1⟩
  have hlt : ∀ Q : Subgroup X, ¬ Q.Normal → Y Q < D := by
    intro Q hQ
    refine lt_of_le_of_ne (hYle Q) fun hEq => hQ ?_
    constructor
    intro n hn g
    have hg : ι g ∈ Y Q := by rw [hEq]; exact hD ⟨g, rfl⟩
    have h2 := (mem_normalizer_map_conj_iff hinj Q (ι g)).1 hg.2
    have h3 : (ι g).toMonoidHom n ∈ Q.map (ι g).toMonoidHom := ⟨n, hn, rfl⟩
    rw [h2] at h3
    simpa [hι, MulAut.conj_apply] using h3
  have hN_le : inner X ≤ Y Q₁ ⊔ Y Q₂ := by
    have h1 : inner X = (Q₁ ⊔ Q₂).map ι := by
      rw [hgen]; exact (MonoidHom.range_eq_map ι)
    rw [h1, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · intro a ha
      exact ⟨hD (Subgroup.map_le_range ι Q₁ ha), Subgroup.le_normalizer ha⟩
    · intro a ha
      exact ⟨hD (Subgroup.map_le_range ι Q₂ ha), Subgroup.le_normalizer ha⟩
  have hD_le : D ≤ Y Q₁ ⊔ Y Q₂ := by
    intro d hd
    have hSyl' : IsSylowOf p ((U.map ι).map (MulAut.conj d).toMonoidHom)
        ((inner X).map (MulAut.conj d).toMonoidHom) :=
      isSylowOf_map_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective hU
    have hNd : (inner X).map (MulAut.conj d).toMonoidHom = inner X := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        exact (inner_normal X).conj_mem n hn d
      · intro n hn
        refine ⟨d⁻¹ * n * d, ?_, ?_⟩
        · simpa using (inner_normal X).conj_mem n hn d⁻¹
        · change MulAut.conj d (d⁻¹ * n * d) = n
          rw [MulAut.conj_apply]; group
    rw [hNd] at hSyl'
    obtain ⟨k, hkN, hk⟩ := hSyl'.exists_mem_conj hU
    have hmem : (k * d)⁻¹ ∈ Subgroup.normalizer
        ((U.map ι : Subgroup (MulAut X)) : Set (MulAut X)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hk x, Subgroup.mem_map_equiv]
      simp only [MulAut.conj_symm_apply]
      have : d⁻¹ * (k⁻¹ * x * k) * d = (k * d)⁻¹ * x * (k * d)⁻¹⁻¹ := by group
      rw [this]
    have hm : k * d ∈ Subgroup.normalizer
        ((U.map ι : Subgroup (MulAut X)) : Set (MulAut X)) := by
      simpa using inv_mem hmem
    have hmY := (hY (k * d) (mul_mem (hD hkN) hd) hm).1
    have : d = k⁻¹ * (k * d) := by group
    rw [this]
    exact mul_mem (inv_mem (hN_le hkN)) (Subgroup.mem_sup_left hmY)
  have hRY : ∀ r ∈ R, r ∈ Y Q₁ ∧ r ∈ Y Q₂ := fun r hr => hY r (hRD hr) (hRn r hr)
  exact ⟨Y Q₁, Y Q₂, fun r hr => (hRY r hr).1, fun r hr => (hRY r hr).2, hlt Q₁ hn₁, hlt Q₂ hn₂,
    le_antisymm (sup_le (hYle _) (hYle _)) hD_le⟩


theorem lift_weak {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center X = ⊥) {U Q₁ Q₂ : Subgroup X} (hU : IsSylowOf p U ⊤)
    (hn₁ : ¬ Q₁.Normal) (hn₂ : ¬ Q₂.Normal) (hgen : Q₁ ⊔ Q₂ = ⊤)
    {D : Subgroup (MulAut X)} (hD : inner X ≤ D)
    (hinv : ∀ α ∈ D, U.map α.toMonoidHom = U →
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂)
    {R : Subgroup (MulAut X)} (hR : IsSylowOf p R D) : HasTwoGeneratingOvergroups D R := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set ι : X →* MulAut X := MulAut.conj with hι
  have hU' : IsSylowOf p (U.map ι) (inner X) := by
    have := isSylowOf_map_injective ι hinj hU
    rwa [← MonoidHom.range_eq_map] at this
  have hRN : IsSylowOf p (R ⊓ inner X) (inner X) :=
    hR.inf_of_le_normalizer hD Subgroup.le_normalizer_of_normal
  obtain ⟨k, hkN, hk⟩ := hU'.exists_mem_conj hRN
  have hkD : k ∈ D := hD hkN
  have hk'D : k⁻¹ ∈ D := D.inv_mem hkD
  have hDk' : D.map (MulAut.conj k⁻¹).toMonoidHom = D := map_conj_eq_of_mem' hk'D
  have hR' : IsSylowOf p (R.map (MulAut.conj k⁻¹).toMonoidHom) D := by
    have := isSylowOf_map_injective (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective hR
    rwa [hDk'] at this
  have hR'le : R.map (MulAut.conj k⁻¹).toMonoidHom ≤ D := hR'.le
  have hR'U : R.map (MulAut.conj k⁻¹).toMonoidHom ⊓ inner X = U.map ι := by
    ext y
    have hyN : y ∈ inner X ↔ k * y * k⁻¹ ∈ inner X := by
      constructor
      · intro hy; exact (inner_normal X).conj_mem y hy k
      · intro hy
        have := (inner_normal X).conj_mem _ hy k⁻¹
        have e : k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y := by group
        rwa [e] at this
    have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    constructor
    · intro hy
      obtain ⟨hyR, hyI⟩ := Subgroup.mem_inf.1 hy
      have h1 : k * y * k⁻¹ ∈ R := by
        have := Subgroup.mem_map_equiv.1 hyR
        simpa [MulAut.conj_symm_apply] using this
      have h2 := (hk (k * y * k⁻¹)).1 (Subgroup.mem_inf.2 ⟨h1, hyN.1 hyI⟩)
      rwa [e] at h2
    · intro hy
      have h2 := (hk (k * y * k⁻¹)).2 (by rw [e]; exact hy)
      obtain ⟨h2R, h2I⟩ := Subgroup.mem_inf.1 h2
      refine Subgroup.mem_inf.2 ⟨?_, hyN.2 h2I⟩
      rw [Subgroup.mem_map_equiv]
      simpa [MulAut.conj_symm_apply] using h2R
  have h0 := lift_of_inf_eq_weak hinj hn₁ hn₂ hgen hD hinv hU' hR'le hR'U
  have hDk : D.map (MulAut.conj k).toMonoidHom = D := map_conj_eq_of_mem' hkD
  have h2 := h0.map (MulAut.conj k)
  rw [hDk] at h2
  have hback : (R.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj k).toMonoidHom = R := by
    rw [Subgroup.map_map]
    have : (MulAut.conj k).toMonoidHom.comp (MulAut.conj k⁻¹).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun x => ?_
      change MulAut.conj k (MulAut.conj k⁻¹ x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]; group
    rw [this, Subgroup.map_id]
  rwa [hback] at h2


end Lift

section Flag

open Matrix
open CFSG.QuasithinUnique.Setup.Family (finrank_map_mulVecLin_gl map_toMonoidHom_mul
  not_normal_flagStabilizer flagStabilizer_sup_eq_top_of_disjoint)

variable {K : Type} [Field K] {n : ℕ}

theorem invariant_of_projUnitriangular_le {W : Submodule K (Fin n → K)}
    (h : projUnitriangular n K ≤ projStabilizer W) :
    ∀ u ∈ unitriangular n K, ∀ v ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W := by
  intro u hu v hv
  obtain ⟨s, hs, hsu⟩ := h (Subgroup.mem_map_of_mem _ hu)
  have hz : s⁻¹ * u ∈ scalars n K := proj_eq_proj_iff.mp hsu
  have hu' : u ∈ stabilizer W := by
    have : u = s * (s⁻¹ * u) := by group
    rw [this]
    exact (stabilizer W).mul_mem hs (scalars_le_stabilizer W hz)
  have h2 := mem_stabilizer.1 hu'
  have h3 : (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
      W.map (mulVecLin (u : Matrix (Fin n) (Fin n) K)) := ⟨v, hv, rfl⟩
  rwa [h2] at h3

theorem projStabilizer_eq_flag_of_le {W : Submodule K (Fin n → K)}
    (h : projUnitriangular n K ≤ projStabilizer W) :
    projStabilizer W = projStabilizer (flagSpace n K (Module.finrank K W)) := by
  obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant (invariant_of_projUnitriangular_le h)
  have hfin : Module.finrank K W = m := by rw [hW, finrank_flagSpace hm]
  rw [hfin, ← hW]

theorem coordImage_flagSpace (σ : K ≃+* K) (d : ℕ) :
    coordImage σ (flagSpace n K d) = flagSpace n K d := by
  ext v
  rw [mem_coordImage, mem_flagSpace, mem_flagSpace]
  constructor
  · intro hv k hk
    have := hv k hk
    simpa using this
  · intro hv k hk
    simp [hv k hk]

theorem projUnitriangular_le_projStabilizer_flag (d : ℕ) :
    projUnitriangular n K ≤ projStabilizer (flagSpace n K d) := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨u, mem_flagStabilizer.1 (upperTriangular_le_flagStabilizer (K := K) (n := n) {d}
    (unitriangular_le_upperTriangular n _ hu)) d (Set.mem_singleton d), rfl⟩

theorem semilinear_flag {α : MulAut (projectiveSL n K)} (hα : α ∈ semilinearAutGroup n K)
    (hU : (projUnitriangular n K).map α.toMonoidHom = projUnitriangular n K) {d : ℕ} (hd : d ≤ n) :
    (projStabilizer (flagSpace n K d)).map α.toMonoidHom = projStabilizer (flagSpace n K d) := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hα
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have h7 : ∀ (B : GL (Fin n) K) (W : Submodule K (Fin n → K)),
      (projStabilizer W).map (conjAut n K B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin n) (Fin n) K))) :=
    fun B W => htrans.2.2.2.2.2.2.1 B W
  have h8 : ∀ (τ : K ≃+* K) (W : Submodule K (Fin n → K)),
      (projStabilizer W).map (fieldAut n K τ).toMonoidHom = projStabilizer (coordImage τ W) :=
    fun τ W => htrans.2.2.2.2.2.2.2.1 τ W
  have hmap : (projStabilizer (flagSpace n K d)).map
      (conjAut n K A * fieldAut n K σ).toMonoidHom =
      projStabilizer ((flagSpace n K d).map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) := by
    rw [map_toMonoidHom_mul, h8, coordImage_flagSpace, h7]
  have hle : projUnitriangular n K ≤
      projStabilizer ((flagSpace n K d).map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) := by
    rw [← hmap, ← hU]
    exact Subgroup.map_mono (projUnitriangular_le_projStabilizer_flag d)
  rw [hmap, projStabilizer_eq_flag_of_le hle, finrank_map_mulVecLin_gl, finrank_flagSpace hd]

end Flag

section Overgroups

open CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.QuasithinUnique.Setup.X7a (conj_injective_projectiveSL)
open CFSG.QuasithinUnique.Setup.Family (not_normal_flagStabilizer
  flagStabilizer_sup_eq_top_of_disjoint)
open Matrix

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] in
theorem center_projectiveSL_eq_bot : Subgroup.center (projectiveSL 3 F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply conj_injective_projectiveSL (F := F)
  ext y
  rw [map_one, MulAut.conj_apply, MulAut.one_apply]
  have := Subgroup.mem_center_iff.mp hx y
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem flagStabilizer_singleton {K : Type} [Field K] {n : ℕ} (d : ℕ) :
    flagStabilizer n K {d} = stabilizer (flagSpace n K d) := by
  ext g
  simp [mem_flagStabilizer]

theorem not_normal_projStabilizer_flag {K : Type} [Field K] {n d : ℕ} (hd1 : 1 ≤ d)
    (hdn : d < n) : ¬ (projStabilizer (flagSpace n K d)).Normal := by
  intro hN
  have h := hN.comap (proj n K)
  have hc : (projStabilizer (flagSpace n K d)).comap (proj n K) = flagStabilizer n K {d} := by
    rw [flagStabilizer_singleton, projStabilizer, Subgroup.comap_map_eq, ker_proj]
    exact sup_eq_left.2 (scalars_le_stabilizer _)
  rw [hc] at h
  exact not_normal_flagStabilizer (K := K) (n := n) (I := {d}) (fun i hi => by
    rw [Set.mem_singleton_iff.1 hi]; exact hdn.le) (Set.mem_singleton d) hd1 hdn h

theorem projStabilizer_flag_sup_eq_top {K : Type} [Field K] :
    projStabilizer (flagSpace 3 K 1) ⊔ projStabilizer (flagSpace 3 K 2) = ⊤ := by
  have h := flagStabilizer_sup_eq_top_of_disjoint (K := K) (n := 3) (I := {1}) (J := {2}) (by
    intro i hi1 hi3
    by_cases h : i = 1
    · right; simp [h]
    · left; simp [h])
  rw [flagStabilizer_singleton, flagStabilizer_singleton] at h
  rw [projStabilizer, projStabilizer, ← Subgroup.map_sup, h,
    Subgroup.map_top_of_surjective _ (proj_surjective 3 K)]

theorem hasTwoGeneratingOvergroups_of_le_semilinear
    {D R : Subgroup (MulAut (projectiveSL 3 F))} (hD : inner (projectiveSL 3 F) ≤ D)
    (hDE : D ≤ semilinearAutGroup 3 F) (hR : CFSG.QuasithinUnique.IsSylowTwoOf R D) :
    HasTwoGeneratingOvergroups D R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pu, hPu⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU : IsSylowOf 2 (projUnitriangular 3 F) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hPu]; exact Pu.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hPu]; exact Pu.not_dvd_index
  refine lift_weak center_projectiveSL_eq_bot hU
    (not_normal_projStabilizer_flag (by norm_num) (by norm_num))
    (not_normal_projStabilizer_flag (by norm_num) (by norm_num)) projStabilizer_flag_sup_eq_top
    hD ?_ (isSylowTwoOf_iff_isSylowOf.1 hR)
  intro α hα hαU
  exact ⟨semilinear_flag (hDE hα) hαU (by norm_num), semilinear_flag (hDE hα) hαU (by norm_num)⟩

end Overgroups

section TypeExchange

open CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {Λ : Type} [Group Λ] {φ : SL(3, F) →* Λ}

omit [CharP F 2] in
theorem Cover.theta_conj_mem (h : Cover φ) (l : Λ) :
    h.theta (MulAut.conj l) ∈ linearAutGroup 3 F := by
  obtain ⟨y, rfl⟩ := h.surjective l
  rw [h.theta_conj]
  exact (standard_outer_quotients (n := 3) (K := F)).1 ⟨proj 3 F y, rfl⟩

omit [CharP F 2] [Fintype F] in
theorem Cover.inner_le (h : Cover φ) :
    inner (projectiveSL 3 F) ≤ (inner Λ).map h.theta := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨y, rfl⟩ := proj_surjective 3 F p
  exact ⟨MulAut.conj (φ y), ⟨φ y, rfl⟩, h.theta_conj y⟩

theorem Cover.exists_typeExchanging [Finite Λ] [Group.IsPerfect Λ] (h : Cover φ)
    {A S P : Subgroup (MulAut Λ)} (hAS : A = inner Λ ⊔ S)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S A)
    (hmax : S ≤ P ∧ P ⋖ A ∧ ∀ M, M ⋖ A → S ≤ M → M = P) :
    ∃ α ∈ S, h.theta α ∉ semilinearAutGroup 3 F := by
  by_contra hcon
  push Not at hcon
  have hΘinj := h.theta_injective
  have hAi : inner Λ ≤ A := hAS ▸ le_sup_left
  have hD : inner (projectiveSL 3 F) ≤ A.map h.theta :=
    h.inner_le.trans (Subgroup.map_mono hAi)
  have hDE : A.map h.theta ≤ semilinearAutGroup 3 F := by
    rw [hAS, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
      exact linearAutGroup_le_semilinearAutGroup (h.theta_conj_mem l)
    · rintro _ ⟨α, hα, rfl⟩
      exact hcon α hα
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf (S.map h.theta) (A.map h.theta) :=
    isSylowTwoOf_iff_isSylowOf.2
      (isSylowOf_map_injective h.theta hΘinj (isSylowTwoOf_iff_isSylowOf.1 hS))
  have h2 := hasTwoGeneratingOvergroups_of_le_semilinear hD hDE hS'
  have h3 := h2.of_map_injective hS.1 h.theta hΘinj
  exact h3.not_uniqueMaximal hmax

end TypeExchange

section Dichotomy

open CFSG.QuasithinUnique.Setup.X7a (pow_eq_self_of_sq)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ} {Λ : Type} [Group Λ]
  {φ : SL(3, F) →* Λ}

theorem Cover.dichotomy (h : Cover φ) (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (α : MulAut Λ) :
    h.theta α ∈ semilinearAutGroup 3 F ∨
      ∃ (A : GL (Fin 3) F) (j : ℕ), ∀ x : SL(3, F), α (φ x) = φ (graphFieldHom A j x) := by
  obtain ⟨A, σ, ε, hε, hθ, hlift⟩ := h.exists_stdAut_lift α
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    rw [hθ]
    exact mem_semilinearAutGroup_iff.mpr ⟨A, σ, by simp⟩
  · right
    obtain ⟨j, hj⟩ := stdAut_one_apply hF hf A σ
    exact ⟨A, j, fun x => by rw [hlift x, hj x]⟩

omit [CharP F 2] in
theorem exists_involution_lift (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    {p : projectiveSL 3 F} (hp : p * p = 1) : ∃ s : SL(3, F), s * s = 1 ∧ proj 3 F s = p := by
  obtain ⟨y, rfl⟩ := proj_surjective 3 F p
  have hy2 : y * y ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_mul]
    exact hp
  have hkodd : Odd (Nat.card (scalars 3 F)) := by
    have hdvd := card_scalars_dvd (K := F) (n := 3) (by norm_num)
    have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
    have hodd : Odd (Nat.card F - 1) := by
      rw [hNat]
      have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      rw [Nat.odd_iff]
      omega
    exact Odd.of_dvd_nat hodd hdvd
  set k := Nat.card (scalars 3 F) with hk
  have htsq : y ^ k * y ^ k = 1 := by
    have h1 : y ^ k * y ^ k = (y * y) ^ k := by
      rw [← pow_add, ← two_mul, pow_mul, sq]
    rw [h1]
    have h2 : (⟨y * y, hy2⟩ : scalars 3 F) ^ k = 1 := pow_card_eq_one'
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hproj : proj 3 F (y ^ k) = proj 3 F y := by
    rw [map_pow]
    exact pow_eq_self_of_sq hp hkodd
  exact ⟨y ^ k, htsq, hproj⟩

omit [CharP F 2] in
theorem linear_involution_mem_inner (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    {q : MulAut (projectiveSL 3 F)} (hq : q ∈ linearAutGroup 3 F) (hq2 : q * q = 1) :
    q ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F) := by
  classical
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hq
  have hm : Odd (Fintype.card Fˣ) := by
    rw [Fintype.card_units, hF]
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [Nat.odd_iff]
    omega
  set m := Fintype.card Fˣ with hmdef
  have hdet : (Matrix.GeneralLinearGroup.det (B ^ m) : Fˣ) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one
  have hsl : ∃ g : SL(3, F), Matrix.SpecialLinearGroup.toGL g = B ^ m := by
    refine ⟨⟨((B ^ m : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), ?_⟩, ?_⟩
    · have := congrArg (fun u : Fˣ => (u : F)) hdet
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    · apply Units.ext
      rfl
  obtain ⟨g, hg⟩ := hsl
  have h1 : (conjAut 3 F B) ^ m = conjAut 3 F B := pow_eq_self_of_sq hq2 hm
  rw [← h1, ← map_pow, ← hg, conjAut_toGL]
  exact ⟨proj 3 F g, rfl⟩

end Dichotomy

section Index

theorem index_comap_le_two {A Γ : Type*} [Group A] [Group Γ] [Finite Γ] (θ : A →* Γ)
    (E D₀ I₀ : Subgroup Γ) (hθE : ∀ a, θ a ∈ E)
    (hnorm : ∀ e ∈ E, ∀ d ∈ D₀, e * d * e⁻¹ ∈ D₀)
    (hcyc : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D₀)
    (hI : ∀ q ∈ D₀, q * q = 1 → q ∈ I₀) (hA2 : ∀ a : A, a * a = 1) :
    (I₀.comap θ).index ≤ 2 := by
  classical
  let D' : Subgroup ↥E := D₀.subgroupOf E
  have hD'n : D'.Normal := by
    constructor
    intro d hd e
    exact hnorm e.1 e.2 d.1 hd
  let θ' : A →* ↥E := θ.codRestrict E hθE
  obtain ⟨g, hgE, hg⟩ := hcyc
  have : Fintype (↥E ⧸ D') := Fintype.ofFinite _
  have hcyc' : IsCyclic (↥E ⧸ D') := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨((⟨g, hgE⟩ : ↥E) : ↥E ⧸ D'), ?_⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk⟩ := hg x.1 x.2
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-k, ?_⟩
    have h1 : (QuotientGroup.mk ((⟨g, hgE⟩ : ↥E) ^ k * x) : ↥E ⧸ D') = 1 :=
      (QuotientGroup.eq_one_iff _).2 hk
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  let ψ : A →* ↥E ⧸ D' := (QuotientGroup.mk' D').comp θ'
  have hψ2 : ∀ a : A, ψ a ^ 2 = 1 := fun a => by
    rw [pow_two, ← map_mul, hA2 a, map_one]
  have hrange : Nat.card ψ.range ≤ 2 := by
    have h1 := IsCyclic.card_pow_eq_one_le (α := ↥E ⧸ D') (n := 2) (by norm_num)
    have h2 : Nat.card ψ.range ≤ Nat.card {z : ↥E ⧸ D' // z ^ 2 = 1} := by
      refine Nat.card_le_card_of_injective (fun z => ⟨z.1, ?_⟩) ?_
      · obtain ⟨_, a, rfl⟩ := z
        exact hψ2 a
      · intro z w hzw
        exact Subtype.ext (by simpa using congrArg Subtype.val hzw)
    have h3 : Nat.card {z : ↥E ⧸ D' // z ^ 2 = 1} =
        (Finset.univ.filter fun z : ↥E ⧸ D' => z ^ 2 = 1).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    omega
  have hker : (ψ.ker).index = Nat.card ψ.range := Subgroup.index_ker ψ
  have hle : ψ.ker ≤ I₀.comap θ := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have hD' : θ' a ∈ D' := (QuotientGroup.eq_one_iff (θ' a)).1 ha
    have hD : (θ' a : Γ) ∈ D₀ := hD'
    exact hI _ hD (by rw [← map_mul, hA2 a, map_one])
  have hpos : 0 < Nat.card ψ.range := Nat.card_pos
  have := Nat.le_of_dvd (by rw [hker]; exact hpos) (Subgroup.index_dvd_of_le hle)
  omega

end Index

section IndexAut

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

omit [CharP F 2] in
theorem index_inner_le_two (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {A : Type*} [Group A]
    (θ : A →* MulAut (projectiveSL 3 F)) (hθE : ∀ a, θ a ∈ semilinearAutGroup 3 F)
    (hA2 : ∀ a : A, a * a = 1) :
    ((OuterAutomorphisms.inner (projectiveSL 3 F)).comap θ).index ≤ 2 := by
  obtain ⟨-, -, hDnormR, -, -, hcyc, -⟩ := standard_outer_quotients (n := 3) (K := F)
  have hER : semilinearAutGroup 3 F ≤ standardAutGroup 3 F :=
    semilinearAutGroup_le_standardAutGroup
  refine index_comap_le_two θ (semilinearAutGroup 3 F) (linearAutGroup 3 F)
    (OuterAutomorphisms.inner (projectiveSL 3 F)) hθE (fun e he d hd => ?_) hcyc (fun q hq hq2 => linear_involution_mem_inner hF hf hq hq2) hA2
  have hdR : (⟨d, linearAutGroup_le_semilinearAutGroup.trans hER hd⟩ : ↥(standardAutGroup 3 F)) ∈
      (linearAutGroup 3 F).subgroupOf (standardAutGroup 3 F) := hd
  exact hDnormR.conj_mem _ hdR ⟨e, hER he⟩

end IndexAut

section Alpha

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ} {N : Type} [Group N]
  {L : Subgroup N} [L.Normal] {φ : SL(3, F) →* ↥L}

@[expose] noncomputable def alphaP (h : Cover φ) : N →* MulAut (projectiveSL 3 F) :=
  h.theta.comp (MulAut.conjNormal (H := L))

omit [CharP F 2] [Fintype F] in
theorem alphaP_apply (h : Cover φ) (n : N) :
    alphaP h n = h.theta (MulAut.conjNormal (H := L) n) := rfl

omit [CharP F 2] [Fintype F] in
theorem alphaP_of_mem (h : Cover φ) (y : SL(3, F)) :
    alphaP h ((φ y : ↥L) : N) = MulAut.conj (proj 3 F y) := by
  rw [alphaP_apply, MulAut.conjNormal_val, h.theta_conj]

omit [CharP F 2] [Fintype F] in
theorem alphaP_eq_one_iff [Group.IsPerfect ↥L] (h : Cover φ) (n : N) :
    alphaP h n = 1 ↔ n ∈ Subgroup.centralizer (L : Set N) := by
  constructor
  · intro h1
    have h2 : MulAut.conjNormal (H := L) n = 1 := by
      apply h.theta_injective
      rw [map_one]
      exact h1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg (fun e : MulAut ↥L => ((e ⟨l, hl⟩ : ↥L) : N)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro hn
    rw [alphaP_apply]
    have h2 : MulAut.conjNormal (H := L) n = 1 := by
      apply MulEquiv.ext
      intro l
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hn l l.2).symm
    rw [h2, map_one]

omit [CharP F 2] in
theorem exists_inner_involution [Group.IsPerfect ↥L] (h : Cover φ) (hF : Fintype.card F = 2 ^ f)
    (hf : 1 ≤ f) {a : N} (ha2 : a * a = 1)
    (hin : alphaP h a ∈ OuterAutomorphisms.inner (projectiveSL 3 F)) :
    ∃ s : SL(3, F), s * s = 1 ∧ ∀ l : ↥L, a * (l : N) * a⁻¹ =
      ((φ s : ↥L) : N) * (l : N) * ((φ s : ↥L) : N)⁻¹ := by
  obtain ⟨p, hp⟩ := hin
  have hp2 : p * p = 1 := by
    apply CFSG.QuasithinUnique.Setup.X7a.conj_injective_projectiveSL (F := F)
    rw [map_mul, hp, ← map_mul, ha2, map_one, map_one]
  obtain ⟨s, hs2, hsp⟩ := exists_involution_lift hF hf hp2
  refine ⟨s, hs2, fun l => ?_⟩
  have h1 : alphaP h a = alphaP h ((φ s : ↥L) : N) := by
    rw [alphaP_of_mem, hsp, hp]
  have h2 : MulAut.conjNormal (H := L) a = MulAut.conjNormal (H := L) ((φ s : ↥L) : N) :=
    h.theta_injective h1
  have := congrArg (fun e : MulAut ↥L => ((e l : ↥L) : N)) h2
  simpa [MulAut.conjNormal_apply] using this

theorem exists_exchange_lift (h : Cover φ) (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (n : N)
    (hn : alphaP h n ∉ semilinearAutGroup 3 F) :
    ∃ (A : GL (Fin 3) F) (j : ℕ), ∀ x : SL(3, F),
      n * ((φ x : ↥L) : N) * n⁻¹ = ((φ (graphFieldHom A j x) : ↥L) : N) := by
  rcases h.dichotomy hF hf (MulAut.conjNormal (H := L) n) with h1 | ⟨A, j, hAj⟩
  · exact absurd h1 hn
  · refine ⟨A, j, fun x => ?_⟩
    have := congrArg (fun l : ↥L => (l : N)) (hAj x)
    simpa [MulAut.conjNormal_apply] using this

end Alpha

end CoverSec

end CFSG.QuasithinUnique.Setup.X7Sec
