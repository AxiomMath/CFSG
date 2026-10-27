module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal inner_map_congr)

@[expose] def HasTwoGeneratingOvergroups {K : Type*} [Group K] (D R : Subgroup K) : Prop :=
  ∃ Y₁ Y₂ : Subgroup K, R ≤ Y₁ ∧ R ≤ Y₂ ∧ Y₁ < D ∧ Y₂ < D ∧ Y₁ ⊔ Y₂ = D

@[expose] def TwoGeneratingSylowOvergroups (X : Type) [Group X] : Prop :=
  ∀ D : Subgroup (MulAut X), inner X ≤ D → ∀ R : Subgroup (MulAut X),
    CFSG.QuasithinUnique.IsSylowTwoOf R D → HasTwoGeneratingOvergroups D R

theorem isSylowTwoOf_iff_isSylowOf {G : Type*} [Group G] [Finite G] {S H : Subgroup G} :
    CFSG.QuasithinUnique.IsSylowTwoOf S H ↔ IsSylowOf 2 S H := by
  rw [isSylowOf_iff]
  rfl

theorem isSylowOf_map_injective {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    {p : ℕ} [Fact p.Prime] {P K : Subgroup G} (f : G →* G') (hf : Function.Injective f)
    (h : IsSylowOf p P K) : IsSylowOf p (P.map f) (K.map f) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.map f, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective _ _ hf]

section Generalities

variable {K K' : Type*} [Group K] [Group K']

theorem HasTwoGeneratingOvergroups.map {D R : Subgroup K} (h : HasTwoGeneratingOvergroups D R)
    (e : K ≃* K') : HasTwoGeneratingOvergroups (D.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  obtain ⟨Y₁, Y₂, h₁, h₂, hl₁, hl₂, hs⟩ := h
  refine ⟨Y₁.map e.toMonoidHom, Y₂.map e.toMonoidHom, Subgroup.map_mono h₁, Subgroup.map_mono h₂,
    (Subgroup.map_lt_map_iff_of_injective e.injective).2 hl₁,
    (Subgroup.map_lt_map_iff_of_injective e.injective).2 hl₂, ?_⟩
  rw [← Subgroup.map_sup, hs]

theorem HasTwoGeneratingOvergroups.of_map_injective {A S : Subgroup K} (hSA : S ≤ A)
    (c : K →* K') (hc : Function.Injective c)
    (h : HasTwoGeneratingOvergroups (A.map c) (S.map c)) : HasTwoGeneratingOvergroups A S := by
  obtain ⟨Y₁, Y₂, h₁, h₂, hl₁, hl₂, hs⟩ := h
  have hY : ∀ Y : Subgroup K', Y ≤ A.map c → (Y.comap c ⊓ A).map c = Y := by
    intro Y hY
    have hYr : Y ≤ c.range := hY.trans (Subgroup.map_le_range _ _)
    rw [Subgroup.map_inf_eq _ _ _ hc, Subgroup.map_comap_eq, inf_eq_right.2 hYr, inf_eq_left.2 hY]
  have hSY : ∀ Y : Subgroup K', S.map c ≤ Y → S ≤ Y.comap c ⊓ A := fun Y hY =>
    le_inf (fun s hs => hY ⟨s, hs, rfl⟩) hSA
  have hlt : ∀ Y : Subgroup K', Y < A.map c → Y.comap c ⊓ A < A := by
    intro Y hY'
    refine lt_of_le_of_ne inf_le_right fun hEq => hY'.ne ?_
    rw [← hY Y hY'.le, hEq]
  refine ⟨Y₁.comap c ⊓ A, Y₂.comap c ⊓ A, hSY _ h₁, hSY _ h₂, hlt _ hl₁, hlt _ hl₂, ?_⟩
  apply Subgroup.map_injective hc
  rw [Subgroup.map_sup, hY _ hl₁.le, hY _ hl₂.le, hs]

theorem map_conj_eq_of_mem' {D : Subgroup K} {k : K} (hk : k ∈ D) :
    D.map (MulAut.conj k).toMonoidHom = D := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact D.mul_mem (D.mul_mem hk hx) (D.inv_mem hk)
  · intro x hx
    refine ⟨k⁻¹ * x * k, D.mul_mem (D.mul_mem (D.inv_mem hk) hx) hk, ?_⟩
    change MulAut.conj k (k⁻¹ * x * k) = x
    rw [MulAut.conj_apply]; group

variable [Finite K]

theorem HasTwoGeneratingOvergroups.exists_two_maximal {D R : Subgroup K}
    (h : HasTwoGeneratingOvergroups D R) :
    ∃ M₁ M₂ : Subgroup K, M₁ ≠ M₂ ∧ M₁ ⋖ D ∧ M₂ ⋖ D ∧ R ≤ M₁ ∧ R ≤ M₂ := by
  obtain ⟨Y₁, Y₂, h₁, h₂, hl₁, hl₂, hs⟩ := h
  obtain ⟨M₁, hM₁, hM₁D⟩ := exists_le_covBy_of_lt hl₁
  obtain ⟨M₂, hM₂, hM₂D⟩ := exists_le_covBy_of_lt hl₂
  refine ⟨M₁, M₂, fun hEq => ?_, hM₁D, hM₂D, h₁.trans hM₁, h₂.trans hM₂⟩
  have : D ≤ M₁ := by
    rw [← hs]
    exact sup_le hM₁ (hEq ▸ hM₂)
  exact absurd hM₁D.lt (not_lt_of_ge this)

theorem HasTwoGeneratingOvergroups.not_uniqueMaximal {D R P : Subgroup K}
    (h : HasTwoGeneratingOvergroups D R)
    (hP : R ≤ P ∧ P ⋖ D ∧ ∀ M, M ⋖ D → R ≤ M → M = P) : False := by
  obtain ⟨M₁, M₂, hne, h1, h2, hR1, hR2⟩ := h.exists_two_maximal
  exact hne ((hP.2.2 M₁ h1 hR1).trans (hP.2.2 M₂ h2 hR2).symm)

end Generalities

section Inner

variable {X : Type} [Group X]

theorem conj_conj_inv (α : MulAut X) (x : X) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem mem_normalizer_map_conj_iff (hinj : Function.Injective (MulAut.conj : X →* MulAut X))
    (W : Subgroup X) (α : MulAut X) :
    α ∈ Subgroup.normalizer
        ((W.map (MulAut.conj : X →* MulAut X) : Subgroup (MulAut X)) : Set (MulAut X)) ↔
      W.map α.toMonoidHom = W := by
  have key : ∀ α : MulAut X, α ∈ Subgroup.normalizer
      ((W.map (MulAut.conj : X →* MulAut X) : Subgroup (MulAut X)) : Set (MulAut X)) →
      W.map α.toMonoidHom ≤ W := by
    intro α hα w hw
    obtain ⟨w', hw', rfl⟩ := hw
    have h := (Subgroup.mem_normalizer_iff.1 hα (MulAut.conj w')).1 ⟨w', hw', rfl⟩
    rw [conj_conj_inv] at h
    obtain ⟨w'', hw'', hh⟩ := h
    have := hinj hh
    show α w' ∈ W
    rw [← this]
    exact hw''
  constructor
  · intro hα
    refine le_antisymm (key α hα) ?_
    have := key α⁻¹ (inv_mem hα)
    intro w hw
    have hw' : α⁻¹ w ∈ W := this ⟨w, hw, rfl⟩
    exact ⟨α⁻¹ w, hw', by simp⟩
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨α w, ?_, ?_⟩
      · rw [← h]; exact ⟨w, hw, rfl⟩
      · simp [conj_conj_inv]
    · rintro ⟨w, hw, hwg⟩
      have : g = α⁻¹ * MulAut.conj w * α := by
        rw [hwg]; group
      have hw2 : α⁻¹ w ∈ W := by
        rw [← h] at hw
        obtain ⟨v, hv, hvw⟩ := hw
        have : α⁻¹ w = v := by rw [← hvw]; simp
        rw [this]; exact hv
      refine ⟨α⁻¹ w, hw2, ?_⟩
      rw [this]
      have := conj_conj_inv α⁻¹ w
      simpa [mul_assoc] using this.symm

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut X => φ g) hx
    simp only [MulAut.conj_apply] at h
    have h2 : x * g = g * x := mul_inv_eq_iff_eq_mul.1 h
    exact h2.symm
  rw [hZ] at hc
  exact hc

end Inner

section Lift

variable {X : Type} [Group X] [Finite X]

theorem lift_of_inf_eq {p : ℕ} [Fact p.Prime]
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {U Q₁ Q₂ : Subgroup X}
    (hn₁ : ¬ Q₁.Normal) (hn₂ : ¬ Q₂.Normal) (hgen : Q₁ ⊔ Q₂ = ⊤)
    (hinv : ∀ α : MulAut X, U.map α.toMonoidHom = U →
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂)
    (hU : IsSylowOf p (U.map (MulAut.conj : X →* MulAut X)) (inner X))
    {D : Subgroup (MulAut X)} (hD : inner X ≤ D) {R : Subgroup (MulAut X)}
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
    obtain ⟨h1, h2⟩ := hinv α hαn
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

theorem automorphism_invariant_generating_Sylow_overgroups_lift {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center X = ⊥) {U Q₁ Q₂ : Subgroup X} (hU : IsSylowOf p U ⊤)
    (hn₁ : ¬ Q₁.Normal) (hn₂ : ¬ Q₂.Normal) (hgen : Q₁ ⊔ Q₂ = ⊤)
    (hinv : ∀ α : MulAut X, U.map α.toMonoidHom = U →
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂)
    {D : Subgroup (MulAut X)} (hD : inner X ≤ D) {R : Subgroup (MulAut X)}
    (hR : IsSylowOf p R D) : HasTwoGeneratingOvergroups D R := by
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
  have h0 := lift_of_inf_eq hinj hn₁ hn₂ hgen hinv hU' hD hR'le hR'U
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

section Node1

variable {X : Type} [Group X] [Finite X]

theorem not_normal_of_covBy_normalizer {U P : Subgroup X} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hP : Subgroup.normalizer (U : Set X) ⋖ P) (hP' : P ≠ ⊤) : ¬ P.Normal := by
  intro hn
  have hU' := isSylowTwoOf_iff_isSylowOf.1 hU
  have hUp : IsPGroup 2 U := hU.2.1
  have hUi : ¬ 2 ∣ U.index := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right] at hU'
    exact hU'.2.2
  have hUP : U ≤ P := (Subgroup.le_normalizer).trans hP.lt.le
  have h := Sylow.normalizer_sup_eq_top' (p := 2) (N := P) (hUp.toSylow hUi) hUP
  have e : ((hUp.toSylow hUi : Sylow 2 X) : Set X) = (U : Set X) :=
    Set.ext fun x => IsPGroup.mem_toSylow hUp hUi
  rw [e] at h
  exact hP' (top_unique (h ▸ sup_le hP.lt.le le_rfl))

theorem unequal_intrinsic_Sylow_normalizer_overgroups_exclude (hZ : Subgroup.center X = ⊥)
    {U P₁ P₂ : Subgroup X} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hcov : ∀ A : Subgroup X, Subgroup.normalizer (U : Set X) ⋖ A ↔ A = P₁ ∨ A = P₂)
    (h₁ : P₁ ≠ ⊤) (h₂ : P₂ ≠ ⊤) (hgen : P₁ ⊔ P₂ = ⊤)
    (hidx : (Subgroup.normalizer (U : Set X)).relIndex P₁ ≠
      (Subgroup.normalizer (U : Set X)).relIndex P₂)
    {D : Subgroup (MulAut X)} (hD : inner X ≤ D) {R : Subgroup (MulAut X)}
    (hR : CFSG.QuasithinUnique.IsSylowTwoOf R D) :
    HasTwoGeneratingOvergroups D R ∧
      ∃ M₁ M₂ : Subgroup (MulAut X), M₁ ≠ M₂ ∧ M₁ ⋖ D ∧ M₂ ⋖ D ∧ R ≤ M₁ ∧ R ≤ M₂ := by
  have hU' := isSylowTwoOf_iff_isSylowOf.1 hU
  have hR' := isSylowTwoOf_iff_isSylowOf.1 hR
  have hB1 : Subgroup.normalizer (U : Set X) ⋖ P₁ := (hcov P₁).2 (Or.inl rfl)
  have hB2 : Subgroup.normalizer (U : Set X) ⋖ P₂ := (hcov P₂).2 (Or.inr rfl)
  have hnn : ∀ P : Subgroup X, Subgroup.normalizer (U : Set X) ⋖ P → P ≠ ⊤ → ¬ P.Normal :=
    fun P hP hP' => not_normal_of_covBy_normalizer hU hP hP'
  have hinv : ∀ α : MulAut X, U.map α.toMonoidHom = U →
      P₁.map α.toMonoidHom = P₁ ∧ P₂.map α.toMonoidHom = P₂ := by
    intro α hα
    set B := Subgroup.normalizer (U : Set X) with hB
    have hBα : B.map α.toMonoidHom = B := by
      rw [hB, Subgroup.map_equiv_normalizer_eq, hα]
    have hcovα : ∀ P : Subgroup X, B ⋖ P →
        P.map α.toMonoidHom = P₁ ∨ P.map α.toMonoidHom = P₂ := by
      intro P hP
      have h := (apply_covBy_apply_iff (MulEquiv.mapSubgroup α)).2 hP
      change B.map α.toMonoidHom ⋖ P.map α.toMonoidHom at h
      rw [hBα] at h
      exact (hcov _).1 h
    have hrel : ∀ P : Subgroup X, B.relIndex (P.map α.toMonoidHom) = B.relIndex P := by
      intro P
      have := Subgroup.relIndex_map_map_of_injective (f := α.toMonoidHom) B P α.injective
      rwa [hBα] at this
    refine ⟨?_, ?_⟩
    · rcases hcovα P₁ hB1 with h | h
      · exact h
      · exact absurd ((hrel P₁).symm.trans (by rw [h])) hidx
    · rcases hcovα P₂ hB2 with h | h
      · exact absurd ((hrel P₂).symm.trans (by rw [h])).symm hidx
      · exact h
  have h := automorphism_invariant_generating_Sylow_overgroups_lift hZ hU' (hnn P₁ hB1 h₁)
    (hnn P₂ hB2 h₂) hgen hinv hD hR'
  exact ⟨h, h.exists_two_maximal⟩

end Node1

section Ambient

variable {M : Type} [Group M]

theorem subgroupOf_covBy_iff {C A B : Subgroup M} (hA : A ≤ C) (hB : B ≤ C) :
    A.subgroupOf C ⋖ B.subgroupOf C ↔ A ⋖ B := by
  let f : Subgroup C ↪o Subgroup M := OrderEmbedding.ofMapLEIff (fun H => H.map C.subtype)
    fun _ _ => Subgroup.map_subtype_le_map_subtype
  have hrange : Set.range f = Set.Iic C := by
    ext H
    constructor
    · rintro ⟨H', rfl⟩
      exact Subgroup.map_subtype_le H'
    · intro h
      exact ⟨H.subgroupOf C, Subgroup.map_subgroupOf_eq_of_le h⟩
  have h := Set.OrdConnected.apply_covBy_apply_iff f (hrange ▸ Set.ordConnected_Iic)
    (a := A.subgroupOf C) (b := B.subgroupOf C)
  have hfA : f (A.subgroupOf C) = A := Subgroup.map_subgroupOf_eq_of_le hA
  have hfB : f (B.subgroupOf C) = B := Subgroup.map_subgroupOf_eq_of_le hB
  rw [hfA, hfB] at h
  exact h.symm

theorem normalizer_subgroupOf_eq' {U C : Subgroup M} (hUC : U ≤ C) :
    Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) =
      (C ⊓ Subgroup.normalizer (U : Set M)).subgroupOf C := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro m
    by_cases hm : m ∈ C
    · exact (Subgroup.mem_normalizer_iff.1 hx) ⟨m, hm⟩
    · refine iff_of_false (fun h => hm (hUC h)) fun h => hm ?_
      have e : m = (x : M)⁻¹ * ((x : M) * m * (x : M)⁻¹) * (x : M) := by group
      rw [e]
      exact C.mul_mem (C.mul_mem (C.inv_mem x.2) (hUC h)) x.2
  · rintro ⟨-, hx⟩
    exact Subgroup.mem_normalizer_iff.2 fun y => (Subgroup.mem_normalizer_iff.1 hx) y

theorem isSylowTwoOf_subgroupOf_top [Finite M] {C U : Subgroup M}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U C) :
    CFSG.QuasithinUnique.IsSylowTwoOf (U.subgroupOf C) ⊤ := by
  refine isSylowTwoOf_iff_isSylowOf.2 ?_
  refine (isSylowOf_map_subtype_iff C).1 ?_
  rw [Subgroup.map_subgroupOf_eq_of_le hU.1, Subgroup.map_top, Subgroup.range_subtype]
  exact isSylowTwoOf_iff_isSylowOf.1 hU

theorem isSylowTwoOf_map_subtype [Finite M] {C : Subgroup M} {U : Subgroup C}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (U.map C.subtype) C := by
  have h := isSylowOf_map_injective (p := 2) C.subtype C.subtype_injective
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  exact isSylowTwoOf_iff_isSylowOf.2 h

@[expose] def HasUnequalCovers (X : Type*) [Group X] (U : Subgroup X) (n₁ n₂ : ℕ) : Prop :=
  ∃ P₁ P₂ : Subgroup X, (∀ A : Subgroup X, Subgroup.normalizer (U : Set X) ⋖ A ↔ A = P₁ ∨ A = P₂) ∧
    P₁ ≠ ⊤ ∧ P₂ ≠ ⊤ ∧ P₁ ⊔ P₂ = ⊤ ∧ (Subgroup.normalizer (U : Set X)).relIndex P₁ = n₁ ∧
    (Subgroup.normalizer (U : Set X)).relIndex P₂ = n₂

@[expose] def HasInvariantCovers (X : Type*) [Group X] (U : Subgroup X) : Prop :=
  ∃ P₁ P₂ : Subgroup X, (∀ A : Subgroup X, Subgroup.normalizer (U : Set X) ⋖ A ↔ A = P₁ ∨ A = P₂) ∧
    P₁ ≠ ⊤ ∧ P₂ ≠ ⊤ ∧ P₁ ⊔ P₂ = ⊤ ∧
    ∀ α : MulAut X, U.map α.toMonoidHom = U →
      P₁.map α.toMonoidHom = P₁ ∧ P₂.map α.toMonoidHom = P₂

theorem ambient_covers_data {C U B P₁ P₂ : Subgroup M} (hUC : U ≤ C)
    (hB : C ⊓ Subgroup.normalizer (U : Set M) = B)
    (hcov : ∀ A : Subgroup M, A ≤ C → (B ⋖ A ↔ A = P₁ ∨ A = P₂))
    (hP₁ : P₁ ≤ C) (hP₂ : P₂ ≤ C) (h₁ : P₁ ≠ C) (h₂ : P₂ ≠ C) (hgen : P₁ ⊔ P₂ = C) :
    (∀ A : Subgroup C, Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) ⋖ A ↔
      A = P₁.subgroupOf C ∨ A = P₂.subgroupOf C) ∧ P₁.subgroupOf C ≠ ⊤ ∧
    P₂.subgroupOf C ≠ ⊤ ∧ P₁.subgroupOf C ⊔ P₂.subgroupOf C = ⊤ ∧
    Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) = B.subgroupOf C := by
  have hBC : B ≤ C := hB ▸ inf_le_left
  have hnorm : Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) = B.subgroupOf C := by
    rw [normalizer_subgroupOf_eq' hUC, hB]
  refine ⟨?_, fun h => h₁ (le_antisymm hP₁ (Subgroup.subgroupOf_eq_top.1 h)),
    fun h => h₂ (le_antisymm hP₂ (Subgroup.subgroupOf_eq_top.1 h)), ?_, hnorm⟩
  · intro A
    have hA : A.map C.subtype ≤ C := Subgroup.map_subtype_le A
    have hAeq : A = (A.map C.subtype).subgroupOf C :=
      (Subgroup.comap_map_eq_self_of_injective C.subtype_injective A).symm
    rw [hnorm]
    conv_lhs => rw [hAeq]
    rw [subgroupOf_covBy_iff hBC hA, hcov _ hA]
    have key : ∀ P : Subgroup M, P ≤ C → (A.map C.subtype = P ↔ A = P.subgroupOf C) := by
      intro P hP
      constructor
      · rintro rfl; exact hAeq
      · rintro rfl; exact Subgroup.map_subgroupOf_eq_of_le hP
    rw [key _ hP₁, key _ hP₂]
  · apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hP₁,
      Subgroup.map_subgroupOf_eq_of_le hP₂, hgen, Subgroup.map_top, Subgroup.range_subtype]

theorem hasUnequalCovers_of_ambient {C U B P₁ P₂ : Subgroup M} {n₁ n₂ : ℕ}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U C)
    (hB : C ⊓ Subgroup.normalizer (U : Set M) = B)
    (hcov : ∀ A : Subgroup M, A ≤ C → (B ⋖ A ↔ A = P₁ ∨ A = P₂))
    (hP₁ : P₁ ≤ C) (hP₂ : P₂ ≤ C) (h₁ : P₁ ≠ C) (h₂ : P₂ ≠ C) (hgen : P₁ ⊔ P₂ = C)
    (hi₁ : B.relIndex P₁ = n₁) (hi₂ : B.relIndex P₂ = n₂) :
    HasUnequalCovers C (U.subgroupOf C) n₁ n₂ := by
  obtain ⟨hc, hn₁, hn₂, hg, hnorm⟩ := ambient_covers_data hU.1 hB hcov hP₁ hP₂ h₁ h₂ hgen
  refine ⟨_, _, hc, hn₁, hn₂, hg, ?_, ?_⟩
  · rw [hnorm, Subgroup.relIndex_subgroupOf hP₁]; exact hi₁
  · rw [hnorm, Subgroup.relIndex_subgroupOf hP₂]; exact hi₂

theorem hasInvariantCovers_of_ambient {C U B P₁ P₂ : Subgroup M}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U C)
    (hB : C ⊓ Subgroup.normalizer (U : Set M) = B)
    (hcov : ∀ A : Subgroup M, A ≤ C → (B ⋖ A ↔ A = P₁ ∨ A = P₂))
    (hP₁ : P₁ ≤ C) (hP₂ : P₂ ≤ C) (h₁ : P₁ ≠ C) (h₂ : P₂ ≠ C) (hgen : P₁ ⊔ P₂ = C)
    (hinv : ∀ α : MulAut C, (U.subgroupOf C).map α.toMonoidHom = U.subgroupOf C →
      (P₁.subgroupOf C).map α.toMonoidHom = P₁.subgroupOf C ∧
        (P₂.subgroupOf C).map α.toMonoidHom = P₂.subgroupOf C) :
    HasInvariantCovers C (U.subgroupOf C) := by
  obtain ⟨hc, hn₁, hn₂, hg, -⟩ := ambient_covers_data hU.1 hB hcov hP₁ hP₂ h₁ h₂ hgen
  exact ⟨_, _, hc, hn₁, hn₂, hg, hinv⟩

end Ambient

section Cosets

theorem ncard_image_coset_eq_relIndex {G : Type*} [Group G] (B P : Subgroup G) :
    ((fun g : G => (g : G ⧸ B)) '' (P : Set G)).ncard = B.relIndex P := by
  have key : ∀ g : G, g • ((1 : G) : G ⧸ B) = ((g : G) : G ⧸ B) := fun g => by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hstab : MulAction.stabilizer P ((1 : G) : G ⧸ B) = B.subgroupOf P := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((x : G) • ((1 : G) : G ⧸ B) = ((1 : G) : G ⧸ B)) ↔ _
    rw [key]
    constructor
    · intro h
      have := QuotientGroup.eq.1 h.symm
      simpa using this
    · intro h
      exact (QuotientGroup.eq.2 (by simpa using h)).symm
  have horbit : MulAction.orbit P ((1 : G) : G ⧸ B) =
      (fun g : G => (g : G ⧸ B)) '' (P : Set G) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x : G), x.2, ?_⟩
      change ((x : G) : G ⧸ B) = (x : G) • ((1 : G) : G ⧸ B)
      rw [key]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      change (g : G) • ((1 : G) : G ⧸ B) = _
      rw [key]
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horbit]

theorem covBy_iff_minimal_of_le {α : Type*} [PartialOrder α] {B C A : α} (hA : A ≤ C) :
    B ⋖ A ↔ Minimal (fun X => B < X ∧ X ≤ C) A := by
  constructor
  · intro h
    refine ⟨⟨h.lt, hA⟩, fun y hy hyA => ?_⟩
    by_contra hne
    exact h.2 hy.1 (lt_of_le_not_ge hyA hne)
  · rintro ⟨⟨hlt, -⟩, hmin⟩
    refine ⟨hlt, fun c hBc hcA => ?_⟩
    exact absurd (hmin ⟨hBc, hcA.le.trans hA⟩ hcA.le) (not_le_of_gt hcA)

end Cosets

section UnequalCovers

theorem map_symm_map {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (P : Subgroup X) :
    (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by ext x; simp
  rw [this, Subgroup.map_id]

theorem HasUnequalCovers.map {X X' : Type*} [Group X] [Group X'] {U : Subgroup X} {n₁ n₂ : ℕ}
    (h : HasUnequalCovers X U n₁ n₂) (e : X ≃* X') :
    HasUnequalCovers X' (U.map e.toMonoidHom) n₁ n₂ := by
  obtain ⟨P₁, P₂, hcov, h₁, h₂, hgen, i₁, i₂⟩ := h
  have hn : Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup X') : Set X') =
      (Subgroup.normalizer (U : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq U e).symm
  have htop : ∀ P : Subgroup X, P.map e.toMonoidHom = ⊤ → P = ⊤ := by
    intro P hP
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hP, Subgroup.map_top_of_surjective _ e.surjective]
  have key : ∀ x y : Subgroup X, x.map e.toMonoidHom ⋖ y.map e.toMonoidHom ↔ x ⋖ y :=
    fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup e)
  refine ⟨P₁.map e.toMonoidHom, P₂.map e.toMonoidHom, ?_, fun h => h₁ (htop _ h),
    fun h => h₂ (htop _ h), ?_, ?_, ?_⟩
  · intro A
    rw [hn]
    have hA : (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := by
      have := map_symm_map e.symm A
      simpa using this
    conv_lhs => rw [← hA]
    rw [key, hcov]
    constructor
    · rintro (h | h)
      · left; rw [← h, hA]
      · right; rw [← h, hA]
    · rintro (h | h)
      · left; rw [h, map_symm_map]
      · right; rw [h, map_symm_map]
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ e.surjective]
  · rw [hn, Subgroup.relIndex_map_map_of_injective _ _ e.injective]; exact i₁
  · rw [hn, Subgroup.relIndex_map_map_of_injective _ _ e.injective]; exact i₂

theorem HasUnequalCovers.of_isSylow {X X' : Type*} [Group X] [Group X'] [Finite X] [Finite X']
    (e : X ≃* X') {U₀ : Subgroup X'} {n₁ n₂ : ℕ} (h₀ : HasUnequalCovers X' U₀ n₁ n₂)
    (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasUnequalCovers X U n₁ n₂ := by
  have hU' : IsSylowOf 2 (U.map e.toMonoidHom) ⊤ := by
    have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
      (isSylowTwoOf_iff_isSylowOf.1 hU)
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj hU'
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U.map e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have h1 := h₀.map (MulAut.conj k)
  rw [hconj] at h1
  have h2 := h1.map e.symm
  rwa [map_symm_map] at h2

theorem HasUnequalCovers.twoGenerating {X : Type} [Group X] [Finite X] {U : Subgroup X} {n₁ n₂ : ℕ}
    (hZ : Subgroup.center X = ⊥) (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (h : HasUnequalCovers X U n₁ n₂) (hne : n₁ ≠ n₂) : TwoGeneratingSylowOvergroups X := by
  obtain ⟨P₁, P₂, hcov, h₁, h₂, hgen, i₁, i₂⟩ := h
  intro D hD R hR
  exact (unequal_intrinsic_Sylow_normalizer_overgroups_exclude hZ hU hcov h₁ h₂ hgen
    (by rw [i₁, i₂]; exact hne) hD hR).1

theorem map_comm_equiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (α' : MulAut X')
    (P : Subgroup X) :
    (P.map e.toMonoidHom).map α'.toMonoidHom =
      (P.map (e.trans (α'.trans e.symm)).toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem HasInvariantCovers.map {X X' : Type*} [Group X] [Group X'] {U : Subgroup X}
    (h : HasInvariantCovers X U) (e : X ≃* X') :
    HasInvariantCovers X' (U.map e.toMonoidHom) := by
  obtain ⟨P₁, P₂, hcov, h₁, h₂, hgen, hinv⟩ := h
  have hn : Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup X') : Set X') =
      (Subgroup.normalizer (U : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq U e).symm
  have htop : ∀ P : Subgroup X, P.map e.toMonoidHom = ⊤ → P = ⊤ := by
    intro P hP
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hP, Subgroup.map_top_of_surjective _ e.surjective]
  have key : ∀ x y : Subgroup X, x.map e.toMonoidHom ⋖ y.map e.toMonoidHom ↔ x ⋖ y :=
    fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup e)
  refine ⟨P₁.map e.toMonoidHom, P₂.map e.toMonoidHom, ?_, fun h => h₁ (htop _ h),
    fun h => h₂ (htop _ h), ?_, ?_⟩
  · intro A
    rw [hn]
    have hA : (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := by
      have := map_symm_map e.symm A
      simpa using this
    conv_lhs => rw [← hA]
    rw [key, hcov]
    constructor
    · rintro (h | h)
      · left; rw [← h, hA]
      · right; rw [← h, hA]
    · rintro (h | h)
      · left; rw [h, map_symm_map]
      · right; rw [h, map_symm_map]
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ e.surjective]
  · intro α' hα'
    set α : MulAut X := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h := hα'
      rw [map_comm_equiv] at h
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h
    obtain ⟨h1, h2⟩ := hinv α hαU
    refine ⟨?_, ?_⟩
    · rw [map_comm_equiv, ← hα, h1]
    · rw [map_comm_equiv, ← hα, h2]

theorem HasInvariantCovers.of_isSylow {X X' : Type*} [Group X] [Group X'] [Finite X] [Finite X']
    (e : X ≃* X') {U₀ : Subgroup X'} (h₀ : HasInvariantCovers X' U₀)
    (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasInvariantCovers X U := by
  have hU' : IsSylowOf 2 (U.map e.toMonoidHom) ⊤ := by
    have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
      (isSylowTwoOf_iff_isSylowOf.1 hU)
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj hU'
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U.map e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have h1 := h₀.map (MulAut.conj k)
  rw [hconj] at h1
  have h2 := h1.map e.symm
  rwa [map_symm_map] at h2

theorem HasInvariantCovers.twoGenerating {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hZ : Subgroup.center X = ⊥) (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (h : HasInvariantCovers X U) : TwoGeneratingSylowOvergroups X := by
  obtain ⟨P₁, P₂, hcov, h₁, h₂, hgen, hinv⟩ := h
  have hB1 : Subgroup.normalizer (U : Set X) ⋖ P₁ := (hcov P₁).2 (Or.inl rfl)
  have hB2 : Subgroup.normalizer (U : Set X) ⋖ P₂ := (hcov P₂).2 (Or.inr rfl)
  intro D hD R hR
  exact automorphism_invariant_generating_Sylow_overgroups_lift hZ
    (isSylowTwoOf_iff_isSylowOf.1 hU) (not_normal_of_covBy_normalizer hU hB1 h₁)
    (not_normal_of_covBy_normalizer hU hB2 h₂) hgen hinv hD (isSylowTwoOf_iff_isSylowOf.1 hR)


end UnequalCovers

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem TwoGeneratingSylowOvergroups.of_mulEquiv [Finite X] (e : X ≃* X')
    (h : TwoGeneratingSylowOvergroups X) : TwoGeneratingSylowOvergroups X' := by
  have : Finite X' := Finite.of_equiv X e.toEquiv
  intro D' hD' R' hR'
  set φ : MulAut X ≃* MulAut X' := MulAut.congr e with hφ
  have hinner : (inner X).map φ.toMonoidHom = inner X' := inner_map_congr e
  have hD : inner X ≤ D'.map φ.symm.toMonoidHom := by
    intro x hx
    have : φ x ∈ inner X' := hinner ▸ ⟨x, hx, rfl⟩
    exact ⟨φ x, hD' this, by simp⟩
  have hR : CFSG.QuasithinUnique.IsSylowTwoOf (R'.map φ.symm.toMonoidHom)
      (D'.map φ.symm.toMonoidHom) :=
    isSylowTwoOf_iff_isSylowOf.2 (isSylowOf_map_injective _ φ.symm.injective
      (isSylowTwoOf_iff_isSylowOf.1 hR'))
  have h1 := (h _ hD _ hR).map φ
  have e1 : (D'.map φ.symm.toMonoidHom).map φ.toMonoidHom = D' := by
    rw [Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [this, Subgroup.map_id]
  have e2 : (R'.map φ.symm.toMonoidHom).map φ.toMonoidHom = R' := by
    rw [Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [this, Subgroup.map_id]
  rwa [e1, e2] at h1

theorem false_of_twoGeneratingSylowOvergroups {L Q : Type} [Group L] [Group Q] [Finite L]
    [Finite Q] (c : MulAut L →* MulAut Q) (hc : Function.Injective c)
    (hinner : inner Q ≤ (inner L).map c) {A S P : Subgroup (MulAut L)} (hAi : inner L ≤ A)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S A)
    (hmax : S ≤ P ∧ P ⋖ A ∧ ∀ M, M ⋖ A → S ≤ M → M = P)
    (hQ : TwoGeneratingSylowOvergroups Q) : False := by
  have hS' := isSylowTwoOf_iff_isSylowOf.1 hS
  have h1 : inner Q ≤ A.map c := hinner.trans (Subgroup.map_mono hAi)
  have h2 : CFSG.QuasithinUnique.IsSylowTwoOf (S.map c) (A.map c) :=
    isSylowTwoOf_iff_isSylowOf.2 (isSylowOf_map_injective c hc hS')
  exact ((hQ _ h1 _ h2).of_map_injective hS'.le c hc).not_uniqueMaximal hmax

end Transport

end CFSG.QuasithinUnique.Setup.X6
