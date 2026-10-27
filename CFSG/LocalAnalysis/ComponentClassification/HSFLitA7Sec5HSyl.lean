module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HKer

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Sec8

namespace Sec5H

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

@[expose] def sEl (D : S.Sec5 F T₁) : X := D.w₂ * D.g

@[expose] def hEl (D : S.Sec5 F T₁) : X := sEl D * sEl D * sEl D

@[expose] def nEl (D : S.Sec5 F T₁) : X := D.g * D.w₂

@[expose] def vEl (D : S.Sec5 F T₁) : X := D.g⁻¹ * ((nEl D)⁻¹ * (hEl D * D.w₂) * nEl D)

@[expose] def L₀ (D : S.Sec5 F T₁) : Subgroup X := M D ⊔ zpowers D.w₂

@[expose] def L (D : S.Sec5 F T₁) : Subgroup X := L₀ D ⊔ zpowers (hEl D)

@[expose] def πs (σ : Fin 8 → Fin 8) : Fin 8 → Fin 8 := RH.wtau ∘ σ

@[expose] def πh (σ : Fin 8 → Fin 8) : Fin 8 → Fin 8 := πs σ ∘ πs σ ∘ πs σ

structure PermFacts (σ : Fin 8 → Fin 8) : Prop where
  σ_inv : ∀ i : Fin 8, i.val < 6 → (σ i).val < 6 ∧ σ (σ i) = i
  τ_inv : ∀ i : Fin 8, i.val < 6 → (RH.wtau i).val < 6 ∧ RH.wtau (RH.wtau i) = i
  πs_lt : ∀ i : Fin 8, i.val < 6 → (πs σ i).val < 6
  πh_inv : ∀ i : Fin 8, i.val < 6 → (πh σ i).val < 6 ∧ πh σ (πh σ i) = i
  πh_zero : πh σ 0 = 2
  πh_two : πh σ 2 = 0
  πh_free : ∀ i : Fin 8, i.val < 6 → πh σ i ≠ i ∧ (πh σ ∘ RH.wtau) i ≠ i
  hh_fix : (πh σ ∘ πh σ) 0 = 0 ∧ (πh σ ∘ πh σ) 1 = 1
  comm_fix : (((πh σ ∘ RH.wtau) ∘ πh σ) ∘ RH.wtau) 0 = 0 ∧
    (((πh σ ∘ RH.wtau) ∘ πh σ) ∘ RH.wtau) 1 = 1
  v_fix : (σ ∘ ((RH.wtau ∘ σ) ∘ (πh σ ∘ RH.wtau)) ∘ (σ ∘ RH.wtau)) 0 = 0 ∧
    (σ ∘ ((RH.wtau ∘ σ) ∘ (πh σ ∘ RH.wtau)) ∘ (σ ∘ RH.wtau)) 1 = 1
  hw_fix : ((RH.wtau ∘ πh σ) ∘ (RH.wtau ∘ πh σ)) 0 = 0 ∧
    ((RH.wtau ∘ πh σ) ∘ (RH.wtau ∘ πh σ)) 1 = 1

theorem permFacts_A : PermFacts Setup.σA where
  σ_inv := by decide
  τ_inv := by decide
  πs_lt := by decide
  πh_inv := by decide
  πh_zero := by decide
  πh_two := by decide
  πh_free := by decide
  hh_fix := by decide
  comm_fix := by decide
  v_fix := by decide
  hw_fix := by decide

theorem permFacts_B : PermFacts Setup.σB where
  σ_inv := by decide
  τ_inv := by decide
  πs_lt := by decide
  πh_inv := by decide
  πh_zero := by decide
  πh_two := by decide
  πh_free := by decide
  hh_fix := by decide
  comm_fix := by decide
  v_fix := by decide
  hw_fix := by decide

theorem perm_facts {σ : Fin 8 → Fin 8} (hσ : σ ∈ [Setup.σA, Setup.σB]) : PermFacts σ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl
  · exact permFacts_A
  · exact permFacts_B

section Generic

variable {G : Type*} [Group G]

theorem sq_eq_one_of_mem_sup {A Z : Subgroup G} (hA : ∀ a ∈ A, a * a = 1)
    (hZ : ∀ z ∈ Z, z * z = 1) (hAZ : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a) :
    ∀ x ∈ A ⊔ Z, x * x = 1 := by
  have comm2 : ∀ {H : Subgroup G}, (∀ a ∈ H, a * a = 1) → ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro H hH a ha b hb
    have h1 := hH _ (mul_mem ha hb)
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * (b * a) * (b * b) := by group
      _ = b * a := by rw [hH a ha, hH b hb, one_mul, mul_one]
  have hcA : A ⊔ Z ≤ centralizer (A : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_iff.mpr fun b hb => comm2 hA b hb a ha) ?_
    exact fun z hz => mem_centralizer_iff.mpr fun a ha => hAZ a ha z hz
  have hcZ : A ⊔ Z ≤ centralizer (Z : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_iff.mpr fun z hz => (hAZ a ha z hz).symm) ?_
    exact fun z hz => mem_centralizer_iff.mpr fun b hb => comm2 hZ b hb z hz
  have hcomm : ∀ x ∈ A ⊔ Z, ∀ y ∈ A ⊔ Z, x * y = y * x := by
    intro x hx y hy
    have hle : A ⊔ Z ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun z hz => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp (hcA hx) a ha)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp (hcZ hx) z hz)
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  let W : Subgroup G :=
    { carrier := {x | x ∈ A ⊔ Z ∧ x * x = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
        refine ⟨mul_mem hx hy, ?_⟩
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hcomm y hy x hx]
          _ = 1 := by rw [← mul_assoc, hx2, one_mul, hy2]
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := by
        rintro x ⟨hx, hx2⟩
        refine ⟨inv_mem hx, ?_⟩
        rw [← mul_inv_rev, hx2, inv_one] }
  have hle : A ⊔ Z ≤ W := sup_le (fun a ha => ⟨le_sup_left (a := A) ha, hA a ha⟩)
    (fun z hz => ⟨le_sup_right (b := Z) hz, hZ z hz⟩)
  exact fun x hx => (hle hx).2

end Generic

namespace Setup

variable {D : S.Sec5 F T₁} (C : Setup D)

include C in
theorem g_mem_N : D.g ∈ normalizer (D.T₂ : Set X) := conjSub_eq_self_iff.mp (C.conjSub_T₁ D.g_mem)

theorem w₂_mem_N : D.w₂ ∈ normalizer (D.T₂ : Set X) :=
  conjSub_eq_self_iff.mp (conjSub_R D (w₂_mem_R D))

include C in
theorem hEl_mem_N : hEl D ∈ normalizer (D.T₂ : Set X) := by
  have hs : sEl D ∈ normalizer (D.T₂ : Set X) := mul_mem (w₂_mem_N (D := D)) C.g_mem_N
  exact mul_mem (mul_mem hs hs) hs

include C in
theorem nEl_mem_N : nEl D ∈ normalizer (D.T₂ : Set X) := mul_mem C.g_mem_N (w₂_mem_N (D := D))

theorem exists_σ : ∃ σ ∈ [σA, σB], C.Acts D.g σ := by
  rcases C.g_acts with h | h
  · exact ⟨σA, by simp, h⟩
  · exact ⟨σB, by simp, h⟩

theorem acts_s {σ : Fin 8 → Fin 8} (hσ : σ ∈ [σA, σB]) (hg : C.Acts D.g σ) :
    C.Acts (sEl D) (πs σ) :=
  Acts.mul C hg C.acts_w₂ fun i hi => ((perm_facts hσ).σ_inv i hi).1

theorem acts_h {σ : Fin 8 → Fin 8} (hσ : σ ∈ [σA, σB]) (hg : C.Acts D.g σ) :
    C.Acts (hEl D) (πh σ) := by
  have hs := C.acts_s hσ hg
  have h6 := (perm_facts hσ).πs_lt
  have := Acts.mul C hs (Acts.mul C hs hs h6) h6
  exact this

theorem acts_h_inv {σ : Fin 8 → Fin 8} (hσ : σ ∈ [σA, σB]) (hg : C.Acts D.g σ) :
    C.Acts (hEl D)⁻¹ (πh σ) :=
  Acts.inv C (C.acts_h hσ hg) (perm_facts hσ).πh_inv

theorem acts_w₂_inv : C.Acts D.w₂⁻¹ RH.wtau :=
  Acts.inv C C.acts_w₂ permFacts_A.τ_inv

include C in
theorem hh_mem_M : hEl D * hEl D ∈ M D := by
  obtain ⟨σ, hσ, hg⟩ := C.exists_σ
  have hh := C.acts_h hσ hg
  have hp := perm_facts hσ
  exact Acts.mem_M C (Acts.mul C hh hh fun i hi => (hp.πh_inv i hi).1)
    (mul_mem C.hEl_mem_N C.hEl_mem_N) hp.hh_fix.1 hp.hh_fix.2

include C in
theorem comm_mem_M : hEl D * D.w₂ * (hEl D)⁻¹ * D.w₂⁻¹ ∈ M D := by
  obtain ⟨σ, hσ, hg⟩ := C.exists_σ
  have hh := C.acts_h hσ hg
  have hh' := C.acts_h_inv hσ hg
  have hp := perm_facts hσ
  have hw := hp.τ_inv
  have hhp := hp.πh_inv
  have h1 := Acts.mul C C.acts_w₂ hh fun i hi => (hw i hi).1
  have h2 := Acts.mul C hh' h1 fun i hi => (hhp i hi).1
  have h3 := Acts.mul C C.acts_w₂_inv h2 fun i hi => (hw i hi).1
  refine Acts.mem_M C h3 ?_ hp.comm_fix.1 hp.comm_fix.2
  exact mul_mem (mul_mem (mul_mem C.hEl_mem_N (w₂_mem_N (D := D))) (inv_mem C.hEl_mem_N))
    (inv_mem (w₂_mem_N (D := D)))

include C in
theorem acts_g_inv {σ : Fin 8 → Fin 8} (hσ : σ ∈ [σA, σB]) (hg : C.Acts D.g σ) :
    C.Acts D.g⁻¹ σ :=
  Acts.inv C hg (perm_facts hσ).σ_inv

include C in
theorem v_mem_M : vEl D ∈ M D := by
  obtain ⟨σ, hσ, hg⟩ := C.exists_σ
  have hp := perm_facts hσ
  have hh := C.acts_h hσ hg
  have hgi := C.acts_g_inv hσ hg
  have hσl : ∀ i : Fin 8, i.val < 6 → (σ i).val < 6 := fun i hi => (hp.σ_inv i hi).1
  have hτl : ∀ i : Fin 8, i.val < 6 → (RH.wtau i).val < 6 := fun i hi => (hp.τ_inv i hi).1
  have hhl : ∀ i : Fin 8, i.val < 6 → (πh σ i).val < 6 := fun i hi => (hp.πh_inv i hi).1
  have hn : C.Acts (nEl D) (σ ∘ RH.wtau) := Acts.mul C C.acts_w₂ hg hτl
  have hni : C.Acts (nEl D)⁻¹ (RH.wtau ∘ σ) := by
    rw [nEl, mul_inv_rev]
    exact Acts.mul C hgi C.acts_w₂_inv hσl
  have hhw : C.Acts (hEl D * D.w₂) (πh σ ∘ RH.wtau) := Acts.mul C C.acts_w₂ hh hτl
  have h1 := Acts.mul C hhw hni fun i hi => hhl _ (hτl i hi)
  have h2 := Acts.mul C hn h1 fun i hi => hσl _ (hτl i hi)
  have h3 := Acts.mul C h2 hgi fun i hi => hτl _ (hσl _ (hhl _ (hτl _ (hσl _ (hτl i hi)))))
  refine Acts.mem_M C h3 ?_ hp.v_fix.1 hp.v_fix.2
  exact mul_mem (inv_mem C.g_mem_N) (mul_mem (mul_mem (inv_mem C.nEl_mem_N)
    (mul_mem C.hEl_mem_N (w₂_mem_N (D := D)))) C.nEl_mem_N)

include C in
theorem w₂_sq_mem_M : D.w₂ * D.w₂ ∈ M D := by
  rw [w₂_sq_H D C.hH]; exact T₂_le_M D (y_mem_T₂ D)

include C in
theorem mem_L₀_cases {x : X} (hx : x ∈ L₀ D) : x ∈ M D ∨ D.w₂⁻¹ * x ∈ M D :=
  mem_or_mem_of_mem_sup C.w₂_sq_mem_M (fun _ hm => conj_mem_M D (w₂_mem_N (D := D)) hm) hx

theorem M_le_L₀ : M D ≤ L₀ D := le_sup_left

theorem w₂_mem_L₀ : D.w₂ ∈ L₀ D := le_sup_right (a := M D) (mem_zpowers _)

theorem R_le_L₀ : D.R ≤ L₀ D := by
  rw [D.R_eq]
  exact sup_le ((T₂_le_M D).trans M_le_L₀) (zpowers_le.mpr w₂_mem_L₀)

theorem L₀_le_L : L₀ D ≤ L D := le_sup_left

theorem hEl_mem_L : hEl D ∈ L D := le_sup_right (a := L₀ D) (mem_zpowers _)

include C in
theorem hEl_conj_mem_L₀ {ℓ : X} (hℓ : ℓ ∈ L₀ D) : hEl D * ℓ * (hEl D)⁻¹ ∈ L₀ D := by
  rcases C.mem_L₀_cases hℓ with h | h
  · exact M_le_L₀ (conj_mem_M D C.hEl_mem_N h)
  · have e : hEl D * ℓ * (hEl D)⁻¹ = (hEl D * D.w₂ * (hEl D)⁻¹ * D.w₂⁻¹) * D.w₂ *
        (hEl D * (D.w₂⁻¹ * ℓ) * (hEl D)⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (M_le_L₀ C.comm_mem_M) w₂_mem_L₀)
      (M_le_L₀ (conj_mem_M D C.hEl_mem_N h))

include C in
theorem mem_L_cases {x : X} (hx : x ∈ L D) : x ∈ L₀ D ∨ (hEl D)⁻¹ * x ∈ L₀ D :=
  mem_or_mem_of_mem_sup (M_le_L₀ C.hh_mem_M) (fun _ hℓ => C.hEl_conj_mem_L₀ hℓ) hx

theorem L₀_fix {x : X} (hx : x ∈ L₀ D) : conjSub x (C.Fs 0) = C.Fs 0 := by
  rcases C.mem_L₀_cases hx with h | h
  · exact C.acts_M h 0 (by decide)
  · calc conjSub x (C.Fs 0) = conjSub D.w₂ (conjSub (D.w₂⁻¹ * x) (C.Fs 0)) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
      _ = C.Fs 0 := by rw [C.acts_M h 0 (by decide), id, C.conjSub_w₂]; rfl

include C in
theorem hEl_not_mem_L₀ : hEl D ∉ L₀ D := by
  intro h
  obtain ⟨σ, hσ, hg⟩ := C.exists_σ
  have h1 := C.acts_h hσ hg 0 (by decide)
  rw [C.L₀_fix h, (perm_facts hσ).πh_zero] at h1
  exact C.Fs_ne (i := 0) (j := 2) (by decide) h1

include C in
theorem relIndex_L₀ : (L₀ D).relIndex (L D) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨hEl D, hEl_mem_L, fun b hb => ?_⟩
  by_cases hb0 : b ∈ L₀ D
  · refine Or.inr ⟨hb0, fun h => C.hEl_not_mem_L₀ ?_⟩
    have := mul_mem (inv_mem hb0) h
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨?_, hb0⟩
    rcases C.mem_L_cases hb with h | h
    · exact absurd h hb0
    · have e : b * hEl D = hEl D * ((hEl D)⁻¹ * b) * (hEl D)⁻¹ * (hEl D * hEl D) := by group
      rw [e]
      exact mul_mem (C.hEl_conj_mem_L₀ h) (M_le_L₀ C.hh_mem_M)

include C in
theorem exists_P : ∃ P : Subgroup X, IsPGroup 2 P ∧ D.R ≤ P ∧ P ≤ L D ∧ ¬ P ≤ L₀ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRL : D.R ≤ L D := R_le_L₀.trans L₀_le_L
  have hR' : IsPGroup 2 (D.R.subgroupOf (L D)) :=
    D.isPGroup_R.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hR'.exists_le_sylow
  refine ⟨(Q : Subgroup (L D)).map (L D).subtype, Q.isPGroup'.map _, fun r hr => ?_,
    map_subtype_le _, fun hle => ?_⟩
  · exact ⟨⟨r, hRL hr⟩, hQ (show (⟨r, hRL hr⟩ : L D) ∈ D.R.subgroupOf (L D) from hr), rfl⟩
  · have h1 : (Q : Subgroup (L D)) ≤ (L₀ D).subgroupOf (L D) := fun x hx =>
      show (x : X) ∈ L₀ D from hle ⟨x, hx, rfl⟩
    have hdvd : 2 ∣ (Q : Subgroup (L D)).index := by
      rw [← Subgroup.relIndex_mul_index h1]
      exact dvd_mul_of_dvd_right (by rw [← Subgroup.relIndex, C.relIndex_L₀]) _
    exact Q.not_dvd_index hdvd

include C in
theorem mem_T₂_of_mem_M {P : Subgroup X} (hP : IsPGroup 2 P) (hRP : D.R ≤ P) {y : X}
    (hyP : y ∈ P) (hyM : y ∈ M D) : y ∈ D.T₂ := by
  obtain ⟨-, τ, hτ, hyτ⟩ := hyM
  have hc : τ⁻¹ * y ∈ centralizer (D.T₂ : Set X) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := hyτ a ha
    calc a * (τ⁻¹ * y) = τ⁻¹ * (τ * a * τ⁻¹) * y := by group
      _ = τ⁻¹ * (y * a * y⁻¹) * y := by rw [this]
      _ = τ⁻¹ * y * a := by group
  have hcE : τ⁻¹ * y ∈ centralizer (F.E₁ : Set X) :=
    centralizer_le (SetLike.coe_subset_coe.mpr C.E₁_le_T₂) hc
  have hcP : τ⁻¹ * y ∈ P := mul_mem (inv_mem (hRP (D.T₂_le hτ))) hyP
  have hle : zpowers (τ⁻¹ * y) ≤ F.E₁ :=
    D.le_E _ (hP.to_le (zpowers_le.mpr hcP)) (zpowers_le.mpr hcE)
  have := mul_mem hτ (C.E₁_le_T₂ (hle (mem_zpowers _)))
  rwa [mul_inv_cancel_left] at this

include C in
theorem mem_R_of_mem_L₀ {P : Subgroup X} (hP : IsPGroup 2 P) (hRP : D.R ≤ P) {x : X}
    (hxP : x ∈ P) (hxL : x ∈ L₀ D) : x ∈ D.R := by
  rcases C.mem_L₀_cases hxL with h | h
  · exact D.T₂_le (C.mem_T₂_of_mem_M hP hRP hxP h)
  · have hT := C.mem_T₂_of_mem_M hP hRP (mul_mem (inv_mem (hRP (w₂_mem_R D))) hxP) h
    have := mul_mem (w₂_mem_R D) (D.T₂_le hT)
    rwa [mul_inv_cancel_left] at this

section P

variable {P : Subgroup X} (hP : IsPGroup 2 P) (hRP : D.R ≤ P) (hPL : P ≤ L D)

include C hP hRP hPL in
theorem cases_out {f : X} (hfP : f ∈ P) (hfR : f ∉ D.R) :
    (hEl D)⁻¹ * f ∈ M D ∨ D.w₂⁻¹ * ((hEl D)⁻¹ * f) ∈ M D := by
  have hfL₀ : f ∉ L₀ D := fun h => hfR (C.mem_R_of_mem_L₀ hP hRP hfP h)
  rcases C.mem_L_cases (hPL hfP) with h | h
  · exact absurd h hfL₀
  · exact C.mem_L₀_cases h

theorem acts_out {σ : Fin 8 → Fin 8} (hσ : σ ∈ [σA, σB]) (hg : C.Acts D.g σ) {f : X}
    (hf : (hEl D)⁻¹ * f ∈ M D ∨ D.w₂⁻¹ * ((hEl D)⁻¹ * f) ∈ M D) :
    C.Acts f (πh σ) ∨ C.Acts f (πh σ ∘ RH.wtau) := by
  have hh := C.acts_h hσ hg
  rcases hf with h | h
  · left
    have := Acts.mul C (C.acts_M h) hh fun i hi => hi
    rwa [mul_inv_cancel_left] at this
  · right
    have h1 := Acts.mul C (C.acts_M h) C.acts_w₂ fun i hi => hi
    have h2 := Acts.mul C h1 hh fun i hi => ((perm_facts hσ).τ_inv i hi).1
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at h2
    exact h2

theorem out_perm {f : X} (hf : (hEl D)⁻¹ * f ∈ M D ∨ D.w₂⁻¹ * ((hEl D)⁻¹ * f) ∈ M D) :
    (∀ i : Fin 8, i.val < 6 → conjSub f (C.Fs i) ≠ C.Fs i) ∧
      conjSub f (C.Fs 0) = C.Fs 2 ∧ conjSub f (C.Fs 2) = C.Fs 0 := by
  obtain ⟨σ, hσ, hg⟩ := C.exists_σ
  have hp := perm_facts hσ
  rcases C.acts_out hσ hg hf with h | h
  · refine ⟨fun i hi he => ?_, by rw [h 0 (by decide), hp.πh_zero],
      by rw [h 2 (by decide), hp.πh_two]⟩
    rw [h i hi] at he
    exact (hp.πh_free i hi).1 (C.Fs_injective he)
  · refine ⟨fun i hi he => ?_, ?_, ?_⟩
    · rw [h i hi] at he
      exact (hp.πh_free i hi).2 (C.Fs_injective he)
    · rw [h 0 (by decide), Function.comp_apply, show RH.wtau 0 = 0 from rfl, hp.πh_zero]
    · rw [h 2 (by decide), Function.comp_apply, show RH.wtau 2 = 2 from rfl, hp.πh_two]

include C in
theorem s_z : sEl D * S.z * (sEl D)⁻¹ = S.z := by
  have hw : D.w₂ * S.z * D.w₂⁻¹ = S.z := conj_of_comm D.w₂_z
  calc sEl D * S.z * (sEl D)⁻¹ = D.w₂ * (D.g * S.z * D.g⁻¹) * D.w₂⁻¹ := by rw [sEl]; group
    _ = S.z := by rw [C.g_z, hw]

theorem s_k : sEl D * F.kF * (sEl D)⁻¹ = S.z * F.kF := by
  have hw : D.w₂ * S.z * D.w₂⁻¹ = S.z := conj_of_comm D.w₂_z
  have hwk : D.w₂ * F.kF * D.w₂⁻¹ = F.kF := conj_of_comm D.w₂_k
  calc sEl D * F.kF * (sEl D)⁻¹ = D.w₂ * (D.g * F.kF * D.g⁻¹) * D.w₂⁻¹ := by rw [sEl]; group
    _ = (D.w₂ * S.z * D.w₂⁻¹) * (D.w₂ * F.kF * D.w₂⁻¹) := by rw [D.g_k]; group
    _ = S.z * F.kF := by rw [hw, hwk]

include C in
theorem h_z : hEl D * S.z * (hEl D)⁻¹ = S.z := by
  calc hEl D * S.z * (hEl D)⁻¹ = sEl D * (sEl D * (sEl D * S.z * (sEl D)⁻¹) * (sEl D)⁻¹) *
        (sEl D)⁻¹ := by rw [hEl]; group
    _ = S.z := by rw [C.s_z, C.s_z, C.s_z]

include C in
theorem h_k : hEl D * F.kF * (hEl D)⁻¹ = S.z * F.kF := by
  have hzk : sEl D * (S.z * F.kF) * (sEl D)⁻¹ = F.kF := by
    calc sEl D * (S.z * F.kF) * (sEl D)⁻¹ = (sEl D * S.z * (sEl D)⁻¹) *
          (sEl D * F.kF * (sEl D)⁻¹) := by group
      _ = F.kF := by rw [C.s_z, s_k, ← mul_assoc, z_mul_z, one_mul]
  calc hEl D * F.kF * (hEl D)⁻¹ = sEl D * (sEl D * (sEl D * F.kF * (sEl D)⁻¹) * (sEl D)⁻¹) *
        (sEl D)⁻¹ := by rw [hEl]; group
    _ = S.z * F.kF := by rw [s_k, hzk, s_k]

include C in
theorem out_z_k {f : X} (hf : (hEl D)⁻¹ * f ∈ M D ∨ D.w₂⁻¹ * ((hEl D)⁻¹ * f) ∈ M D) :
    f * S.z * f⁻¹ = S.z ∧ f * F.kF * f⁻¹ = S.z * F.kF := by
  have hw : D.w₂ * S.z * D.w₂⁻¹ = S.z := conj_of_comm D.w₂_z
  have hwk : D.w₂ * F.kF * D.w₂⁻¹ = F.kF := conj_of_comm D.w₂_k
  rcases hf with h | h
  · obtain ⟨hmz, hmk⟩ := C.M_fix_z_k h
    have e : ∀ a : X, f * a * f⁻¹ = hEl D * (((hEl D)⁻¹ * f) * a * ((hEl D)⁻¹ * f)⁻¹) *
        (hEl D)⁻¹ := fun a => by group
    rw [e, e, hmz, hmk, C.h_z, C.h_k]
    exact ⟨rfl, rfl⟩
  · obtain ⟨hmz, hmk⟩ := C.M_fix_z_k h
    have e : ∀ a : X, f * a * f⁻¹ = hEl D * (D.w₂ * ((D.w₂⁻¹ * ((hEl D)⁻¹ * f)) * a *
        (D.w₂⁻¹ * ((hEl D)⁻¹ * f))⁻¹) * D.w₂⁻¹) * (hEl D)⁻¹ := fun a => by group
    rw [e, e, hmz, hmk, hw, hwk, C.h_z, C.h_k]
    exact ⟨rfl, rfl⟩

include C in
theorem sq_ne_one {f : X} (hf : D.w₂⁻¹ * ((hEl D)⁻¹ * f) ∈ M D) : f * f ≠ 1 := by
  set m := D.w₂⁻¹ * ((hEl D)⁻¹ * f) with hm_def
  have hnN := C.nEl_mem_N
  have hm' : vEl D * ((nEl D)⁻¹ * m * (nEl D)⁻¹⁻¹) ∈ M D :=
    mul_mem C.v_mem_M (conj_mem_M D (inv_mem hnN) hf)
  set m' := vEl D * ((nEl D)⁻¹ * m * (nEl D)⁻¹⁻¹) with hm'_def
  have hf' : (nEl D)⁻¹ * f * nEl D = D.g * m' := by
    rw [hm'_def, hm_def, vEl]; group
  obtain ⟨hm'z, hm'k⟩ := C.M_fix_z_k hm'
  obtain ⟨-, τ, hτ, hm'τ⟩ := hm'
  have ht' : m' * S.t * m'⁻¹ = S.t ∨ m' * S.t * m'⁻¹ = S.z * S.t := by
    rw [hm'τ _ (t_mem_T₂ D)]; exact (C.T₂_orbit hτ).1
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hzk : S.z * F.kF = F.kF * S.z := S.z_comm_of_mem_T F.kF_mem
  have htk : S.t * F.kF = F.kF * S.t := (S.data.commute_t F.kF_mem).symm
  set f' := D.g * m' with hf'_def
  have hgz := C.g_z
  have f'z : f' * S.z * f'⁻¹ = S.z := by
    calc f' * S.z * f'⁻¹ = D.g * (m' * S.z * m'⁻¹) * D.g⁻¹ := by rw [hf'_def]; group
      _ = S.z := by rw [hm'z, hgz]
  have f'k : f' * F.kF * f'⁻¹ = S.z * F.kF := by
    calc f' * F.kF * f'⁻¹ = D.g * (m' * F.kF * m'⁻¹) * D.g⁻¹ := by rw [hf'_def]; group
      _ = S.z * F.kF := by rw [hm'k, D.g_k]
  have f't : f' * S.t * f'⁻¹ = S.t * F.kF ∨ f' * S.t * f'⁻¹ = S.z * (S.t * F.kF) := by
    have e : f' * S.t * f'⁻¹ = D.g * (m' * S.t * m'⁻¹) * D.g⁻¹ := by rw [hf'_def]; group
    rcases ht' with h | h
    · left; rw [e, h, D.g_t]
    · right
      rw [e, h]
      calc D.g * (S.z * S.t) * D.g⁻¹ = (D.g * S.z * D.g⁻¹) * (D.g * S.t * D.g⁻¹) := by group
        _ = S.z * (S.t * F.kF) := by rw [hgz, D.g_t]
  have hkk : F.kF * F.kF = 1 := k_mul_k
  have hzz : S.z * S.z = 1 := z_mul_z
  have htkzk : S.t * F.kF * (S.z * F.kF) = S.t * S.z := by
    calc S.t * F.kF * (S.z * F.kF) = S.t * (F.kF * S.z) * F.kF := by group
      _ = S.t * (S.z * F.kF) * F.kF := by rw [hzk]
      _ = S.t * S.z * (F.kF * F.kF) := by group
      _ = S.t * S.z := by rw [hkk, mul_one]
  have f'2 : (f' * f') * S.t * (f' * f')⁻¹ = S.t * S.z := by
    have e : ∀ a b : X, f' * (a * b) * f'⁻¹ = (f' * a * f'⁻¹) * (f' * b * f'⁻¹) :=
      fun a b => by group
    have e2 : (f' * f') * S.t * (f' * f')⁻¹ = f' * (f' * S.t * f'⁻¹) * f'⁻¹ := by group
    rw [e2]
    rcases f't with h | h
    · rw [h, e, h, f'k, htkzk]
    · rw [h, e, e, f'z, h, f'k]
      calc S.z * (S.z * (S.t * F.kF) * (S.z * F.kF)) = (S.z * S.z) * (S.t * F.kF *
            (S.z * F.kF)) := by group
        _ = S.t * S.z := by rw [hzz, one_mul, htkzk]
  intro hf2
  have h1 : f' * f' = 1 := by
    rw [← hf']
    calc (nEl D)⁻¹ * f * nEl D * ((nEl D)⁻¹ * f * nEl D) = (nEl D)⁻¹ * (f * f) * nEl D := by
          group
      _ = 1 := by rw [hf2]; group
  rw [h1, one_mul, inv_one, mul_one] at f'2
  exact S.z_ne_one (by
    have := congrArg (S.t⁻¹ * ·) f'2
    simpa using this.symm)

include C in
theorem Zs_le_T₂ : C.Zs ≤ D.T₂ := by
  intro f hf
  rcases C.mem_Zs.mp hf with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact z_mem_T₂ D
  · exact k_mem_T₂ D
  · exact mul_mem (z_mem_T₂ D) (k_mem_T₂ D)

include C in
theorem Zs_sq {f : X} (hf : f ∈ C.Zs) : f * f = 1 := by
  rcases C.mem_Zs.mp hf with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact z_mul_z
  · exact k_mul_k
  · have hzk : S.z * F.kF = F.kF * S.z := S.z_comm_of_mem_T F.kF_mem
    calc S.z * F.kF * (S.z * F.kF) = S.z * (F.kF * S.z) * F.kF := by group
      _ = S.z * S.z * (F.kF * F.kF) := by rw [← hzk]; group
      _ = 1 := by rw [z_mul_z, k_mul_k, one_mul]

include C in
theorem conj_out_mem_Zs {f : X} (hf : (hEl D)⁻¹ * f ∈ M D ∨ D.w₂⁻¹ * ((hEl D)⁻¹ * f) ∈ M D)
    {x : X} (hx : x ∈ C.Zs) : f * x * f⁻¹ ∈ C.Zs := by
  obtain ⟨hfz, hfk⟩ := C.out_z_k hf
  rw [C.mem_Zs] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · left; group
  · right; left; exact hfz
  · right; right; right; exact hfk
  · right; right; left
    calc f * (S.z * F.kF) * f⁻¹ = (f * S.z * f⁻¹) * (f * F.kF * f⁻¹) := by group
      _ = F.kF := by rw [hfz, hfk, ← mul_assoc, z_mul_z, one_mul]

include C hP hRP hPL in
theorem le_R_of_elem (A : Subgroup X) (hAP : A ≤ P) (hA : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A = 16) : A ≤ D.R := by
  by_contra hnot
  obtain ⟨f₀, hf₀A, hf₀R⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hout : ∀ a ∈ A, a ∉ D.R → (hEl D)⁻¹ * a ∈ M D := by
    intro a ha haR
    rcases C.cases_out hP hRP hPL (hAP ha) haR with h | h
    · exact h
    · exact absurd (hA a ha) (C.sq_ne_one h)
  have hf₀M := hout f₀ hf₀A hf₀R
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 := hA _ (mul_mem ha hb)
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * (b * a) * (b * b) := by group
      _ = b * a := by rw [hA a ha, hA b hb, one_mul, mul_one]
  have hART : ∀ a ∈ A, a ∈ D.R → a ∈ D.T₂ := by
    intro a ha haR
    by_contra haT
    have hafR : a * f₀ ∉ D.R := fun h => hf₀R (by
      have := mul_mem (inv_mem haR) h
      rwa [inv_mul_cancel_left] at this)
    have h1 := hout _ (mul_mem ha hf₀A) hafR
    have h2 : (hEl D)⁻¹ * a * hEl D ∈ M D := by
      have e : (hEl D)⁻¹ * a * hEl D =
          ((hEl D)⁻¹ * (a * f₀)) * ((hEl D)⁻¹ * f₀)⁻¹ := by group
      rw [e]; exact mul_mem h1 (inv_mem hf₀M)
    have h3 : a ∈ M D := by
      have := conj_mem_M D C.hEl_mem_N h2
      rwa [show hEl D * ((hEl D)⁻¹ * a * hEl D) * (hEl D)⁻¹ = a by group] at this
    exact haT (C.mem_T₂_of_mem_M hP hRP (hAP ha) h3)
  have hcover : ∀ b ∈ A, f₀⁻¹ * b ∈ D.T₂ ∨ b ∈ D.T₂ := by
    intro b hb
    by_cases hbR : b ∈ D.R
    · exact Or.inr (hART b hb hbR)
    · left
      have h1 := hout b hb hbR
      have hM : f₀⁻¹ * b ∈ M D := by
        have e : f₀⁻¹ * b = ((hEl D)⁻¹ * f₀)⁻¹ * ((hEl D)⁻¹ * b) := by group
        rw [e]; exact mul_mem (inv_mem hf₀M) h1
      exact C.mem_T₂_of_mem_M hP hRP (mul_mem (inv_mem (hAP hf₀A)) (hAP hb)) hM
  have hrel : D.T₂.relIndex A ∣ 2 :=
    Subgroup.relIndex_dvd_two_iff'.mpr ⟨f₀⁻¹, inv_mem hf₀A, hcover⟩
  have hrel1 : D.T₂.relIndex A ≠ 1 := fun h =>
    hf₀R (D.T₂_le (Subgroup.relIndex_eq_one.mp h hf₀A))
  have hrel2 : D.T₂.relIndex A = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hrel
    have hpos : D.T₂.relIndex A ≠ 0 := fun h => by rw [h] at hrel; norm_num at hrel
    omega
  have hmc := Subgroup.relIndex_mul_card (H := D.T₂) (K := A)
  rw [hrel2, hcard] at hmc
  have hcard8 : Nat.card (D.T₂ ⊓ A : Subgroup X) = 8 := by omega
  obtain ⟨-, hf₀k⟩ := C.out_z_k (Or.inl hf₀M)
  have hkA : F.kF ∉ A := by
    intro hk
    have h1 : f₀ * F.kF * f₀⁻¹ = F.kF := by
      rw [hcommA f₀ hf₀A F.kF hk, mul_inv_cancel_right]
    rw [hf₀k] at h1
    exact S.z_ne_one (by simpa using h1)
  have hBsq : ∀ b ∈ (D.T₂ ⊓ A) ⊔ C.Zs, b * b = 1 :=
    sq_eq_one_of_mem_sup (fun a ha => hA a ha.2) (fun f hf => C.Zs_sq hf)
      (fun a ha f hf => by
        rcases C.mem_Zs.mp hf with rfl | rfl | rfl | rfl
        · group
        · exact (C.comm_z_k (D.T₂_le ha.1)).1
        · exact (C.comm_z_k (D.T₂_le ha.1)).2
        · rw [← mul_assoc, (C.comm_z_k (D.T₂_le ha.1)).1, mul_assoc,
            (C.comm_z_k (D.T₂_le ha.1)).2, mul_assoc])
  have hBT : (D.T₂ ⊓ A) ⊔ C.Zs ≤ D.T₂ := sup_le inf_le_left C.Zs_le_T₂
  have hBcard : 16 ≤ Nat.card ((D.T₂ ⊓ A) ⊔ C.Zs : Subgroup X) := by
    have hdvd : Nat.card (D.T₂ ⊓ A : Subgroup X) ∣ Nat.card ((D.T₂ ⊓ A) ⊔ C.Zs : Subgroup X) :=
      Subgroup.card_dvd_of_le le_sup_left
    rw [hcard8] at hdvd
    have hne : Nat.card ((D.T₂ ⊓ A) ⊔ C.Zs : Subgroup X) ≠ 8 := by
      intro h8
      have heq : D.T₂ ⊓ A = (D.T₂ ⊓ A) ⊔ C.Zs :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h8, hcard8])
      have hk : F.kF ∈ (D.T₂ ⊓ A) ⊔ C.Zs :=
        le_sup_right (a := D.T₂ ⊓ A) (C.mem_Zs.mpr (Or.inr (Or.inr (Or.inl rfl))))
      rw [← heq] at hk
      exact hkA hk.2
    obtain ⟨c, hc⟩ := hdvd
    have hpos : 0 < Nat.card ((D.T₂ ⊓ A) ⊔ C.Zs : Subgroup X) := Nat.card_pos
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  obtain ⟨i, hi⟩ := C.le_Fs_of_elem _ (hBT.trans D.T₂_le) hBsq hBcard
  have hBi : (D.T₂ ⊓ A) ⊔ C.Zs = C.Fs i :=
    Subgroup.eq_of_le_of_card_ge hi (by rw [C.card_Fs]; exact hBcard)
  have hi6 : i.val < 6 := by
    by_contra h6
    have h1 : C.Fs i ⊓ D.T₂ = C.Fs i := inf_eq_left.mpr (hBi ▸ hBT)
    have h2 := C.card_Fs_inf_T₂ (i := i) (by omega)
    rw [h1, C.card_Fs] at h2
    omega
  have hf₀B : conjSub f₀ ((D.T₂ ⊓ A) ⊔ C.Zs) = (D.T₂ ⊓ A) ⊔ C.Zs := by
    refine conjSub_eq_of_le ?_ le_rfl
    rw [conjSub, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · refine conjSub_le_iff.mpr fun a ha => ?_
      rw [hcommA f₀ hf₀A a ha.2, mul_inv_cancel_right]
      exact ha
    · exact conjSub_le_iff.mpr fun x hx => C.conj_out_mem_Zs (Or.inl hf₀M) hx
  exact (C.out_perm (Or.inl hf₀M)).1 i hi6 (hBi ▸ hf₀B)

include C in
theorem R_le_sup : D.R ≤ C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2 ⊔ C.Fs 6 := by
  rw [← C.range_eq]
  refine RH.range_le C.ι fun g hg => ?_
  have h0 : ∀ c, RH.pG 0 c = true → C.ι c ∈ C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2 ⊔ C.Fs 6 :=
    fun c hc => le_sup_left (a := C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2) (le_sup_left (a := C.Fs 0 ⊔ C.Fs 1)
      (le_sup_left (a := C.Fs 0) (C.ι_mem_Fs.mpr hc)))
  have h1 : ∀ c, RH.pG 1 c = true → C.ι c ∈ C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2 ⊔ C.Fs 6 :=
    fun c hc => le_sup_left (a := C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2) (le_sup_left (a := C.Fs 0 ⊔ C.Fs 1)
      (le_sup_right (a := C.Fs 0) (C.ι_mem_Fs.mpr hc)))
  have h2 : ∀ c, RH.pG 2 c = true → C.ι c ∈ C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2 ⊔ C.Fs 6 :=
    fun c hc => le_sup_left (a := C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2)
      (le_sup_right (a := C.Fs 0 ⊔ C.Fs 1) (C.ι_mem_Fs.mpr hc))
  have h6 : ∀ c, RH.pG 6 c = true → C.ι c ∈ C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2 ⊔ C.Fs 6 :=
    fun c hc => le_sup_right (a := C.Fs 0 ⊔ C.Fs 1 ⊔ C.Fs 2) (C.ι_mem_Fs.mpr hc)
  simp only [RH.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show RH.w₂ = RH.w₂ * RH.t * RH.t⁻¹ by group, map_mul, map_inv]
    exact mul_mem (h6 _ (by decide +kernel)) (inv_mem (h0 _ (by decide +kernel)))
  · exact h2 _ (by decide +kernel)
  · rw [show RH.x = RH.u * RH.y⁻¹ by rw [RH.u]; group, map_mul, map_inv]
    exact mul_mem (h1 _ (by decide +kernel)) (inv_mem (h0 _ (by decide +kernel)))
  · exact h0 _ (by decide +kernel)
  · exact h0 _ (by decide +kernel)
  · exact h0 _ (by decide +kernel)
  · exact h0 _ (by decide +kernel)

include C hP hRP hPL in
theorem isSylow_P {q : X} (hqP : q ∈ P) (hqL : q ∉ L₀ D) :
    ∃ Syl : Sylow 2 X, (Syl : Subgroup X) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨w, hwN, hwP, hwp⟩ := exists_mem_normalizer_not_mem hP hne
  have hqR : q ∉ D.R := fun h => hqL (R_le_L₀ h)
  obtain ⟨-, hq0, hq2⟩ := C.out_perm (C.cases_out hP hRP hPL hqP hqR)
  have hwP' : conjSub w P = P := conjSub_eq_self_iff.mpr hwN
  have hconjR : ∀ i : Fin 8, conjSub w (C.Fs i) ≤ D.R := by
    intro i
    refine C.le_R_of_elem hP hRP hPL _ ?_ ?_ (by rw [card_conjSub, C.card_Fs])
    · rw [← hwP']; exact conjSub_mono _ ((C.Fs_le_R i).trans hRP)
    · intro a ha
      have hb := C.sq_of_mem_Fs (mem_conjSub.mp ha)
      calc a * a = w * ((w⁻¹ * a * w) * (w⁻¹ * a * w)) * w⁻¹ := by group
        _ = 1 := by rw [hb, mul_one, mul_inv_cancel]
  have hwR : conjSub w D.R = D.R := by
    refine conjSub_eq_of_le ?_ le_rfl
    refine (conjSub_mono _ C.R_le_sup).trans ?_
    rw [conjSub, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le (sup_le (sup_le (hconjR 0) (hconjR 1)) (hconjR 2)) (hconjR 6)
  obtain ⟨j, hj⟩ := C.eq_Fs_of_elem (conjSub w (C.Fs 0)) (hconjR 0) (fun a ha => by
      have hb := C.sq_of_mem_Fs (mem_conjSub.mp ha)
      calc a * a = w * ((w⁻¹ * a * w) * (w⁻¹ * a * w)) * w⁻¹ := by group
        _ = 1 := by rw [hb, mul_one, mul_inv_cancel])
    (by rw [card_conjSub, C.card_Fs])
  have hnorm : ∀ r ∈ D.R, ∀ f ∈ C.Fs j, r * f * r⁻¹ ∈ C.Fs j := by
    intro r hr f hf
    rw [← hj] at hf ⊢
    obtain ⟨e, he, rfl⟩ := hf
    have hr' : w⁻¹ * r * w ∈ D.R := by
      rw [← mem_conjSub, hwR]; exact hr
    have hrE : w⁻¹ * r * w ∈ normalizer (F.E₁ : Set X) := D.R_le hr'
    have he' : (w⁻¹ * r * w) * e * (w⁻¹ * r * w)⁻¹ ∈ C.Fs 0 := by
      rw [C.Fs_zero] at he ⊢
      exact (mem_normalizer_iff.mp hrE e).mp he
    refine ⟨_, he', ?_⟩
    show w * ((w⁻¹ * r * w) * e * (w⁻¹ * r * w)⁻¹) * w⁻¹ = r * (w * e * w⁻¹) * r⁻¹
    group
  have hR2 : ∀ u : X, u ∈ P ⊔ zpowers w → conjSub u (C.Fs 0) = C.Fs 0 → u ∈ D.R := by
    intro u hu hu0
    have hle : D.R ⊔ zpowers u ≤ P ⊔ zpowers w :=
      sup_le (hRP.trans le_sup_left) (zpowers_le.mpr hu)
    have hEu : u ∈ normalizer (F.E₁ : Set X) := by
      rw [← C.Fs_zero]; exact conjSub_eq_self_iff.mp hu0
    have := D.R_maximal _ (hwp.to_le hle) le_sup_left
      (sup_le D.R_le (zpowers_le.mpr hEu))
    rw [← this]
    exact le_sup_right (a := D.R) (mem_zpowers u)
  have hwPw : w ∈ P ⊔ zpowers w := le_sup_right (a := P) (mem_zpowers w)
  rcases C.normal_cases hnorm with rfl | rfl
  · exact hwP (hRP (hR2 w hwPw hj))
  · have h1 : conjSub (q⁻¹ * w) (C.Fs 0) = C.Fs 0 := by
      rw [conjSub_mul, hj, ← hq0, conjSub_inv_conjSub]
    have h2 := hR2 (q⁻¹ * w) (mul_mem (inv_mem (le_sup_left (a := P) hqP)) hwPw) h1
    apply hwP
    have := mul_mem hqP (hRP h2)
    rwa [mul_inv_cancel_left] at this

end P

end Setup

end Sec5H

end CFSG.ComponentClassification.HSFLit
