module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type*} [Field K] (σ : K ≃+* K) {m : ℕ}

@[expose] def perp (S : Submodule K (Fin m → K)) : Submodule K (Fin m → K) where
  carrier := {v | ∀ s ∈ S, herm σ v s = 0}
  zero_mem' s _ := herm_zero_left σ s
  add_mem' {u v} hu hv s hs := by rw [herm_add_left, hu s hs, hv s hs, add_zero]
  smul_mem' c v hv s hs := by rw [herm_smul_left, hv s hs, mul_zero]

@[expose] def rad (S : Submodule K (Fin m → K)) : Submodule K (Fin m → K) := S ⊓ perp σ S

@[expose] def Nondeg (S : Submodule K (Fin m → K)) : Prop :=
  ∀ s ∈ S, (∀ t ∈ S, herm σ s t = 0) → s = 0

@[expose] def IsTotIso (S : Submodule K (Fin m → K)) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, herm σ s t = 0

@[expose] def Orth (σ : K ≃+* K) (x y : Submodule K (Fin m → K)) : Prop :=
  ∀ u ∈ x, ∀ v ∈ y, herm σ u v = 0

variable {σ}

theorem mem_perp {S : Submodule K (Fin m → K)} {v : Fin m → K} :
    v ∈ perp σ S ↔ ∀ s ∈ S, herm σ v s = 0 := Iff.rfl

theorem mem_rad {S : Submodule K (Fin m → K)} {v : Fin m → K} :
    v ∈ rad σ S ↔ v ∈ S ∧ ∀ s ∈ S, herm σ v s = 0 := Iff.rfl

theorem nondeg_iff_rad_eq_bot {S : Submodule K (Fin m → K)} : Nondeg σ S ↔ rad σ S = ⊥ := by
  rw [Submodule.eq_bot_iff]
  exact ⟨fun h v hv => h v hv.1 hv.2, fun h v hv hv' => h v ⟨hv, hv'⟩⟩

theorem mem_perp_span_singleton {a v : Fin m → K} :
    v ∈ perp σ (K ∙ a) ↔ herm σ v a = 0 := by
  refine ⟨fun h => h a (Submodule.mem_span_singleton_self a), fun h s hs => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  rw [herm_smul_right, h, mul_zero]

theorem herm_self_ne_zero_of_nondeg_span {a : Fin m → K} (ha : a ≠ 0) (h : Nondeg σ (K ∙ a)) :
    herm σ a a ≠ 0 := by
  intro h0
  refine ha (h a (Submodule.mem_span_singleton_self a) fun t ht => ?_)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
  rw [herm_smul_right, h0, mul_zero]

theorem nondeg_span_singleton {a : Fin m → K} (ha : herm σ a a ≠ 0) : Nondeg σ (K ∙ a) := by
  intro s hs hs'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have := hs' a (Submodule.mem_span_singleton_self a)
  rw [herm_smul_left] at this
  rcases mul_eq_zero.mp this with h | h
  · rw [(map_eq_zero_iff σ σ.injective).mp h, zero_smul]
  · exact absurd h ha

section Basic

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem herm_eq_zero_iff (x y : Fin m → K) : herm σ x y = 0 ↔ herm σ y x = 0 :=
  ⟨herm_eq_zero_comm σ hσ.invol, herm_eq_zero_comm σ hσ.invol⟩

theorem exists_aniso_of_not_isTotIso {S : Submodule K (Fin m → K)} (h : ¬ IsTotIso σ S) :
    ∃ v ∈ S, herm σ v v ≠ 0 := by
  by_contra! hv
  exact h fun s hs t ht => herm_eq_zero_of_forall_isotropic hσ hv hs ht

theorem exists_aniso_of_nondeg {S : Submodule K (Fin m → K)} (hS : Nondeg σ S) (hne : S ≠ ⊥) :
    ∃ v ∈ S, herm σ v v ≠ 0 := by
  refine exists_aniso_of_not_isTotIso hσ fun htot => hne ?_
  rw [Submodule.eq_bot_iff]
  exact fun s hs => hS s hs (htot s hs)

theorem Nondeg.sup_of_orth {A B : Submodule K (Fin m → K)} (hA : Nondeg σ A) (hB : Nondeg σ B)
    (hAB : Orth σ A B) : Nondeg σ (A ⊔ B) := by
  intro s hs hs'
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hs
  have hBA : ∀ b ∈ B, ∀ a ∈ A, herm σ b a = 0 := fun b hb a ha =>
    (herm_eq_zero_iff hσ _ _).mp (hAB a ha b hb)
  have h1 : a = 0 := by
    refine hA a ha fun t ht => ?_
    have := hs' t (Submodule.mem_sup_left ht)
    rwa [herm_add_left, hBA b hb t ht, add_zero] at this
  have h2 : b = 0 := by
    refine hB b hb fun t ht => ?_
    have := hs' t (Submodule.mem_sup_right ht)
    have hat : herm σ a t = 0 := hAB a ha t ht
    rwa [herm_add_left, hat, zero_add] at this
  rw [h1, h2, add_zero]

end Basic

@[expose] def projPerp (σ : K ≃+* K) (a : Fin m → K) : (Fin m → K) →ₗ[K] (Fin m → K) :=
  LinearMap.id - ((herm σ a a)⁻¹ • hermL σ a).smulRight a

theorem projPerp_apply (a v : Fin m → K) :
    projPerp σ a v = v - ((herm σ a a)⁻¹ * herm σ a v) • a := by
  simp [projPerp]

section Proj

variable (hσ : IsUnitaryInvolution σ) {a : Fin m → K} (ha : herm σ a a ≠ 0)
include hσ ha

theorem herm_projPerp_left (v : Fin m → K) : herm σ (projPerp σ a v) a = 0 := by
  rw [projPerp_apply, herm_sub_left, herm_smul_left, map_mul, map_inv₀, herm_self_fixed σ hσ.invol,
    ← herm_conj σ hσ.invol]
  field_simp
  ring

theorem herm_projPerp_right (v : Fin m → K) : herm σ a (projPerp σ a v) = 0 :=
  (herm_eq_zero_iff hσ _ _).mp (herm_projPerp_left hσ ha v)

omit hσ in
theorem projPerp_smul_self (c : K) : projPerp σ a (c • a) = 0 := by
  rw [projPerp_apply, herm_smul_right]
  have : (herm σ a a)⁻¹ * (c * herm σ a a) = c := by field_simp
  rw [this, sub_self]

theorem herm_projPerp_projPerp (v w : Fin m → K) :
    herm σ (projPerp σ a v) (projPerp σ a w) =
      herm σ v w - (herm σ a a)⁻¹ * (herm σ v a * herm σ a w) := by
  have h1 : herm σ (projPerp σ a v) (projPerp σ a w) = herm σ (projPerp σ a v) w := by
    rw [projPerp_apply a w, herm_sub_right, herm_smul_right, herm_projPerp_left hσ ha, mul_zero,
      sub_zero]
  rw [h1, projPerp_apply a v, herm_sub_left, herm_smul_left, map_mul, map_inv₀,
    herm_self_fixed σ hσ.invol, ← herm_conj σ hσ.invol]
  ring

omit hσ in
theorem projPerp_eq_zero_iff {v : Fin m → K} : projPerp σ a v = 0 ↔ v ∈ K ∙ a := by
  constructor
  · intro h
    rw [projPerp_apply, sub_eq_zero] at h
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  · intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    exact projPerp_smul_self ha c

omit hσ ha in
theorem span_sup_span_projPerp (x : Fin m → K) :
    K ∙ a ⊔ K ∙ projPerp σ a x = K ∙ a ⊔ K ∙ x := by
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_singleton_le_iff_mem _ _ |>.mpr ?_)
    rw [projPerp_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)))
  · refine sup_le le_sup_left (Submodule.span_singleton_le_iff_mem _ _ |>.mpr ?_)
    have : x = projPerp σ a x + ((herm σ a a)⁻¹ * herm σ a x) • a := by
      rw [projPerp_apply]; abel
    have hmem : projPerp σ a x + ((herm σ a a)⁻¹ * herm σ a x) • a ∈ K ∙ a ⊔ K ∙ projPerp σ a x :=
      Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)))
    rwa [← this] at hmem

theorem nondeg_span_pair_iff {x : Fin m → K} (hx : x ∉ K ∙ a) :
    Nondeg σ (K ∙ a ⊔ K ∙ x) ↔ herm σ (projPerp σ a x) (projPerp σ a x) ≠ 0 := by
  rw [← span_sup_span_projPerp (σ := σ) (a := a) x]
  have hy0 : projPerp σ a x ≠ 0 := fun h => hx ((projPerp_eq_zero_iff ha).mp h)
  constructor
  · intro hnd hyy
    have := hnd (projPerp σ a x) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      fun t ht => by
        obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp ht
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [herm_add_right, herm_smul_right, herm_smul_right, herm_projPerp_left hσ ha, hyy,
          mul_zero, mul_zero, add_zero]
    exact hy0 this
  · intro hyy
    refine Nondeg.sup_of_orth hσ (nondeg_span_singleton ha) (nondeg_span_singleton hyy) ?_
    intro u hu w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [herm_smul_left, herm_smul_right, herm_projPerp_right hσ ha, mul_zero, mul_zero]

end Proj

theorem finrank_sup_of_disjoint {S T : Submodule K (Fin m → K)} (h : Disjoint S T) :
    finrank K ↥(S ⊔ T) = finrank K S + finrank K T := by
  have := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [h.eq_bot, finrank_bot] at this
  omega

section Split2

variable (hσ : IsUnitaryInvolution σ) {S : Submodule K (Fin m → K)} {a : Fin m → K}
  (haS : a ∈ S) (ha : herm σ a a ≠ 0)

include ha in
theorem disjoint_span_perp : Disjoint (K ∙ a) (perp σ (K ∙ a)) := by
  rw [Submodule.disjoint_def]
  intro v hv hv'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have := mem_perp_span_singleton.mp hv'
  rw [herm_smul_left] at this
  rcases mul_eq_zero.mp this with h | h
  · rw [(map_eq_zero_iff σ σ.injective).mp h, zero_smul]
  · exact absurd h ha

include hσ haS ha in
theorem span_sup_inf_perp : K ∙ a ⊔ (S ⊓ perp σ (K ∙ a)) = S := by
  apply le_antisymm
  · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr haS) inf_le_left
  · intro v hv
    have hv' : v = projPerp σ a v + ((herm σ a a)⁻¹ * herm σ a v) • a := by
      rw [projPerp_apply]; abel
    rw [hv']
    refine Submodule.add_mem _ (Submodule.mem_sup_right ⟨?_, ?_⟩)
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)))
    · rw [projPerp_apply]
      exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ haS)
    · exact mem_perp_span_singleton.mpr (herm_projPerp_left hσ ha v)

include hσ haS ha in
theorem finrank_eq_inf_perp_add_one :
    finrank K S = finrank K ↥(S ⊓ perp σ (K ∙ a)) + 1 := by
  have h := finrank_sup_of_disjoint
    ((disjoint_span_perp ha).mono_right (inf_le_right : S ⊓ perp σ (K ∙ a) ≤ _))
  rw [span_sup_inf_perp hσ haS ha, finrank_span_singleton (fun h0 => ha (by rw [h0]; simp))] at h
  omega

include hσ haS ha in
theorem Nondeg.inf_perp_span_singleton (hS : Nondeg σ S) :
    Nondeg σ (S ⊓ perp σ (K ∙ a)) := by
  intro s hs hs'
  refine hS s hs.1 fun t ht => ?_
  have hsplit : t ∈ K ∙ a ⊔ (S ⊓ perp σ (K ∙ a)) := by rwa [span_sup_inf_perp hσ haS ha]
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hsplit
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [herm_add_right, herm_smul_right, hs' w hw]
  have : herm σ s a = 0 := mem_perp_span_singleton.mp hs.2
  rw [this]; ring

end Split2

theorem Orth.symm (hσ : IsUnitaryInvolution σ) {x y : Submodule K (Fin m → K)} (h : Orth σ x y) :
    Orth σ y x := fun v hv u hu => (herm_eq_zero_iff hσ _ _).mp (h u hu v hv)

theorem orth_span_singleton_iff {a b : Fin m → K} : Orth σ (K ∙ a) (K ∙ b) ↔ herm σ a b = 0 := by
  constructor
  · exact fun h => h a (Submodule.mem_span_singleton_self a) b
      (Submodule.mem_span_singleton_self b)
  · intro h u hu v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [herm_smul_left, herm_smul_right, h, mul_zero, mul_zero]

theorem Orth.sup_right {x y z : Submodule K (Fin m → K)} (hy : Orth σ x y) (hz : Orth σ x z) :
    Orth σ x (y ⊔ z) := by
  intro u hu v hv
  obtain ⟨y', hy', z', hz', rfl⟩ := Submodule.mem_sup.mp hv
  rw [herm_add_right, hy u hu y' hy', hz u hu z' hz', add_zero]

theorem Orth.sup_left {x y z : Submodule K (Fin m → K)} (hx : Orth σ x z) (hy : Orth σ y z) :
    Orth σ (x ⊔ y) z := by
  intro u hu v hv
  obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.mp hu
  rw [herm_add_left, hx x' hx' v hv, hy y' hy' v hv, add_zero]

theorem Orth.mono {x y x' y' : Submodule K (Fin m → K)} (h : Orth σ x y) (hx : x' ≤ x)
    (hy : y' ≤ y) : Orth σ x' y' := fun u hu v hv => h u (hx hu) v (hy hv)

theorem not_mem_span_of_ne {a c : Fin m → K} (hc : herm σ c c ≠ 0) (h : K ∙ a ≠ K ∙ c) :
    c ∉ K ∙ a := by
  intro hmem
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  have ht : t ≠ 0 := by
    rintro rfl
    apply hc
    simp
  exact h (Submodule.span_singleton_smul_eq (IsUnit.mk0 t ht) a).symm

theorem finrank_span_singleton_le_one (v : Fin m → K) : finrank K ↥(K ∙ v) ≤ 1 := by
  by_cases hv : v = 0
  · rw [hv, Submodule.span_zero_singleton, finrank_bot]
    exact Nat.zero_le _
  · rw [finrank_span_singleton hv]

section Decomp

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem sup_inf_perp_of_nondeg :
    ∀ (n : ℕ) {P W : Submodule K (Fin m → K)}, finrank K ↥P = n → Nondeg σ P → P ≤ W →
      P ⊔ (W ⊓ perp σ P) = W := by
  intro n
  induction n with
  | zero =>
    intro P W hP _ hPW
    have : P = ⊥ := Submodule.finrank_eq_zero.mp hP
    subst this
    have : perp σ (⊥ : Submodule K (Fin m → K)) = ⊤ := by
      rw [eq_top_iff]
      intro v _ s hs
      rw [Submodule.mem_bot] at hs
      rw [hs, herm_zero_right]
    rw [this, inf_top_eq, bot_sup_eq]
  | succ n ih =>
    intro P W hP hPnd hPW
    have hne : P ≠ ⊥ := by rintro rfl; simp at hP
    obtain ⟨s, hsP, hs⟩ := exists_aniso_of_nondeg hσ hPnd hne
    have hsW : s ∈ W := hPW hsP
    have hdim := finrank_eq_inf_perp_add_one hσ hsP hs
    have hP'nd : Nondeg σ (P ⊓ perp σ (K ∙ s)) := Nondeg.inf_perp_span_singleton hσ hsP hs hPnd
    have hP'n : finrank K ↥(P ⊓ perp σ (K ∙ s)) = n := by omega
    have hP'W : P ⊓ perp σ (K ∙ s) ≤ W ⊓ perp σ (K ∙ s) := inf_le_inf_right _ hPW
    have hih := ih (P := P ⊓ perp σ (K ∙ s)) (W := W ⊓ perp σ (K ∙ s)) hP'n hP'nd hP'W
    apply le_antisymm
    · exact sup_le hPW inf_le_left
    · intro w hw
      have hw' : w ∈ K ∙ s ⊔ (W ⊓ perp σ (K ∙ s)) := by rwa [span_sup_inf_perp hσ hsW hs]
      obtain ⟨u, hu, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hw'
      have hw₁' : w₁ ∈ (P ⊓ perp σ (K ∙ s)) ⊔
          ((W ⊓ perp σ (K ∙ s)) ⊓ perp σ (P ⊓ perp σ (K ∙ s))) := by
        rwa [hih]
      obtain ⟨p', hp', x, hx, rfl⟩ := Submodule.mem_sup.mp hw₁'
      have huP : u ∈ P := (Submodule.span_singleton_le_iff_mem _ _).mpr hsP hu
      have hxP : x ∈ W ⊓ perp σ P := by
        refine ⟨hx.1.1, fun y hy => ?_⟩
        rw [← span_sup_inf_perp hσ hsP hs] at hy
        obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.mp hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu'
        rw [herm_add_right, herm_smul_right, mem_perp_span_singleton.mp hx.1.2, mul_zero,
          zero_add]
        exact hx.2 w' hw'
      have hrw : u + (p' + x) = (u + p') + x := by abel
      rw [hrw]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (P.add_mem huP hp'.1))
        (Submodule.mem_sup_right hxP)

variable {P W : Submodule K (Fin m → K)}

omit hσ in
theorem disjoint_inf_perp_of_nondeg (hP : Nondeg σ P) : Disjoint P (W ⊓ perp σ P) := by
  rw [Submodule.disjoint_def]
  intro x hxP hxW
  exact hP x hxP hxW.2

theorem finrank_eq_add_finrank_inf_perp (hP : Nondeg σ P) (hPW : P ≤ W) :
    finrank K W = finrank K P + finrank K ↥(W ⊓ perp σ P) := by
  have h := finrank_sup_of_disjoint (disjoint_inf_perp_of_nondeg (W := W) hP)
  rwa [sup_inf_perp_of_nondeg hσ _ rfl hP hPW] at h

theorem Nondeg.inf_perp (hW : Nondeg σ W) (hP : Nondeg σ P) (hPW : P ≤ W) :
    Nondeg σ (W ⊓ perp σ P) := by
  intro x hx hx'
  refine hW x hx.1 fun y hy => ?_
  rw [← sup_inf_perp_of_nondeg hσ _ rfl hP hPW] at hy
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [herm_add_right, hx' w hw, hx.2 u hu, zero_add]

end Decomp

section NondegPlane

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem exists_nondeg_plane_le {U : Submodule K (Fin m → K)} (hU : Nondeg σ U)
    (h2 : 2 ≤ finrank K U) :
    ∃ L : Submodule K (Fin m → K), L ≤ U ∧ finrank K L = 2 ∧ Nondeg σ L := by
  obtain ⟨u₁, hu₁, h₁⟩ := exists_aniso_of_nondeg hσ hU (by rintro rfl; simp at h2)
  have hU' : Nondeg σ (U ⊓ perp σ (K ∙ u₁)) :=
    Nondeg.inf_perp_span_singleton hσ hu₁ h₁ hU
  have hdim := finrank_eq_inf_perp_add_one hσ hu₁ h₁
  obtain ⟨u₂, hu₂, h₂⟩ := exists_aniso_of_nondeg hσ hU' (fun h => by
    rw [h, finrank_bot] at hdim
    omega)
  have hu₂p : herm σ u₁ u₂ = 0 :=
    (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp hu₂.2)
  have hdisj : Disjoint (K ∙ u₁) (K ∙ u₂) :=
    (disjoint_span_perp h₁).mono_right
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hu₂.2)
  have hu₂0 : u₂ ≠ 0 := fun h => h₂ (by rw [h]; simp)
  have hu₁0 : u₁ ≠ 0 := fun h => h₁ (by rw [h]; simp)
  refine ⟨K ∙ u₁ ⊔ K ∙ u₂, sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hu₁)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hu₂.1), ?_,
    Nondeg.sup_of_orth hσ (nondeg_span_singleton h₁) (nondeg_span_singleton h₂) ?_⟩
  · rw [finrank_sup_of_disjoint hdisj, finrank_span_singleton hu₁0, finrank_span_singleton hu₂0]
  · intro u hu w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [herm_smul_left, herm_smul_right, hu₂p, mul_zero, mul_zero]

include hσ in
theorem exists_nondeg_plane_orth {W P : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (hP : Nondeg σ P) (hPW : P ≤ W) (hP2 : finrank K P = 2) (h4 : 4 ≤ finrank K W) :
    ∃ L : Submodule K (Fin m → K), L ≤ W ∧ Nondeg σ L ∧ finrank K L = 2 ∧ Orth σ L P := by
  have hU := Nondeg.inf_perp hσ hW hP hPW
  have hdim := finrank_eq_add_finrank_inf_perp hσ hP hPW
  obtain ⟨L, hLU, hL2, hLnd⟩ := exists_nondeg_plane_le hσ hU (by omega)
  exact ⟨L, hLU.trans inf_le_left, hLnd, hL2, fun u hu v hv => (hLU hu).2 v hv⟩

end NondegPlane

end CFSG.ClassicalInvolution.Phan
