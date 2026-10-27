module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSCore

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open

variable {G : Type} [Group G] {S M : Subgroup G} {r s : ℕ}

@[expose] def ThetaTypeI (S L : Subgroup G) (r s : ℕ) : Prop :=
  ∃ θ : ↥(L ⊔ S) →* Perm (OmegaE r s),
    (∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S) ∧
    (∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥(L ⊔ S), θ m = x) ∧
    ((thompsonJ S).subgroupOf (L ⊔ S)).map θ = Wr r s

theorem normalizer_theta_S_le [Finite G] (hA : Asc81bHyp M S) (hSM : S ≤ M) {Ω : Type*}
    (θ : ↥M →* Perm Ω) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S) (hrange : θ.range = ⊤) :
    ∀ g ∈ Subgroup.normalizer (((S.subgroupOf M).map θ : Subgroup (Perm Ω)) : Set (Perm Ω)),
      g ∈ Subgroup.normalizer
        ((((thompsonJ S).subgroupOf M).map θ : Subgroup (Perm Ω)) : Set (Perm Ω)) := by
  intro g hg
  obtain ⟨m, rfl⟩ : g ∈ θ.range := by rw [hrange]; trivial
  have key : ∀ m' : ↥M, θ m' ∈ Subgroup.normalizer
      (((S.subgroupOf M).map θ : Subgroup (Perm Ω)) : Set (Perm Ω)) →
      ∀ x : ↥M, (x : G) ∈ S → ((m' * x * m'⁻¹ : ↥M) : G) ∈ S := by
    intro m' hm' x hx
    have hxP : θ x ∈ (S.subgroupOf M).map θ := ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have h1 : θ m' * θ x * (θ m')⁻¹ ∈ (S.subgroupOf M).map θ :=
      ((Subgroup.mem_normalizer_iff.1 hm') (θ x)).1 hxP
    obtain ⟨z, hz, hzθ⟩ := h1
    have hzS : (z : G) ∈ S := Subgroup.mem_subgroupOf.1 hz
    have hk : θ (z⁻¹ * (m' * x * m'⁻¹)) = 1 := by
      rw [map_mul, map_inv, hzθ]; simp only [map_mul, map_inv]; group
    have := hker _ hk
    have h2 : ((m' * x * m'⁻¹ : ↥M) : G) = (z : G) * ((z⁻¹ * (m' * x * m'⁻¹) : ↥M) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [h2]
    exact S.mul_mem hzS this
  have hm : (m : G) ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := key m hg ⟨x, hSM hx⟩ hx
      simpa using this
    · intro hx
      have hginv : θ m⁻¹ ∈ Subgroup.normalizer
          (((S.subgroupOf M).map θ : Subgroup (Perm Ω)) : Set (Perm Ω)) := by
        rw [map_inv]; exact inv_mem hg
      have hxM : x ∈ M := by
        have h1 : (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * (m : G) ∈ M :=
          M.mul_mem (M.mul_mem (M.inv_mem m.2) (hSM hx)) m.2
        simpa [mul_assoc] using h1
      have := key m⁻¹ hginv ⟨(m : G) * x * (m : G)⁻¹, hSM hx⟩ hx
      simpa [mul_assoc] using this
  exact theta_mem_normalizer_W θ m hm

theorem normal_isPGroup_le_Wr_two {r : ℕ} (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r)
    (U : Subgroup (Perm (OmegaE r 2))) (hU : IsPGroup 2 U)
    (hUN : ∀ g ∈ U, g ∈ Subgroup.normalizer (Wr r 2 : Set (Perm (OmegaE r 2))))
    (hnorm : ∀ h ∈ Subgroup.normalizer (Wr r 2 : Set (Perm (OmegaE r 2))), ∀ u ∈ U,
      h * u * h⁻¹ ∈ U) :
    ∀ u ∈ U, ∃ σ₁ ∈ blockFix (Fin r), ∃ σ₂ : Perm (Fin 2),
      u = embL r 2 σ₁ * Perm.sumCongr 1 σ₂ := by
  classical
  let ι : ↥(wStab (Fin r) Bool) × Perm (Fin 2) →* Perm (OmegaE r 2) :=
    (Perm.sumCongrHom (Fin r × Bool) (Fin 2)).comp
      (MonoidHom.prodMap (wStab (Fin r) Bool).subtype (MonoidHom.id _))
  have hι : ∀ x, ι x = Perm.sumCongr x.1.1 x.2 := fun x => rfl
  have hιinj : Function.Injective ι := by
    intro x y h
    have h1 := Perm.sumCongrHom_injective (α := Fin r × Bool) (β := Fin 2)
      (show Perm.sumCongrHom (Fin r × Bool) (Fin 2) (x.1.1, x.2) =
        Perm.sumCongrHom (Fin r × Bool) (Fin 2) (y.1.1, y.2) from h)
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    exact Prod.ext (Subtype.ext e1) e2
  have hιN : ∀ x, ι x ∈ Subgroup.normalizer (Wr r 2 : Set (Perm (OmegaE r 2))) := fun x => by
    rw [hι]; exact sumCongr_mem_normalizer x.1.2 x.2
  let Uh : Subgroup (↥(wStab (Fin r) Bool) × Perm (Fin 2)) := U.comap ι
  have hUh2 : IsPGroup 2 Uh := hU.comap_of_injective ι hιinj
  have hUhn : Uh.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ι (g * n * g⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hιN g) _ hn
  let Ψ : ↥(wStab (Fin r) Bool) × Perm (Fin 2) →* Perm (Fin r) :=
    (wStabAction (Fin r)).comp (MonoidHom.fst _ _)
  have hΨ : Function.Surjective Ψ := by
    intro π
    refine ⟨(⟨wLift π, wLift_mem_wStab π⟩, 1), ?_⟩
    refine Equiv.ext fun a => ?_
    have := wStabAction_apply (ι := Fin r) ⟨wLift π, wLift_mem_wStab π⟩ (a, false)
    show wStabAction (Fin r) ⟨wLift π, wLift_mem_wStab π⟩ a = π a
    simpa [wLift_apply] using this
  have hle : Uh.map Ψ ≤ CFSG.pCore 2 (Perm (Fin r)) :=
    le_sSup ⟨Subgroup.Normal.map hUhn Ψ hΨ, hUh2.map Ψ⟩
  rw [pCore_perm_eq_bot (by omega)] at hle
  intro u hu
  obtain ⟨σ1, h1, σ2, rfl⟩ := mem_normalizer_Wr_iff.1 (hUN u hu)
  have hx : (⟨σ1, h1⟩, σ2) ∈ Uh := by
    show ι (⟨σ1, h1⟩, σ2) ∈ U
    rw [hι]; exact hu
  have h0 : Ψ (⟨σ1, h1⟩, σ2) = 1 := by
    have : Ψ (⟨σ1, h1⟩, σ2) ∈ (⊥ : Subgroup _) := hle ⟨_, hx, rfl⟩
    simpa using this
  have hσ1 : σ1 ∈ blockFix (Fin r) := by
    intro p
    have h4 : wStabAction (Fin r) ⟨σ1, h1⟩ = 1 := h0
    have h3 := wStabAction_apply (ι := Fin r) ⟨σ1, h1⟩ p
    rw [h4] at h3
    exact h3.symm
  refine ⟨σ1, hσ1, σ2, ?_⟩
  show Perm.sumCongr σ1 σ2 = Perm.sumCongr σ1 1 * Perm.sumCongr 1 σ2
  rw [Perm.sumCongr_mul, mul_one, one_mul]


theorem false_of_theta_s_two [Finite G] (hA : Asc81bHyp M S) (hSM : S ≤ M)
    (θ : ↥M →* Perm (OmegaE r 2))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r 2), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r 2) (hr1 : 1 ≤ r)
    (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) : False := by
  classical
  obtain ⟨hPN, hP2, hPnorm, hPmax⟩ := theta_S_normal_pCore hA hSM θ hker hAlt hW hr1
  have hrange := theta_range_eq_top θ hAlt hW hr1
  set P : Subgroup (Perm (OmegaE r 2)) := (S.subgroupOf M).map θ with hP
  have hWP : Wr r 2 ≤ P := by
    rw [← hW]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, Subgroup.mem_subgroupOf.2 (thompsonJ_le_self S (Subgroup.mem_subgroupOf.1 hj)), rfl⟩
  let i0 : Fin r := ⟨0, hr1⟩
  let a : OmegaE r 2 := Sum.inl (i0, false)
  let b : OmegaE r 2 := Sum.inl (i0, true)
  let c0 : OmegaE r 2 := Sum.inr 0
  let c1 : OmegaE r 2 := Sum.inr 1
  have hab : a ≠ b := by simp [a, b]
  have hac0 : a ≠ c0 := by simp [a, c0]
  have hac1 : a ≠ c1 := by simp [a, c1]
  have hbc0 : b ≠ c0 := by simp [b, c0]
  have hbc1 : b ≠ c1 := by simp [b, c1]
  have hc : c0 ≠ c1 := by simp [c0, c1]
  have ht0 : swap a b ∈ Wr r 2 := by
    have h := embL_blockTransp r 2 i0 false
    simp only [Bool.not_false] at h
    rw [h]
    exact ⟨blockTransp i0, swap_mem_blockFix rfl, rfl⟩
  have hu0 : swap c0 c1 = Perm.sumCongr (1 : Perm (Fin r × Bool)) (swap (0 : Fin 2) 1) :=
    (Equiv.Perm.sumCongr_one_swap (0 : Fin 2) 1).symm
  have hu0N : swap c0 c1 ∈ Subgroup.normalizer (Wr r 2 : Set (Perm (OmegaE r 2))) :=
    mem_normalizer_Wr_iff.2 ⟨1, Subgroup.one_mem _, swap (0 : Fin 2) 1, hu0⟩
  have hsq : swap c0 c1 ^ 2 = 1 := by rw [pow_two, swap_mul_self]
  have hcomm : ∀ h ∈ Subgroup.normalizer (Wr r 2 : Set (Perm (OmegaE r 2))),
      Commute h (swap c0 c1) := by
    intro h hh
    obtain ⟨σ1, h1, σ2, rfl⟩ := mem_normalizer_Wr_iff.1 hh
    rw [hu0]
    show Perm.sumCongr σ1 σ2 * Perm.sumCongr 1 (swap (0 : Fin 2) 1) =
      Perm.sumCongr 1 (swap (0 : Fin 2) 1) * Perm.sumCongr σ1 σ2
    rw [Perm.sumCongr_mul, Perm.sumCongr_mul, mul_one, one_mul]
    have hσ : ∀ σ : Perm (Fin 2), σ * swap (0 : Fin 2) 1 = swap (0 : Fin 2) 1 * σ := by decide
    rw [hσ σ2]
  have hu0P : swap c0 c1 ∈ P := by
    have hle : Subgroup.zpowers (swap c0 c1) ≤
        Subgroup.normalizer (Wr r 2 : Set (Perm (OmegaE r 2))) := Subgroup.zpowers_le.2 hu0N
    have hp : IsPGroup 2 (Subgroup.zpowers (swap c0 c1)) := by
      rintro ⟨x, k, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      show ((swap c0 c1) ^ k) ^ (2 ^ 1) = 1
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm k ((2 : ℕ) : ℤ), zpow_mul, zpow_natCast,
        hsq, one_zpow]
    have hn : ∀ h ∈ Subgroup.normalizer (Wr r 2 : Set (Perm (OmegaE r 2))),
        ∀ u ∈ Subgroup.zpowers (swap c0 c1), h * u * h⁻¹ ∈ Subgroup.zpowers (swap c0 c1) := by
      rintro h hh u ⟨k, rfl⟩
      have := ((hcomm h hh).zpow_right k).mul_inv_cancel
      rw [this]
      exact ⟨k, rfl⟩
    exact hPmax _ hle hp hn (Subgroup.mem_zpowers _)
  have hPle : P ≤ Wr r 2 ⊔ Subgroup.zpowers (swap c0 c1) := by
    intro x hx
    obtain ⟨σ1, h1, σ2, rfl⟩ :=
      normal_isPGroup_le_Wr_two hr P hP2 (fun g hg => hPN hg) hPnorm x hx
    refine Subgroup.mul_mem_sup ⟨σ1, h1, rfl⟩ ?_
    have h2 : ∀ σ : Perm (Fin 2), σ = 1 ∨ σ = swap (0 : Fin 2) 1 := by decide
    rcases h2 σ2 with rfl | rfl
    · have h1 : Perm.sumCongr (1 : Perm (Fin r × Bool)) (1 : Perm (Fin 2)) = 1 :=
        Equiv.ext fun z => by rcases z with z | z <;> rfl
      rw [h1]; exact Subgroup.one_mem _
    · rw [← hu0]; exact Subgroup.mem_zpowers _
  let g : Perm (OmegaE r 2) := swap a c0 * swap b c1
  have hga : g a = c0 := by
    show swap a c0 (swap b c1 a) = c0
    rw [swap_apply_of_ne_of_ne hab hac1, swap_apply_left]
  have hgb : g b = c1 := by
    show swap a c0 (swap b c1 b) = c1
    rw [swap_apply_left, swap_apply_of_ne_of_ne hac1.symm hc.symm]
  have hgc0 : g c0 = a := by
    show swap a c0 (swap b c1 c0) = a
    rw [swap_apply_of_ne_of_ne hbc0.symm hc, swap_apply_right]
  have hgc1 : g c1 = b := by
    show swap a c0 (swap b c1 c1) = b
    rw [swap_apply_right, swap_apply_of_ne_of_ne hab.symm hbc0]
  have hgfix : ∀ z : OmegaE r 2, z ≠ a → z ≠ b → z ≠ c0 → z ≠ c1 → g z = z := by
    intro z h1 h2 h3 h4
    show swap a c0 (swap b c1 z) = z
    rw [swap_apply_of_ne_of_ne h2 h4, swap_apply_of_ne_of_ne h1 h3]
  have hg2 : g * g = 1 := by
    refine Equiv.ext fun z => ?_
    show g (g z) = z
    by_cases h1 : z = a
    · rw [h1, hga, hgc0]
    by_cases h2 : z = b
    · rw [h2, hgb, hgc1]
    by_cases h3 : z = c0
    · rw [h3, hgc0, hga]
    by_cases h4 : z = c1
    · rw [h4, hgc1, hgb]
    rw [hgfix z h1 h2 h3 h4, hgfix z h1 h2 h3 h4]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hgconj : ∀ p q : OmegaE r 2, g * swap p q * g⁻¹ = swap (g p) (g q) := fun p q =>
    (swap_apply_apply g p q).symm
  have hcl : ∀ x ∈ Wr r 2 ⊔ Subgroup.zpowers (swap c0 c1), g * x * g⁻¹ ∈ P := by
    have hWr : Wr r 2 = Subgroup.closure (embL r 2 '' Set.range (blockTransp (ι := Fin r))) := by
      unfold Wr
      rw [blockFix_eq_closure, MonoidHom.map_closure]
    have hWc : Wr r 2 ≤ P.comap (MulAut.conj g).toMonoidHom := by
      rw [hWr, Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have h1 := embL_blockTransp r 2 i false
      simp only [Bool.not_false] at h1
      show g * embL r 2 (blockTransp i) * g⁻¹ ∈ P
      rw [← h1, hgconj]
      by_cases hi : i = i0
      · subst hi
        have e1 : g (Sum.inl (i0, false) : OmegaE r 2) = c0 := hga
        have e2 : g (Sum.inl (i0, true) : OmegaE r 2) = c1 := hgb
        rw [e1, e2]; exact hu0P
      · have hne1 : (Sum.inl (i, false) : OmegaE r 2) ≠ a := by
          simp [a]; intro h; exact hi h
        have hne2 : (Sum.inl (i, false) : OmegaE r 2) ≠ b := by
          simp [b]
        have hne3 : (Sum.inl (i, true) : OmegaE r 2) ≠ a := by
          simp [a]
        have hne4 : (Sum.inl (i, true) : OmegaE r 2) ≠ b := by
          simp [b]; intro h; exact hi h
        rw [hgfix _ hne1 hne2 (by simp [c0]) (by simp [c1]),
          hgfix _ hne3 hne4 (by simp [c0]) (by simp [c1])]
        rw [h1]
        exact hWP ⟨blockTransp i, swap_mem_blockFix rfl, rfl⟩
    have hZc : Subgroup.zpowers (swap c0 c1) ≤ P.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      show g * swap c0 c1 * g⁻¹ ∈ P
      rw [hgconj, hgc0, hgc1]
      exact hWP ht0
    intro x hx
    exact (sup_le hWc hZc) hx
  have hgN : g ∈ Subgroup.normalizer (P : Set (Perm (OmegaE r 2))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hcl x (hPle hx)
    · intro hx
      have h1 := hcl _ (hPle hx)
      have : g * (g * x * g⁻¹) * g⁻¹ = x := by
        rw [hginv]
        calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
          _ = x := by rw [hg2]; simp
      rwa [this] at h1
  have hgW := normalizer_theta_S_le hA hSM θ hker hrange g hgN
  rw [hW] at hgW
  have hmem := ((Subgroup.mem_normalizer_iff.1 hgW) (swap a b)).1 ht0
  rw [hgconj, hga, hgb] at hmem
  have := Wr_apply_inr hmem (0 : Fin 2)
  have h2 : swap c0 c1 c0 = c1 := swap_apply_left _ _
  have h3 : (Sum.inr 0 : OmegaE r 2) = c0 := rfl
  rw [h3, h2] at this
  exact hc this.symm


end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
