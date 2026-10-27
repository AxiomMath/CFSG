module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Commutator

variable {G : Type*} [Group G]

theorem eq_one_of_centralizes_commutator (hZ : Subgroup.center G = ⊥)
    (hZ' : ∀ n ∈ commutator G, (∀ m ∈ commutator G, n * m = m * n) → n = 1)
    {z : G} (hz : ∀ t ∈ commutator G, z * t = t * z) : z = 1 := by
  have hcent : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro u
    have hc : z * u * z⁻¹ * u⁻¹ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hn : ∀ m ∈ commutator G, (z * u * z⁻¹ * u⁻¹) * m = m * (z * u * z⁻¹ * u⁻¹) := by
      intro m hm
      have hnorm : ∀ w : G, ∀ m' ∈ commutator G, w * m' * w⁻¹ ∈ commutator G := fun w m' hm' =>
        (inferInstance : (commutator G).Normal).conj_mem m' hm' w
      have h1 : z * m = m * z := hz m hm
      have hm1 : u⁻¹ * m * u ∈ commutator G := by
        have := hnorm u⁻¹ m hm
        simpa using this
      have h2 : z * (u⁻¹ * m * u) = (u⁻¹ * m * u) * z := hz _ hm1
      calc (z * u * z⁻¹ * u⁻¹) * m
          = z * (u * z⁻¹ * u⁻¹ * m * u) * u⁻¹ := by group
        _ = z * ((u * z⁻¹ * u⁻¹) * m * u) * u⁻¹ := by group
        _ = m * (z * u * z⁻¹ * u⁻¹) := by
          have h3 : z⁻¹ * (u⁻¹ * m * u) = (u⁻¹ * m * u) * z⁻¹ := by
            calc z⁻¹ * (u⁻¹ * m * u) = z⁻¹ * ((u⁻¹ * m * u) * z) * z⁻¹ := by group
              _ = z⁻¹ * (z * (u⁻¹ * m * u)) * z⁻¹ := by rw [h2]
              _ = (u⁻¹ * m * u) * z⁻¹ := by group
          calc z * (u * z⁻¹ * u⁻¹ * m * u) * u⁻¹
              = z * (u * (z⁻¹ * (u⁻¹ * m * u))) * u⁻¹ := by group
            _ = z * (u * ((u⁻¹ * m * u) * z⁻¹)) * u⁻¹ := by rw [h3]
            _ = (z * m) * (u * z⁻¹ * u⁻¹) := by group
            _ = (m * z) * (u * z⁻¹ * u⁻¹) := by rw [h1]
            _ = m * (z * u * z⁻¹ * u⁻¹) := by group
    have h1 := hZ' _ hc hn
    have h2 : z * u * z⁻¹ * u⁻¹ = 1 := h1
    calc u * z = (z * u * z⁻¹ * u⁻¹) * (u * z) := by rw [h2, one_mul]
      _ = z * u := by group
  rw [hZ, Subgroup.mem_bot] at hcent
  exact hcent

end Commutator

theorem exists_noncomm_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ x y : A, x * y ≠ y * x) : ∃ x y : B, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨e x, e y, fun h' => hxy (e.injective (by rw [map_mul, map_mul]; exact h'))⟩

section NormalForm

variable {Γ A : Type*} [Group Γ] [Group A]

theorem zpow_apply_eq_of_fix {T : Set Γ} {g : MulAut Γ} (hg : ∀ t ∈ T, g t = t) (i : ℤ) {t : Γ}
    (ht : t ∈ T) : (g ^ i) t = t := by
  have hmem : g ∈ fixingSubgroup (MulAut Γ) T := (mem_fixingSubgroup_iff _).2 hg
  have := (mem_fixingSubgroup_iff (MulAut Γ)).1 (Subgroup.zpow_mem _ hmem i) t ht
  exact this

theorem fieldCoreAt_of_normalForm [Finite Γ] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ))
    (hA : ∀ u v : A, u * v = v * u) (φ : A →* MulAut Γ)
    (hNF : ∀ α : MulAut Γ, ∃ (x : Γ) (τ : A), α = MulAut.conj x * φ τ)
    {σ : A} (hσp : orderOf (φ σ) = p) {T : Subgroup Γ} (hTJ : ∀ t ∈ T, φ σ t = t)
    (hTn : ∀ f : Γ, φ σ f = f → ∀ t ∈ T, f * t * f⁻¹ ∈ T)
    (hTq : CFSG.IsQuasisimple T) (hTp : ¬ Nat.Coprime p (Nat.card T))
    (hCJ : ∀ z : Γ, φ σ z = z → (∀ t ∈ T, z * t = t * z) → z = 1)
    (hres : ∀ (x : Γ) (τ : A), φ σ x = x → (∀ j : Γ, φ σ j = j → x * φ τ j * x⁻¹ = j) →
      τ ∈ Subgroup.zpowers σ) : FieldCoreAt p (φ σ) := by
  set δ := φ σ with hδ
  refine ⟨T, fun t ht => hTJ t ht, fun f hf t ht => hTn f (mem_fixSub.1 hf) t ht, hTq, hTp, ?_⟩
  intro g hgp hgδ hgT
  obtain ⟨x, τ, rfl⟩ := hNF g
  have hτδ : φ τ * δ = δ * φ τ := by rw [hδ, ← map_mul, ← map_mul, hA]
  have hcx : δ * MulAut.conj x = MulAut.conj x * δ := by
    have h1 : MulAut.conj x * δ * φ τ = δ * MulAut.conj x * φ τ := by
      calc MulAut.conj x * δ * φ τ = MulAut.conj x * (δ * φ τ) := by rw [mul_assoc]
        _ = MulAut.conj x * (φ τ * δ) := by rw [hτδ]
        _ = (MulAut.conj x * φ τ) * δ := by rw [mul_assoc]
        _ = δ * (MulAut.conj x * φ τ) := hgδ
        _ = δ * MulAut.conj x * φ τ := by rw [mul_assoc]
    exact (mul_right_cancel h1).symm
  have hx : δ x = x := mem_fixSub_of_commute hinj hcx
  have hRj : ∀ j : Γ, (MulAut.conj x * φ τ) j = x * φ τ j * x⁻¹ := fun j => by
    simp [MulAut.mul_apply, MulAut.conj_apply]
  have hτfix : ∀ j : Γ, δ j = j → δ (φ τ j) = φ τ j := by
    intro j hj
    have h := congrArg (fun m : MulAut Γ => m j) hτδ.symm
    simp only [MulAut.mul_apply] at h
    rw [h, hj]
  have hfixJ : ∀ j : Γ, δ j = j → x * φ τ j * x⁻¹ = j := by
    intro j hj
    have hRJ : δ ((MulAut.conj x * φ τ) j) = (MulAut.conj x * φ τ) j := by
      rw [hRj, map_mul, map_mul, map_inv, hx, hτfix j hj]
    have hz : δ (j⁻¹ * (MulAut.conj x * φ τ) j) = j⁻¹ * (MulAut.conj x * φ τ) j := by
      rw [map_mul, map_inv, hj, hRJ]
    have hzc : ∀ t ∈ T, (j⁻¹ * (MulAut.conj x * φ τ) j) * t =
        t * (j⁻¹ * (MulAut.conj x * φ τ) j) := by
      intro t ht
      have hjt : j * t * j⁻¹ ∈ T := hTn j hj t ht
      have e1 : (MulAut.conj x * φ τ) (j * t * j⁻¹) = j * t * j⁻¹ := hgT _ hjt
      rw [map_mul, map_mul, map_inv, hgT t ht] at e1
      calc (j⁻¹ * (MulAut.conj x * φ τ) j) * t
          = j⁻¹ * ((MulAut.conj x * φ τ) j * t * ((MulAut.conj x * φ τ) j)⁻¹) * j *
              (j⁻¹ * (MulAut.conj x * φ τ) j) := by group
        _ = j⁻¹ * (j * t * j⁻¹) * j * (j⁻¹ * (MulAut.conj x * φ τ) j) := by rw [e1]
        _ = t * (j⁻¹ * (MulAut.conj x * φ τ) j) := by group
    have h1 := hCJ _ hz hzc
    rw [← hRj]
    exact (inv_mul_eq_one.1 h1).symm
  have hτz := hres x τ hx hfixJ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hτz
  have hφτ : φ τ = δ ^ i := by rw [hδ, ← map_zpow, hi]
  have hx1 : x = 1 := by
    refine hCJ x hx fun t ht => ?_
    have h1 : (MulAut.conj x * φ τ) t = t := hgT t ht
    rw [hRj, hφτ, zpow_apply_eq_of_fix (T := (T : Set Γ)) hTJ i ht] at h1
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [h1]
  subst hx1
  rw [map_one, one_mul] at hgp ⊢
  have hmem : φ τ ∈ Subgroup.zpowers δ := ⟨i, by rw [hφτ]⟩
  have hdvd : orderOf (φ τ) ∣ p := hσp ▸ orderOf_dvd_of_mem_zpowers hmem
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

theorem fieldCoreAt_of_normalForm_derived [Finite Γ] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ))
    (hA : ∀ u v : A, u * v = v * u) (φ : A →* MulAut Γ)
    (hNF : ∀ α : MulAut Γ, ∃ (x : Γ) (τ : A), α = MulAut.conj x * φ τ)
    {σ : A} (hσp : orderOf (φ σ) = p) {J : Subgroup Γ} (hJ : ∀ z : Γ, z ∈ J ↔ φ σ z = z)
    (hZJ : Subgroup.center J = ⊥) (hS : IsSimpleGroup (commutator J))
    (hNA : ∃ x y : commutator J, x * y ≠ y * x)
    (hTp : ¬ Nat.Coprime p (Nat.card (commutator J)))
    (hres : ∀ (x : Γ) (τ : A), φ σ x = x → (∀ j : Γ, φ σ j = j → x * φ τ j * x⁻¹ = j) →
      τ ∈ Subgroup.zpowers σ) : FieldCoreAt p (φ σ) := by
  have hZc : Subgroup.center (commutator J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (commutator J)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hNA
      exact hxy ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x)
  have hZ' : ∀ n ∈ commutator J, (∀ m ∈ commutator J, n * m = m * n) → n = 1 := by
    intro n hn hc
    have : (⟨n, hn⟩ : commutator J) ∈ Subgroup.center (commutator J) :=
      Subgroup.mem_center_iff.2 fun m => Subtype.ext (hc m.1 m.2).symm
    rw [hZc, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  set T : Subgroup Γ := (commutator J).map J.subtype with hT
  let eJ : commutator J ≃* T := (commutator J).equivMapOfInjective J.subtype J.subtype_injective
  have hTq : CFSG.IsQuasisimple T := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ ?_
    refine isQuasisimple_of_simple_nonabelian fun hc => ?_
    obtain ⟨x, y, hxy⟩ := hNA
    exact hxy (hc x y)
  have hTJ : ∀ t ∈ T, φ σ t = t := by
    rintro _ ⟨t', -, rfl⟩
    exact (hJ _).1 t'.2
  have hTn : ∀ f : Γ, φ σ f = f → ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
    rintro f hf _ ⟨t', ht', rfl⟩
    refine ⟨(⟨f, (hJ f).2 hf⟩ : J) * t' * (⟨f, (hJ f).2 hf⟩ : J)⁻¹, ?_, rfl⟩
    exact (inferInstance : (commutator J).Normal).conj_mem t' ht' _
  have hCJ : ∀ z : Γ, φ σ z = z → (∀ t ∈ T, z * t = t * z) → z = 1 := by
    intro z hz hzc
    have hzJ : z ∈ J := (hJ z).2 hz
    have h1 := eq_one_of_centralizes_commutator (G := J) hZJ hZ' (z := ⟨z, hzJ⟩)
      (fun t' ht' => Subtype.ext (hzc t'.1 ⟨t', ht', rfl⟩))
    exact congrArg Subtype.val h1
  have hcardT : Nat.card T = Nat.card (commutator J) := (Nat.card_congr eJ.toEquiv).symm
  exact fieldCoreAt_of_normalForm hinj hA φ hNF hσp hTJ hTn hTq (by rwa [hcardT]) hCJ hres

end NormalForm

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
