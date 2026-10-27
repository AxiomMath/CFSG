module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbeddingD2

open scoped commutatorElement

theorem three_lt_index_of_isSimpleGroup {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    (h6 : 6 < Nat.card Γ) {H : Subgroup Γ} (hH : H ≠ ⊤) : 3 < H.index := by
  by_contra hle
  have hle' : H.index ≤ 3 := by omega
  have hker_le : (MulAction.toPermHom Γ (Γ ⧸ H)).ker ≤ H := by
    rw [← Subgroup.normalCore_eq_ker]
    exact Subgroup.normalCore_le H
  have hbot : (MulAction.toPermHom Γ (Γ ⧸ H)).ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (MulAction.toPermHom Γ (Γ ⧸ H)).ker with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ hker_le)) hH
  have hinj : Function.Injective (MulAction.toPermHom Γ (Γ ⧸ H)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hbot
  have hcard : Nat.card Γ ≤ Nat.card (Equiv.Perm (Γ ⧸ H)) :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm, ← Subgroup.index_eq_card] at hcard
  have hfac : H.index.factorial ≤ (3 : ℕ).factorial := Nat.factorial_le hle'
  have h3 : (3 : ℕ).factorial = 6 := by decide
  omega

theorem eq_one_of_forall_mul_inv_mem_center {Λ : Type*} [Group Λ]
    (hperf : ⁅(⊤ : Subgroup Λ), ⊤⁆ = (⊤ : Subgroup Λ)) (a : MulAut Λ)
    (ha : ∀ x, a x * x⁻¹ ∈ Subgroup.center Λ) : a = 1 := by
  obtain ⟨f, hf⟩ : ∃ f : Λ →* Λ, ∀ x, f x = a x * x⁻¹ := by
    refine ⟨{ toFun := fun x => a x * x⁻¹
              map_one' := by simp
              map_mul' := fun x y => ?_ }, fun x => rfl⟩
    have hy := (Subgroup.mem_center_iff.mp (ha y)) x⁻¹
    simp only [map_mul, mul_inv_rev]
    calc a x * a y * (y⁻¹ * x⁻¹) = a x * (a y * y⁻¹) * x⁻¹ := by simp only [mul_assoc]
      _ = a x * (a y * y⁻¹ * x⁻¹) := by simp only [mul_assoc]
      _ = a x * (x⁻¹ * (a y * y⁻¹)) := by rw [hy]
      _ = a x * x⁻¹ * (a y * y⁻¹) := by simp only [mul_assoc]
  have hker : ⁅(⊤ : Subgroup Λ), ⊤⁆ ≤ f.ker := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨g₁, -, g₂, -, rfl⟩
    show f ⁅g₁, g₂⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hf, hf]
    exact (Subgroup.mem_center_iff.mp (ha g₁) (a g₂ * g₂⁻¹)).symm
  have hall : ∀ g : Λ, f g = 1 := by
    intro g
    have hg : g ∈ (⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ : Subgroup Λ) := by
      rw [hperf]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp (hker hg)
  apply MulEquiv.ext
  intro x
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp (by simpa [hf] using hall x)

theorem map_eq_one_of_simple_quotient {Γ Λ : Type*} [Group Γ] [Group Λ] [Finite Γ] [Finite Λ]
    {p : ℕ} (N : Subgroup Γ) [N.Normal] (hN : p.Coprime (Nat.card N))
    (hsimple : IsSimpleGroup (Γ ⧸ N)) (hnab : ∃ a b : Γ ⧸ N, a * b ≠ b * a)
    (hΛ : p.Coprime (Nat.card Λ))
    (hout : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer Λ))
    (ρ : Γ →* MulAut Λ) {x : Γ} (hx : IsPGroup p (Subgroup.zpowers x)) : ρ x = 1 := by
  obtain ⟨j, hj⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have hxj : x ^ p ^ j = 1 := by
    simpa using congrArg Subtype.val hj
  set θ : Γ →* CFSG.ComponentClassification.OuterAutomorphisms.Outer Λ :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Λ)).comp ρ
  have hsup : N ⊔ θ.ker = ⊤ := by
    have hnorm : ((N ⊔ θ.ker).map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map (Subgroup.sup_normal N θ.ker) (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)
    obtain hbot | htop :=
      Subgroup.Normal.eq_bot_or_eq_top ((N ⊔ θ.ker).map (QuotientGroup.mk' N))
    · exfalso
      have hle : N ⊔ θ.ker ≤ N := by
        intro g hg
        have hmem : QuotientGroup.mk' N g ∈ (N ⊔ θ.ker).map (QuotientGroup.mk' N) :=
          Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hg
        rw [hbot, Subgroup.mem_bot] at hmem
        exact (QuotientGroup.eq_one_iff g).mp hmem
      have hker_le : θ.ker ≤ N := le_trans le_sup_right hle
      have hsolvK : Group.IsSolvable (Γ ⧸ θ.ker) :=
        Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective (φ := θ))
      have hh : θ.ker ≤ N.comap (MonoidHom.id Γ) := by simpa using hker_le
      have hquot : Group.IsSolvable (Γ ⧸ N) := by
        have hsurj : Function.Surjective (QuotientGroup.map θ.ker N (MonoidHom.id Γ) hh) := by
          intro y
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
          exact ⟨(g : Γ ⧸ θ.ker), QuotientGroup.map_mk θ.ker N (MonoidHom.id Γ) hh g⟩
        exact Group.isSolvable_of_surjective hsurj
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hquot a b)
    · have hf : (QuotientGroup.mk' N).ker ≤ N ⊔ θ.ker := by
        rw [QuotientGroup.ker_mk']
        exact le_sup_left
      have h := Subgroup.comap_map_eq_self hf
      rw [htop, Subgroup.comap_top] at h
      exact h.symm
  have hθx : θ x = 1 := by
    have hmem : x ∈ N ⊔ θ.ker := by
      rw [hsup]
      exact Subgroup.mem_top x
    obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hθn : θ x = θ n := by
      rw [← hnk, map_mul, MonoidHom.mem_ker.mp hk, mul_one]
    have hmemH : θ x ∈ N.map θ := by
      rw [hθn]
      exact Subgroup.mem_map_of_mem θ hn
    have hd1 : orderOf (θ x) ∣ Nat.card ↥(N.map θ) := by
      have h := orderOf_dvd_natCard (⟨θ x, hmemH⟩ : ↥(N.map θ))
      rwa [Subgroup.orderOf_mk] at h
    have hd2 : orderOf (θ x) ∣ Nat.card N :=
      dvd_trans hd1 (Subgroup.card_map_dvd (H := N) θ)
    have hd3 : orderOf (θ x) ∣ p ^ j :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxj, map_one])
    have hcop : Nat.Coprime (p ^ j) (orderOf (θ x)) :=
      Nat.Coprime.coprime_dvd_right hd2 (Nat.Coprime.pow_left j hN)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm hd3)
  have hρx : ρ x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Λ :=
    (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner Λ)
      (ρ x)).mp hθx
  have hd1 : orderOf (ρ x) ∣
      Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner Λ) := by
    have h := orderOf_dvd_natCard
      (⟨ρ x, hρx⟩ : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner Λ))
    rwa [Subgroup.orderOf_mk] at h
  have hd2 : orderOf (ρ x) ∣ Nat.card Λ :=
    dvd_trans hd1 (Subgroup.card_range_dvd (MulAut.conj : Λ →* MulAut Λ))
  have hd3 : orderOf (ρ x) ∣ p ^ j :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxj, map_one])
  have hcop : Nat.Coprime (p ^ j) (orderOf (ρ x)) :=
    Nat.Coprime.coprime_dvd_right hd2 (Nat.Coprime.pow_left j hΛ)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm hd3)

end CFSG.AGLEmbeddingD2
