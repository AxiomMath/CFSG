module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Case2

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem psi_a2 : H.psi (0, 0, 2) = H.a ^ 2 := by simp [psi, psiN]

theorem a_sq_mem_S : H.a ^ 2 ∈ H.S := H.psi_a2 ▸ H.psi_mem_S _

theorem conj_mem_W {x c : G} (hx : x ∈ Subgroup.normalizer (H.S : Set G)) (hc : c ∈ H.W) :
    x * c * x⁻¹ ∈ H.W := by
  have hxn := Subgroup.mem_normalizer_iff.1 hx
  have hcS : c ∈ H.S := H.W_le_S hc
  have hS : x * c * x⁻¹ ∈ H.S := (hxn _).1 hcS
  refine H.central_mem_W hS fun s' hs' => ?_
  have h1 : x⁻¹ * s' * x ∈ H.S :=
    (hxn _).2 (by rw [show x * (x⁻¹ * s' * x) * x⁻¹ = s' by group]; exact hs')
  have h2 := H.W_central hc _ h1
  calc x * c * x⁻¹ * s' = x * (c * (x⁻¹ * s' * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * s' * x) * c) * x⁻¹ := by rw [h2]
    _ = s' * (x * c * x⁻¹) := by group

theorem conj_z {x : G} (hx : x ∈ Subgroup.normalizer (H.S : Set G)) :
    x * H.a ^ 4 * x⁻¹ = H.a ^ 4 := by
  have hxn := Subgroup.mem_normalizer_iff.1 hx
  obtain ⟨w, hw, hψ⟩ := H.conj_mem_W hx H.z_mem_W
  obtain ⟨y, hy⟩ := (mem_S H).1 ((hxn _).1 H.a_sq_mem_S)
  have hsq : H.psi (SMod.mul y y) = H.psi w := by
    rw [H.psi_mul, hy, hψ]
    calc x * H.a ^ 2 * x⁻¹ * (x * H.a ^ 2 * x⁻¹) = x * (H.a ^ 2 * H.a ^ 2) * x⁻¹ := by group
      _ = x * H.a ^ 4 * x⁻¹ := by rw [← pow_add]
  have hww : SMod.mul y y = w := H.psi_injective hsq
  have hw1 : w.1 = 0 := hww ▸ SMod.sq_fst y
  rcases SMod.inW_cases w hw with rfl | rfl | rfl | rfl
  · exfalso
    apply H.a4
    have h1 : x * H.a ^ 4 * x⁻¹ = 1 := hψ.symm.trans H.psi_one
    calc H.a ^ 4 = x⁻¹ * (x * H.a ^ 4 * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · simp [SMod.tt] at hw1
  · exact hψ.symm.trans H.psi_zz
  · simp at hw1

theorem conj_b {x : G} (hx : x ∈ Subgroup.normalizer (H.S : Set G)) :
    ∃ u : SMod, u.2.1 = 1 ∧ SMod.inH u ∧ x * H.b * x⁻¹ = H.psi u := by
  have hxn := Subgroup.mem_normalizer_iff.1 hx
  obtain ⟨u, hu⟩ := (mem_S H).1 ((hxn _).1 H.b_mem_S)
  have hu2 : SMod.mul u u = SMod.one := by
    apply H.psi_injective
    rw [H.psi_mul, hu, H.psi_one]
    calc x * H.b * x⁻¹ * (x * H.b * x⁻¹) = x * (H.b * H.b) * x⁻¹ := by group
      _ = 1 := by rw [H.b_sq]; group
  have hnW : ¬ SMod.inW u := by
    intro hW
    have h1 : x * H.b * x⁻¹ ∈ H.W := ⟨u, hW, hu⟩
    have h2 := H.conj_mem_W (Subgroup.inv_mem _ hx) h1
    have h3 : H.b ∈ H.W := by
      rwa [show x⁻¹ * (x * H.b * x⁻¹) * x⁻¹⁻¹ = H.b by group] at h2
    obtain ⟨w, hw, hwb⟩ := h3
    have := H.psi_injective (hwb.trans H.psi_bb.symm)
    subst this
    exact absurd hw (by decide)
  obtain ⟨h1, h2⟩ := SMod.noncentral_invol u hu2 hnW
  exact ⟨u, h1, h2, hu.symm⟩

theorem E1_le_closure : H.E1 ≤ Subgroup.closure ({H.t, H.a ^ 4, H.b} : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [psi_def]
  have ht : H.t ∈ Subgroup.closure ({H.t, H.a ^ 4, H.b} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hz : H.a ^ 4 ∈ Subgroup.closure ({H.t, H.a ^ 4, H.b} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hb : H.b ∈ Subgroup.closure ({H.t, H.a ^ 4, H.b} : Set G) :=
    Subgroup.subset_closure (by simp)
  refine mul_mem (pow_mem ht _) (mul_mem (pow_mem hb _) ?_)
  have hj : x.2.2.val = 0 ∨ x.2.2.val = 4 := by
    unfold SMod.inE1 at hx
    rcases hx with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  rcases hj with h | h
  · rw [h, pow_zero]; exact Subgroup.one_mem _
  · rw [h]; exact hz

theorem E1_map_le {K : Subgroup G} (f : G →* G) (h1 : f H.t ∈ K) (h2 : f (H.a ^ 4) ∈ K)
    (h3 : f H.b ∈ K) : ∀ e ∈ H.E1, f e ∈ K := by
  intro e he
  have hle : Subgroup.closure ({H.t, H.a ^ 4, H.b} : Set G) ≤ K.comap f := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  exact hle (H.E1_le_closure he)

theorem mem_normalizer_of_forall {K : Subgroup G} {y : G} (h : ∀ e ∈ K, y * e * y⁻¹ ∈ K) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => h e he, fun he => ?_⟩
  let f : K → K := fun k => ⟨y * k * y⁻¹, h k k.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨y * e * y⁻¹, he⟩
  have := congrArg Subtype.val hk
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact k.2

@[expose] def cj (x : G) : G →* G := (MulAut.conj x).toMonoidHom

omit [Finite G] in
theorem cj_apply (x g : G) : cj x g = x * g * x⁻¹ := rfl

theorem psi_conj (x y : SMod) :
    H.psi x * H.psi y * (H.psi x)⁻¹ = H.psi (SMod.mul (SMod.mul x y) (SMod.inv x)) := by
  rw [H.psi_mul, H.psi_mul, H.psi_inv]

theorem psi_conj_inv (x y : SMod) :
    (H.psi x)⁻¹ * H.psi y * H.psi x = H.psi (SMod.mul (SMod.mul (SMod.inv x) y) x) := by
  rw [H.psi_mul, H.psi_mul, H.psi_inv]

theorem b_mem_E1 : H.b ∈ H.E1 := ⟨SMod.bb, by decide, H.psi_bb⟩

theorem t_mem_E1 : H.t ∈ H.E1 := H.W_le_E1 H.t_mem_W

theorem z_mem_E1 : H.a ^ 4 ∈ H.E1 := H.W_le_E1 H.z_mem_W

theorem conj_E1 {x : G} (hx : x ∈ Subgroup.normalizer (H.S : Set G))
    (htz : x * H.t * x⁻¹ = H.t * H.a ^ 4) :
    (∀ e ∈ H.E1, x * e * x⁻¹ ∈ H.E1) ∨ (∀ e ∈ H.E1, x * e * x⁻¹ ∈ H.E2) := by
  obtain ⟨u, hu1, hu2, hub⟩ := H.conj_b hx
  have hz := H.conj_z hx
  have hW : H.t * H.a ^ 4 ∈ H.W := H.W.mul_mem H.t_mem_W H.z_mem_W
  rcases SMod.inE1_or_inE2 u hu1 hu2 with h | h
  · left
    refine H.E1_map_le (K := H.E1) (cj x) ?_ ?_ ?_
    · rw [cj_apply, htz]; exact H.W_le_E1 hW
    · rw [cj_apply, hz]; exact H.z_mem_E1
    · rw [cj_apply, hub]; exact ⟨u, h, rfl⟩
  · right
    refine H.E1_map_le (K := H.E2) (cj x) ?_ ?_ ?_
    · rw [cj_apply, htz]; exact H.W_le_E2 hW
    · rw [cj_apply, hz]; exact H.W_le_E2 H.z_mem_W
    · rw [cj_apply, hub]; exact ⟨u, h, rfl⟩

theorem exists_y {P : Subgroup G} (hP : IsPGroup 2 P) (hcard : Nat.card P = 64) (hSP : H.S ≤ P) :
    ∃ y ∈ P, y ∉ H.S ∧ y ∈ Subgroup.normalizer (H.E1 : Set G) := by
  obtain ⟨x, hxP, hxS⟩ := H.exists_mem_P_not_mem_S hcard hSP
  have hxn := H.mem_normalizer_of_mem_P hcard hSP hxP
  have htz := H.conj_eq_tz hP hcard hSP hxP hxS
  rcases H.conj_E1 hxn htz with h | h
  · exact ⟨x, hxP, hxS, mem_normalizer_of_forall h⟩
  · refine ⟨H.a⁻¹ * x, P.mul_mem (P.inv_mem (hSP H.a_mem_S)) hxP, ?_, ?_⟩
    · intro hy
      apply hxS
      have : x = H.a * (H.a⁻¹ * x) := by group
      rw [this]
      exact H.S.mul_mem H.a_mem_S hy
    · apply mem_normalizer_of_forall
      intro e he
      obtain ⟨m, hm, hme⟩ := h e he
      have : H.a⁻¹ * x * e * (H.a⁻¹ * x)⁻¹ = (H.psi SMod.aa)⁻¹ * H.psi m * H.psi SMod.aa := by
        rw [H.psi_aa, hme]; group
      rw [this, H.psi_conj_inv]
      exact ⟨_, SMod.conj_a_E2 m hm, rfl⟩

theorem g_mem_normalizer : H.g ∈ Subgroup.normalizer (H.E1 : Set G) := by
  apply mem_normalizer_of_forall
  refine H.E1_map_le (K := H.E1) (cj H.g) ?_ ?_ ?_
  · rw [cj_apply]
    have : H.g * H.t * H.g⁻¹ = H.t := by
      have := H.comm H.g H.g_mem
      calc H.g * H.t * H.g⁻¹ = (H.g * H.t) * H.g⁻¹ := rfl
        _ = (H.t * H.g) * H.g⁻¹ := by rw [← this]
        _ = H.t := by group
    rw [this]; exact H.t_mem_E1
  · rw [cj_apply, H.g_z]; exact H.b_mem_E1
  · rw [cj_apply, H.g_b]; exact H.E1.mul_mem H.z_mem_E1 H.b_mem_E1

theorem H0_le_normalizer : H.H0 ≤ Subgroup.normalizer (H.E1 : Set G) := by
  rintro _ ⟨m, hm, rfl⟩
  apply mem_normalizer_of_forall
  rintro _ ⟨m', hm', rfl⟩
  rw [H.psi_conj]
  exact ⟨_, SMod.inH_normalizes_E1 m m' hm hm', rfl⟩

end Setting

end CFSG.EvenSporadicStandard.M11Std
