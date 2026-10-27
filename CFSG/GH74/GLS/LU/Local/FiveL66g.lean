module

public import CFSG.GH74.GLS.LU.Local.FiveL66f

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section TT

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

theorem FiveCtx.t_ne_one (c : FiveCtx G p f z S K₁ K₂ t u) : t ≠ 1 :=
  CFSG.GH74.GLS.LU.Local.t_ne_one c.hs

theorem FiveCtx.z_ne_one (c : FiveCtx G p f z S K₁ K₂ t u) : z ≠ 1 := by
  intro h
  have := c.hs.z_inv
  rw [h, orderOf_one] at this
  omega

theorem FiveCtx.t_ne_z (c : FiveCtx G p f z S K₁ K₂ t u) : t ≠ z := by
  intro h
  have h1 : cjL t K₁ = K₂ := c.hs.t_swap
  have h2 : cjL t K₁ = K₁ := by
    rw [h]
    apply cjL_eq_of_comm
    intro a ha
    exact (c.hc.cz₁ ha).symm
  exact c.hc.ne (h2.symm.trans h1)

theorem FiveCtx.card_TT (c : FiveCtx G p f z S K₁ K₂ t u) : Nat.card ↥(TT z t) = 4 := by
  have hz2 : z * z = 1 := c.hs.z_sq
  have ht2 : t * t = 1 := c.hs.t_sq
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a :=
    commute_zpowers_zu c.hs.zt_comm
  have hdisj : zpowers z ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rcases mem_zpowers_of_sq_eq_one hz2 hx1 with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rcases mem_zpowers_of_sq_eq_one ht2 hx2 with h2 | h2
      · rw [h2]; exact Subgroup.one_mem _
      · exact absurd (h2.symm.trans h1) c.t_ne_z
  rw [TT, card_sup_of_commute_disjoint hcomm hdisj]
  have hz : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers]; exact c.hs.z_inv
  have ht : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) c.t_ne_one
  rw [hz, ht]

end TT

section C0Assembly

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem conj_mem_normalizer_of_cj {K : Subgroup G} {g u : G}
    (h : ∀ a ∈ cj K g, u * a * u⁻¹ ∈ cj K g) : g * u * g⁻¹ ∈ normalizer (K : Set G) := by
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro k hk
  have ha : g⁻¹ * k * g ∈ cj K g := by
    rw [mem_cj]; simpa [mul_assoc] using hk
  have h1 := mem_cj.mp (h _ ha)
  have e : g * (u * (g⁻¹ * k * g) * u⁻¹) * g⁻¹ = (g * u * g⁻¹) * k * (g * u * g⁻¹)⁻¹ := by group
  rw [e] at h1
  exact h1

omit [Finite G] in
theorem ModelPic.c0_key (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    {X₀ : Subgroup G} (hX₀c : Nat.card ↥X₀ = 5) (hXu : ∀ x ∈ X₀, u * x * u⁻¹ = x⁻¹)
    {s r g : G} (hg : g * s * g⁻¹ = z) (hrs : r * s = s * r) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrne : r ≠ s)
    (hX₀s : ∀ x ∈ X₀, s * x = x * s) (hX₀r : ∀ x ∈ X₀, r * x = x * r)
    (hus : u * s = s * u) (hgu : g * u * g⁻¹ ∈ normalizer (K₁ : Set G)) :
    ∃ Xs : Subgroup G, Xs ≤ centralizer (X₀ : Set G) ∧ IsElemAb 5 Xs ∧ Nat.card ↥Xs = 25 ∧
      (∀ x ∈ Xs, u * x * u⁻¹ = x⁻¹) ∧
      centralizer ({s} : Set G) ⊓ centralizer (X₀ : Set G) = Xs ⊔ (zpowers s ⊔ zpowers r) ∧
      Xs ⊓ (zpowers s ⊔ zpowers r) = ⊥ ∧
      ∀ g ∈ centralizer ({s} : Set G) ⊓ centralizer (X₀ : Set G), ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs := by
  classical
  have hsC : s ∈ centralizer ({s} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hrC : r ∈ centralizer ({s} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hrs
  have huC : u ∈ centralizer ({s} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hus
  have hX₀le : X₀ ≤ centralizer ({s} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hX₀s x hx).symm
  have hρs : pe ((conjIso hg).trans ψ) s hsC = z' := by
    show ((ψ ((conjIso hg) ⟨s, hsC⟩) : ↥(Cz z')) : Gs) = z'
    rw [show (conjIso hg) ⟨s, hsC⟩ = ⟨z, mem_Cz_self z⟩ from Subtype.ext hg]
    exact pic.psi_z
  have hv : pe ((conjIso hg).trans ψ) u huC ∈ normalizer (K₁' : Set Gs) := by
    have hmem : g * u * g⁻¹ ∈ Cz z := ((conjIso hg) ⟨u, huC⟩).2
    have h1 := (mem_normalizer_pull ψ pic.K₁'_le hmem).mp (by rw [pic.K₁_eq]; exact hgu)
    exact h1
  exact pic.c0_at ((conjIso hg).trans ψ) hsC hρs hrC hr2 hr1 hrne hX₀le hX₀c hX₀r huC hv hXu

end C0Assembly

section C0Final

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem TT_eq_sup_of {z t s r : G}
    (h : (s = z ∧ r = t) ∨ (s = t ∧ r = z) ∨ (s = z * t ∧ r = z)) :
    zpowers s ⊔ zpowers r = TT z t := by
  rcases h with ⟨hs, hr⟩ | ⟨hs, hr⟩ | ⟨hs, hr⟩ <;> rw [hs, hr]
  · exact sup_comm _ _
  · apply le_antisymm
    · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)))
    · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))) ?_
      refine Subgroup.zpowers_le.mpr ?_
      have h1 : z * t ∈ zpowers (z * t) ⊔ zpowers z := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      have h2 : z⁻¹ ∈ zpowers (z * t) ⊔ zpowers z :=
        Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
      have := Subgroup.mul_mem _ h2 h1
      simpa using this

end C0Final

end CFSG.GH74.GLS.LU.Local.Five
