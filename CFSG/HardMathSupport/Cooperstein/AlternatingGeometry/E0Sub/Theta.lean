module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Pieces
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.AltOn

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm CFSG.Quasithin

namespace Theta

variable {N : ℕ} {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}

@[expose] def setStab (Ω₁ : Finset (Fin N)) : Subgroup (Perm (Fin N)) where
  carrier := {g | ∀ x, x ∈ Ω₁ ↔ g x ∈ Ω₁}
  mul_mem' {g h} hg hh x := (hh x).trans (hg (h x))
  one_mem' _ := Iff.rfl
  inv_mem' {g} hg x := by simpa using (hg (g⁻¹ x)).symm

theorem mem_setStab {Ω₁ : Finset (Fin N)} {g : Perm (Fin N)} :
    g ∈ setStab Ω₁ ↔ ∀ x, x ∈ Ω₁ ↔ g x ∈ Ω₁ :=
  Iff.rfl

theorem mem_omegaOne_iff {a x : Fin N} :
    x ∈ omegaOne Δ₀ ω a ↔ x = a ∨ x = ω a ∨ x ∈ Δ₀ := by
  rw [omegaOne, Finset.mem_insert, Finset.mem_insert]

theorem subset_omegaOne (a : Fin N) : Δ₀ ⊆ omegaOne Δ₀ ω a := fun x hx => by
  rw [mem_omegaOne_iff]
  exact Or.inr (Or.inr hx)

theorem mem_omegaOne_omega_iff (h : E0Data Δ₀ P ω) {a x : Fin N} (hx : x ∉ Δ₀) :
    x ∈ omegaOne Δ₀ ω a ↔ ω x ∈ omegaOne Δ₀ ω a := by
  rw [mem_omegaOne_iff, mem_omegaOne_iff]
  have h1 : ω x ∉ Δ₀ := h.ω_not_mem hx
  simp only [hx, h1, or_false]
  constructor
  · rintro (hxa | hxa)
    · exact Or.inr (by rw [hxa])
    · exact Or.inl (by rw [hxa, h.ω_invol])
  · rintro (hxa | hxa)
    · exact Or.inr (by rw [← h.ω_invol x, hxa])
    · exact Or.inl (by rw [← h.ω_invol x, hxa, h.ω_invol])

theorem swap_mem_setStab {Ω₁ : Finset (Fin N)} {u v : Fin N} (h : u ∈ Ω₁ ↔ v ∈ Ω₁) :
    swap u v ∈ setStab Ω₁ := by
  refine mem_setStab.2 fun x => ?_
  by_cases hxu : x = u
  · rw [hxu, swap_apply_left]
    exact h
  · by_cases hxv : x = v
    · rw [hxv, swap_apply_right]
      exact h.symm
    · rw [swap_apply_of_ne_of_ne hxu hxv]

theorem mem_setStab_of_fix {Δ₀ Ω₁ : Finset (Fin N)} (hΔ : Δ₀ ⊆ Ω₁) {g : Perm (Fin N)}
    (hg : ∀ x, x ∉ Δ₀ → g x = x) : g ∈ setStab Ω₁ := by
  refine mem_setStab.2 fun x => ?_
  by_cases hx : x ∈ Δ₀
  · have hgx : g x ∈ Δ₀ := by
      by_contra hgx
      have e : g x = x := g.injective (hg _ hgx)
      exact hgx (by rw [e]; exact hx)
    exact iff_of_true (hΔ hx) (hΔ hgx)
  · rw [hg x hx]

theorem image_S_le_setStab (h : E0Data Δ₀ P ω) (a : Fin N) :
    P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)} ≤
      setStab (omegaOne Δ₀ ω a) := by
  refine sup_le (fun p hp => mem_setStab_of_fix (subset_omegaOne a) (h.P_fix p hp)) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact swap_mem_setStab (mem_omegaOne_omega_iff h hx)

theorem theta_mem_setStab {G : Type} [Group G] {X S L : Subgroup G}
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hE : E0NS X S L N θ Δ₀ P ω) (a : Fin N)
    {m : ↥(L ⊔ S)} (hm : (m : G) ∈ S) : θ m ∈ setStab (omegaOne Δ₀ ω a) := by
  have h1 : θ m ∈ (S.subgroupOf (L ⊔ S)).map θ := Subgroup.mem_map_of_mem θ hm
  rw [hE.image_S] at h1
  exact image_S_le_setStab hE.toE0Data a h1

theorem subgroupOf_perfectCore {G : Type} [Group G] [Finite G] {H K : Subgroup G} (hHK : H ≤ K) :
    (perfectCore H).subgroupOf K = perfectCore (H.subgroupOf K) := by
  have h1 : perfectCore H = (perfectCore (H.subgroupOf K)).map K.subtype := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hHK]
  rw [h1]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem map_subL_eq {G : Type} [Group G] [Finite G] {S L : Subgroup G}
    {θ : ↥(L ⊔ S) →* Perm (Fin N)}
    (hnat : ∀ σ ∈ alternatingGroup (Fin N),
      ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ)
    {Ω₁ : Finset (Fin N)} (hΩ : 5 ≤ Ω₁.card) :
    ((subL S L θ Ω₁).subgroupOf (L ⊔ S)).map θ = altOn Ω₁ := by
  have hHK : L ⊓ ((altOn Ω₁).comap θ).map (L ⊔ S).subtype ≤ L ⊔ S :=
    inf_le_left.trans le_sup_left
  have hmap : ((L ⊓ ((altOn Ω₁).comap θ).map (L ⊔ S).subtype).subgroupOf (L ⊔ S)).map θ =
      altOn Ω₁ := by
    refine le_antisymm ?_ fun σ hσ => ?_
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨m', hm', hmm⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hm).2
      have e : m' = m := Subtype.ext hmm
      exact e ▸ hm'
    · obtain ⟨l, hl⟩ := hnat σ (Subgroup.mem_inf.1 hσ).1
      refine Subgroup.mem_map.2 ⟨⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩, ?_, hl⟩
      refine Subgroup.mem_inf.2 ⟨l.2, Subgroup.mem_map.2
        ⟨⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩, ?_, rfl⟩⟩
      rw [Subgroup.mem_comap, hl]
      exact hσ
  rw [subL, subgroupOf_perfectCore hHK, map_perfectCore, hmap,
    perfectCore_eq_self_of_perfect (commutator_altOn hΩ)]

theorem normalizer_map_comap {G : Type} [Group G] {S L : Subgroup G}
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} {Ω₁ : Finset (Fin N)}
    (hS : ∀ m : ↥(L ⊔ S), (m : G) ∈ S → θ m ∈ setStab Ω₁) :
    S ≤ Subgroup.normalizer (((altOn Ω₁).comap θ).map (L ⊔ S).subtype : Set G) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro s hs y hy
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
  have hsK : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
  refine Subgroup.mem_map.2 ⟨⟨s, hsK⟩ * m * ⟨s, hsK⟩⁻¹, ?_, rfl⟩
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_set_normalizer_iff.1 (le_normalizer_altOn (hS ⟨s, hsK⟩ hs)) _).1 hm

end Theta

theorem thetaSubLStmt_holds : ThetaSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁
  subst hL₁
  obtain ⟨_, -, -, hnat, -, -⟩ := hE.natural
  exact Theta.map_subL_eq hnat (by rw [hE.toE0Data.card_omegaOne ha]; norm_num)

theorem normSubLStmt_holds : NormSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁
  subst hL₁
  refine ⟨subL_le S L θ _, subL_perfect S L θ _, ?_⟩
  have hM := Theta.normalizer_map_comap (fun m hm => Theta.theta_mem_setStab hE a hm)
  have hN : S ≤ Subgroup.normalizer ((L ⊓ ((altOn (omegaOne Δ₀ ω a)).comap θ).map
      (L ⊔ S).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    intro s hs y hy
    exact ⟨(Subgroup.mem_set_normalizer_iff.1 (hE.normalizes hs) y).1 hy.1,
      Subgroup.le_set_normalizer_iff.1 hM s hs y hy.2⟩
  exact hN.trans (normalizer_le_normalizer_perfectCore _)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
