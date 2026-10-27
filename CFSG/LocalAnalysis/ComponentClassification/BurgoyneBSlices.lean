module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem actsProperly_of_core [Finite G] {B : Subgroup G} {t : G} {Y S : Subgroup G}
    (ht : orderOf t = 2) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCoreIn B t)
    (htN : t ∈ normalizer (S : Set G)) (htC : ∃ a ∈ S, t * a ≠ a * t)
    (hON : oddCoreIn B t ≤ normalizer (S : Set G))
    (hOC : ∀ y ∈ oddCoreIn B t, (∀ a ∈ S, y * a = a * y) → y = 1) :
    ActsProperly t Y S ⊥ := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hYt : ∀ y ∈ Y, y * t = t * y := fun y hy => commute_of_mem_oddCoreIn (hYO hy)
  have hbot : ∀ g : G, g ∈ normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [mem_normalizer_iff]
    intro h
    simp only [mem_bot]
    constructor
    · rintro rfl
      group
    · intro h1
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
  refine ⟨?_, ?_, ?_⟩
  · rw [closure_le]
    intro x hx
    refine ⟨?_, hbot x⟩
    rcases hx with rfl | hx
    · exact htN
    · exact hON (hYO hx)
  · intro g hg hcomm
    have hcen : ∀ a ∈ S, g * a = a * g := fun a ha => by
      have h1 := hcomm a ha
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rcases mem_or_mul_mem_of_mem_closure_insert htt hYt hg with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, hta⟩ := htC
      set y := g * t with hydef
      have hgy : g = y * t := by rw [hydef, mul_assoc, htt, mul_one]
      obtain ⟨k, hk⟩ := odd_orderOf_of_mem_oddCoreIn (hYO h)
      have hpow : g ^ orderOf y = t := by
        rw [hgy, (Commute.mul_pow (hYt y h) _), pow_orderOf_eq_one, one_mul, hk, pow_succ,
          pow_mul, pow_two, htt, one_pow, one_mul]
      have hgC : g ∈ centralizer (S : Set G) :=
        mem_centralizer_iff.2 fun a ha => (hcen a ha).symm
      have htC' : t ∈ centralizer (S : Set G) := hpow ▸ pow_mem hgC _
      exact hta (mem_centralizer_iff.1 htC' a ha).symm
  · obtain ⟨⟨y, hy⟩, hy1⟩ := (ne_bot_iff_exists_ne_one).1 hY
    by_contra hall
    push Not at hall
    apply hy1
    refine Subtype.ext (hOC y (hYO hy) fun a ha => ?_)
    have h1 := hall y hy a ha
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

variable {X : Type} [Group X] [Finite X]

theorem twin_comap {ψ : X →* G} (hψ : Function.Injective ψ) {t : X} {Y : Subgroup X}
    {S₁ S₂ : Subgroup G} (hS₁ : S₁ ≤ ψ.range) (hS₂ : S₂ ≤ ψ.range) {u : G} (huX : u ∈ ψ.range)
    (hu : orderOf u = 2) {p n : ℕ} [Fact p.Prime]
    (e₁ : S₁ ≃* SL(2, GaloisField p n)) (e₂ : S₂ ≃* SL(2, GaloisField p n))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a) (hu₁ : u ∈ S₁) (hu₂ : u ∈ S₂)
    (hint : ∀ x, x ∈ S₁ → x ∈ S₂ → x = 1 ∨ x = u)
    (hS₁u : S₁ ≤ centralizer ({u} : Set G))
    (hc₁ : IsPComponent 2 (S₁.subgroupOf (ψ.range ⊓ centralizer ({u} : Set G))))
    (hS₂u : S₂ ≤ centralizer ({u} : Set G))
    (hc₂ : IsPComponent 2 (S₂.subgroupOf (ψ.range ⊓ centralizer ({u} : Set G))))
    (hprop₁ : ActsProperly (ψ t) (Y.map ψ) S₁ ⊥) (hprop₂ : ActsProperly (ψ t) (Y.map ψ) S₂ ⊥) :
    ∃ ū : X, ψ ū = u ∧ orderOf ū = 2 ∧
      Nonempty (S₁.comap ψ ≃* SL(2, GaloisField p n)) ∧
      Nonempty (S₂.comap ψ ≃* SL(2, GaloisField p n)) ∧
      (∀ a ∈ S₁.comap ψ, ∀ b ∈ S₂.comap ψ, a * b = b * a) ∧ ū ∈ S₁.comap ψ ∧
      ū ∈ S₂.comap ψ ∧ (∀ x, x ∈ S₁.comap ψ → x ∈ S₂.comap ψ → x = 1 ∨ x = ū) ∧
      S₁.comap ψ ≤ centralizer ({ū} : Set X) ∧
      ((S₁.comap ψ).subgroupOf (centralizer ({ū} : Set X))).IsSubnormal ∧
      S₂.comap ψ ≤ centralizer ({ū} : Set X) ∧
      ((S₂.comap ψ).subgroupOf (centralizer ({ū} : Set X))).IsSubnormal ∧
      ActsProperly t Y (S₁.comap ψ) ⊥ ∧ ActsProperly t Y (S₂.comap ψ) ⊥ := by
  obtain ⟨ū, rfl⟩ := huX
  have hmap₁ : (S₁.comap ψ).map ψ = S₁ := map_comap_eq_self hS₁
  have hmap₂ : (S₂.comap ψ).map ψ = S₂ := map_comap_eq_self hS₂
  have eq₁ : S₁.comap ψ ≃* S₁ := ((S₁.comap ψ).equivMapOfInjective ψ hψ).trans
    (MulEquiv.subgroupCongr hmap₁)
  have eq₂ : S₂.comap ψ ≃* S₂ := ((S₂.comap ψ).equivMapOfInjective ψ hψ).trans
    (MulEquiv.subgroupCongr hmap₂)
  have hCmap : (centralizer ({ū} : Set X)).map ψ = ψ.range ⊓ centralizer ({ψ ū} : Set G) :=
    map_centralizer_singleton_of_injective hψ ū
  have hle : ∀ {S : Subgroup G}, S ≤ ψ.range → S ≤ centralizer ({ψ ū} : Set G) →
      S.comap ψ ≤ centralizer ({ū} : Set X) := by
    intro S hS hSu x hx
    have h1 := mem_centralizer_singleton_iff.1 (hSu hx)
    rw [← map_mul, ← map_mul] at h1
    exact mem_centralizer_singleton_iff.2 (hψ h1)
  have hcomp : ∀ {S : Subgroup G}, S ≤ ψ.range →
      IsPComponent 2 (S.subgroupOf (ψ.range ⊓ centralizer ({ψ ū} : Set G))) →
      IsPComponent 2 ((S.comap ψ).subgroupOf (centralizer ({ū} : Set X))) := by
    intro S hS hc
    rw [isPComponent_subgroupOf_map_iff 2 Nat.prime_two hψ, map_comap_eq_self hS, hCmap]
    exact hc
  have hsub : ∀ {S : Subgroup G}, S ≤ ψ.range → S ≤ centralizer ({ψ ū} : Set G) →
      IsPComponent 2 (S.subgroupOf (ψ.range ⊓ centralizer ({ψ ū} : Set G))) →
      ((S.comap ψ).subgroupOf (centralizer ({ū} : Set X))).IsSubnormal := fun hS hSu hc =>
    (isPComponent_data (hle hS hSu) (hcomp hS hc)).1
  have hprop : ∀ {S : Subgroup G}, S ≤ ψ.range → ActsProperly (ψ t) (Y.map ψ) S ⊥ →
      ActsProperly t Y (S.comap ψ) ⊥ := by
    intro S hS h
    refine ActsProperly.of_map hψ ?_
    rw [map_comap_eq_self hS, Subgroup.map_bot]
    exact h
  refine ⟨ū, rfl, by rwa [orderOf_injective ψ hψ] at hu, ⟨eq₁.trans e₁⟩, ⟨eq₂.trans e₂⟩, ?_, hu₁,
    hu₂, ?_, hle hS₁ hS₁u, hsub hS₁ hS₁u hc₁, hle hS₂ hS₂u, hsub hS₂ hS₂u hc₂, hprop hS₁ hprop₁,
    hprop hS₂ hprop₂⟩
  · intro a ha b hb
    exact hψ (by rw [map_mul, map_mul]; exact hcomm _ ha _ hb)
  · intro x hx₁ hx₂
    rcases hint _ hx₁ hx₂ with h | h
    · exact Or.inl (hψ (by rw [h, map_one]))
    · exact Or.inr (hψ h)

omit [Finite X] in
@[expose] def factorHom {G' : Type*} [Group G'] {ψ : X →* G} (hψ : Function.Injective ψ)
    (f : G' →* G) (hf : ∀ g, f g ∈ ψ.range) : G' →* X :=
  (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp (f.codRestrict ψ.range hf)

omit [Finite X] in
theorem factorHom_spec {G' : Type*} [Group G'] {ψ : X →* G} (hψ : Function.Injective ψ)
    (f : G' →* G) (hf : ∀ g, f g ∈ ψ.range) (g : G') : ψ (factorHom hψ f hf g) = f g := by
  have := (MonoidHom.ofInjective hψ).apply_symm_apply ⟨f g, hf g⟩
  exact congrArg Subtype.val this

omit [Finite X] in
theorem factorHom_eq_one_iff {G' : Type*} [Group G'] {ψ : X →* G} (hψ : Function.Injective ψ)
    (f : G' →* G) (hf : ∀ g, f g ∈ ψ.range) (g : G') : factorHom hψ f hf g = 1 ↔ f g = 1 := by
  rw [← factorHom_spec hψ f hf g]
  exact ⟨fun h => by rw [h, map_one], fun h => hψ (by rw [h, map_one])⟩

omit [Finite X] in
theorem mem_comap_of_factorHom {G' : Type*} [Group G'] {ψ : X →* G} (hψ : Function.Injective ψ)
    (f : G' →* G) (hf : ∀ g, f g ∈ ψ.range) {S : Subgroup G} {g : G'} (hg : f g ∈ S) :
    factorHom hψ f hf g ∈ S.comap ψ := by
  rw [mem_comap, factorHom_spec]
  exact hg

end CFSG.ComponentClassification.Burgoyne.B
