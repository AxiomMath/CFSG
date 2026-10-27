module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.WreathBlocks
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.WreathWr

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.EvenSporadicStandard.M22Std

variable {V : Type} [Group V] {G : Type} [Group G] {ρ : G →* MulAut V}

@[expose] def NormalizerHom : Prop :=
  ∀ (W : Type) [Group W] [Finite W], (∀ x y : W, x * y = y * x) → (∀ x : W, x * x = 1) →
    Nat.card W = 16 → ∀ A : Subgroup (MulAut W), Nonempty (A ≃* alternatingGroup (Fin 6)) →
    ∃ σ : ↥(normalizer (A : Set (MulAut W))) →* Equiv.Perm (Fin 6), Function.Injective σ

theorem rho_inv_apply (g : G) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

@[expose] def resHom (B : Subgroup V) (h : ∀ g : G, ∀ v ∈ B, ρ g v ∈ B) : G →* MulAut B where
  toFun g :=
    { toFun := fun u => ⟨ρ g (u : V), h g (u : V) u.2⟩
      invFun := fun u => ⟨ρ g⁻¹ (u : V), h g⁻¹ (u : V) u.2⟩
      left_inv := fun u => Subtype.ext (rho_inv_apply g (u : V))
      right_inv := fun u => Subtype.ext (by simp)
      map_mul' := fun u u' => Subtype.ext (map_mul (ρ g) (u : V) (u' : V)) }
  map_one' := by ext u; simp
  map_mul' := by intro g h'; ext u; simp

theorem resHom_apply (B : Subgroup V) (h : ∀ g : G, ∀ v ∈ B, ρ g v ∈ B) (g : G) (u : B) :
    ((resHom B h g u : B) : V) = ρ g u := rfl

theorem ns_block (hσ : NormalizerHom) (hc : ∀ x y : V, x * y = y * x) (hs : ∀ x : V, x * x = 1)
    (B : Subgroup V) (hB : Nat.card B = 16) (h : ∀ g : G, ∀ v ∈ B, ρ g v ∈ B)
    (S : Subgroup G) (eS : S ≃* alternatingGroup (Fin 6)) (hS : ∀ g : G, cj g S = S)
    (hfaith : ∀ x ∈ S, (∀ v ∈ B, ρ x v = v) → x = 1) :
    ∃ N : G →* Equiv.Perm (Fin 6), ∀ g, N g = 1 → ∀ v ∈ B, ρ g v = v := by
  have hfin : Finite B := Nat.finite_of_card_ne_zero (by omega)
  let r := resHom B h
  have hinj : Function.Injective (r.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have hx' : ∀ v ∈ B, ρ x v = v := by
      intro v hv
      have := congrArg (fun a : MulAut B => ((a ⟨v, hv⟩ : B) : V)) hx
      simp [r, resHom_apply] at this
      exact this
    exact hfaith x x.2 hx'
  let A := (r.comp S.subtype).range
  let eA : A ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hinj).symm.trans eS
  have hmem : ∀ g : G, r g ∈ normalizer (A : Set (MulAut B)) := by
    intro g n
    have hS1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S := fun x hx => by
      have : g * x * g⁻¹ ∈ cj g S := by rw [mem_cj]; simpa [mul_assoc] using hx
      rwa [hS g] at this
    have hS2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S := fun x hx => by
      have : x ∈ cj g S := by rwa [hS g]
      rwa [mem_cj] at this
    simp only [SetLike.mem_coe, A, MonoidHom.mem_range]
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      refine ⟨⟨g * x * g⁻¹, hS1 x hx⟩, ?_⟩
      simp [map_mul]
    · rintro ⟨⟨y, hy⟩, hyn⟩
      refine ⟨⟨g⁻¹ * y * g, hS2 y hy⟩, ?_⟩
      have hyn' : r y = r g * n * (r g)⁻¹ := hyn
      show r (g⁻¹ * y * g) = n
      rw [map_mul, map_mul, map_inv, hyn']
      group
  obtain ⟨σ, hσinj⟩ := hσ B (fun x y => Subtype.ext (hc x y)) (fun x => Subtype.ext (hs x)) hB A
    ⟨eA⟩
  refine ⟨σ.comp (r.codRestrict _ hmem), ?_⟩
  intro g hg
  have h1 : σ (r.codRestrict _ hmem g) = 1 := hg
  have h2 := (injective_iff_map_eq_one σ).1 hσinj _ h1
  have h3 : r g = 1 := congrArg Subtype.val h2
  intro v hv
  have := congrArg (fun a : MulAut B => ((a ⟨v, hv⟩ : B) : V)) h3
  simpa [r, resHom_apply] using this

theorem Config.exists_wreath_ns [Finite G] (hσ : NormalizerHom) (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) (hρ : Function.Injective ρ)
    (c : Config ρ) (hnorm : ∀ g : G, cj g c.C = c.C ∧ cj g c.D = c.D) :
    ∃ f : G →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2 := by
  have h1 : ∀ g : G, ∀ v ∈ c.U₁, ρ g v ∈ c.U₁ := by
    intro g v hv
    rw [← c.D_fix] at hv ⊢
    exact fix_map (hnorm g).2 hv
  have h2 : ∀ g : G, ∀ v ∈ c.U₂, ρ g v ∈ c.U₂ := by
    intro g v hv
    rw [← c.C_fix] at hv ⊢
    exact fix_map (hnorm g).1 hv
  have hfC : ∀ x ∈ c.C, (∀ v ∈ c.U₁, ρ x v = v) → x = 1 := fun x hx hfix =>
    c.eq_one_of_fix hV hρ x hfix (fun v hv => (c.C_fix v).2 hv x hx)
  have hfD : ∀ x ∈ c.D, (∀ v ∈ c.U₂, ρ x v = v) → x = 1 := fun x hx hfix =>
    c.eq_one_of_fix hV hρ x (fun v hv => (c.D_fix v).2 hv x hx) hfix
  obtain ⟨N₁, hN₁⟩ := ns_block hσ hc hs c.U₁ c.card_U₁ h1 c.C c.eC (fun g => (hnorm g).1) hfC
  obtain ⟨N₂, hN₂⟩ := ns_block hσ hc hs c.U₂ c.card_U₂ h2 c.D c.eD (fun g => (hnorm g).2) hfD
  refine exists_wr_hom (fun _ => false) (fun g i => bif i then N₂ g else N₁ g)
    (fun _ _ => rfl) ?_ ?_
  · intro g h i
    cases i <;> simp [map_mul]
  · intro g _ h0 h1
    exact c.eq_one_of_fix hV hρ g (hN₁ g (by simpa using h0)) (hN₂ g (by simpa using h1))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
