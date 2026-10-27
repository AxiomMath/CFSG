module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveZetAut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoCent

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix

section LeviX

variable {G : Type*} [Group G]

@[expose] def seitzLeviX (W₁ W₂ : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.perfectCore (normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G))

theorem seitzLeviX_le_normalizer_left (W₁ W₂ : Subgroup G) :
    seitzLeviX W₁ W₂ ≤ normalizer (W₁ : Set G) :=
  (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

theorem seitzLeviX_le_normalizer_right (W₁ W₂ : Subgroup G) :
    seitzLeviX W₁ W₂ ≤ normalizer (W₂ : Set G) :=
  (CFSG.Quasithin.perfectCore_le _).trans inf_le_right

theorem conj_mem_normalizer_of_conj_subset {W W' : Subgroup G} {g x : G}
    (h : ∀ w ∈ W, g * w * g⁻¹ ∈ W') (h' : ∀ w ∈ W', g⁻¹ * w * g ∈ W)
    (hx : x ∈ normalizer (W : Set G)) : g * x * g⁻¹ ∈ normalizer (W' : Set G) := by
  rw [mem_normalizer_iff] at hx ⊢
  intro w
  constructor
  · intro hw
    have h3 := h _ ((hx _).1 (h' w hw))
    rwa [show g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ by
      group] at h3
  · intro hw
    have h1 := h' _ hw
    rw [show g⁻¹ * (g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * w * g) * x⁻¹ by
      group] at h1
    have h3 := h _ ((hx _).2 h1)
    rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at h3

theorem conj_mem_seitzLeviX [Finite G] {W₁ W₂ : Subgroup G} {g : G}
    (h : ∀ x ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G),
      g * x * g⁻¹ ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G))
    (h' : ∀ x ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G),
      g⁻¹ * x * g ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G))
    {x : G} (hx : x ∈ seitzLeviX W₁ W₂) : g * x * g⁻¹ ∈ seitzLeviX W₁ W₂ := by
  set H := normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G) with hH
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact h z hz
    · intro hy
      refine ⟨g⁻¹ * y * g, h' y hy, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have h1 := CFSG.Quasithin.map_perfectCore (MulAut.conj g).toMonoidHom H
  rw [hmap] at h1
  have h2 : (MulAut.conj g).toMonoidHom x ∈ (CFSG.Quasithin.perfectCore H).map
      (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [h1] at h2
  exact h2

theorem le_centralizer_of_perfect_of_card_le_four [Finite G] {X Z : Subgroup G}
    (hX : ⁅X, X⁆ = X) (hXZ : X ≤ normalizer (Z : Set G)) (hZ : Nat.card Z ≤ 4) :
    X ≤ centralizer (Z : Set G) := by
  classical
  set N := normalizer (Z : Set G) with hNdef
  let ρ : N →* Equiv.Perm Z := (MulAut.toPerm Z).comp Z.normalizerMonoidHom
  set X' : Subgroup N := X.subgroupOf N with hX'def
  have hX'map : X'.map N.subtype = X := by
    rw [hX'def, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hXZ
  have hX' : ⁅X', X'⁆ = X' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, hX'map, hX]
  set H := X'.map ρ with hHdef
  have hH : ⁅H, H⁆ = H := by rw [hHdef, ← Subgroup.map_commutator, hX']
  obtain ⟨n, hn⟩ := (Equiv.Perm.isSolvable (α := Z) hZ).solvable
  have hle : ∀ k, H ≤ derivedSeries (Equiv.Perm Z) k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hH]
      exact Subgroup.commutator_mono ih ih
  have hbot : H = ⊥ := eq_bot_iff.2 (hn ▸ hle n)
  intro x hx
  rw [mem_centralizer_iff]
  intro z hz
  have hρ : ρ ⟨x, hXZ hx⟩ = 1 := by
    have h : ρ ⟨x, hXZ hx⟩ ∈ H := ⟨⟨x, hXZ hx⟩, hx, rfl⟩
    rw [hbot] at h
    exact h
  have h1 : ρ ⟨x, hXZ hx⟩ ⟨z, hz⟩ = ⟨z, hz⟩ := by rw [hρ]; rfl
  have h2 : x * z * x⁻¹ = z := by
    have h3 : ((Z.normalizerMonoidHom ⟨x, hXZ hx⟩ ⟨z, hz⟩ : Z) : G) = z := congrArg Subtype.val h1
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  calc z * x = x * z * x⁻¹ * x := by rw [h2]
    _ = x * z := by group

theorem card_inf_mul_of_additive {F : Type} [Field F] (hF : Nat.card F = 4) {W₁ W₂ : Subgroup G}
    {μ : G → Fin 3 → F} (hadd : ∀ w ∈ W₁, ∀ w' ∈ W₁, μ (w * w') = μ w + μ w')
    (hsurj : ∀ v, ∃ w ∈ W₁, μ w = v) (hker : ∀ w ∈ W₁, μ w = 0 ↔ w ∈ W₂) :
    Nat.card (W₁ ⊓ W₂ : Subgroup G) * 4 ^ 3 = Nat.card W₁ := by
  have hμ1 : μ 1 = 0 := by
    have h := hadd 1 (one_mem _) 1 (one_mem _)
    rw [one_mul] at h
    simpa using h
  let f : W₁ →* Multiplicative (Fin 3 → F) :=
    { toFun := fun w => Multiplicative.ofAdd (μ w)
      map_one' := by
        change Multiplicative.ofAdd (μ 1) = 1
        rw [hμ1]
        rfl
      map_mul' := fun a b => by
        change Multiplicative.ofAdd (μ (a * b)) = Multiplicative.ofAdd (μ a + μ b)
        rw [hadd _ a.2 _ b.2] }
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, hwv⟩ := hsurj (Multiplicative.toAdd v)
    exact ⟨⟨w, hw⟩, by
      change Multiplicative.ofAdd (μ w) = v
      rw [hwv]
      rfl⟩
  have hkerf : f.ker = W₂.subgroupOf W₁ := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker w w.2]
    change Multiplicative.ofAdd (μ w) = 1 ↔ μ w = 0
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => by rw [h]; rfl⟩
  have hcardker : Nat.card f.ker = Nat.card (W₁ ⊓ W₂ : Subgroup G) := by
    rw [hkerf, ← Subgroup.card_map_of_injective W₁.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hrange, Subgroup.card_top, hcardker] at h
  rw [← h]
  congr 1
  change 4 ^ 3 = Nat.card (Fin 3 → F)
  rw [Nat.card_fun, hF, Nat.card_eq_fintype_card, Fintype.card_fin]

end LeviX

section Swap

variable {G : Type} [Group G]

theorem graph_swap_facts_of_sylowData {L : Subgroup G} {t : G} {W₁ : Subgroup G}
    (htN : t ∈ normalizer (W₁ : Set G)) {Kc : Subgroup (seitzHat W₁)} {S₀ : Subgroup G} {d : G}
    (hdata : IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d) :
    (∀ w ∈ W₁, d * w * d⁻¹ ∈ W₁.map (MulAut.conj d).toMonoidHom) ∧
      (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom, d * w * d⁻¹ ∈ W₁) ∧
      (∀ w ∈ W₁, d⁻¹ * w * d ∈ W₁.map (MulAut.conj d).toMonoidHom) ∧
      (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom, d⁻¹ * w * d ∈ W₁) ∧
      (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom,
        t * w * t⁻¹ ∈ W₁.map (MulAut.conj d).toMonoidHom) ∧
      (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom,
        t⁻¹ * w * t ∈ W₁.map (MulAut.conj d).toMonoidHom) := by
  obtain ⟨-, hS₀N, -, -, -, hdt, hd2, -⟩ := hdata
  have hdd : d * d ∈ normalizer (W₁ : Set G) := (hS₀N.trans (seitzTilde_le_normalizer W₁ Kc)) hd2
  have hN := mem_normalizer_iff.1 hdd
  have hW₂ : ∀ y, y ∈ W₁.map (MulAut.conj d).toMonoidHom ↔ d⁻¹ * y * d ∈ W₁ := by
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show d⁻¹ * (d * v * d⁻¹) * d = v by group]
    · intro hy
      exact ⟨d⁻¹ * y * d, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hdt1 : d⁻¹ * t = t * d⁻¹ := by
    calc d⁻¹ * t = d⁻¹ * (t * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * t) * d⁻¹ := by rw [hdt]
      _ = t * d⁻¹ := by group
  have hdt2 : t⁻¹ * d = d * t⁻¹ := by
    calc t⁻¹ * d = t⁻¹ * (d * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * d) * t⁻¹ := by rw [hdt]
      _ = d * t⁻¹ := by group
  refine ⟨fun w hw => (hW₂ _).2 (by rwa [show d⁻¹ * (d * w * d⁻¹) * d = w by group]),
    fun w hw => ?_, fun w hw => ?_, fun w hw => (hW₂ w).1 hw, fun w hw => ?_, fun w hw => ?_⟩
  · have h1 := (hN _).1 ((hW₂ w).1 hw)
    rwa [show d * d * (d⁻¹ * w * d) * (d * d)⁻¹ = d * w * d⁻¹ by group] at h1
  · rw [hW₂]
    refine (hN _).2 ?_
    rwa [show d * d * (d⁻¹ * (d⁻¹ * w * d) * d) * (d * d)⁻¹ = w by group]
  · rw [hW₂] at hw ⊢
    have h1 := (mem_normalizer_iff.1 htN _).1 hw
    have heq : d⁻¹ * (t * w * t⁻¹) * d = t * (d⁻¹ * w * d) * t⁻¹ := by
      calc d⁻¹ * (t * w * t⁻¹) * d = (d⁻¹ * t) * w * (t⁻¹ * d) := by group
        _ = (t * d⁻¹) * w * (d * t⁻¹) := by rw [hdt1, hdt2]
        _ = t * (d⁻¹ * w * d) * t⁻¹ := by group
    rw [heq]
    exact h1
  · rw [hW₂] at hw ⊢
    have h1 := (mem_normalizer_iff.1 (inv_mem htN) _).1 hw
    have hdt3 : d⁻¹ * t⁻¹ = t⁻¹ * d⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hdt]
    have heq : d⁻¹ * (t⁻¹ * w * t) * d = t⁻¹ * (d⁻¹ * w * d) * t⁻¹⁻¹ := by
      calc d⁻¹ * (t⁻¹ * w * t) * d = (d⁻¹ * t⁻¹) * w * (t * d) := by group
        _ = (t⁻¹ * d⁻¹) * w * (d * t) := by rw [hdt3, hdt]
        _ = t⁻¹ * (d⁻¹ * w * d) * t⁻¹⁻¹ := by group
    rw [heq]
    exact h1

end Swap

@[expose] def LFiveGraphLeviInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      ∃ (F : Type) (_ : Field F) (_ : CharP F 2), Nat.card F = 4 ∧
      ∃ φ : seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom) →*
          SpecialLinearGroup (Fin 3) F,
        Function.Surjective φ ∧
        (∀ x, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₁.map (MulAut.conj d).toMonoidHom) ∧
        S₀ ≤ seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom) ∧
        (∃ B : GL (Fin 3) F, ∀ x : seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom),
          ∀ hx : t * x * t⁻¹ ∈ seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom),
            ((φ ⟨t * x * t⁻¹, hx⟩ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
              (B : Matrix (Fin 3) (Fin 3) F) *
                (φ x : Matrix (Fin 3) (Fin 3) F).map (frobenius F 2) *
                  ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∧
        (∃ μ₁ : G → Fin 3 → F,
          (∀ w ∈ W₁, ∀ w' ∈ W₁, μ₁ (w * w') = μ₁ w + μ₁ w') ∧ (∀ v, ∃ w ∈ W₁, μ₁ w = v) ∧
          (∀ w ∈ W₁, μ₁ w = 0 ↔ w ∈ W₁.map (MulAut.conj d).toMonoidHom) ∧
          ∀ x : seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom), ∀ w ∈ W₁,
            μ₁ ((x : G) * w * (x : G)⁻¹) =
              (((φ x)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ μ₁ w) ∧
        (∃ μ₂ : G → Fin 3 → F,
          (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom, ∀ w' ∈ W₁.map (MulAut.conj d).toMonoidHom,
            μ₂ (w * w') = μ₂ w + μ₂ w') ∧
          (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom, μ₂ w = 0 ↔ w ∈ W₁) ∧
          ∀ x : seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom),
            ∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom,
              μ₂ ((x : G) * w * (x : G)⁻¹) =
                ((φ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ w)

theorem exists_graphField_conj_of_seitzLeviX {G : Type*} [Group G] [Finite G] {F : Type}
    [Field F] [CharP F 2] (hF : Nat.card F = 4) {W₁ W₂ S₀ : Subgroup G} {d t : G}
    (φ : seitzLeviX W₁ W₂ →* SpecialLinearGroup (Fin 3) F) (hφ : Function.Surjective φ)
    (hker : ∀ x, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₂) (hS₀X : S₀ ≤ seitzLeviX W₁ W₂) (hd2 : d * d ∈ S₀)
    (B : GL (Fin 3) F)
    (hB : ∀ x : seitzLeviX W₁ W₂, ∀ hx : t * x * t⁻¹ ∈ seitzLeviX W₁ W₂,
      ((φ ⟨t * x * t⁻¹, hx⟩ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (B : Matrix (Fin 3) (Fin 3) F) * (φ x : Matrix (Fin 3) (Fin 3) F).map (frobenius F 2) *
          ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    {μ₁ μ₂ : G → Fin 3 → F}
    (hμ₁add : ∀ w ∈ W₁, ∀ w' ∈ W₁, μ₁ (w * w') = μ₁ w + μ₁ w')
    (hμ₁surj : ∀ v, ∃ w ∈ W₁, μ₁ w = v) (hμ₁ker : ∀ w ∈ W₁, μ₁ w = 0 ↔ w ∈ W₂)
    (hμ₁act : ∀ x : seitzLeviX W₁ W₂, ∀ w ∈ W₁, μ₁ ((x : G) * w * (x : G)⁻¹) =
      (((φ x)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ μ₁ w)
    (hμ₂add : ∀ w ∈ W₂, ∀ w' ∈ W₂, μ₂ (w * w') = μ₂ w + μ₂ w')
    (hμ₂ker : ∀ w ∈ W₂, μ₂ w = 0 ↔ w ∈ W₁)
    (hμ₂act : ∀ x : seitzLeviX W₁ W₂, ∀ w ∈ W₂, μ₂ ((x : G) * w * (x : G)⁻¹) =
      ((φ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ w)
    (hd₁₂ : ∀ w ∈ W₁, d * w * d⁻¹ ∈ W₂) (hd₂₁ : ∀ w ∈ W₂, d * w * d⁻¹ ∈ W₁)
    (hd₁₂' : ∀ w ∈ W₁, d⁻¹ * w * d ∈ W₂) (hd₂₁' : ∀ w ∈ W₂, d⁻¹ * w * d ∈ W₁)
    (htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁) (htW₁' : ∀ w ∈ W₁, t⁻¹ * w * t ∈ W₁)
    (htW₂ : ∀ w ∈ W₂, t * w * t⁻¹ ∈ W₂) (htW₂' : ∀ w ∈ W₂, t⁻¹ * w * t ∈ W₂)
    (hdt : d * t = t * d) (ht2 : t * t = 1) :
    ∃ d₁ : G, (d₁ = d ∨ d₁ = d * t) ∧
      ∃ (A : SpecialLinearGroup (Fin 3) F)
        (hd₁X : ∀ x ∈ seitzLeviX W₁ W₂, d₁ * x * d₁⁻¹ ∈ seitzLeviX W₁ W₂),
        ∀ x : seitzLeviX W₁ W₂, φ ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩ = A * graphFieldSL F (φ x) * A⁻¹ := by
  have hNd : ∀ x ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G),
      d * x * d⁻¹ ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G) := fun x hx =>
    mem_inf.2 ⟨conj_mem_normalizer_of_conj_subset hd₂₁ hd₁₂' (mem_inf.1 hx).2,
      conj_mem_normalizer_of_conj_subset hd₁₂ hd₂₁' (mem_inf.1 hx).1⟩
  have hNd' : ∀ x ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G),
      d⁻¹ * x * d ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G) := fun x hx => by
    have h1 := conj_mem_normalizer_of_conj_subset (g := d⁻¹) (W := W₁) (W' := W₂)
      (by simpa only [inv_inv] using hd₁₂') (by simpa only [inv_inv] using hd₂₁) (mem_inf.1 hx).1
    have h2 := conj_mem_normalizer_of_conj_subset (g := d⁻¹) (W := W₂) (W' := W₁)
      (by simpa only [inv_inv] using hd₂₁') (by simpa only [inv_inv] using hd₁₂) (mem_inf.1 hx).2
    rw [inv_inv] at h1 h2
    exact mem_inf.2 ⟨h2, h1⟩
  have hNt : ∀ x ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G),
      t * x * t⁻¹ ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G) := fun x hx =>
    mem_inf.2 ⟨conj_mem_normalizer_of_conj_subset htW₁ htW₁' (mem_inf.1 hx).1,
      conj_mem_normalizer_of_conj_subset htW₂ htW₂' (mem_inf.1 hx).2⟩
  have hNt' : ∀ x ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G),
      t⁻¹ * x * t ∈ normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G) := fun x hx => by
    have h1 := conj_mem_normalizer_of_conj_subset (g := t⁻¹) (W := W₁) (W' := W₁)
      (by simpa only [inv_inv] using htW₁') (by simpa only [inv_inv] using htW₁) (mem_inf.1 hx).1
    have h2 := conj_mem_normalizer_of_conj_subset (g := t⁻¹) (W := W₂) (W' := W₂)
      (by simpa only [inv_inv] using htW₂') (by simpa only [inv_inv] using htW₂) (mem_inf.1 hx).2
    rw [inv_inv] at h1 h2
    exact mem_inf.2 ⟨h1, h2⟩
  have hdX : ∀ x ∈ seitzLeviX W₁ W₂, d * x * d⁻¹ ∈ seitzLeviX W₁ W₂ := fun x hx =>
    conj_mem_seitzLeviX hNd hNd' hx
  have hdX' : ∀ x ∈ seitzLeviX W₁ W₂, d⁻¹ * x * d ∈ seitzLeviX W₁ W₂ := fun x hx => by
    have h := conj_mem_seitzLeviX (g := d⁻¹) (fun y hy => by rw [inv_inv]; exact hNd' y hy)
      (fun y hy => by rw [inv_inv]; exact hNd y hy) hx
    rwa [inv_inv] at h
  have htX : ∀ x ∈ seitzLeviX W₁ W₂, t * x * t⁻¹ ∈ seitzLeviX W₁ W₂ := fun x hx =>
    conj_mem_seitzLeviX hNt hNt' hx
  have hXW₁ : ∀ x ∈ seitzLeviX W₁ W₂, ∀ w ∈ W₁, x * w * x⁻¹ ∈ W₁ := fun x hx w hw =>
    (mem_normalizer_iff.1 (seitzLeviX_le_normalizer_left W₁ W₂ hx) w).1 hw
  have hXW₂ : ∀ x ∈ seitzLeviX W₁ W₂, ∀ w ∈ W₂, x * w * x⁻¹ ∈ W₂ := fun x hx w hw =>
    (mem_normalizer_iff.1 (seitzLeviX_le_normalizer_right W₁ W₂ hx) w).1 hw
  exact exists_graphField_conj_of_levi hF φ hφ hker hXW₁ hXW₂ hμ₁add hμ₁surj hμ₁ker hμ₁act
    hμ₂add hμ₂ker hμ₂act hdX hdX' htX hd₁₂ hd₂₁ hd₁₂' hd₂₁' hdt ht2 (hS₀X hd2) B
    (fun x => hB x (htX x x.2))

theorem lFiveGraphXCentralInput_of_leviInput (hX : LFiveGraphLeviInput) :
    LFiveGraphXCentralInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  obtain ⟨F, _, _, hF, φ, hφ, hker, hS₀X, ⟨B, hB⟩, ⟨μ₁, hμ₁add, hμ₁surj, hμ₁ker, hμ₁act⟩,
    ⟨μ₂, hμ₂add, hμ₂ker, hμ₂act⟩⟩ :=
    hX G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  have hZc : Nat.card (W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) = 4 := by
    have h : Nat.card (W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) * 4 ^ 3 = 2 ^ 8 :=
      (card_inf_mul_of_additive hF hμ₁add hμ₁surj hμ₁ker).trans hW₁c
    omega
  have hXZ : seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom) ≤
      centralizer ((W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) :=
    le_centralizer_of_perfect_of_card_le_four (CFSG.Quasithin.perfectCore_perfect _)
      (le_normalizer_of_forall_conj_mem fun x hx w hw => mem_inf.2
        ⟨(mem_normalizer_iff.1 (seitzLeviX_le_normalizer_left _ _ hx) w).1 (mem_inf.1 hw).1,
          (mem_normalizer_iff.1 (seitzLeviX_le_normalizer_right _ _ hx) w).1 (mem_inf.1 hw).2⟩)
      hZc.le
  obtain ⟨hd₁₂, hd₂₁, hd₁₂', hd₂₁', htW₂, htW₂'⟩ := graph_swap_facts_of_sylowData htN hdata
  obtain ⟨-, -, -, -, -, hdt, hd2, -⟩ := hdata
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁ := fun w hw => (mem_normalizer_iff.1 htN w).1 hw
  have htW₁' : ∀ w ∈ W₁, t⁻¹ * w * t ∈ W₁ := fun w hw => by
    have h := (mem_normalizer_iff.1 (inv_mem htN) w).1 hw
    rwa [inv_inv] at h
  obtain ⟨d₁, hd₁, A, hd₁X, hA⟩ := exists_graphField_conj_of_seitzLeviX hF φ hφ hker hS₀X hd2 B
    hB hμ₁add hμ₁surj hμ₁ker hμ₁act hμ₂add hμ₂ker hμ₂act hd₁₂ hd₂₁ hd₁₂' hd₂₁' htW₁ htW₁' htW₂
    htW₂' hdt ht2
  refine ⟨d₁, hd₁, F, inferInstance, inferInstance, hF, _, φ, A, hd₁X, hφ, hker, hS₀X, ?_, ?_⟩
  · exact hA
  · exact hXZ

end CFSG.SeitzReduction.LinearPilot
