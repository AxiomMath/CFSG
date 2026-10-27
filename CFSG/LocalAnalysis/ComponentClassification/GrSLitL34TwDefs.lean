module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

@[ext] structure WrE where
  a : Equiv.Perm (Fin 42)
  b : Equiv.Perm (Fin 42)
  e : Bool

namespace WrE

instance : Mul WrE where
  mul x y :=
    if y.e then ⟨x.b * y.a, x.a * y.b, xor x.e y.e⟩ else ⟨x.a * y.a, x.b * y.b, xor x.e y.e⟩

instance : One WrE := ⟨⟨1, 1, false⟩⟩

instance : Inv WrE where
  inv x := if x.e then ⟨x.b⁻¹, x.a⁻¹, true⟩ else ⟨x.a⁻¹, x.b⁻¹, false⟩

theorem mul_def (x y : WrE) :
    x * y = if y.e then ⟨x.b * y.a, x.a * y.b, xor x.e y.e⟩
      else ⟨x.a * y.a, x.b * y.b, xor x.e y.e⟩ := rfl

theorem one_def : (1 : WrE) = ⟨1, 1, false⟩ := rfl

theorem inv_def (x : WrE) :
    x⁻¹ = if x.e then ⟨x.b⁻¹, x.a⁻¹, true⟩ else ⟨x.a⁻¹, x.b⁻¹, false⟩ := rfl

instance : Group WrE :=
  Group.ofLeftAxioms
    (fun x y z => by
      rcases x with ⟨xa, xb, xe⟩
      rcases y with ⟨ya, yb, ye⟩
      rcases z with ⟨za, zb, ze⟩
      cases xe <;> cases ye <;> cases ze <;> simp [mul_def, mul_assoc])
    (fun x => by
      rcases x with ⟨xa, xb, xe⟩
      cases xe <;> simp [mul_def, one_def])
    (fun x => by
      rcases x with ⟨xa, xb, xe⟩
      cases xe <;> simp [mul_def, inv_def, one_def])

instance : Finite WrE :=
  Finite.of_injective (fun x : WrE => (x.a, x.b, x.e)) fun x y h => by
    simp only [Prod.mk.injEq] at h
    exact WrE.ext h.1 h.2.1 h.2.2

end WrE

@[expose] def wrR : Subgroup WrE where
  carrier := {x | x.a ∈ R ∧ x.b ∈ R}
  one_mem' := ⟨R.one_mem, R.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, WrE.mul_def]
    cases hye : y.e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨R.mul_mem hx.1 hy.1, R.mul_mem hx.2 hy.2⟩
    · simp only [↓reduceIte]
      exact ⟨R.mul_mem hx.2 hy.1, R.mul_mem hx.1 hy.2⟩
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, WrE.inv_def]
    cases hxe : x.e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨R.inv_mem hx.1, R.inv_mem hx.2⟩
    · simp only [↓reduceIte]
      exact ⟨R.inv_mem hx.2, R.inv_mem hx.1⟩

@[expose] def ssS : Subgroup WrE where
  carrier := {x | x.e = false ∧ x.a ∈ S ∧ x.b ∈ S}
  one_mem' := ⟨rfl, S.one_mem, S.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, WrE.mul_def, hy.1]
    simp only [Bool.false_eq_true, ↓reduceIte, hx.1, Bool.xor_false, true_and]
    exact ⟨S.mul_mem hx.2.1 hy.2.1, S.mul_mem hx.2.2 hy.2.2⟩
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, WrE.inv_def, hx.1]
    simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    exact ⟨S.inv_mem hx.2.1, S.inv_mem hx.2.2⟩

@[expose] def isUni (r : Equiv.Perm (Fin 42)) : Prop := ∃ c ∈ R, r = c * r₄ * c⁻¹

@[expose] def IsA (x : WrE) : Prop :=
  x.e = false ∧ x * x = 1 ∧
    ((x.a = 1 ∧ x.b ≠ 1 ∧ x.b ∈ S) ∨ (x.b = 1 ∧ x.a ≠ 1 ∧ x.a ∈ S))

@[expose] def IsD (x : WrE) : Prop :=
  x.e = false ∧ x * x = 1 ∧ x.a ≠ 1 ∧ x.b ≠ 1 ∧ x.a ∈ S ∧ x.b ∈ S

@[expose] def IsUU (x : WrE) : Prop :=
  x.e = false ∧ x * x = 1 ∧ isUni x.a ∧ isUni x.b

structure GoodX (X : Subgroup WrE) : Prop where
  le_wrR : X ≤ wrR
  two : IsPGroup 2 X
  card_ss : Nat.card ↥(X ⊓ ssS) = 2 ^ 12
  swap : ∃ g ∈ X, g.e = true
  h13 : ∀ g ∈ X, g.e = true → g * g ≠ 1
  h14 : ∃ g ∈ X, g.e = true ∧ g ^ 4 = 1
  h20 : ∀ g ∈ X, g.e = true → (g * g).a ∉ S
  h22 : ∀ g ∈ X, g.e = true → (∀ h ∈ X, h.e = true → orderOf g ≤ orderOf h) →
    ¬ ∃ F ≤ X ⊓ centralizer ({g * g} : Set WrE), GrSLit.IsEightGroup F ∧
      ∃ w ∈ X ⊓ centralizer ({g * g} : Set WrE), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧ w ∉ F

structure ConcX (X : Subgroup WrE) : Prop where
  d_central : ∃ d ∈ X, (∀ x ∈ X, x * d = d * x) ∧ IsD d
  swap_min : ∀ g ∈ X, g.e = true → (∀ h ∈ X, h.e = true → orderOf g ≤ orderOf h) →
    g ^ 4 = 1 ∧ IsUU (g * g)
  inv_types : ∀ x ∈ X, x * x = 1 → x ≠ 1 → IsA x ∨ IsD x ∨ IsUU x
  a_noncentral : ∀ b ∈ X, IsA b → ∃ x ∈ X, x * b ≠ b * x
  a_big : ∀ b ∈ X, IsA b → 2 ^ 10 ≤ Nat.card ↥(X ⊓ centralizer ({b} : Set WrE))
  pair_card : ∀ a' ∈ X, ∀ y' ∈ X, IsA a' → IsUU y' → a' * y' = y' * a' →
    Nat.card ↥(X ⊓ centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE)) ≤ 2 ^ 7
  pair_rank : ∀ a' ∈ X, ∀ y' ∈ X, IsA a' → IsUU y' → a' * y' = y' * a' →
    ¬ ∃ E ≤ X ⊓ centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE),
      GrSLit.IsElemTwo E ∧ Nat.card E = 16
  pair_sq : ∀ a' ∈ X, ∀ y' ∈ X, IsA a' → IsUU y' → a' * y' = y' * a' →
    ∀ x ∈ X ⊓ centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE), x * x ≠ 1 →
      x * x = a' ∨ (IsA (x * x) ∧ IsD (a' * (x * x))) ∨ (IsD (x * x) ∧ IsA (a' * (x * x)))

structure TwHyp (G : Type) [Group G] [Finite G] (a x : G) (J S W K T : Subgroup G) (t : G) :
    Prop where
  hset : L34Sec4Setting G a x J S
  hcent : ∀ s ∈ S, s * a = a * s
  hZ1 : S ⊓ zStarIn J = ⊥
  hW : W ≠ ⊥
  hWodd : Odd (Nat.card W)
  hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)
  hKM : K ≤ normalizer (W : Set G)
  hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G)))
  hKL : IsL34Type (K ⧸ Open.fusionZStar K)
  hsup : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G))
  hTsyl : IsSylowTwoIn T (normalizer (W : Set G))
  hST : S ≤ T
  hTG : ∃ P : Sylow 2 G, (P : Subgroup G) = T
  htT : t ∈ T
  htK : t ∉ normalizer (K : Set G)
  hr2 : ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t
  hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1
  hinv : ∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G)
  hu : ∃ u ∈ T, u ∉ normalizer (K : Set G) ∧ u ^ 4 = 1
  haKt : a ∈ conjugate K t
  hE4 : ∀ w ∈ T ⊓ normalizer (K : Set G), w * w ∈ K ⊔ conjugate K t
  hE5 : ∀ v ∈ T, v ∉ normalizer (K : Set G) → v * v ∉ withKernel K
  hE6 : ∀ v ∈ T, v ∉ normalizer (K : Set G) →
    (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
    ∃ g : G, g⁻¹ * v * g ∈ T ⊓ normalizer (K : Set G)
  hE7 : ∀ v ∈ T, v ∉ normalizer (K : Set G) →
    (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
    ¬ ∃ F ≤ T ⊓ centralizer ({v * v} : Set G), IsEightGroup F ∧
      ∃ w ∈ T ⊓ centralizer ({v * v} : Set G), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧ w ∉ F

structure TwModel {G : Type} [Group G] (M K : Subgroup G) (t : G) (ρ : ↥M →* WrE) : Prop where
  mem_wrR : ∀ m, ρ m ∈ wrR
  ker_iff : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ oddIn M
  swap_iff : ∀ m : ↥M, (ρ m).e = true ↔ (m : G) ∉ normalizer (K : Set G)
  withKernel_iff : ∀ m : ↥M, (m : G) ∈ normalizer (K : Set G) →
    ((m : G) ∈ withKernel K ↔ (ρ m).a ∈ S)
  K_img : ∀ m : ↥M, (m : G) ∈ K → (ρ m).e = false ∧ (ρ m).b = 1 ∧ (ρ m).a ∈ S
  Kt_img : ∀ m : ↥M, (m : G) ∈ conjugate K t → (ρ m).e = false ∧ (ρ m).a = 1 ∧ (ρ m).b ∈ S
  K_surj : ∀ s ∈ S, ∃ m : ↥M, (m : G) ∈ K ∧ ρ m = ⟨s, 1, false⟩
  Kt_surj : ∀ s ∈ S, ∃ m : ↥M, (m : G) ∈ conjugate K t ∧ ρ m = ⟨1, s, false⟩

@[expose] def imgT {G : Type} [Group G] (T M : Subgroup G) (ρ : ↥M →* WrE) : Subgroup WrE :=
  (T.subgroupOf M).map ρ

end CFSG.ComponentClassification.GrSLit.L34Tw
