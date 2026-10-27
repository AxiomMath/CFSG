module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFacts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure U4NatData (G : Type) [Group G] (n : ℕ) (L V : Subgroup G) where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  card_F : Nat.card F = (2 ^ n) ^ 2
  ε : ↥L →* ↥(StatedSU 4 (2 ^ n) F)
  φ : ↥V →* Multiplicative (Fin 4 → F)
  ε_surj : Function.Surjective ε
  φ_bij : Function.Bijective φ
  ε_ker : ε.ker = CFSG.pCore 2 ↥L
  equiv : ∀ (l : ↥L) (v v' : ↥V), (l : G) * (v : G) * (l : G)⁻¹ = (v' : G) →
    φ v' = Multiplicative.ofAdd
      (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (φ v)))

attribute [instance] U4NatData.instField U4NatData.instFinite

@[expose] def U4NatData.sing {n : ℕ} {L V : Subgroup G} (d : U4NatData G n L V) (x : G) : Prop :=
  ∃ hx : x ∈ V, ∑ i, (Multiplicative.toAdd (d.φ ⟨x, hx⟩)) i ^ (2 ^ n + 1) = 0

structure O6NatData (G : Type) [Group G] (n : ℕ) (L V : Subgroup G) where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  card_F : Nat.card F = 2 ^ n
  b : F
  c : F
  irred : ∀ s : F, s ^ 2 + b * s + c ≠ 0
  ε : ↥L →* ↥(StatedOmega (StatedQuadMinus 3 F b c))
  φ : ↥V →* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)
  ε_surj : Function.Surjective ε
  φ_bij : Function.Bijective φ
  ε_ker : ε.ker = CFSG.pCore 2 ↥L
  equiv : ∀ (l : ↥L) (v v' : ↥V), (l : G) * (v : G) * (l : G)⁻¹ = (v' : G) →
    φ v' = Multiplicative.ofAdd
      (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
        (Multiplicative.toAdd (φ v)))

attribute [instance] O6NatData.instField O6NatData.instFinite

@[expose] def O6NatData.sing {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V) (x : G) : Prop :=
  ∃ hx : x ∈ V, StatedQuadMinus 3 d.F d.b d.c (Multiplicative.toAdd (d.φ ⟨x, hx⟩)) = 0

@[expose] def cjIso (g : G) (L : Subgroup G) : ↥(cj g L) ≃* ↥L where
  toFun x := ⟨g⁻¹ * (x : G) * g, mem_cj_iff.mp x.2⟩
  invFun l := ⟨g * (l : G) * g⁻¹, mem_cj_iff.mpr (by simpa [mul_assoc] using l.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv l := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]

@[simp] theorem coe_cjIso (g : G) (L : Subgroup G) (x : ↥(cj g L)) :
    ((cjIso g L x : ↥L) : G) = g⁻¹ * (x : G) * g := rfl

@[simp] theorem coe_cjIso_symm (g : G) (L : Subgroup G) (l : ↥L) :
    (((cjIso g L).symm l : ↥(cj g L)) : G) = g * (l : G) * g⁻¹ := rfl

theorem ker_comp_cjIso {L : Subgroup G} {N : Type} [Group N] (g : G) (ε : ↥L →* N)
    (h : ε.ker = CFSG.pCore 2 ↥L) :
    (ε.comp (cjIso g L).toMonoidHom).ker = CFSG.pCore 2 ↥(cj g L) := by
  have h1 : (CFSG.pCore 2 ↥(cj g L)).map (cjIso g L).toMonoidHom = CFSG.pCore 2 ↥L :=
    CFSG.pCore_map_iso 2 (cjIso g L)
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, h, ← h1]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := (cjIso g L).injective hyx
    rw [← this]
    exact hy
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

@[expose] noncomputable def U4NatData.conj {n : ℕ} {L V : Subgroup G} (d : U4NatData G n L V) (g : G) :
    U4NatData G n (cj g L) (cj g V) where
  F := d.F
  card_F := d.card_F
  ε := d.ε.comp (cjIso g L).toMonoidHom
  φ := d.φ.comp (cjIso g V).toMonoidHom
  ε_surj := d.ε_surj.comp (cjIso g L).surjective
  φ_bij := d.φ_bij.comp (cjIso g V).bijective
  ε_ker := ker_comp_cjIso g d.ε d.ε_ker
  equiv := by
    intro l v v' h
    refine d.equiv (cjIso g L l) (cjIso g V v) (cjIso g V v') ?_
    show g⁻¹ * (l : G) * g * (g⁻¹ * (v : G) * g) * (g⁻¹ * (l : G) * g)⁻¹ = g⁻¹ * (v' : G) * g
    rw [← h]
    group

theorem U4NatData.sing_conj {n : ℕ} {L V : Subgroup G} (d : U4NatData G n L V) (g : G) :
    (d.conj g).sing = fun x => d.sing (g⁻¹ * x * g) := by
  funext x
  apply propext
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨mem_cj_iff.mp hx, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨mem_cj_iff.mpr hx, h⟩

@[expose] noncomputable def O6NatData.conj {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V) (g : G) :
    O6NatData G n (cj g L) (cj g V) where
  F := d.F
  card_F := d.card_F
  b := d.b
  c := d.c
  irred := d.irred
  ε := d.ε.comp (cjIso g L).toMonoidHom
  φ := d.φ.comp (cjIso g V).toMonoidHom
  ε_surj := d.ε_surj.comp (cjIso g L).surjective
  φ_bij := d.φ_bij.comp (cjIso g V).bijective
  ε_ker := ker_comp_cjIso g d.ε d.ε_ker
  equiv := by
    intro l v v' h
    refine d.equiv (cjIso g L l) (cjIso g V v) (cjIso g V v') ?_
    show g⁻¹ * (l : G) * g * (g⁻¹ * (v : G) * g) * (g⁻¹ * (l : G) * g)⁻¹ = g⁻¹ * (v' : G) * g
    rw [← h]
    group

theorem O6NatData.sing_conj {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V) (g : G) :
    (d.conj g).sing = fun x => d.sing (g⁻¹ * x * g) := by
  funext x
  apply propext
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨mem_cj_iff.mp hx, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨mem_cj_iff.mpr hx, h⟩

structure U4ChiefData (G : Type) [Group G] (n : ℕ) (L U : Subgroup G) where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  card_F : Nat.card F = (2 ^ n) ^ 2
  ε : ↥L →* ↥(StatedSU 4 (2 ^ n) F)
  φ : ↥U →* Multiplicative (Fin 4 → F)
  ε_surj : Function.Surjective ε
  φ_surj : Function.Surjective φ
  ε_ker : ε.ker = CFSG.pCore 2 ↥L
  φ_ker : φ.ker = (U ⊓ centralizer (L : Set G)).subgroupOf U
  equiv : ∀ (l : ↥L) (u u' : ↥U), (l : G) * (u : G) * (l : G)⁻¹ = (u' : G) →
    φ u' = Multiplicative.ofAdd
      (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (φ u)))

attribute [instance] U4ChiefData.instField U4ChiefData.instFinite

structure O6ChiefData (G : Type) [Group G] (n : ℕ) (L U : Subgroup G) where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  card_F : Nat.card F = 2 ^ n
  b : F
  c : F
  irred : ∀ s : F, s ^ 2 + b * s + c ≠ 0
  ε : ↥L →* ↥(StatedOmega (StatedQuadMinus 3 F b c))
  φ : ↥U →* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)
  ε_surj : Function.Surjective ε
  φ_surj : Function.Surjective φ
  ε_ker : ε.ker = CFSG.pCore 2 ↥L
  φ_ker : φ.ker = (U ⊓ centralizer (L : Set G)).subgroupOf U
  equiv : ∀ (l : ↥L) (u u' : ↥U), (l : G) * (u : G) * (l : G)⁻¹ = (u' : G) →
    φ u' = Multiplicative.ofAdd
      (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
        (Multiplicative.toAdd (φ u)))

attribute [instance] O6ChiefData.instField O6ChiefData.instFinite

@[expose] def U4ChiefData.toNat {n : ℕ} {L U : Subgroup G} (d : U4ChiefData G n L U)
    (h : U ⊓ centralizer (L : Set G) = ⊥) : U4NatData G n L U where
  F := d.F
  card_F := d.card_F
  ε := d.ε
  φ := d.φ
  ε_surj := d.ε_surj
  φ_bij := ⟨(MonoidHom.ker_eq_bot_iff d.φ).mp (by rw [d.φ_ker, h]; exact Subgroup.bot_subgroupOf U),
    d.φ_surj⟩
  ε_ker := d.ε_ker
  equiv := d.equiv

@[expose] def O6ChiefData.toNat {n : ℕ} {L U : Subgroup G} (d : O6ChiefData G n L U)
    (h : U ⊓ centralizer (L : Set G) = ⊥) : O6NatData G n L U where
  F := d.F
  card_F := d.card_F
  b := d.b
  c := d.c
  irred := d.irred
  ε := d.ε
  φ := d.φ
  ε_surj := d.ε_surj
  φ_bij := ⟨(MonoidHom.ker_eq_bot_iff d.φ).mp (by rw [d.φ_ker, h]; exact Subgroup.bot_subgroupOf U),
    d.φ_surj⟩
  ε_ker := d.ε_ker
  equiv := d.equiv

@[expose] def U4ModuleFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n : ℕ) (M L V : Subgroup G) (d : U4NatData G n L V),
    p.Prime → p ∣ 2 ^ n + 1 → 1 ≤ n → L ≤ M → V ≤ M → M ≤ normalizer (L : Set G) →
    M ≤ normalizer (V : Set G) → U4LocalFacts p n M L V d.sing

@[expose] def O6ModuleFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n : ℕ) (M L V : Subgroup G) (d : O6NatData G n L V),
    p.Prime → p ∣ 2 ^ n + 1 → 1 ≤ n → L ≤ M → V ≤ M → M ≤ normalizer (L : Set G) →
    M ≤ normalizer (V : Set G) → O6LocalFacts p n M L V d.sing

@[expose] def U4ChiefFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n : ℕ) (L U : Subgroup G) (d : U4ChiefData G n L U),
    p.Prime → p ∣ 2 ^ n + 1 → 1 ≤ n → L ≤ normalizer (U : Set G) →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S L →
      ∃ Q : Subgroup G, Q ≤ S ∧ ∃ x ∈ L ⊓ normalizer (Q : Set G), x ≠ 1 ∧ x ^ p = 1 ∧
        ∀ u ∈ U, (∀ s ∈ Q, ⁅s, u⁆ ∈ centralizer (L : Set G)) → ⁅x, u⁆ ∈ centralizer (L : Set G)

@[expose] def O6ChiefFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n : ℕ) (L U : Subgroup G) (d : O6ChiefData G n L U),
    p.Prime → p ∣ 2 ^ n + 1 → 1 ≤ n → L ≤ normalizer (U : Set G) →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S L →
      ∃ Q : Subgroup G, Q ≤ S ∧ ∃ x ∈ L ⊓ normalizer (Q : Set G), x ≠ 1 ∧ x ^ p = 1 ∧
        ∀ u ∈ U, (∀ s ∈ Q, ⁅s, u⁆ ∈ centralizer (L : Set G)) → ⁅x, u⁆ ∈ centralizer (L : Set G)

end CFSG.LocalAnalysis.RankThreeUC
