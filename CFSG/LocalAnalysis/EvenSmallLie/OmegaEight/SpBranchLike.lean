module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

@[expose] noncomputable def nInv (C : Subgroup G) : ℕ :=
  Nat.card {x : G // x ∈ C ∧ x * x = 1 ∧ x ≠ 1}

@[expose] noncomputable def nOrd4 (C : Subgroup G) : ℕ :=
  Nat.card {x : G // x ∈ C ∧ x * x ≠ 1 ∧ x * x * (x * x) = 1}

@[expose] def Like (T : Subgroup G) (t u : G) : Prop :=
  u ∈ T ∧ u * u = 1 ∧
    Nat.card (T ⊓ centralizer ({u} : Set G) : Subgroup G) =
      Nat.card (T ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
    nInv (T ⊓ centralizer ({u} : Set G)) = nInv (T ⊓ centralizer ({t} : Set G)) ∧
    nOrd4 (T ⊓ centralizer ({u} : Set G)) = nOrd4 (T ⊓ centralizer ({t} : Set G))

theorem card_subtype_map (φ : G ≃* G) {p q : G → Prop} (hpq : ∀ x, q (φ x) ↔ p x) :
    Nat.card {x : G // q x} = Nat.card {x : G // p x} := by
  refine Nat.card_congr
    { toFun := fun y => ⟨φ.symm y, (hpq _).1 (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
      invFun := fun x => ⟨φ x, (hpq _).2 x.2⟩
      left_inv := fun y => Subtype.ext (φ.apply_symm_apply _)
      right_inv := fun x => Subtype.ext (φ.symm_apply_apply _) }

theorem card_map (φ : G ≃* G) (C : Subgroup G) :
    Nat.card (C.map φ.toMonoidHom) = Nat.card C := by
  have h1 : Nat.card (C.map φ.toMonoidHom) = Nat.card {x : G // x ∈ C.map φ.toMonoidHom} := rfl
  have h2 : Nat.card C = Nat.card {x : G // x ∈ C} := rfl
  rw [h1, h2]
  exact card_subtype_map φ fun x => by simp

theorem nInv_map (φ : G ≃* G) (C : Subgroup G) : nInv (C.map φ.toMonoidHom) = nInv C := by
  unfold nInv
  refine card_subtype_map φ fun x => ?_
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, ← map_mul, ne_eq,
    EmbeddingLike.map_eq_one_iff]

theorem nOrd4_map (φ : G ≃* G) (C : Subgroup G) : nOrd4 (C.map φ.toMonoidHom) = nOrd4 C := by
  unfold nOrd4
  refine card_subtype_map φ fun x => ?_
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, ← map_mul, ne_eq,
    EmbeddingLike.map_eq_one_iff]

theorem map_conj_inf_centralizer {T : Subgroup G} {g : G} (hg : g ∈ normalizer (T : Set G))
    (u : G) : (T ⊓ centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom =
      T ⊓ centralizer ({g * u * g⁻¹} : Set G) := by
  ext x
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨hyT, hyu⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.1 hg y).1 hyT, ?_⟩
    calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [hyu]
      _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  · rintro ⟨hxT, hxu⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by group⟩
    · have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hxT
      simpa using this
    · calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * u * g⁻¹ * x) * g := by rw [hxu]
        _ = u * (g⁻¹ * x * g) := by group

theorem like_conj {T : Subgroup G} {t u g : G} (hg : g ∈ normalizer (T : Set G)) :
    Like T t (g * u * g⁻¹) ↔ Like T t u := by
  unfold Like
  rw [← map_conj_inf_centralizer hg, card_map, nInv_map, nOrd4_map]
  have hmem : g * u * g⁻¹ ∈ T ↔ u ∈ T := by
    constructor
    · intro h
      have := (mem_normalizer_iff.1 (inv_mem hg) _).1 h
      simpa [mul_assoc] using this
    · exact fun h => (mem_normalizer_iff.1 hg u).1 h
  have hsq : g * u * g⁻¹ * (g * u * g⁻¹) = 1 ↔ u * u = 1 := by
    rw [show g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group]
    constructor
    · intro h
      have : u * u = g⁻¹ * (g * (u * u) * g⁻¹) * g := by group
      rw [this, h]; group
    · intro h; rw [h]; group
  rw [hmem, hsq]

section Abstract

variable {H : Type*} [Group H]

@[expose] noncomputable def aInv (u : H) : ℕ :=
  Nat.card {x : H // x * x = 1 ∧ x ≠ 1 ∧ x * u = u * x}

@[expose] noncomputable def aOrd4 (u : H) : ℕ :=
  Nat.card {x : H // x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * u = u * x}

@[expose] def ALike (t u : H) : Prop :=
  u * u = 1 ∧ Nat.card (centralizer ({u} : Set H)) = Nat.card (centralizer ({t} : Set H)) ∧
    aInv u = aInv t ∧ aOrd4 u = aOrd4 t

theorem aLike_conj {t u : H} (g : H) : ALike t (g * u * g⁻¹) ↔ ALike t u := by
  have h := like_conj (T := (⊤ : Subgroup H)) (t := t) (u := u) (g := g)
    (mem_normalizer_iff.2 fun x => by simp)
  have key : ∀ v : H, ALike t v ↔ Like ⊤ t v := by
    intro v
    unfold ALike Like aInv aOrd4 nInv nOrd4
    simp only [top_inf_eq, mem_top, true_and, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, ?_, ?_⟩
      · exact h2
      · rw [show (Nat.card {x : H // x * v = v * x ∧ x * x = 1 ∧ x ≠ 1}) =
            Nat.card {x : H // x * x = 1 ∧ x ≠ 1 ∧ x * v = v * x} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        rw [show (Nat.card {x : H // x * t = t * x ∧ x * x = 1 ∧ x ≠ 1}) =
            Nat.card {x : H // x * x = 1 ∧ x ≠ 1 ∧ x * t = t * x} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        exact h3
      · rw [show (Nat.card {x : H // x * v = v * x ∧ x * x ≠ 1 ∧ x * x * (x * x) = 1}) =
            Nat.card {x : H // x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * v = v * x} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        rw [show (Nat.card {x : H // x * t = t * x ∧ x * x ≠ 1 ∧ x * x * (x * x) = 1}) =
            Nat.card {x : H // x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * t = t * x} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        exact h4
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [show (Nat.card {x : H // x * x = 1 ∧ x ≠ 1 ∧ x * v = v * x}) =
            Nat.card {x : H // x * v = v * x ∧ x * x = 1 ∧ x ≠ 1} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        rw [show (Nat.card {x : H // x * x = 1 ∧ x ≠ 1 ∧ x * t = t * x}) =
            Nat.card {x : H // x * t = t * x ∧ x * x = 1 ∧ x ≠ 1} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        exact h3
      · rw [show (Nat.card {x : H // x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * v = v * x}) =
            Nat.card {x : H // x * v = v * x ∧ x * x ≠ 1 ∧ x * x * (x * x) = 1} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        rw [show (Nat.card {x : H // x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * t = t * x}) =
            Nat.card {x : H // x * t = t * x ∧ x * x ≠ 1 ∧ x * x * (x * x) = 1} from
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by tauto)]
        exact h4
  rw [key, key, h]

end Abstract

end CFSG.EvenSmallLie.OmegaEight.SpBranch
