module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

@[expose] def L34FieldNormalUTSection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P W : Subgroup G), L34FieldNormalSetting G t P →
    Odd (Nat.card W) → W ≠ ⊥ → normalizer (P : Set G) ≤ normalizer (W : Set G) →
    (∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W) →
    ∃ S Y : Subgroup G, IsSylowTwoIn S (normalizer (W : Set G)) ∧
      Y ≤ normalizer (W : Set G) ∧ (Y.subgroupOf (normalizer (W : Set G))).Normal ∧
      ⁅⁅S ⊓ Y, S ⊓ Y⁆, S ⊓ Y⁆ = ⊥ ∧ (∀ x ∈ S ⊓ Y, x ^ 4 = 1) ∧
      (∃ E : Subgroup G, E ≤ S ⊓ Y ∧ Open.IsElemAbelian 2 E ∧ 16 ≤ Nat.card E) ∧
      (∃ A : Subgroup G, A ≤ S ∧ S ≤ normalizer (A : Set G) ∧ Open.IsElemAbelian 2 A ∧
        32 ≤ Nat.card A ∧ GrSLit.wGroup A = W) ∧
      (∃ B : Subgroup G, B ≤ S ∧ S ≤ normalizer (B : Set G) ∧ Open.IsElemAbelian 2 B ∧
        32 ≤ Nat.card B ∧ ∀ x ∈ S ⊓ Y, ∀ y ∈ B, x * y = y * x)

section FixedPoints

variable {G : Type} [Group G] [Finite G]

theorem card_le_card_inf_centralizer_sq_of_sq {E : Subgroup G} {a : G} (hE : IsElemTwo E)
    (haE : a ∈ normalizer (E : Set G)) (ha2 : ∀ e ∈ E, a * a * e = e * (a * a)) :
    Nat.card E ≤ Nat.card ↥(E ⊓ centralizer ({a} : Set G)) ^ 2 := by
  have hconj : ∀ e ∈ E, a * e * a⁻¹ ∈ E := fun e he => (mem_normalizer_iff.mp haE e).mp he
  let f : E →* E :=
    { toFun := fun e => ⟨(e : G)⁻¹ * (a * e * a⁻¹), mul_mem (inv_mem e.2) (hconj e e.2)⟩
      map_one' := by ext; simp
      map_mul' := fun e₁ e₂ => by
        apply Subtype.ext
        show ((e₁ : G) * e₂)⁻¹ * (a * (e₁ * e₂) * a⁻¹) =
          ((e₁ : G)⁻¹ * (a * e₁ * a⁻¹)) * ((e₂ : G)⁻¹ * (a * e₂ * a⁻¹))
        have h1 := hE.1 _ (hconj _ e₁.2) _ (inv_mem e₂.2)
        calc ((e₁ : G) * e₂)⁻¹ * (a * (e₁ * e₂) * a⁻¹) =
              (e₂ : G)⁻¹ * (e₁ : G)⁻¹ * ((a * e₁ * a⁻¹) * (a * e₂ * a⁻¹)) := by group
          _ = (e₁ : G)⁻¹ * (e₂ : G)⁻¹ * ((a * e₁ * a⁻¹) * (a * e₂ * a⁻¹)) := by
              rw [hE.1 _ (inv_mem e₂.2) _ (inv_mem e₁.2)]
          _ = (e₁ : G)⁻¹ * ((e₂ : G)⁻¹ * (a * e₁ * a⁻¹)) * (a * e₂ * a⁻¹) := by group
          _ = (e₁ : G)⁻¹ * ((a * e₁ * a⁻¹) * (e₂ : G)⁻¹) * (a * e₂ * a⁻¹) := by rw [h1]
          _ = ((e₁ : G)⁻¹ * (a * e₁ * a⁻¹)) * ((e₂ : G)⁻¹ * (a * e₂ * a⁻¹)) := by group }
  have hker : Nat.card f.ker = Nat.card ↥(E ⊓ centralizer ({a} : Set G)) := by
    refine Nat.card_congr ⟨fun e => ⟨((e : E) : G), mem_inf.mpr ⟨(e : E).2, ?_⟩⟩,
      fun c => ⟨⟨c, (mem_inf.mp c.2).1⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · have h := MonoidHom.mem_ker.mp e.2
      have h' : ((e : E) : G)⁻¹ * (a * ((e : E) : G) * a⁻¹) = 1 := congrArg Subtype.val h
      rw [mem_centralizer_singleton_iff]
      have h'' : ((e : E) : G) = a * ((e : E) : G) * a⁻¹ := inv_mul_eq_one.mp h'
      calc ((e : E) : G) * a = a * ((e : E) : G) * a⁻¹ * a := by rw [← h'']
        _ = a * (e : E) := by group
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (c : G)⁻¹ * (a * c * a⁻¹) = 1
      have hc := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
      rw [← hc]
      group
  have hrange : Nat.card f.range ≤ Nat.card ↥(E ⊓ centralizer ({a} : Set G)) := by
    have hle : (f.range).map E.subtype ≤ E ⊓ centralizer ({a} : Set G) := by
      rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
      refine mem_inf.mpr ⟨(f e).2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      show ((e : G)⁻¹ * (a * e * a⁻¹)) * a = a * ((e : G)⁻¹ * (a * e * a⁻¹))
      set c : G := (e : G)⁻¹ * (a * e * a⁻¹) with hcdef
      have h1 : a * c * a⁻¹ = (a * e * a⁻¹)⁻¹ * ((a * a) * e * (a * a)⁻¹) := by
        rw [hcdef]
        group
      rw [ha2 e e.2, mul_assoc (e : G), mul_inv_cancel, mul_one] at h1
      have h2 : (a * e * a⁻¹)⁻¹ * (e : G) = c := by
        have hinv1 : (a * e * a⁻¹)⁻¹ = a * e * a⁻¹ := by
          rw [inv_eq_iff_mul_eq_one]; exact hE.2 _ (hconj e e.2)
        have hinv2 : (e : G)⁻¹ = e := by rw [inv_eq_iff_mul_eq_one]; exact hE.2 e e.2
        rw [hcdef, hinv1, hinv2, hE.1 _ (hconj e e.2) _ e.2]
      have h3 := h1.trans h2
      calc c * a = a * c * a⁻¹ * a := by rw [h3]
        _ = a * c := by group
    calc Nat.card f.range = Nat.card ↥((f.range).map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card ↥(E ⊓ centralizer ({a} : Set G)) := Subgroup.card_le_of_le hle
  have hcard : Nat.card E = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard, hker, pow_two]
  exact Nat.mul_le_mul_left _ hrange

theorem three_le_pRank_of_sq_centralizes {S B : Subgroup G} {y : G} (hBS : B ≤ S)
    (hB : IsElemTwo B) (hB32 : 32 ≤ Nat.card B) (hyB : y ∈ normalizer (B : Set G))
    (hy2 : ∀ e ∈ B, y * y * e = e * (y * y)) :
    3 ≤ pRank 2 ↥(S ⊓ centralizer ({y} : Set G)) := by
  have hsq := card_le_card_inf_centralizer_sq_of_sq hB hyB hy2
  have h8 : 8 ≤ Nat.card ↥(B ⊓ centralizer ({y} : Set G)) :=
    (le_card_of_le_card_sq (hB.isPGroup.to_le inf_le_left)).2 (hB32.trans hsq)
  exact three_le_pRank_of_le (hB.mono inf_le_left) h8 (inf_le_inf_right _ hBS)

end FixedPoints

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
