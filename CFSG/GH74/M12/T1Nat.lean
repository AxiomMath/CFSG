module

public import CFSG.GH74.M12.T1GL
public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup
open scoped Matrix MatrixGroups

variable {G : Type} [Group G]

theorem card_SL3_galois : Nat.card SL(3, GaloisField 2 1) = 168 := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero]
  decide

noncomputable def zmodTwoEquivGalois : ZMod 2 ≃+* GaloisField 2 1 := by
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero, pow_one])

theorem det_eq_one_galois (A : GL (Fin 3) (GaloisField 2 1)) :
    (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 1)).det = 1 := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    simpa using this
  have h1 : Nat.card (GaloisField 2 1)ˣ = 1 := by rw [Nat.card_units, hcard]
  have hsub := (Nat.card_eq_one_iff_unique.1 h1).1
  have : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  exact congrArg Units.val this

theorem naturalSL_of_card [Finite G] {E : Subgroup G} (hE8 : Nat.card ↥E = 8)
    (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a)
    (hC : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hM : Nat.card ↥(normalizer (E : Set G)) = 1344) :
    CFSG.CGT.Timmesfeld75.NaturalSL E (normalizer (E : Set G)) 3 1 := by
  classical
  obtain ⟨f⟩ := exists_coords8 hE8 hEe
  set σ := zmodTwoEquivGalois with hσ
  set M := normalizer (E : Set G) with hMdef
  let ρ : ↥M →* GL (Fin 3) (ZMod 2) := actGL f
  let ρ' : ↥M →* SL(3, GaloisField 2 1) :=
    { toFun := fun m => ⟨(ρ m : Matrix (Fin 3) (Fin 3) (ZMod 2)).map σ, by
        have := det_eq_one_galois ((Matrix.GeneralLinearGroup.map (σ : ZMod 2 →+* _)) (ρ m))
        simpa [Matrix.GeneralLinearGroup.map] using this⟩
      map_one' := by
        apply Subtype.ext
        simp [Matrix.map_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        show (ρ (a * b) : Matrix (Fin 3) (Fin 3) (ZMod 2)).map σ =
          (ρ a : Matrix (Fin 3) (Fin 3) (ZMod 2)).map σ * (ρ b : Matrix (Fin 3) (Fin 3) (ZMod 2)).map σ
        rw [map_mul, Units.val_mul]
        exact Matrix.map_mul (f := (σ : ZMod 2 →+* GaloisField 2 1)) }
  have hρ' : ∀ m, ((ρ' m : SL(3, GaloisField 2 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 2 1)) =
      (ρ m : Matrix (Fin 3) (Fin 3) (ZMod 2)).map σ := fun m => rfl
  have hker : ρ'.ker = E.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ρ m = 1 := by
        apply Units.ext
        have h2 := congrArg (fun A : SL(3, GaloisField 2 1) =>
          ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 1))).map σ.symm) h
        simp only [hρ', Matrix.map_map] at h2
        have hid : (⇑σ.symm ∘ ⇑σ) = id := funext σ.symm_apply_apply
        rw [hid, Matrix.map_id] at h2
        rw [h2]
        simp
      exact hC m ((actGL_eq_one_iff f m).1 h1)
    · intro hm
      have h1 : ρ m = 1 := (actGL_eq_one_iff f m).2 fun e he => (hEe _ hm e he).2
      apply Subtype.ext
      rw [hρ', h1]
      simp
  have hsurj : Function.Surjective ρ' := by
    have h1 := Subgroup.card_mul_index ρ'.ker
    rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer : E ≤ M)).toEquiv, hE8, hM] at h1
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [card_SL3_galois]
    omega
  let τ : (Fin 3 → ZMod 2) ≃+ (Fin 3 → GaloisField 2 1) :=
    AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  let φ : ↥E ≃* Multiplicative (Fin 3 → GaloisField 2 1) :=
    f.symm.trans (AddEquiv.toMultiplicative τ)
  have hφ : ∀ t : ↥E, Multiplicative.toAdd (φ t) = σ ∘ Multiplicative.toAdd (f.symm t) :=
    fun t => rfl
  have hN : (E.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  refine ⟨hN, (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj), φ, ?_⟩
  intro h t hmem
  have he : ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj)) (QuotientGroup.mk h) = ρ' h := rfl
  rw [he]
  apply Multiplicative.toAdd.injective
  rw [hφ, toAdd_ofAdd, hφ, hρ']
  have hact := actGL_mulVec f h (Multiplicative.toAdd (f.symm t))
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply] at hact
  have hfeq : f.symm ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (f.symm t)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hact.symm
  rw [hfeq, toAdd_ofAdd]
  funext i
  exact RingHom.map_mulVec (σ : ZMod 2 →+* GaloisField 2 1) _ _ i

end CFSG.GH74.M12.Thm1
