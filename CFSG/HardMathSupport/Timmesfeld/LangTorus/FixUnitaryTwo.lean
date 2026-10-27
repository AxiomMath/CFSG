module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.LargeExtraspecial.AS35ZSSU3
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Universal.Unitary CFSG.RankThree.Classical2
open scoped MatrixGroups

section SUToSL

open CFSG.Blueprint.Fischer (K)
open CFSG.Fischer.Classification.Unitary (frob)

variable {L : Type} [Field L]

@[expose] noncomputable def suToGL (ι : K →+* L) (H : SL(3, L)) :
    ↥(SUid frob 3) →* GL (Fin 3) L :=
  (MulAut.conj (Matrix.SpecialLinearGroup.toGL H)).toMonoidHom.comp
    ((GeneralLinearGroup.map ι).comp (SUid frob 3).subtype)

theorem suToGL_apply (ι : K →+* L) (H : SL(3, L)) (B : ↥(SUid frob 3)) :
    suToGL ι H B = Matrix.SpecialLinearGroup.toGL H * GeneralLinearGroup.map ι (B : GL (Fin 3) K) *
      (Matrix.SpecialLinearGroup.toGL H)⁻¹ := rfl

theorem det_suToGL (ι : K →+* L) (H : SL(3, L)) (B : ↥(SUid frob 3)) :
    ((suToGL ι H B : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
  rw [suToGL_apply, Units.val_mul, Units.val_mul]
  have h1 := Matrix.det_units_conj (Matrix.SpecialLinearGroup.toGL H)
    ((GeneralLinearGroup.map ι (B : GL (Fin 3) K) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
  rw [h1]
  have h2 : ((GeneralLinearGroup.map ι (B : GL (Fin 3) K) : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) = ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map ι := rfl
  rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ((CFSG.LieType.Universal.Unitary.mem_SUid).1 B.2).1, map_one]

@[expose] noncomputable def suToSL (ι : K →+* L) (H : SL(3, L)) : ↥(SUid frob 3) →* SL(3, L) :=
  MonoidHom.mk' (fun B => ⟨((suToGL ι H B : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L),
    det_suToGL ι H B⟩) fun B C => by
    apply Subtype.ext
    show ((suToGL ι H (B * C) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((suToGL ι H B : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
        ((suToGL ι H C : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
    rw [map_mul, Units.val_mul]

theorem toGL_suToSL (ι : K →+* L) (H : SL(3, L)) (B : ↥(SUid frob 3)) :
    Matrix.SpecialLinearGroup.toGL (suToSL ι H B) = suToGL ι H B :=
  Units.ext rfl

end SUToSL

section Range

open CFSG.Fischer.Classification.Unitary (frob tvU T_eq_closure_tvU tvU_mul_self)

theorem range_le_of_sq {G : Type*} [Group G] (φ : ↥(SUid frob 3) →* G) (N : Subgroup G)
    (h : ∀ x ∈ φ.range, x ^ 2 ∈ N → x ∈ N) : φ.range ≤ N := by
  have hT : CFSG.ClassicalGroups.Unitary.T frob 3 ≤ N.comap φ := by
    rw [T_eq_closure_tvU, Subgroup.closure_le]
    rintro g ⟨v, -, hv, rfl⟩
    refine h _ ⟨_, rfl⟩ ?_
    rw [← map_pow, sq, tvU_mul_self hv, map_one]
    exact N.one_mem
  rintro _ ⟨g, rfl⟩
  refine h _ ⟨g, rfl⟩ ?_
  rw [← map_pow]
  exact hT (CFSG.LargeExtraspecial.AS35ZS.sq_mem_T_three g)

end Range

section Frame


open CFSG.Blueprint.Fischer (K)
open CFSG.Fischer.Classification.Unitary (frob)

theorem unitaryFrame_fix_le_of_two {τ : Tag} {L : Type} [Field L]
    {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hℓf : ℓ ^ f = 2) [CharP L ℓ] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (Ψ : ModGL τ L →* ModGL τ L) (hΨinj : Function.Injective Ψ) (π : Equiv.Perm (Fin 3))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (σ i j) c) = pinnedX τ L (σ (π j) (π i)) ((b : L) * Fr c))
    (N : Subgroup (ModGL τ L))
    (h2 : ∀ x ∈ ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _), x ^ 2 ∈ N → x ∈ N) :
    ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _) ≤ N := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  obtain ⟨⟨H, hH⟩, -, -⟩ := h.fix_unitary hinj hℓ hf hk le_rfl Fr hFr Ψ hΨinj π hΨ
  have hℓ2 : ℓ = 2 :=
    (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓf ▸ dvd_pow_self ℓ (by omega))
  subst hℓ2
  have hf1 : f = 1 :=
    Nat.pow_right_injective le_rfl (hℓf.trans (pow_one 2).symm)
  subst hf1
  obtain ⟨k₂, hk₂, hk₂mem⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_exists_subfield (Ω := L) (ℓ := 2) (f := 1) hf
  haveI : Finite k₂ := Nat.finite_of_card_ne_zero (by rw [hk₂]; norm_num)
  letI : Fintype k₂ := Fintype.ofFinite k₂
  letI : Fintype K := Fintype.ofFinite K
  have hcardeq : Fintype.card K = Fintype.card k₂ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk₂,
      CFSG.Fischer.Classification.Unitary.card_K]
  let e : K ≃+* k₂ := FiniteField.ringEquivOfCardEq hcardeq
  let ι : K →+* L := k₂.subtype.comp e.toRingHom
  have hrange : ∀ c : L, c ∈ Set.range ι ↔ c ^ (2 ^ 1) ^ 2 = c := fun c => by
    rw [← hk₂mem]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hc
      obtain ⟨a, ha⟩ := e.surjective ⟨c, hc⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hI := CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_image_SUid (F := K) (ℓ := 2) (f := 1) ι
    hrange 3
  have hKmem : ∀ B : ↥(SUid frob 3),
      GeneralLinearGroup.map ι (B : GL (Fin 3) K) ∈ unitarySet (2 ^ 1) 3 := fun B => by
    rw [← hI]
    exact ⟨B, B.2, rfl⟩
  have hfix : ∀ B : ↥(SUid frob 3), Ψ (ρ (suToSL ι H B)) = ρ (suToSL ι H B) := fun B =>
    (hH (suToSL ι H B)).2 ⟨_, hKmem B, toGL_suToSL ι H B⟩
  let φ : ↥(SUid frob 3) →* ModGL τ L := ρ.comp (suToSL ι H)
  have hφle : φ.range ≤ ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _) := by
    rintro _ ⟨B, rfl⟩
    exact ⟨⟨suToSL ι H B, rfl⟩, hfix B⟩
  have hφN : φ.range ≤ N :=
    range_le_of_sq φ N (fun x hx => h2 x (hφle hx))
  rintro _ ⟨⟨X, rfl⟩, hX⟩
  obtain ⟨Y, hY, hXY⟩ := (hH X).1 hX
  rw [← hI] at hY
  obtain ⟨B, hB, rfl⟩ := hY
  have hXB : X = suToSL ι H ⟨B, hB⟩ :=
    Matrix.SpecialLinearGroup.toGL_injective (hXY.trans (toGL_suToSL ι H ⟨B, hB⟩).symm)
  exact hφN ⟨⟨B, hB⟩, by simp [φ, hXB]⟩

end Frame

end CFSG.HardMathSupport.Timmesfeld.LangTorus
