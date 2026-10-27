module

public import CFSG.GH74.GLS.Classes
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS

private abbrev SDWK3 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private def sdwK3_aux_w : SDWK3 := ⟨!![1, 1; 0, 1], by decide⟩

private def sdwK3_aux_k : SDWK3 := ⟨!![0, 1; -1, 0], by decide⟩

private theorem sdwK3_aux_mul : ∀ a b : SDWK3, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by decide

private theorem sdwK3_aux_w_cube : sdwK3_aux_w ^ 3 = 1 := by decide

private theorem sdwK3_aux_w_fourth : sdwK3_aux_w ^ 4 ≠ 1 := by decide

private theorem sdwK3_aux_conj :
    sdwK3_aux_k ^ 4 = 1 ∧ sdwK3_aux_w * sdwK3_aux_k * sdwK3_aux_w⁻¹ ≠ sdwK3_aux_k := by decide

private theorem sdwK3_aux_cover : ∀ g : SDWK3,
    g ^ 4 = 1 ∨ (g * sdwK3_aux_w⁻¹) ^ 4 = 1 ∨ (g * (sdwK3_aux_w ^ 2)⁻¹) ^ 4 = 1 := by decide

private theorem sdwK3_aux_core {H : Type} [Group H] (φ : H ≃* SDWK3) :
    (∀ a b : H, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1) ∧
      ∃ w : H, w ^ 3 = 1 ∧ w ^ 4 ≠ 1 ∧ (∃ k : H, k ^ 4 = 1 ∧ w * k * w⁻¹ ≠ k) ∧
        ∀ g : H, g ^ 4 = 1 ∨ (g * w⁻¹) ^ 4 = 1 ∨ (g * (w ^ 2)⁻¹) ^ 4 = 1 := by
  have key : ∀ (h : H) (n : ℕ), h ^ n = 1 ↔ φ h ^ n = 1 := fun h n => by
    rw [← map_pow]
    exact (map_eq_one_iff φ φ.injective).symm
  refine ⟨fun a b ha hb => ?_, φ.symm sdwK3_aux_w, ?_, ?_, ?_, ?_⟩
  · rw [key, map_mul]
    exact sdwK3_aux_mul _ _ ((key a 4).1 ha) ((key b 4).1 hb)
  · rw [key, φ.apply_symm_apply]
    exact sdwK3_aux_w_cube
  · intro h
    have h' := (key _ 4).1 h
    rw [φ.apply_symm_apply] at h'
    exact sdwK3_aux_w_fourth h'
  · refine ⟨φ.symm sdwK3_aux_k, ?_, fun h => sdwK3_aux_conj.2 ?_⟩
    · rw [key, φ.apply_symm_apply]
      exact sdwK3_aux_conj.1
    · simpa using congrArg φ h
  · intro g
    rcases sdwK3_aux_cover (φ g) with h | h | h
    · exact Or.inl ((key g 4).2 h)
    · refine Or.inr (Or.inl ((key _ 4).2 ?_))
      simpa using h
    · refine Or.inr (Or.inr ((key _ 4).2 ?_))
      simpa using h

private def sdwK3_aux_slEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)

private theorem sdwK3_aux_equiv {K : Type} [Group K] (hK : HasSL2Model K (fun q => q = 3)) :
    Nonempty (K ≃* SDWK3) := by
  obtain ⟨F, iF, iFin, hF, ⟨e₀⟩⟩ := hK
  let e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  exact ⟨e.trans (sdwK3_aux_slEquiv (ZMod.ringEquivOfPrime F Nat.prime_three hFc).symm)⟩

theorem sdwK_three_structure {X : Type} [Group X] {K : Subgroup X}
    (hK : HasSL2Model ↥K (fun q => q = 3)) :
    ∃ (Q : Subgroup X) (w : X), Q ≤ K ∧ w ∈ K ∧ IsPGroup 2 Q ∧ w ^ 3 = 1 ∧ w ∉ Q ∧
      (∃ k ∈ Q, w * k * w⁻¹ ≠ k) ∧
      ∀ g ∈ K, g ∈ Q ∨ (∃ q ∈ Q, g = q * w) ∨ (∃ q ∈ Q, g = q * w ^ 2) := by
  obtain ⟨φ⟩ := sdwK3_aux_equiv hK
  obtain ⟨hmul, w, hw3, hw4, ⟨k, hk4, hkw⟩, hcov⟩ := sdwK3_aux_core φ
  have hcoe : ∀ (a : ↥K) (n : ℕ), a ^ n = 1 ↔ (a : X) ^ n = 1 := fun a n => by
    rw [← Subgroup.coe_pow, OneMemClass.coe_eq_one]
  let Q : Subgroup X :=
    { carrier := {x | x ∈ K ∧ x ^ 4 = 1}
      mul_mem' := fun {a b} ha hb =>
        ⟨K.mul_mem ha.1 hb.1, by
          have := hmul ⟨a, ha.1⟩ ⟨b, hb.1⟩ ((hcoe _ 4).2 ha.2) ((hcoe _ 4).2 hb.2)
          exact (hcoe _ 4).1 this⟩
      one_mem' := ⟨K.one_mem, one_pow 4⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hQ : ∀ x : X, x ∈ Q ↔ x ∈ K ∧ x ^ 4 = 1 := fun x => Iff.rfl
  refine ⟨Q, (w : X), fun x hx => ((hQ x).1 hx).1, w.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    refine ⟨2, ?_⟩
    have h4 : (g : X) ^ 4 = 1 := ((hQ g).1 g.2).2
    apply Subtype.ext
    simpa using h4
  · exact (hcoe w 3).1 hw3
  · intro h
    exact hw4 ((hcoe w 4).2 ((hQ _).1 h).2)
  · refine ⟨(k : X), (hQ _).2 ⟨k.2, (hcoe k 4).1 hk4⟩, fun h => hkw ?_⟩
    apply Subtype.ext
    simpa using h
  · intro g hg
    rcases hcov ⟨g, hg⟩ with h | h | h
    · exact Or.inl ((hQ g).2 ⟨hg, (hcoe _ 4).1 h⟩)
    · refine Or.inr (Or.inl ⟨g * (w : X)⁻¹, (hQ _).2 ⟨?_, ?_⟩, ?_⟩)
      · exact K.mul_mem hg (K.inv_mem w.2)
      · simpa using (hcoe _ 4).1 h
      · simp
    · refine Or.inr (Or.inr ⟨g * ((w : X) ^ 2)⁻¹, (hQ _).2 ⟨?_, ?_⟩, ?_⟩)
      · exact K.mul_mem hg (K.inv_mem (K.pow_mem w.2 2))
      · simpa using (hcoe _ 4).1 h
      · simp

end CFSG.GH74.GLS.Stage4.Rest
