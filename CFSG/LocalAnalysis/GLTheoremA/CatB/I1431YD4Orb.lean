module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmBasic
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import CFSG.LocalAnalysis.SteinbergBVA7BinaryIsometryTwoParts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

open Matrix CFSG.AGLEmbedding CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon (Q8 Q8_nondegenerate polar_Q8 mem_Om8_iff_omegaGroup)

abbrev VV : Type := Fin 4 ⊕ Fin 4 → ZMod 2

@[expose, instance_reducible] noncomputable def omAction : MulAction ↥Om8 VV :=
  MulAction.compHom VV ((toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2)).toMonoidHom.comp Om8.subtype)

theorem om8_apply_Q (x : ↥Om8) (v : VV) :
    Q8 (((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v) =
      Q8 v := by
  have h := (mem_Om8_iff_omegaGroup (x : CFSG.LocalAnalysis.GLTheoremA.HSubT.SpGL)).mp x.2
  have h2 := (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp h).1
  exact CFSG.ClassicalGroups.Orthogonal.map_of_mem h2 v

theorem ncard_Q8_one : {v : VV | Q8 v = 1}.ncard = 120 := by
  have h := CFSG.LocalAnalysis.SteinbergBV.BinaryTwoParts.two_mul_ncard_quadPlus 3
  have h' : 2 * {v : VV | Q8 v = 1}.ncard + 2 ^ 4 = 4 ^ 4 := by
    simpa [Q8] using h
  norm_num at h'
  omega

theorem card_singular : Nat.card {v : VV // v ≠ 0 ∧ Q8 v = 0} = 135 := by
  classical
  have h1 : ({v : VV | Q8 v = 1}ᶜ).ncard = 136 := by
    rw [Set.ncard_compl, ncard_Q8_one]
    simp [VV, Nat.card_fun, Nat.card_zmod]
  have h2 : {v : VV | v ≠ 0 ∧ Q8 v = 0} = {v : VV | Q8 v = 1}ᶜ \ {0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_compl_iff, Set.mem_singleton_iff]
    have : Q8 v = 0 ∨ Q8 v = 1 := by
      generalize Q8 v = a
      revert a
      decide
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨by rw [h0]; decide, hv⟩
    · rintro ⟨h1, hv⟩
      exact ⟨hv, this.resolve_right h1⟩
  have h0 : (0 : VV) ∈ {v : VV | Q8 v = 1}ᶜ := by
    simp
  have : Nat.card ↥{v : VV | v ≠ 0 ∧ Q8 v = 0} = 135 := by
    rw [Nat.card_coe_set_eq, h2, Set.ncard_diff_singleton_of_mem h0, h1]
  exact this

section Orbit

attribute [local instance] omAction

theorem card_orbit_singular {r : VV} (hr0 : r ≠ 0) (hrQ : Q8 r = 0) :
    Nat.card (MulAction.orbit ↥Om8 r) = 135 := by
  have hset : (MulAction.orbit ↥Om8 r : Set VV) = {v | v ≠ 0 ∧ Q8 v = 0} := by
    ext v
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, rfl⟩
      have hx : x • r =
        ((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ r :=
        rfl
      rw [hx]
      refine ⟨fun h0 => hr0 ?_, by rw [om8_apply_Q, hrQ]⟩
      have := congrArg (fun w => (((x⁻¹ : ↥Om8) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ w) h0
      simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
    · rintro ⟨hv0, hvQ⟩
      obtain ⟨A, hA, hAv⟩ := CFSG.ClassicalGroups.Orthogonal.statedOmegaPlus_exists_mulVec_eq
        (K := ZMod 2) (m := 4) (by norm_num) hr0 hv0 (by
          have h1 : Q8 r = Q8 v := by rw [hrQ, hvQ]
          simpa [Q8] using h1)
      exact ⟨⟨A, hA⟩, hAv⟩
  rw [Nat.card_coe_set_eq, hset, ← Nat.card_coe_set_eq]
  exact card_singular

theorem not_dvd_card_of_fixing (hcard : Nat.card ↥Om8 = 3 ^ 5 * 716800) {r : VV} (hr0 : r ≠ 0)
    (hrQ : Q8 r = 0) {P : Subgroup ↥Om8}
    (hP : ∀ x ∈ P,
      ((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ r =
        r) : ¬ 27 ∣ Nat.card P := by
  have hstab : 135 * Nat.card (MulAction.stabilizer ↥Om8 r) = Nat.card ↥Om8 := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥Om8 r)
    rw [Nat.card_prod] at h
    have h2 := card_orbit_singular hr0 hrQ
    exact (congrArg (fun n => n * Nat.card (MulAction.stabilizer ↥Om8 r)) h2.symm).trans h
  have hPle : P ≤ MulAction.stabilizer ↥Om8 r := fun x hx => hP x hx
  have hdvd : Nat.card P ∣ Nat.card (MulAction.stabilizer ↥Om8 r) :=
    Subgroup.card_dvd_of_le hPle
  intro h27
  have h1 := h27.trans hdvd
  have hsv : Nat.card (MulAction.stabilizer ↥Om8 r) = 1290240 := by omega
  rw [hsv] at h1
  norm_num at h1

end Orbit

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

end
