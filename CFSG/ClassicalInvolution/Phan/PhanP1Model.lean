module

public import CFSG.ClassicalInvolution.Phan.PhanD12Model
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.Phan.PhanD11Twin
public import CFSG.ClassicalInvolution.Phan.PhanD3Spin
public import CFSG.ClassicalInvolution.Phan.PhanD5Indep
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.PhanD4
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open CFSG.LieType.Steinberg
open scoped MatrixGroups commutatorElement

section Frames

variable {F : Type} [Field F]

@[expose] noncomputable def stdFrames (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    Fin 4 → Frame (quadPlus 4 F) :=
  ![frame0, frame1 ε hε h4, frame2, (frame2 (F := F)).swap]

end Frames

section Spec

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

structure ModelSpec {F : Type} [Field F] (S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F)))
    (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) : Prop where
  map_range : ∀ k, (S.ι k).range.map (spinAction (quadPlus 4 F)) = (stdFrames ε hε h4 k).La.range
  inj : ∀ k, ∀ r ∈ (S.ι k).range, spinAction (quadPlus 4 F) r = 1 → r = 1

end Spec

section Model

variable {p e : ℕ} [Fact p.Prime]


theorem exists_model_groups (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    ∃ (ε : GaloisField p e) (hε : ε ≠ 0) (h4 : (4 : GaloisField p e) ≠ 0),
      ¬ IsSquare (-ε) ∧
      ∃ R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField p e))),
        (∀ k, R k ∈ longestFundamental (plusDatum 4 (GaloisField p e) (by norm_num))) ∧
        (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
          ∀ a ∈ R i, ∀ b ∈ R j, a * b = b * a) ∧
        (∀ i j : Fin 4, edgeD 4 i j →
          ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R i) (R j)) ∧
        (∀ i j : Fin 4, i ≠ j → R i ⊓ R j = ⊥) ∧
        (∀ k, (R k).map (spinAction (quadPlus 4 (GaloisField p e))) =
          (stdFrames ε hε h4 k).La.range) ∧
        (∀ k, ∀ r ∈ R k, spinAction (quadPlus 4 (GaloisField p e)) r = 1 → r = 1) := by
  classical
  obtain ⟨ε, hε, h4, hεs⟩ := exists_eps (e := e) hp2
  obtain ⟨R0, h0mem, h0img, h0perf, h0inj⟩ := exists_lift_frame hp2 hq frame0
  obtain ⟨R1, h1mem, h1img, h1perf, h1inj⟩ := exists_lift_frame hp2 hq (frame1 ε hε h4)
  obtain ⟨R2, R3, h2mem, h3mem, h2img, h3img, h2perf, h3perf, h2inj, h3inj, h23⟩ :=
    exists_lift_frame_twin hp2 hq (frame2 (F := GaloisField p e))
  let R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField p e))) := ![R0, R1, R2, R3]
  have hRspec : ∀ k, (R k).map (spinAction (quadPlus 4 (GaloisField p e))) =
      (stdFrames ε hε h4 k).La.range ∧
      ⁅R k, R k⁆ = R k ∧
      ∀ r ∈ R k, spinAction (quadPlus 4 (GaloisField p e)) r = 1 → r = 1 := by
    intro k
    fin_cases k
    · exact ⟨h0img, h0perf, h0inj⟩
    · exact ⟨h1img, h1perf, h1inj⟩
    · exact ⟨h2img, h2perf, h2inj⟩
    · exact ⟨h3img, h3perf, h3inj⟩
  obtain ⟨hcomm, hpair⟩ := weakPhan_of_lifts hp2 hq hε h4 hεs R hRspec
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  obtain ⟨hodd, -⟩ := card_galoisField_facts hp2 hq
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hK' : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e he
  have : Algebra (GaloisField p e) (GaloisField p (2 * e)) :=
    Classical.choice (Aniso.nonempty_algebra hK hK')
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have hθ01 := exists_hom_01 (p := p) (e := e) (K' := GaloisField p (2 * e)) hε h4 h2 hεs hK hK'
    hodd
  have hθ12 := exists_hom_12 (p := p) (e := e) (K' := GaloisField p (2 * e)) hε h4 h2 hεs hK hK'
    hodd
  have hθ13 := exists_hom_13 (p := p) (e := e) (K' := GaloisField p (2 * e)) hε h4 h2 hεs hK hK'
    hodd
  have hmapinf : ∀ A B : Subgroup (spinGroup (quadPlus 4 (GaloisField p e))),
      (∀ r ∈ A, spinAction (quadPlus 4 (GaloisField p e)) r = 1 → r = 1) →
      A.map (spinAction (quadPlus 4 (GaloisField p e))) ⊓
        B.map (spinAction (quadPlus 4 (GaloisField p e))) = ⊥ → A ⊓ B = ⊥ := by
    intro A B hA h
    rw [eq_bot_iff]
    rintro g ⟨hgA, hgB⟩
    have : spinAction (quadPlus 4 (GaloisField p e)) g ∈
        A.map (spinAction (quadPlus 4 (GaloisField p e))) ⊓
          B.map (spinAction (quadPlus 4 (GaloisField p e))) :=
      ⟨⟨g, hgA, rfl⟩, ⟨g, hgB, rfl⟩⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (hA g hgA this)
  have d01 : R 0 ⊓ R 1 = ⊥ := by
    obtain ⟨θ, hinj, -, hU, hV⟩ := hθ01
    refine hmapinf _ _ h0inj ?_
    show R0.map _ ⊓ R1.map _ = ⊥
    rw [h0img, h1img, ← hU, ← hV, ← Subgroup.map_inf _ _ θ hinj, B12_inf_B23, Subgroup.map_bot]
  have d12 : R 1 ⊓ R 2 = ⊥ := by
    obtain ⟨θ, hinj, -, hU, hV⟩ := hθ12
    refine hmapinf _ _ h1inj ?_
    show R1.map _ ⊓ R2.map _ = ⊥
    rw [h1img, h2img, ← hU, ← hV, ← Subgroup.map_inf _ _ θ hinj, B12_inf_B23, Subgroup.map_bot]
  have d13 : R 1 ⊓ R 3 = ⊥ := by
    obtain ⟨θ, hinj, -, hU, hV⟩ := hθ13
    refine hmapinf _ _ h1inj ?_
    show R1.map _ ⊓ R3.map _ = ⊥
    rw [h1img, h3img, ← hU, ← hV, ← Subgroup.map_inf _ _ θ hinj, B12_inf_B23, Subgroup.map_bot]
  have d02 : R 0 ⊓ R 2 = ⊥ := by
    refine hmapinf _ _ h0inj ?_
    show R0.map _ ⊓ R2.map _ = ⊥
    rw [h0img, h2img]
    exact La_range_inf_of_orth polar_incl_frame0_frame2
  have d03 : R 0 ⊓ R 3 = ⊥ := by
    refine hmapinf _ _ h0inj ?_
    show R0.map _ ⊓ R3.map _ = ⊥
    rw [h0img, h3img]
    exact La_range_inf_of_orth (fun X Y => by rw [Frame.incl_swap, polar_incl_frame0_frame2])
  refine ⟨ε, hε, h4, hεs, R, ?_, hcomm, hpair, ?_, fun k => (hRspec k).1, fun k => (hRspec k).2.2⟩
  · intro k
    fin_cases k
    · exact h0mem
    · exact h1mem
    · exact h2mem
    · exact h3mem
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | assumption | (rwa [inf_comm])

theorem exists_model_family (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    ∃ (ε : GaloisField p e) (hε : ε ≠ 0) (h4 : (4 : GaloisField p e) ≠ 0),
      ¬ IsSquare (-ε) ∧
      ∃ S : PhanFamilyD4 (GaloisField p (2 * e)) p e (spinGroup (quadPlus 4 (GaloisField p e))),
        GoodFamily S ∧ (S.ι 0).range ∈ Generic.fundamentalSubgroups .POmegaPlus
          (plusDatum 4 (GaloisField p e) (by norm_num)) ∧ ModelSpec S ε hε h4 := by
  obtain ⟨ε, hε, h4, hεs, R, hmem, hcomm, hpair, hdisj, himg, hinj⟩ := exists_model_groups hp2 hq
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  have hK' : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e he
  obtain ⟨S, hSr, hSi, hSk⟩ := exists_family hK' R (fun i j h1 h2 h3 => hcomm i j h1 h2 h3) hpair
  refine ⟨ε, hε, h4, hεs, S, ⟨hSi, fun i j hij => ?_, hSk⟩, ?_, ⟨fun k => ?_, fun k => ?_⟩⟩
  · rw [hSr i, hSr j]
    exact hdisj i j hij
  · rw [hSr 0]
    exact longestFundamental_subset .POmegaPlus _ (hmem 0)
  · rw [hSr k]
    exact himg k
  · rw [hSr k]
    exact hinj k

end Model

end CFSG.ClassicalInvolution.PhanP
