module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.EvenClassical
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearPerfect
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearPerfectTwo

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSL)

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem exists_perfect_of_equiv {G H : Type} [Group G] [Group H] (θ : G ≃* H) (g : G)
    (hex : ∃ Q : Subgroup H, Q ≤ centralizer ({θ g} : Set H) ∧ ⁅Q, Q⁆ = Q ∧ 3 ∣ Nat.card Q) :
    ∃ V : Subgroup G, V ≤ centralizer ({g} : Set G) ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  obtain ⟨Q, hQc, hQp, hQ3⟩ := hex
  refine ⟨Q.map θ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hQc hq)
    have h2 : θ (θ.symm q * g) = θ (g * θ.symm q) := by
      simpa using this
    exact θ.injective h2
  · rw [← Subgroup.map_commutator, hQp]
  · rwa [Subgroup.card_map_of_injective θ.symm.injective]

noncomputable def statedProjSLEquiv' (n : ℕ) (F : Type) [Field F] :
    StatedProj (StatedSL n F) ≃* projectiveSL n F :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n F).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)

theorem false_of_psl_model (h : E27Config X K R T z) (hz : z ∈ K) {n p f : ℕ}
    (hcl : StatedClassicalModel K .PSL n p f) (hp3 : p ≠ 3)
    (hr : (4 ≤ n ∧ 4 ≤ p ^ f) ∨ (5 ≤ n ∧ p ^ f = 2)) : False := by
  obtain ⟨⟨hp, hf, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  have : CharP F p := charP_of_card_eq_prime_pow hcard
  have h3 : (3 : F) ≠ 0 := by
    have : ((3 : ℕ) : F) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff F p]
      intro hd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)
    exact_mod_cast this
  let θ : ↥K ≃* projectiveSL n F := e.trans (statedProjSLEquiv' n F)
  have hz3 : (θ ⟨z, hz⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hz⟩ : K) ^ 3 = 1 := Subtype.ext (h.elem.2 z h.z_mem)
    rw [this, map_one]
  refine false_of_perfect_in_K h hz (exists_perfect_of_equiv θ ⟨z, hz⟩ ?_)
  rcases hr with ⟨hn, h4⟩ | ⟨hn, h2⟩
  · exact exists_perfect_three_dvd_centralizer_PSL h3 (by rw [hFcard]; exact h4) hn hz3
  · exact exists_perfect_three_dvd_centralizer_PSL_two (by rw [hFcard]; exact h2) hn hz3

end CFSG.HardMathSupport.Malle.E27Lie
