module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26A02
public import CFSG.ClassicalInvolution.Q3.Q3T8E274A
import CFSG.ClassicalInvolution.Q3.Q3CLWylB

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.StronglyEmbedded.UniqueCoset
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem mem_H274_of_conj_zt_mem_sylow (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) :
    g ∈ T8.H274 Ω K z :=
  Q3CL.Wyl.mem_H274_of_conj_zt_mem_sylow hs.toStd8Core hμ hne hg

theorem fixesUniqueCoset_zt (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : FixesUniqueCoset (z * t) (T8.H274 Ω K z) :=
  Q3CL.Wyl.fixesUniqueCoset_zt hs.toStd8Core hμ hne

theorem h274_eq_top [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K) : T8.H274 Ω K z = ⊤ := by
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := fixesUniqueCoset_z hs hμ hne
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
      exact fixesUniqueCoset_zt hstd
        (muIsoWylD4_transfer hs.stand.modU hs.hW.1 hstd.hW.1 hμ) hne
  obtain ⟨z', hz'cl⟩ := hs.stand.modU.classical K hs.stand.mem
  have hz'z : z' = z := by
    rcases hz.unique z' hz'cl.mem hz'cl.mul_self with h | h
    · exact absurd h hz'cl.ne_one
    · exact h
  have hKm : Q3.IsClassicalMember3 K z := hz'z ▸ hz'cl.toQ3 (by norm_num)
  obtain ⟨x, -, y, -, hxy⟩ := hz'cl.exists_noncomm
  exact Q3T8.false_of_uniqueCoset_of_weakMember3 ⟨x, y, hxy⟩ hH hz2 h1 h2' hKm

end T8YY
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
