module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SignalizerProductComponents
import CFSG.FeitThompson.Local.CanonicalSignalizerConjugation
import CFSG.FeitThompson.Local.SigmaCoreConjugation

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open _root_.CFSG.FeitThompson
  _root_.CFSG.FeitThompson.Prep08

variable {G : Type*} [Group G] {M : Subgroup G}

theorem conjSet_conjSet (Y : Set G) (g h : G) :
    conjSet (conjSet Y g) h = conjSet Y (g * h) := by
  ext y
  simp only [mem_conjSet_iff]
  rw [show g * h * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ from by group]

theorem conjSet_sdiff_one (Y : Set G) (g : G) :
    conjSet (Y \ {1}) g = conjSet Y g \ {1} := by
  ext y
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, mem_conjSet_iff]
  refine ⟨fun h => ⟨h.1, fun hy => h.2 (by rw [hy]; group)⟩, fun h => ⟨h.1, fun hy => h.2 ?_⟩⟩
  have hyy : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [hyy, hy]; group

theorem one_mem_conjSet_iff {Y : Set G} {g : G} : (1 : G) ∈ conjSet Y g ↔ (1 : G) ∈ Y := by simp

theorem conjSet_iUnion {ι : Sort*} (F : ι → Set G) (g : G) :
    conjSet (⋃ i, F i) g = ⋃ i, conjSet (F i) g := by
  simp only [conjSet, Set.image_iUnion]

theorem conjSet_biUnion {ι : Type*} (S : Set ι) (F : ι → Set G) (g : G) :
    conjSet (⋃ i ∈ S, F i) g = ⋃ i ∈ S, conjSet (F i) g := by
  simp only [conjSet, Set.image_iUnion]

theorem coe_sigmaCore_conjSubgroup [Finite G] (M : Subgroup G) (g : G) :
    (sigmaCore (conjSubgroup M g) : Set G) = conjSet (sigmaCore M : Set G) g := by
  rw [conjSubgroup, sigmaCore_conj_smul, ← coe_conjSubgroup, conjSubgroup]

theorem conjSet_smul_coe_sigmaCoreSignalizer [Finite G] (x g : G) :
    conjSet (x • (sigmaCoreSignalizer G x : Set G)) g
      = (g⁻¹ * x * g) • (sigmaCoreSignalizer G (g⁻¹ * x * g) : Set G) :=
  conj_image_smul_coe_canonicalSignalizer_sigmaCore x g

theorem sigmaPacket_conjSubgroup [Finite G] (M : Subgroup G) (g : G) :
    sigmaPacket G (conjSubgroup M g) = conjSet (sigmaPacket G M) g := by
  rw [sigmaPacket, sigmaPacket, coe_sigmaCore_conjSubgroup, ← conjSet_sdiff_one,
    conjSet_biUnion, conjSet, Set.biUnion_image]
  exact Set.iUnion₂_congr fun x _ => (conjSet_smul_coe_sigmaCoreSignalizer x g).symm

theorem sigmaPacketSupport_eq_biUnion [Finite G] (M : Subgroup G) :
    sigmaPacketSupport G M
      = ⋃ x ∈ ⋃ g : G, conjSet ((sigmaCore M : Set G) \ {1}) g,
          x • (sigmaCoreSignalizer G x : Set G) := by
  rw [Set.biUnion_iUnion, sigmaPacketSupport]
  refine Set.iUnion_congr fun g => ?_
  rw [sigmaPacket, conjSet_biUnion, conjSet, Set.biUnion_image]
  exact Set.iUnion₂_congr fun x _ => conjSet_smul_coe_sigmaCoreSignalizer x g

theorem sigmaPacketSupport_conjSubgroup [Finite G] (M : Subgroup G) (g : G) :
    sigmaPacketSupport G (conjSubgroup M g) = sigmaPacketSupport G M := by
  simp only [sigmaPacketSupport, sigmaPacket_conjSubgroup, conjSet_conjSet]
  exact (mul_left_surjective g).iUnion_comp fun h => conjSet (sigmaPacket G M) h

theorem conjSet_sigmaPacketSupport [Finite G] (M : Subgroup G) (g : G) :
    conjSet (sigmaPacketSupport G M) g = sigmaPacketSupport G M := by
  simp only [sigmaPacketSupport, conjSet_iUnion, conjSet_conjSet]
  exact (mul_right_surjective g).iUnion_comp fun h => conjSet (sigmaPacket G M) h

theorem sigmaCoreSignalizer_eq_sigmaSignalizer [Finite G] (x : G) :
    sigmaCoreSignalizer G x = sigmaSignalizer x := (rfl)

theorem one_notMem_sigmaPacket [Finite G]
    (hone : ∀ x ∈ sigmaSupport G, (1 : G) ∉ x • (sigmaSignalizer x : Set G)) (hM : IsCoatom M) :
    (1 : G) ∉ sigmaPacket G M := by
  rw [sigmaPacket]
  rintro h
  obtain ⟨x, hx, h1⟩ := Set.mem_iUnion₂.1 h
  refine hone x (mem_sigmaSupport.2 ⟨M, hM, hx.1, hx.2⟩) ?_
  rwa [← sigmaCoreSignalizer_eq_sigmaSignalizer]

theorem one_notMem_sigmaPacketSupport [Finite G]
    (hone : ∀ x ∈ sigmaSupport G, (1 : G) ∉ x • (sigmaSignalizer x : Set G)) (hM : IsCoatom M) :
    (1 : G) ∉ sigmaPacketSupport G M := by
  rw [sigmaPacketSupport]
  rintro h
  obtain ⟨g, hg⟩ := Set.mem_iUnion.1 h
  exact one_notMem_sigmaPacket hone hM (one_mem_conjSet_iff.1 hg)

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep08

universe u

theorem FTS_packet_conjugation_description
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_packet_conjugation_description.{u} := by
  intro G _ _ hG M hM XM hXM
  have hone := FTS_signalizer_product_components h₁ h₂ G
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  refine ⟨?_, fun g => sigmaPacket_conjSubgroup M g,
    fun g => sigmaPacketSupport_conjSubgroup M g,
    fun g => conjSet_sigmaPacketSupport M g,
    one_notMem_sigmaPacketSupport (fun x hx => (hone x hx).2) hM⟩
  rw [hXM]
  exact sigmaPacketSupport_eq_biUnion M

end

end CFSG.FeitThompson.Proofs
