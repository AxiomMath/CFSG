module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.AGLEmbedding.MaxD2
open Certificates.MaxD2Heis
open Certificates.MaxD2Perm
open CFSG.ComponentClassification.PSL3Four (TabRep)
open CFSG.PSL3Four.Native (idTab)
open CFSG.RankThree.Native

theorem card_normalizer_of_checkHeis {D : Certificates.MaxD2Perm.Data}
    {S : List (Equiv.Perm (Fin D.n))}
    (hS : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hlen : S.length = D.gT.size)
    (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (h : checkHeis D = true) :
    Nat.card ↥(Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S) =
      D.nOrder := by
  simp only [checkHeis, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  rw [normalizer_inf_eq_H hS hgi hlen hcard hR hN hNorm hMoves hMax, card_N hS hgi hN]

section Certificates

private noncomputable def mclFiveS : List (Equiv.Perm (Fin mclFiveDataP.n)) := [mcl275A, mcl275B]

private noncomputable def mclP_D : Subgroup (Equiv.Perm (Fin mclFiveDataP.n)) := mcl275P

private noncomputable def mclFiveR : Subgroup (Equiv.Perm (Fin mclFiveDataP.n)) :=
  Rsub mclFiveDataP mclFiveS

private theorem mclFiveS_closure_eq : Subgroup.closure {g | g ∈ mclFiveS} = mclP_D := by
  rw [mclP_D]
  exact CFSG.AGLEmbeddingD2.mclP_closure_eq

private theorem mclFiveR_le : mclFiveR ≤ mclP_D := by
  rw [← mclFiveS_closure_eq]
  exact Rsub_le_Gsub

private theorem card_normalizer_mclFiveR :
    Nat.card ↥(Subgroup.normalizer (mclFiveR : Set (Equiv.Perm (Fin mclFiveDataP.n))) ⊓
      mclP_D) = 3000 := by
  have h := card_normalizer_of_checkHeis (D := mclFiveDataP) (S := mclFiveS)
    CFSG.AGLEmbeddingD2.mclFiveDataP_hS rfl
    (by rw [mclFiveS_closure_eq, mclP_D, mcl275P_eq]
        exact CFSG.Sporadic.Schreier.card_mclP)
    CFSG.AGLEmbeddingD2.mcl_five_check_P
  rw [← mclFiveS_closure_eq]
  exact h

private theorem card_mclFiveR : Nat.card mclFiveR = 5 ^ 3 := by
  have hInv : checkInv mclFiveDataP = true := by
    have h := CFSG.AGLEmbeddingD2.mcl_five_check_P
    simp only [checkHeis, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1.1.1.1
  have hR : checkHR mclFiveDataP = true := by
    have h := CFSG.AGLEmbeddingD2.mcl_five_check_P
    simp only [checkHeis, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1.1.1.2
  have hgi := giT_rep (S := mclFiveS) CFSG.AGLEmbeddingD2.mclFiveDataP_hS hInv
  have hcard := card_RH (S := mclFiveS) CFSG.AGLEmbeddingD2.mclFiveDataP_hS hgi hR
  rw [show mclFiveDataP.p = 5 by rfl] at hcard
  norm_num at hcard
  simpa [mclFiveR, mclFiveS] using hcard

private noncomputable def mclFiveSylow : Sylow 5 mclP_D :=
  Sylow.ofCard (mclFiveR.subgroupOf mclP_D) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe mclFiveR_le).toEquiv, card_mclFiveR]
    rw [show Nat.card mclP_D = Nat.card mcl275P from rfl]
    rw [factorization_card_mcl275P_five])

private theorem card_normalizer_mclFiveSylow :
    Nat.card ↥(Subgroup.normalizer ((mclFiveSylow : Subgroup mclP_D) : Set mclP_D)) = 3000 := by
  have hcoe : (mclFiveSylow : Subgroup mclP_D) = mclFiveR.subgroupOf mclP_D :=
    Sylow.coe_ofCard _ _
  rw [hcoe, ← Subgroup.subgroupOf_normalizer_eq mclFiveR_le]
  rw [← Subgroup.card_map_of_injective (f := (mclP_D).subtype) (mclP_D).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  exact card_normalizer_mclFiveR

private theorem card_normalizer_sylow_five_mclP (T : Sylow 5 mclP_D) :
    Nat.card ↥(Subgroup.normalizer ((T : Subgroup mclP_D) : Set mclP_D)) = 3000 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq mclP_D mclFiveSylow T
  have hcoe : (T : Subgroup mclP_D) =
      (mclFiveSylow : Subgroup mclP_D).map (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [← hg]
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hcoe, ← Subgroup.map_equiv_normalizer_eq (mclFiveSylow : Subgroup mclP_D)
    (MulAut.conj g), Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact card_normalizer_mclFiveSylow

private theorem card_normalizer_sylow_five_mclP275 (T : Sylow 5 mcl275P) :
    Nat.card ↥(Subgroup.normalizer ((T : Subgroup mcl275P) : Set mcl275P)) = 3000 :=
  card_normalizer_sylow_five_mclP T

private theorem card_normalizer_sylow_five_mcl_of_iso {L : Type} [Group L] [Finite L]
    (e : L ≃* mcl275P) (S : Sylow 5 L) :
    Nat.card ↥(Subgroup.normalizer ((S : Subgroup L) : Set L)) = 3000 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let hS' : Sylow 5 mcl275P := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hcoe : (hS' : Subgroup mcl275P) = (S : Subgroup L).map e.toMonoidHom := by
    show ((Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S : Sylow 5 mcl275P) :
      Subgroup mcl275P) = (S : Subgroup L).map e.toMonoidHom
    exact Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hmap := Subgroup.map_equiv_normalizer_eq (S : Subgroup L) e
  rw [← hcoe] at hmap
  calc Nat.card ↥(Subgroup.normalizer ((S : Subgroup L) : Set L))
      = Nat.card ↥(Subgroup.map e.toMonoidHom
          (Subgroup.normalizer ((S : Subgroup L) : Set L))) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card ↥(Subgroup.normalizer ((hS' : Subgroup mcl275P) : Set mcl275P)) := by
          rw [hmap]
    _ = 3000 := card_normalizer_sylow_five_mclP275 hS'

theorem isCoatom_normalizer_sylow_five_mcl {L : Type} [Group L] [Finite L]
    (e : L ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) (S : Sylow 5 L) :
    IsCoatom (Subgroup.normalizer ((S : Subgroup L) : Set L)) ∧
      Nat.card (Subgroup.normalizer ((S : Subgroup L) : Set L)) = 3000 := by
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let θ : L ≃* mcl275P := (e.trans eC.symm).trans mcl275Equiv
  have hHeis := CFSG.AGLEmbeddingD2.heisLocal_mclP θ S
  have hcard := card_normalizer_sylow_five_mcl_of_iso θ S
  refine ⟨⟨?_, ?_⟩, hcard⟩
  · intro htop
    have hL : Nat.card L = 898128000 := by
      rw [Nat.card_congr θ.toEquiv, mcl275P_eq]
      exact CFSG.Sporadic.Schreier.card_mclP
    rw [htop, Subgroup.card_top, hL] at hcard
    omega
  · intro Y hY
    rcases hHeis.2.1 Y hY.le with h | h
    · exact absurd h hY.ne'
    · exact h

end Certificates

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
