module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSecG
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport

section Carry

variable {A A' : Type} [Group A] [Group A'] (f : A ≃* A')

theorem hyp42_map {z : A} {X : Subgroup A} (h : Hyp42 z X) :
    Hyp42 (f z) (X.map f.toMonoidHom) := by
  obtain ⟨hall, hqs, hcen, hnot⟩ := h
  have hl : (layer A).map f.toMonoidHom = layer A' := map_layer f
  let g : ↥(layer A) ≃* ↥(layer A') := subEquiv f hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (Subgroup.map f.toMonoidHom) hall
    rwa [map_sup, map_sup, hl, map_zpowers, map_top] at this
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv g hqs
  · rw [← map_center g, ← map_pCore g 2, hcen]
  · intro hle
    apply hnot
    have h1 : ⁅layer A, X⁆.map f.toMonoidHom = ⁅layer A', X.map f.toMonoidHom⁆ := by
      rw [map_commutator, hl]
    have h2 : ((center ↥(layer A)).map (layer A).subtype).map f.toMonoidHom =
        (center ↥(layer A')).map (layer A').subtype := by
      rw [← map_map_subtype f hl, map_center g]
    rw [← h1, ← h2] at hle
    exact (Subgroup.map_le_map_iff_of_injective f.injective).1 hle

theorem concl42_map {k : Kind} {z : A} {p : ℕ} {X : Subgroup A} (h : Concl42 k z p X) :
    Concl42 k (f z) p (X.map f.toMonoidHom) := by
  have hl : (layer A).map f.toMonoidHom = layer A' := map_layer f
  let g : ↥(layer A) ≃* ↥(layer A') := subEquiv f hl
  have hXc : Nat.card ↥(X.map f.toMonoidHom) = Nat.card ↥X :=
    (Nat.card_congr (f.subgroupMap X).toEquiv).symm
  have hLC : (layer A ⊓ centralizer ({z} : Set A)).map f.toMonoidHom =
      layer A' ⊓ centralizer ({f z} : Set A') := by
    rw [map_inf, hl, map_centralizer_singleton]
  have hN : (layer A ⊓ normalizer (X : Set A)).map f.toMonoidHom =
      layer A' ⊓ normalizer ((X.map f.toMonoidHom : Subgroup A') : Set A') := by
    rw [map_inf, hl, map_normalizer]
  have hXC : (X ⊔ layer A ⊓ centralizer ({z} : Set A)).map f.toMonoidHom =
      X.map f.toMonoidHom ⊔ layer A' ⊓ centralizer ({f z} : Set A') := by
    rw [map_sup, hLC]
  have hnorm : layer A ⊓ normalizer (X : Set A) ≤ X ⊔ layer A ⊓ centralizer ({z} : Set A) →
      layer A' ⊓ normalizer ((X.map f.toMonoidHom : Subgroup A') : Set A') ≤
        X.map f.toMonoidHom ⊔ layer A' ⊓ centralizer ({f z} : Set A') := by
    intro hle
    rw [← hN, ← hXC]
    exact Subgroup.map_mono hle
  rcases h with ⟨hSL, hc, hp, hXL, hnm⟩ | ⟨n, hn, hSL, hSyl, hnm⟩ |
      ⟨n, hn, hLie, hzL, hEl, hcard, P, hP, hXP, hPe⟩ | ⟨hk, hPGL, hLie3, hc, hcent, hL2, hCC⟩
  · refine Or.inl ⟨hasSL2Model_of_mulEquiv g hSL, hXc.trans hc, hp, ?_, hnorm hnm⟩
    rw [← hl]
    exact Subgroup.map_mono hXL
  · refine Or.inr (Or.inl ⟨n, hn, hasSL2Model_of_mulEquiv g hSL, ?_, hnorm hnm⟩)
    have := isSylowOf_map f p hSyl
    rwa [hl] at this
  · refine Or.inr (Or.inr (Or.inl ⟨n, hn, lieModel_of_mulEquiv g hLie, ?_,
      isElementaryAbelian_of_mulEquiv (f.subgroupMap X) hEl, hXc.trans hcard,
      P.map f.toMonoidHom, ?_, ?_, ?_⟩))
    · have hzs : f z ∈ (layer A ⊔ centralizer ((layer A : Subgroup A) : Set A)).map f.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hzL
      rwa [map_sup, map_centralizer, hl] at hzs
    · have := isMaxParabolicP_map f p hP
      rwa [hl] at this
    · rw [hXP, map_Op]
    · rw [hPe, hXC]
  · have hLX : (layer A ⊔ X).map f.toMonoidHom = layer A' ⊔ X.map f.toMonoidHom := by
      rw [map_sup, hl]
    refine Or.inr (Or.inr (Or.inr ⟨hk, isPGL3Four_of_mulEquiv (subEquiv f hLX) hPGL,
      lieModel_of_mulEquiv g hLie3, hXc.trans hc, ?_, isL2_of_mulEquiv (subEquiv f hLC) hL2, ?_⟩))
    · have := congrArg (Subgroup.map f.toMonoidHom) hcent
      rwa [map_inf, map_inf, hl, map_centralizer_singleton, map_centralizer] at this
    · have e1 : ((layer A ⊔ X ⊔ zpowers z) ⊓
          centralizer ((layer A ⊓ centralizer ({z} : Set A) : Subgroup A) : Set A)).map f.toMonoidHom =
          (layer A' ⊔ X.map f.toMonoidHom ⊔ zpowers (f z)) ⊓
            centralizer ((layer A' ⊓ centralizer ({f z} : Set A') : Subgroup A') : Set A') := by
        rw [map_inf, map_sup, map_sup, hl, map_zpowers, map_centralizer, hLC]
      have e2 : (X ⊔ zpowers z).map f.toMonoidHom = X.map f.toMonoidHom ⊔ zpowers (f z) := by
        rw [map_sup, map_zpowers]
      rw [← e1, ← e2, hCC]

end Carry

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Transport

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem prop4_2_abs (h42 : Prop4_2) (hctx : Stage2Ctx G z k S) {B : Type} [Group B] [Finite B] {b : B}
    (hB : SecOfG G z B b) {p : ℕ} {X : Subgroup B} (hA : Sig4A b (⊤ : Subgroup B) p X)
    (hop : pCore p B = ⊥) (hH : Hyp42 b X) : Concl42 k b p X := by
  obtain ⟨H₀, H₁, hn, hz, hne, hodd, e, he⟩ := hB
  have hz' : e.symm b = zSec z H₀ hz H₁ := by
    rw [← he]
    exact e.symm_apply_apply _
  have hA' : Sig4A (zSec z H₀ hz H₁) (⊤ : Subgroup (Sec H₀ H₁)) p (X.map e.symm.toMonoidHom) := by
    have := Transport.sig4A_top_map e.symm hA
    rwa [hz'] at this
  have hH' : Hyp42 (zSec z H₀ hz H₁) (X.map e.symm.toMonoidHom) := by
    have := Transport.hyp42_map e.symm hH
    rwa [hz'] at this
  have hc := h42 G z k S hctx H₀ H₁ hz p (X.map e.symm.toMonoidHom)
    ⟨hne, hodd, hA', Transport.pCore_eq_bot_map e.symm p hop⟩ hH'
  have := Transport.concl42_map e hc
  rwa [he, Transport.map_symm_map] at this

end Transport

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
