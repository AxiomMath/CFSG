module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

theorem lieModel_psp4_of_isPSp4 {K : Type} [Group K] {p f q : ℕ} (hp : p.Prime) (hpf : p ^ f = q)
    (hq : 3 < q) (h : IVK.IsPSp4 K q) : LieModel K .PSp 2 p f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hpf
      omega
    · exact h
  obtain ⟨F, hF1, hF2, hcard, he⟩ := h
  left
  refine ⟨by decide, ⟨hp, hf, le_refl 2, ?_⟩, F, hF1, hF2, by rw [hcard, hpf], he⟩
  intro hh
  have : p ^ f = 2 := (Prod.mk.inj hh).2
  omega

section Amb

variable {G : Type} [Group G]

theorem generalizedFitting_equiv_quot (M : Subgroup G) (hO : pPrimeCore 2 ↥M = ⊥) :
    Nonempty (↥(generalizedFitting ↥M) ≃* ↥(generalizedFitting (HBar M))) := by
  have hker : (QuotientGroup.mk' (pPrimeCore 2 ↥M)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hO]
  let e : ↥M ≃* HBar M := MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 ↥M))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, QuotientGroup.mk'_surjective _⟩
  exact ⟨(e.subgroupMap _).trans
    (MulEquiv.subgroupCongr (CFSG.QuasithinUnique.Setup.Layer.Actor.generalizedFitting_map e))⟩

theorem isCoatom_subgroupOf_of_barIn (M C : Subgroup G) (hO : pPrimeCore 2 ↥M = ⊥)
    (h : IsCoatom (barIn M C)) : IsCoatom (C.subgroupOf M) := by
  have hker : (QuotientGroup.mk' (pPrimeCore 2 ↥M)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hO]
  let e : ↥M ≃* HBar M := MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 ↥M))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, QuotientGroup.mk'_surjective _⟩
  have hb : barIn M C = (MulEquiv.mapSubgroup e) (C.subgroupOf M) := rfl
  rw [hb] at h
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) _).1 h

end Amb

theorem stage2_sixA (h34 : Leaf_Prop34) (h20 : OddCoreOverC) (hev : EvenOverC) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
      ∀ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), k = Kind.l4 ε →
        Stage1L4 G z S ε q L₁ L₂ → ∀ p f : ℕ, p.Prime → p ^ f = q →
          ∀ M : Subgroup G, IsCoatom M → Cen z < M →
            IsCoatom ((Cen z).subgroupOf M) ∧ LieModel ↥(generalizedFitting ↥M) .PSp 2 p f := by
  intro G _ _ z k S hctx ε q L₁ L₂ hk hL4 p f hp hpf M hMc hlt
  have hMmem : M ∈ maximalOverCentralizer z := ⟨hMc, hlt.le⟩
  have heven := hev G z k S hctx ⟨ε, hk⟩ M hMmem hlt
  have h : Ctx17 G z k S M := ⟨hctx, hMmem, heven⟩
  rcases h.cases h34 with hMC | ⟨ε', q', L₁', L₂', hk', hL4', hq3, hF, hcoat⟩
  · exact absurd hMC hlt.ne'
  · have hO : pPrimeCore 2 ↥M = ⊥ := by
      by_contra hne
      exact hlt.ne' (h20 G z k S hctx M hMmem heven (fun hb => hne ((pPrimeCoreOf_eq_bot_iff M).mp hb)))
    refine ⟨isCoatom_subgroupOf_of_barIn M (Cen z) hO hcoat, ?_⟩
    obtain rfl : ε = ε' := Kind.l4.inj (hk.symm.trans hk')
    obtain rfl : q = q' := stage1L4_q_eq hL4 hL4'
    obtain ⟨e⟩ := generalizedFitting_equiv_quot M hO
    refine lieModel_psp4_of_isPSp4 hp hpf hq3 ?_
    obtain ⟨F, hF1, hF2, hcard, ⟨e'⟩⟩ := hF
    exact ⟨F, hF1, hF2, hcard, ⟨e.trans e'⟩⟩

end CFSG.GH74.GLS.Stage2.Final.Thm4
