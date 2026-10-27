module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup

namespace FixedPrimeLayer

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem pPrimeCore_eq_comap (Y : Subgroup X)
    (hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore p X)).comp Y.subtype)) :
    pPrimeCore p Y = (pPrimeCore p X).comap Y.subtype := by
  apply le_antisymm
  · have hnorm : ((pPrimeCore p Y).map
        ((QuotientGroup.mk' (pPrimeCore p X)).comp Y.subtype)).Normal :=
      (pPrimeCore_normal (p := p) (G := Y)).map _ hY
    have hcop : Nat.Coprime p (Nat.card ((pPrimeCore p Y).map
        ((QuotientGroup.mk' (pPrimeCore p X)).comp Y.subtype))) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _)
        (pPrimeCore_coprime_card (p := p) (G := Y))
    have hbot := pPrimeCore_eq_bot_iff.mp (pPrimeCore_quotient_pPrimeCore_eq_bot (G := X) p) _
      hnorm hcop
    rw [Subgroup.map_eq_bot_iff, ← MonoidHom.comap_ker, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · refine le_sSup ⟨inferInstance, ?_⟩
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ Y.subtype_injective)
      (pPrimeCore_coprime_card (p := p) (G := X))

theorem map_pPrimeCore_eq_inf (Y : Subgroup X)
    (hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore p X)).comp Y.subtype)) :
    (pPrimeCore p Y).map Y.subtype = Y ⊓ pPrimeCore p X := by
  rw [pPrimeCore_eq_comap Y hY, Subgroup.map_comap_eq, Subgroup.range_subtype]

theorem exists_quotient_mulEquiv (Y : Subgroup X)
    (hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore p X)).comp Y.subtype)) :
    ∃ e : Y ⧸ pPrimeCore p Y ≃* X ⧸ pPrimeCore p X,
      ∀ y : Y, e y = ((y : X) : X ⧸ pPrimeCore p X) := by
  have h : pPrimeCore p Y = ((QuotientGroup.mk' (pPrimeCore p X)).comp Y.subtype).ker := by
    rw [pPrimeCore_eq_comap Y hY, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hY), fun y => rfl⟩

end FixedPrimeLayer

open FixedPrimeLayer

theorem fixed_prime_layer_covers_core_quotient {A X : Type*} [Group A] [Group X] [Finite A]
    [Finite X] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (α : A →* MulAut X)
    (hQ : IsQuasisimple (X ⧸ pPrimeCore p X))
    (htriv : ∀ (a : A) (x : X), ((α a x : X) : X ⧸ pPrimeCore p X) = (x : X ⧸ pPrimeCore p X))
    (C : Subgroup X) (hC : ∀ x : X, x ∈ C ↔ ∀ a : A, α a x = x)
    (T : Subgroup X) (hT : T = (pLayer C p).map C.subtype) :
    T ⊔ pPrimeCore p X = ⊤ ∧ (pPrimeCore p T).map T.subtype = T ⊓ pPrimeCore p X ∧
      ∃ e : T ⧸ pPrimeCore p T ≃* X ⧸ pPrimeCore p X,
        ∀ t : T, e t = ((t : X) : X ⧸ pPrimeCore p X) := by
  set N := pPrimeCore p X with hNdef
  have hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := fun a n hn =>
    Subgroup.characteristic_iff_le_comap.mp inferInstance (α a) hn
  have hcop : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (pPrimeCore_coprime_card (p := p) (G := X))
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting p hA α N hN hcop
  have hCsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
    intro q
    have hq : q ∈ {q : X ⧸ N | ∀ a : A,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN a q = q} := by
      intro a
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      exact htriv a x
    rw [hlift] at hq
    obtain ⟨c, hc, hcq⟩ := hq
    exact ⟨⟨c, (hC c).mpr hc⟩, hcq⟩
  obtain ⟨eC, heC⟩ := exists_quotient_mulEquiv C hCsurj
  have hcomp : IsComponent (⊤ : Subgroup (C ⧸ pPrimeCore p C)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (eC.symm.trans Subgroup.topEquiv.symm) hQ,
      Subgroup.IsSubnormal.top⟩
  obtain ⟨L, hL, hLmap⟩ :=
    LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent p hcomp
  have hLT : L ≤ pLayer C p := le_sSup hL
  have hTmap : T.map (QuotientGroup.mk' N) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := eC.surjective q
    obtain ⟨l, hl, hly⟩ : y ∈ L.map (QuotientGroup.mk' (pPrimeCore p C)) :=
      hLmap ▸ Subgroup.mem_top y
    refine ⟨(l : X), ?_, ?_⟩
    · rw [hT]
      exact ⟨l, hLT hl, rfl⟩
    · rw [← hly]
      exact (heC l).symm
  have hTsurj : Function.Surjective ((QuotientGroup.mk' N).comp T.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hTmap
  refine ⟨?_, map_pPrimeCore_eq_inf T hTsurj, exists_quotient_mulEquiv T hTsurj⟩
  have h := Subgroup.comap_map_eq (QuotientGroup.mk' N) T
  rw [hTmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

end CFSG.ComponentClassification.UnbalancedGS
