module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35ZNMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary

namespace AS35Z

@[expose] noncomputable def quotCenterTransfer {L L' X : Type} [Group L] [Group L'] [Group X]
    (e : L ≃* L') (ψ : L ⧸ center L ≃* X) : L' ⧸ center L' ≃* X :=
  (QuotientGroup.congr (center L) (center L') e (Subgroup.map_center_eq e)).symm.trans ψ

theorem quotCenterTransfer_mk {L L' X : Type} [Group L] [Group L'] [Group X]
    (e : L ≃* L') (ψ : L ⧸ center L ≃* X) (x : L) :
    quotCenterTransfer e ψ (QuotientGroup.mk (e x)) = ψ (QuotientGroup.mk x) := by
  rw [quotCenterTransfer, MulEquiv.trans_apply]
  congr 1
  rw [MulEquiv.symm_apply_eq, QuotientGroup.congr_mk]

end AS35Z

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem zuHyp_of (hS : S.SixHyp) (hst : S.Asc512Standing) (hU : S.Asc512Unitary) {k : ℕ}
    (hk : S.width = k + 2) : S.ZUHyp k where
  two_le := by have := hU.1; omega
  width_eq := hk
  weak := hS.weak
  sixFour := hS.sixFour
  normal := hst.normal
  cls := hst.conj
  psu := by
    have h4 := hU.1
    obtain ⟨e⟩ := hU.2.1
    rw [hk] at e
    exact ⟨e.trans (AS35U.pgEquiv (by omega)).symm⟩

theorem zuLocal_of (hS : S.SixHyp) (hU : S.Asc512Unitary) (hP : S14.Asc512PbarStmt)
    (hSym : S14.Asc512SymStmt) {t : S.O} (ht : t ∈ S.DbarAsc) : ∃ P, S.ZULocal t P := by
  obtain ⟨t₀, ht₀, ht₀M, rfl⟩ := ht
  obtain ⟨g, rfl, -⟩ := ht₀.1
  obtain ⟨hmem, hextra, hcard, hcenter, hnorm, htriv, hfix⟩ := hP G S hS g ht₀ ht₀M
  exact ⟨S.PbarAsc g, hU.2.2 g ht₀, hmem, hextra, hcard, hcenter, hnorm, htriv, hfix,
    fun W hW hWf hWc => hSym G S hS g ht₀ ht₀M W hW hWf hWc⟩

end Setting

namespace S14

theorem asc512UnitaryBranch_of (hSym : Asc512SymStmt) (hP : Asc512PbarStmt)
    (hSU : SUModuleInput) : Asc512UnitaryBranch := by
  intro G _ _ S hS hst hU
  obtain ⟨k, hk⟩ : ∃ k, S.width = k + 2 := ⟨S.width - 2, by have := hU.1; omega⟩
  have h : S.ZUHyp k := S.zuHyp_of hS hst hU hk
  have hloc : ∀ t ∈ S.DbarAsc, ∃ P, S.ZULocal t P := fun t ht =>
    S.zuLocal_of hS hU hP hSym ht
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨ψ⟩ := h.psu
  set L : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := (closure S.DbarAsc).map S.O.subtype with hL
  set D : Set (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.O.subtype '' S.DbarAsc with hD
  have hDL : D ⊆ L := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨d, subset_closure hd, rfl⟩
  set e := (closure S.DbarAsc).equivMapOfInjective S.O.subtype S.O.subtype_injective with he
  have hψ : ∃ ψ' : L ⧸ center L ≃* PG (k + 2), ∀ d (hd : d ∈ D),
      ψ' (QuotientGroup.mk (⟨d, hDL hd⟩ : L)) ∈ DG (k + 2) := by
    refine ⟨AS35Z.quotCenterTransfer e ψ, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have e1 : (⟨S.O.subtype d, hDL ⟨d, hd, rfl⟩⟩ : L) = e (Setting.ZUHyp.mkL hd) :=
      Subtype.ext rfl
    rw [e1, AS35Z.quotCenterTransfer_mk]
    exact h.mem_DG ψ (d := Setting.ZUHyp.mkL hd) hd
  obtain ⟨J, hJ3, hJq, hJL⟩ := hSU S.Qt S.q S.q_nondegenerate (k + 2) (by have := h.two_le; omega)
    (by rw [S.finrank_Qt_eq_two_mul_width, hk]) L D hDL
    (by rw [hL, hD, MonoidHom.map_closure])
    (by
      rintro _ ⟨d, hd, rfl⟩
      exact h.isTypeA hd)
    (by
      rintro _ ⟨x, -, rfl⟩ v
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 v)
    hψ
    (fun W hW => h.irreducible hloc W fun d hd w hw =>
      hW _ ⟨d, subset_closure hd, rfl⟩ w hw)
  have hJD : ∀ a ∈ S.DbarAsc, ∀ v,
      (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v) :=
    fun a ha v => hJL _ ⟨a, subset_closure ha, rfl⟩ v
  exact
    { four_le_width := hU.1
      psu := hU.2.1
      pbar_le := hU.2.2
      fstar_card := hst.fstar_card
      three := fun a ha b hb => h.three ha hb
      disjoint := fun a ha b hb _ hab => h.disjoint_of J hJ3 hJD ha hb hab
      conj := hst.conj
      exists_commute := fun a ha => h.exists_commute ha
      fourStruct := h.fourStruct_of hloc J hJ3 hJq hJD }

end S14

end CFSG.LargeExtraspecial
