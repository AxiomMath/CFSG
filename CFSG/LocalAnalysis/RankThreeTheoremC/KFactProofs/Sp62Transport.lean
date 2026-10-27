module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalAut
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem exists_equiv_H6_of_equiv {Y : Type} [Group Y] [Finite Y]
    (Ψ₀ : Y ≃* H6) (T : Sylow 3 Y) :
    ∃ Ψ : Y ≃* H6, (T : Subgroup Y).map Ψ.toMonoidHom = T0 := by
  have hs : Function.Surjective Ψ₀.toMonoidHom := fun x => Ψ₀.surjective x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H6 (Sylow.mapSurjective hs T) T0S
  refine ⟨Ψ₀.trans (MulAut.conj g), ?_⟩
  have h1 := congrArg (fun P : Sylow 3 H6 => (P : Subgroup H6)) hg
  simp only [Sylow.coe_subgroup_smul, coe_T0S, Sylow.coe_mapSurjective] at h1
  rw [← h1]
  show Subgroup.map (Ψ₀.trans (MulAut.conj g)).toMonoidHom (T : Subgroup Y) =
    Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map Ψ₀.toMonoidHom (T : Subgroup Y))
  rw [Subgroup.map_map]
  rfl

theorem nonempty_catGroup_equiv_H6 (d : TauCeti.ValidLieTypeIndex) (hd : IsSpSixTwoIndex d) :
    Nonempty (CatGroup d ≃* H6) := by
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨i, hv⟩ := d
  simp only at hdq
  subst hdq
  exact CFSG.RankThree.PartTwo.Census.nonempty_typeBGroupEquiv_sp6 q hv hqp hqe

theorem exists_equiv_H6_sylow {Y : Type} [Group Y] [Finite Y]
    (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex) (hd : IsSpSixTwoIndex d) [K.Normal]
    (e : K ≃* CatGroup d) (hC : Subgroup.centralizer (K : Set Y) = ⊥) (T : Sylow 3 Y) :
    ∃ Ψ : Y ≃* H6, (T : Subgroup Y).map Ψ.toMonoidHom = T0 := by
  obtain ⟨e₂⟩ := nonempty_catGroup_equiv_H6 d hd
  have hK : K = ⊤ := top_of_centralizer_eq_bot K (e.trans e₂) hC
  exact exists_equiv_H6_of_equiv (Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr hK.symm).trans (e.trans e₂))) T

section Equiv

variable {X Y : Type} [Group X] [Group Y]

theorem sp62_map_normalizer (f : X ≃* Y) (J : Subgroup X) :
    (Subgroup.normalizer (J : Set X)).map f.toMonoidHom =
      Subgroup.normalizer ((J.map f.toMonoidHom : Subgroup Y) : Set Y) :=
  Subgroup.map_normalizer_eq_of_bijective J f.bijective

theorem sp62_map_centralizer (f : X ≃* Y) (J : Subgroup X) :
    (Subgroup.centralizer (J : Set X)).map f.toMonoidHom =
      Subgroup.centralizer ((J.map f.toMonoidHom : Subgroup Y) : Set Y) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (J : Set X) f.toMonoidHom
  · intro y hy
    obtain ⟨x, rfl⟩ := f.surjective y
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    apply f.injective
    have := Subgroup.mem_centralizer_iff.1 hy (f h) ⟨h, hh, rfl⟩
    simpa using this

end Equiv

theorem sp62_a3pInSitu_of_map {Y Y' : Type} [Group Y] [Group Y'] {p : ℕ}
    (φ : Y →* Y') (hφ : Function.Injective φ) {T B Y₀ : Subgroup Y} {T' B' Y₀' : Subgroup Y'}
    (hT : T.map φ = T') (hB : B.map φ = B') (hY₀ : Y₀.map φ = Y₀')
    (h : A3pInSitu p T' B' Y₀') : A3pInSitu p T B Y₀ := by
  subst hT hB hY₀
  have hnorm : ∀ {W : Subgroup Y}, Y₀ ≤ Subgroup.normalizer (W : Set Y) →
      Y₀.map φ ≤ Subgroup.normalizer ((W.map φ : Subgroup Y') : Set Y') := by
    intro W hW y' hy'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hy'
    exact Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ (hW hy))
  refine ⟨?_, ?_, ?_⟩
  · intro W hW hN hc
    have := h.primeCore (W.map φ) (Subgroup.map_mono hW) (hnorm hN)
      (by rwa [Subgroup.card_map_of_injective hφ])
    exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).1 this
  · intro W hW hN
    rcases h.normal_dichotomy (W.map φ) (Subgroup.map_mono hW) (hnorm hN) with h1 | h1
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h1)
    · exact Or.inr ((Subgroup.map_le_map_iff_of_injective hφ).1 h1)
  · intro y hy
    obtain ⟨hy, hyc⟩ := Subgroup.mem_inf.1 hy
    have h1 : φ y ∈ Y₀.map φ ⊓ Subgroup.centralizer ((B.map φ : Subgroup Y') : Set Y') := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem φ hy, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ hb'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hb'
      rw [← map_mul, ← map_mul]
      exact congrArg φ ((Subgroup.mem_centralizer_iff.1 hyc) b hb)
    exact (Subgroup.mem_map_iff_mem hφ).1 (h.centralizer_le h1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
