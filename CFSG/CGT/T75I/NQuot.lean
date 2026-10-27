module

public import CFSG.CGT.T75I.NSix
public import CFSG.CGT.T75I.NSeven
public import CFSG.CGT.T75I.Sigma

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem normalizer_le_hSub [Finite G] (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ 2 2)
    (hC : Subgroup.centralizer (T : Set G) = T)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))) :
    Subgroup.normalizer (T : Set G) ≤ hSub T (normIn T₁ T) := by
  obtain ⟨e⟩ := exists_coords hc
  rcases hhat with h | h
  · obtain ⟨hiso⟩ := hGamma_iso_of hC e 6 (Or.inl rfl) h
    rcases normalizer_cases_of_six hc hC e ⟨hiso⟩ with hle | ⟨x, hxN, hx2, hxH, hcos⟩
    · exact hle
    · exact (false_of_involution_outside h1 h63 hc hC (Or.inl h) hxN hx2 hxH hcos).elim
  · obtain ⟨hiso⟩ := hGamma_iso_of hC e 7 (Or.inr rfl) h
    exact normalizer_le_of_seven hC e ⟨hiso⟩

theorem nquot_equiv_hGamma (hC : Subgroup.centralizer (T : Set G) = T)
    (hN : Subgroup.normalizer (T : Set G) ≤ hSub T (normIn T₁ T))
    (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)) :
    Nonempty (NQuot T ≃* ↥(hGamma T₁ e)) := by
  have hker : (actGL e).ker = T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact actGL_eq_one_iff hC e n
  have hrange : (actGL e).range = hGamma T₁ e := by
    ext g
    rw [mem_hGamma]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : G), hN n.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hSub_le_normalizer' hh⟩, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange (actGL e))).trans (MulEquiv.subgroupCongr hrange)⟩

theorem nquot_equiv [Finite G] (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ 2 2)
    (hC : Subgroup.centralizer (T : Set G) = T)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))) :
    (IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) →
      Nonempty (NQuot T ≃* alternatingGroup (Fin 6))) ∧
    (IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) →
      Nonempty (NQuot T ≃* alternatingGroup (Fin 7))) := by
  obtain ⟨e⟩ := exists_coords hc
  have hN := normalizer_le_hSub h1 h63 hc hC hhat
  obtain ⟨eN⟩ := nquot_equiv_hGamma (T₁ := T₁) hC hN e
  constructor
  · intro h
    obtain ⟨hiso⟩ := hGamma_iso_of hC e 6 (Or.inl rfl) h
    exact ⟨eN.trans hiso⟩
  · intro h
    obtain ⟨hiso⟩ := hGamma_iso_of hC e 7 (Or.inr rfl) h
    exact ⟨eN.trans hiso⟩

end CFSG.CGT.T75I
