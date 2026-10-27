module

public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.GH74.E2.ComponentsBasic

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {K K' : Type} [Group K] [Group K']

theorem ofLieType_of_mulEquiv (e : K ≃* K') (h : OfLieType K) : OfLieType K' := by
  obtain ⟨t, n, p, f, hmod⟩ := h
  exact ⟨t, n, p, f, CFSG.GH74.lieModel_of_mulEquiv
    (QuotientGroup.congr (center K) (center K') e (Subgroup.map_center_eq e)) hmod⟩

theorem isL3Odd_of_mulEquiv (e : K ≃* K') (h : IsL3Odd K) : IsL3Odd K' := by
  obtain ⟨p, f, hp, hp2, h⟩ := h
  exact ⟨p, f, hp, hp2, h.imp (CFSG.GH74.lieModel_of_mulEquiv e)
    (CFSG.GH74.lieModel_of_mulEquiv e)⟩

theorem isL3OddGt3_of_mulEquiv (e : K ≃* K') (h : IsL3OddGt3 K) : IsL3OddGt3 K' := by
  obtain ⟨p, f, hp, hp2, hq, h⟩ := h
  exact ⟨p, f, hp, hp2, hq, h.imp (CFSG.GH74.lieModel_of_mulEquiv e)
    (CFSG.GH74.lieModel_of_mulEquiv e)⟩

theorem inCalK2_of_mulEquiv (e : K ≃* K') (h : InCalK2 K) : InCalK2 K' := by
  obtain ⟨hq, hc, hk⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_,
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv hk e.symm⟩
  have h1 : (center K).map e.toMonoidHom = center K' := Subgroup.map_center_eq e
  have h2 : (CFSG.pCore 2 K).map e.toMonoidHom = CFSG.pCore 2 K' := CFSG.pCore_map_iso 2 e
  rw [← h1, ← h2, hc]

theorem inG2_of_mulEquiv (e : K ≃* K') (h : InG2 K) : InG2 K' :=
  ⟨inCalK2_of_mulEquiv e h.1,
    fun hc => h.2.1 (CFSG.GH74.E2.inC2_of_mulEquiv e.symm hc),
    fun ht => h.2.2 (CFSG.GH74.GLS.TwoThin.inT2_of_mulEquiv e.symm ht)⟩

theorem inG2Depth_of_mulEquiv {i : ℕ} (e : K ≃* K') (h : InG2Depth i K) : InG2Depth i K' := by
  obtain ⟨hG, h⟩ := h
  refine ⟨inG2_of_mulEquiv e hG, ?_⟩
  have hn : ¬ OfLieType K → ¬ OfLieType K' := fun hn h' => hn (ofLieType_of_mulEquiv e.symm h')
  have hS : ∀ {s : TauCeti.SporadicName}, NativeSporadic.IsSporadic K s →
      NativeSporadic.IsSporadic K' s := fun h => CFSG.GH74.isSporadic_of_mulEquiv e h
  have hA : ∀ {n : ℕ}, Nonempty (K ≃* alternatingGroup (Fin n)) →
      Nonempty (K' ≃* alternatingGroup (Fin n)) :=
    fun h => CFSG.GH74.nonempty_alternating_of_mulEquiv e h
  rcases h with ⟨hi, hl, n, hn12, h⟩ | ⟨hi, hl, h⟩ | ⟨hi, hl, h⟩ | ⟨hi, hl, h⟩ | ⟨hi, hl, h⟩ |
    ⟨hi, hl, hl3⟩ | ⟨hi, h⟩ | ⟨hi, hl, h⟩
  · exact Or.inl ⟨hi, hn hl, n, hn12, CFSG.GH74.GLS.TwoThin.isDoubleCoverOfAlt_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨hi, hn hl, h.imp hS (Or.imp hS hS)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hi, hn hl,
      h.imp (fun ⟨n, hn12, h⟩ => ⟨n, hn12, hA h⟩) hS⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, hn hl, h.imp hS (Or.imp hS hS)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, hn hl, hA h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, ofLieType_of_mulEquiv e hl,
      fun h' => hl3 (isL3Odd_of_mulEquiv e.symm h')⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hi, isL3OddGt3_of_mulEquiv e h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hi, hn hl, h.imp hA hA⟩))))))

theorem d2_congr (e : K ≃* K') : d2 K = d2 K' := by
  unfold d2
  congr 1
  ext i
  exact ⟨inG2Depth_of_mulEquiv e, inG2Depth_of_mulEquiv e.symm⟩

theorem hasFValue_of_mulEquiv (e : K ≃* K') {v : ℕ} (h : HasFValue K v) : HasFValue K' v := by
  obtain ⟨t, n, p, f₀, hmod, hv⟩ := h
  exact ⟨t, n, p, f₀, CFSG.GH74.lieModel_of_mulEquiv
    (QuotientGroup.congr (center K) (center K') e (Subgroup.map_center_eq e)) hmod, hv⟩

theorem fRank_congr (e : K ≃* K') : FRank K = FRank K' := by
  unfold FRank
  congr 1
  ext v
  exact ⟨hasFValue_of_mulEquiv e, hasFValue_of_mulEquiv e.symm⟩

end CFSG.GH74.Generic
