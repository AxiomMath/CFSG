module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLCheck
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public import CFSG.Sporadic.SmallOddCore.McLLocal

public noncomputable section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

abbrev mclX : Subgroup (Equiv.Perm (Fin 35)) := genGroup 35 mclXGens mclXPerm

theorem eq_of_tabRep {n : ℕ} {t : Tab} {g h : Equiv.Perm (Fin n)} (hg : TabRep t g)
    (hh : TabRep t h) : g = h := by
  ext i
  rw [← hg.apply i, hh.apply i]

theorem mclX_order_six : ∃ z ∈ mclX, orderOf z = 6 := by
  set z := (mclSixWord.map mclXPerm).prod with hz
  have hlt : ∀ j ∈ mclSixWord, j < mclXGens.size := by
    intro j hj
    have : mclXGens.size = 2 := by simp [mclXGens]
    rw [this]
    simp only [mclSixWord, List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  have hw : ∀ k, TabRep (wordTabS 35 mclXGens (List.replicate k mclSixWord).flatten) (z ^ k) := by
    intro k
    have h := tabRep_wordTabS tabRep_mclXGens (List.replicate k mclSixWord).flatten (by
      intro j hj
      obtain ⟨l, hl, hjl⟩ := List.mem_flatten.1 hj
      rw [List.eq_of_mem_replicate hl] at hjl
      exact hlt j hjl)
    simpa [List.map_flatten, List.prod_flatten, List.map_replicate, List.prod_replicate,
      hz] using h
  refine ⟨z, ?_, ?_⟩
  · refine Subgroup.list_prod_mem (K := mclX) fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact subset_closure ⟨j, hlt j hj, rfl⟩
  · obtain ⟨h6, hk⟩ := mclX_order_six_check
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨?_, fun m hm hm0 hzm => ?_⟩
    · have h := hw 6
      rw [h6] at h
      exact eq_of_tabRep h TabRep.idTab
    · have h := hw m
      rw [hzm] at h
      have htab := TabRep.tab_eq h TabRep.idTab
      have hm' : m ∈ [1, 2, 3, 4, 5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega
      have := hk m hm'
      rw [htab] at this
      simp at this

theorem quotient_center_equiv_of_map_eq_top {E K : Type*} [Group E] [Group K] (ρ : E →* K)
    (hkerZ : ρ.ker ≤ center E) (hK : center K = ⊥) {B : Subgroup E} (hB : B.map ρ = ⊤) :
    Nonempty (B ⧸ center B ≃* K) := by
  set φ : B →* K := ρ.comp B.subtype
  have hφ : Function.Surjective φ := by
    intro k
    have hk : k ∈ B.map ρ := hB ▸ mem_top k
    obtain ⟨b, hb, rfl⟩ := hk
    exact ⟨⟨b, hb⟩, rfl⟩
  have hker : φ.ker = center B := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxZ : (x : E) ∈ center E := hkerZ (MonoidHom.mem_ker.2 hx)
      rw [mem_center_iff] at hxZ ⊢
      intro y
      exact Subtype.ext (hxZ y)
    · intro hx
      have hc : φ x ∈ center K := by
        rw [mem_center_iff]
        intro k
        obtain ⟨y, rfl⟩ := hφ k
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hx) y]
      rw [hK, mem_bot] at hc
      exact hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem isoInvariant_quotient_center_equiv (X : Type*) [Group X] :
    IsoInvariant fun Y _ => Nonempty (Y ⧸ center Y ≃* X) := by
  intro Y Y' _ _ e ⟨f⟩
  exact ⟨(QuotientGroup.congr (center Y) (center Y') e (Subgroup.map_center_eq e)).trans f⟩

theorem mclCt_comps : CompsSatisfy mclCt fun Y _ => Nonempty (Y ⧸ center Y ≃* mclX) := by
  intro B hB
  obtain ⟨hrange, hker⟩ := mclRho_range
  have hkerZ : mclRho.ker ≤ center mclCt := by
    have hz : zpowers (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) = mclRho.ker := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr mclT0_mem_ker)
      rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk, mclT0_facts.2.1]
    rw [← hz, zpowers_le, mem_center_iff]
    intro g
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2
  obtain ⟨hs, hnab⟩ := mclX_simple
  have hs' : IsSimpleGroup mclRho.range := by
    rw [hrange]
    exact hs
  have hnab' : ∃ a b : mclRho.range, a * b ≠ b * a := by
    rw [hrange]
    exact hnab
  have hcen : center mclRho.range = ⊥ := Sporadic.SuzOddCore.center_eq_bot_of_simple' hs' hnab'
  have hkerS : Group.IsSolvable mclRho.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hp : IsPGroup 2 mclRho.ker := IsPGroup.of_card (n := 1) (by rw [hker, pow_one])
    have : Group.IsNilpotent mclRho.ker := hp.isNilpotent
    infer_instance
  have hkerZ' : mclRho.rangeRestrict.ker ≤ center mclCt := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkerZ
  have hmap := map_eq_top_of_isComponent mclRho.rangeRestrict mclRho.rangeRestrict_surjective
    hkerS hs' hB
  obtain ⟨e⟩ := quotient_center_equiv_of_map_eq_top mclRho.rangeRestrict hkerZ' hcen hmap
  exact ⟨e.trans (MulEquiv.subgroupCongr hrange)⟩

theorem mcl_inner_comps {G : Type} [Group G] (e : G ≃* NativeSporadic.McL) (t : G)
    (ht : orderOf t = 2) :
    CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => Nonempty (Y ⧸ center Y ≃* mclX) := by
  refine compsSatisfy_centralizer_of_mulEquiv mclP (isoInvariant_quotient_center_equiv _)
    (fun u hu ho => ?_) (e.trans mclPermEquiv) t ht
  obtain ⟨g, hg, rfl⟩ := mclT0_facts.2.2.2.2 u hu ho
  rw [centralizerIn_conj mclP hg]
  exact CompsSatisfy.of_mulEquiv (isoInvariant_quotient_center_equiv _) (conjEquiv mclCt g).symm
    mclCt_comps

end CFSG.ComponentClassification.RestrictedStd.Spor
