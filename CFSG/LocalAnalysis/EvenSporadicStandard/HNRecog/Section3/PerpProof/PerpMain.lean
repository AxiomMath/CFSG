module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpTrans
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpOrb4A

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem perp_of_hyps (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hT3 : Vert TableIIIFacts a z)
    (hT4 : Vert TableIVFacts a z) (hPar : Vert ParityFacts a z) : PerpFacts a z := by
  have hT4a : TableIVFacts a z := hT4.self
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hsq : ∀ {x : G}, IsConj a x → x ^ 2 = 1 := fun {x} hx => by
    rw [← perp_orderOf_of_isConj_a h hx]; exact pow_orderOf_eq_one x
  have hmemG : ∀ {c x : G}, IsConj a c → x ∈ orb2A a a ∩ orb2A a c → x ∈ Gxy a c := by
    intro c x hc hx
    have hx2 : x ^ 2 = 1 := hsq hx.1.1
    have hc2 : c ^ 2 = 1 := hsq hc
    have hax : a * x = x * a := comm_of_sq_mul ha2 hx2 (hsq hx.1.2)
    have hcx : c * x = x * c := comm_of_sq_mul hc2 hx2 (hsq hx.2.2)
    exact mem_Gxy.mpr ⟨mem_Gx.mpr hax, mem_Gx.mpr hcx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb c hc
    have hcb : c ∈ sBase a b := by
      rcases hc with hc | hc
      · exact hc.1
      · exact hc.1
    have hc2 : c ^ 2 = 1 := hsq hcb.1
    ext y
    rcases hc with hc | hc
    · obtain ⟨hord, hsq2⟩ := perp_orderOf_row_two h hb.1 hc
      have hcen := perp_center_closure_pair ha2 hc2 (k := 2) le_rfl (by rw [hord]) y
      rw [hsq2] at hcen
      constructor
      · intro hy
        exact hcen.mpr (perp_eq_of_row_two hI h hT4a hb hc hy)
      · intro hy
        rw [hcen.mp hy]
        exact perp_self_mem_inter h hb hcb
    · obtain ⟨hord, hcube⟩ := perp_orderOf_row_five h hb.1 hc
      have hcen := perp_center_closure_pair ha2 hc2 (k := 3) (by norm_num) (by rw [hord]) y
      rw [hcube] at hcen
      constructor
      · intro hy
        exact hcen.mpr (perp_eq_of_row_five hI h hT4a hb hc hy)
      · intro hy
        rw [hcen.mp hy]
        exact perp_self_mem_inter h hb hcb
  · intro b hb c hc
    exact perp_isConjOrbit hI h hF1.self hF2.self hT4a hb (Or.inl rfl) hc
  · intro b hb c hc x hx
    have hcx : c ∈ sSet a z x 3 := perp_mem_sSet_three hI h hT4a hc hx
    have hcard := hT4a.card_stab x hx.1 3 c hcx
    have h64 : Nat.card ↥(Gxyz a x c) = 2 ^ 6 := by
      rw [Gxyz_eq_inf]
      simpa using hcard
    exact ⟨IsPGroup.of_card h64, h64⟩
  · intro b hb c hc x hx
    have hc4 : c ∈ orb4A a z a := ⟨hc.1.1, (perp_orderOf_row_three h hc).2⟩
    exact perp_mem_pCoreOf_of_shape (perp_shape_of_mem_orb4A hI h hF1 hT3 hc4)
      (hmemG hc.1.1 hx) (hsq hx.1.1)
  · intro b hb c hc
    exact perp_isConjOrbit hI h hF1.self hF2.self hT4a hb (Or.inr rfl) hc
  · intro b hb c hc x hx
    have hcx : c ∈ sSet a z x 4 := perp_mem_sSet_four hI h hT4a hc hx
    exact hT4a.shape_3A x hx.1 c hcx

end CFSG.EvenSporadicStandard.HNRecog.Section3
