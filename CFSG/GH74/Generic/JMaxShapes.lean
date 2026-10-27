module

public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.GH74.Generic.Context
public import CFSG.GH74.Generic.Front.OuterModels
public import CFSG.LieType.Simplicity.Classical
public import CFSG.GH74.Generic.Shapes

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem ofLieType_of_isSL4Model {K : Type} [Group K] (h : IsSL4Model K) : OfLieType K := by
  rcases h with ⟨F, _, _, -, ⟨e⟩⟩ | ⟨q, F, _, _, hF, -, ⟨e⟩⟩
  · obtain ⟨p, f, hp, hf, hcard⟩ := exists_prime_pow_card F
    have hadm : StatedLieAdmissible .PSL 4 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
    have hmap : (center K).map e.toMonoidHom =
        (StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F) := by
      rw [← center_statedSL_eq]
      exact CFSG.LieType.Universal.Unitary.map_center_mulEquiv e
    exact ⟨.PSL, 4, p, f, Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hcard,
      ⟨QuotientGroup.congr (center K) ((StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F)) e
        hmap⟩⟩⟩
  · obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
    have hf : 1 ≤ f := by
      by_contra hf0
      have hf0' : f = 0 := by omega
      subst hf0'
      simp at hF
      have : 1 < Nat.card F := Finite.one_lt_card
      omega
    have hadm : StatedLieAdmissible .PSU 4 p f := ⟨hp.out, hf, by norm_num, by simp⟩
    have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (n := 4)
      (by norm_num) (fun h => by simp at h)).2
    have hmap : (center K).map e.toMonoidHom =
        (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ f) F) := by
      rw [← hZ]
      exact CFSG.LieType.Universal.Unitary.map_center_mulEquiv e
    exact ⟨.PSU, 4, p, f, Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF,
      ⟨QuotientGroup.congr (center K) ((StatedScalars (Fin 4) F).subgroupOf
        (StatedSU 4 (p ^ f) F)) e hmap⟩⟩⟩

theorem isSimpleGroup_of_lieModel_L3' {K : Type} [Group K] {p f : ℕ}
    (h : LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f) : IsSimpleGroup K := by
  rcases h with h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity K 3 p f (stated_of_lieModel_PSL h)).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity K 3 p f (stated_of_lieModel_PSU h)).2

theorem exists_noncomm_of_isQuasisimple_aux {K : Type} [Group K] (hK : IsQuasisimple K) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, -, a', b', hab'⟩ := hK
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  exact ⟨a, b, fun h' => hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])⟩

theorem center_eq_bot_of_quasisimple_lieModel_L3 {K : Type} [Group K] (hK : IsQuasisimple K)
    {p f : ℕ} (h : LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f) : center K = ⊥ := by
  have hs : IsSimpleGroup K := isSimpleGroup_of_lieModel_L3' h
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple_aux hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hb | ht
  · exact hb
  · exfalso
    apply hab
    have : a ∈ center K := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem ofLieType_of_lieModel_L3 {K : Type} [Group K] (hK : IsQuasisimple K) {p f : ℕ}
    (h : LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f) : OfLieType K := by
  have hc := center_eq_bot_of_quasisimple_lieModel_L3 hK h
  have e := mulEquivOfCenterBot hc
  rcases h with h | h
  · obtain ⟨hadm, F, _, _, hF, ⟨e'⟩⟩ := stated_of_lieModel_PSL h
    exact ⟨.PSL, 3, p, f, Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF,
      ⟨e.symm.trans e'⟩⟩⟩
  · obtain ⟨hadm, F, _, _, hF, ⟨e'⟩⟩ := stated_of_lieModel_PSU h
    exact ⟨.PSU, 3, p, f, Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF,
      ⟨e.symm.trans e'⟩⟩⟩

theorem not_isL3Odd_of_isSL4Model {K : Type} [Group K] (hK : IsQuasisimple K) (h : IsSL4Model K) :
    ¬ IsL3Odd K := by
  rintro ⟨p, f, -, -, hmod⟩
  have hc := center_eq_bot_of_quasisimple_lieModel_L3 hK hmod
  have h2 := h.natCard_center
  rw [hc, Subgroup.card_bot] at h2
  exact absurd h2 (by norm_num)

theorem d2_eq_seven_of_shapeS3 {G : Type} [Group G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hc : IsComponent K) (hG2 : InG2 ↥K) (hsh : ShapeS3 x K) : d2 ↥K = 7 := by
  obtain ⟨⟨p, f, hp, hp2, hq5, hmod⟩, -⟩ := hsh
  have hlie : OfLieType ↥K := ofLieType_of_lieModel_L3 hc.1 hmod
  have hL3 : IsL3Odd ↥K := ⟨p, f, hp, hp2, hmod⟩
  have h7 : InG2Depth 7 ↥K := ⟨hG2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, p, f, hp, hp2, by omega, hmod⟩))))))⟩
  refine le_antisymm (Nat.sInf_le h7) (le_csInf ⟨7, h7⟩ fun i hi => ?_)
  obtain ⟨-, hi⟩ := hi
  rcases hi with ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ |
    ⟨rfl, -, hn⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hL3 hn
  · exact le_rfl
  · omega

theorem d2_le_six_of_shapeS1 {G : Type} [Group G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hc : IsComponent K) (hG2 : InG2 ↥K) (hsh : ShapeS1 x K) : d2 ↥K ≤ 6 :=
  Nat.sInf_le ⟨hG2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, ofLieType_of_isSL4Model hsh.1, not_isL3Odd_of_isSL4Model hc.1 hsh.1⟩)))))⟩

end CFSG.GH74.Generic
