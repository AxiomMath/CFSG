module

public import CFSG.ClassicalInvolution.Q3.Q3WFin
public import CFSG.ClassicalInvolution.Q3.Q3WLift
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPrime
public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

theorem oddCoverSL3_three : OddCoverSL3 F3 := by
  have hK : Nat.card F3 = 3 := Nat.card_zmod 3
  have hnc : NoCover.{0} Odd (CFSG.Assembly.LowTwoRank.StatedSL 3 F3) := by
    intro E _ _ _ π hπ hC hodd
    exact CFSG.SectionRank.OddCover.prime_classical_three_perfect_odd_extension_trivial
      Nat.prime_three (by norm_num) (Or.inl ⟨rfl, hK, rfl⟩) π hπ hC hodd
  have h := NoCover.of_mulEquiv
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F3).symm hnc
  exact fun E _ _ _ π hπ hcen hodd => h E π hπ hcen hodd

theorem sl2_pow_twelve : ∀ x : SL(2, F3), x ^ 12 = 1 := by decide +kernel

theorem pow_twelve_conj_B12 (c : SL(3, F3)) :
    ∀ y ∈ (B12 F3).map (MulAut.conj c⁻¹).toMonoidHom, y ^ 12 = 1 := by
  rintro _ ⟨b, ⟨A, rfl⟩, rfl⟩
  rw [← map_pow, ← map_pow, sl2_pow_twelve A, map_one, map_one]

theorem pow_twelve_conj_B23 (c : SL(3, F3)) :
    ∀ y ∈ (B23 F3).map (MulAut.conj c⁻¹).toMonoidHom, y ^ 12 = 1 := by
  rintro _ ⟨b, ⟨A, rfl⟩, rfl⟩
  rw [← map_pow, ← map_pow, sl2_pow_twelve A, map_one, map_one]

theorem linearBlockStandardPair_lift3 {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) (hO3 : ¬ 3 ∣ Nat.card O)
    {A B : Subgroup Y} (hA : ∀ a ∈ A, a ^ 12 = 1) (hB : ∀ b ∈ B, b ^ 12 = 1)
    {W : Subgroup (Y ⧸ O)}
    (h : LinearBlockStandardPair F3 W (A.map (QuotientGroup.mk' O)) (B.map (QuotientGroup.mk' O))) :
    ∃ W' : Subgroup Y, LinearBlockStandardPair F3 W' A B := by
  have : Group.IsPerfect SL(3, F3) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have hW : W ≤ A.map (QuotientGroup.mk' O) ⊔ B.map (QuotientGroup.mk' O) :=
    linearBlockStandardPair_le_sup' h
  obtain ⟨θb, c, hrange, hker, hcases⟩ := h
  have hθ : θb.range ≤ ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).range := by
    rw [hrange]
    refine hW.trans (sup_le ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨a, Subgroup.mem_sup_left ha⟩, rfl⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b, Subgroup.mem_sup_right hb⟩, rfl⟩
  have hcen' : ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).ker ≤ Subgroup.center ↥(A ⊔ B) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro r
    have : (y : Y) ∈ O := by
      have := MonoidHom.mem_ker.mp hy
      exact (QuotientGroup.eq_one_iff _).mp this
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hOc this) (r : Y))
  have hodd' : Odd (Nat.card ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).ker) := by
    refine hOodd.of_dvd_nat ?_
    let g : ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).ker →* O :=
      { toFun := fun y => ⟨(y.1 : Y), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun y₁ y₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : Y)) h))
  obtain ⟨θ', hθ'⟩ := exists_lift_of_oddCoverSL3 oddCoverSL3_three
    ((QuotientGroup.mk' O).comp (A ⊔ B).subtype) hcen' hodd' θb hθ
  set θ : SL(3, F3) →* Y := (A ⊔ B).subtype.comp θ' with hθdef
  have hπθ : (QuotientGroup.mk' O).comp θ = θb := by
    ext s
    exact DFunLike.congr_fun hθ' s
  have hmapθ : ∀ X : Subgroup SL(3, F3),
      (X.map θ).map (QuotientGroup.mk' O) = X.map θb := by
    intro X
    rw [Subgroup.map_map, hπθ]
  have hexp : ∀ X : Subgroup SL(3, F3), (∀ y ∈ X, y ^ 12 = 1) → ∀ y ∈ X.map θ, y ^ 12 = 1 := by
    rintro X hX _ ⟨y, hy, rfl⟩
    rw [← map_pow, hX y hy, map_one]
  have hker0 : (QuotientGroup.mk' O).ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  have hcop : ∀ n ∈ (QuotientGroup.mk' O).ker, Nat.Coprime (orderOf n) 6 := by
    intro n hn
    rw [QuotientGroup.ker_mk'] at hn
    exact orderOf_coprime_six hOodd hO3 hn
  have heq : ∀ X : Subgroup SL(3, F3), ∀ U : Subgroup Y, (∀ y ∈ X, y ^ 12 = 1) →
      (∀ u ∈ U, u ^ 12 = 1) → X.map θb = U.map (QuotientGroup.mk' O) → X.map θ = U := by
    intro X U hX hU hmap
    have hmap' : (X.map θ).map (QuotientGroup.mk' O) = U.map (QuotientGroup.mk' O) :=
      (hmapθ X).trans hmap
    refine le_antisymm ?_ ?_
    · refine le_of_map_le_of_exponent (QuotientGroup.mk' O) hker0 hcop (hexp X hX) hU
        fun l hl => ?_
      rw [← hmap']
      exact ⟨l, hl, rfl⟩
    · refine le_of_map_le_of_exponent (QuotientGroup.mk' O) hker0 hcop hU (hexp X hX)
        fun l hl => ?_
      rw [hmap']
      exact ⟨l, hl, rfl⟩
  refine ⟨θ.range, θ, c, rfl, ?_, ?_⟩
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker, ← hπθ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨heq _ A (pow_twelve_conj_B12 c) hA h1, heq _ B (pow_twelve_conj_B23 c) hB h2⟩
    · right
      exact ⟨heq _ B (pow_twelve_conj_B12 c) hB h1, heq _ A (pow_twelve_conj_B23 c) hA h2⟩

theorem pow_twelve_of_exact {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
    (hz : IsClassicalMember3 L z) (hL : classicalInvolutionOddCore L = ⊥) :
    ∀ l ∈ L, l ^ 12 = 1 := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hL
  intro l hl
  have := pow_twelve_of_equiv_sl2Three e ⟨l, hl⟩
  simpa using congrArg Subtype.val this

theorem linearBlockStandardPair_of_locImg3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : ¬ 3 ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x))) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {W : Subgroup (locQuot Ω x)}
    (h : LinearBlockStandardPair F3 W (locImg Ω x L) (locImg Ω x L')) :
    ∃ W' : Subgroup G, LinearBlockStandardPair F3 W' L L' := by
  have hexp : ∀ M ∈ centralizingMembers Ω {x},
      ∀ m ∈ M.subgroupOf (locLayer Ω x), m ^ 12 = 1 := by
    intro M hM m hm
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    have := pow_twelve_of_exact hz (hex M hM.1) (m : G) (Subgroup.mem_subgroupOf.mp hm)
    exact Subtype.ext (by simpa using this)
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_lift3
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) hO3 (hexp L hL) (hexp L' hL') h
  have := Models.linearBlockStandardPair_map hW' (locLayer Ω x).subtype
    (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (le_centralizingLayer hL), inf_eq_left.mpr (le_centralizingLayer hL')] at this
  exact ⟨_, this⟩

theorem locImg_injOn3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : ¬ 3 ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x))) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    (h : locImg Ω x L = locImg Ω x L') : L = L' := by
  have hexp : ∀ M ∈ centralizingMembers Ω {x},
      ∀ m ∈ M.subgroupOf (locLayer Ω x), m ^ 12 = 1 := by
    intro M hM m hm
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    have := pow_twelve_of_exact hz (hex M hM.1) (m : G) (Subgroup.mem_subgroupOf.mp hm)
    exact Subtype.ext (by simpa using this)
  have hker0 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).ker ≤
      Subgroup.center ↥(locLayer Ω x) := by
    rw [QuotientGroup.ker_mk']
    exact hP1
  have hcop : ∀ n ∈ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).ker,
      Nat.Coprime (orderOf n) 6 := by
    intro n hn
    rw [QuotientGroup.ker_mk'] at hn
    exact orderOf_coprime_six (CFSG.ComponentClassification.OddCore.odd_card _) hO3 hn
  have h1 : L.subgroupOf (locLayer Ω x) ≤ L'.subgroupOf (locLayer Ω x) :=
    le_of_map_le_of_exponent _ hker0 hcop (hexp L hL) (hexp L' hL') fun l hl => by
      have : locImg Ω x L = locImg Ω x L' := h
      unfold locImg at this
      rw [← this]
      exact ⟨l, hl, rfl⟩
  have h2 : L'.subgroupOf (locLayer Ω x) ≤ L.subgroupOf (locLayer Ω x) :=
    le_of_map_le_of_exponent _ hker0 hcop (hexp L' hL') (hexp L hL) fun l hl => by
      have : locImg Ω x L = locImg Ω x L' := h
      unfold locImg at this
      rw [this]
      exact ⟨l, hl, rfl⟩
  have h3 := le_antisymm h1 h2
  have e1 := Subgroup.subgroupOf_map_subtype L (locLayer Ω x)
  have e2 := Subgroup.subgroupOf_map_subtype L' (locLayer Ω x)
  rw [h3, e2, inf_eq_left.mpr (le_centralizingLayer hL')] at e1
  rw [inf_eq_left.mpr (le_centralizingLayer hL)] at e1
  exact e1.symm

end CFSG.ClassicalInvolution.Q3.Q3W
