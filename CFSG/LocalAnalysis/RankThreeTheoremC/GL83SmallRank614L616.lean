module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Reduce
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Max
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

omit [Finite G] in
private theorem prop614L616_card_eq_eighty_one {P : Subgroup G} (e : P ≃* W₃) :
    Nat.card P = 81 := by
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, wreath_card_zmod_three]
  norm_num

private theorem prop614L616_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime]
    {Q P : Subgroup G} (hP : IsPGroup p P) (hQP : Q < P) :
    ∃ y ∈ P, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQP.ne ?_
    exact le_antisymm hQP.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQP.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem prop614L616_lt_inf_normalizer {p : ℕ} [Fact p.Prime] {S T : Subgroup G}
    (hT : IsPGroup p T) (hST : S < T) : S < T ⊓ normalizer (S : Set G) := by
  obtain ⟨y, hyT, hyN, hyS⟩ := prop614L616_exists_mem_normalizer_not_mem hT hST
  refine lt_of_le_of_ne (le_inf hST.le le_normalizer) fun h => hyS ?_
  rw [h]
  exact mem_inf.mpr ⟨hyT, hyN⟩

omit [Finite G] in
private theorem prop614L616_normalizer_le_normalizer {S S₀ : Subgroup G} (h1 : S₀ ≤ S)
    (h3 : (S₀.subgroupOf S).Characteristic) :
    normalizer (S : Set G) ≤ normalizer (S₀ : Set G) := by
  have key : ∀ g ∈ normalizer (S : Set G), ∀ c ∈ S₀, g * c * g⁻¹ ∈ S₀ := by
    intro g hg c hc
    let φ : S ≃* S :=
      { toFun := fun s => ⟨g * s * g⁻¹, (mem_normalizer_iff.mp hg s).mp s.2⟩
        invFun := fun s => ⟨g⁻¹ * s * g, (mem_normalizer_iff''.mp hg s).mp s.2⟩
        left_inv := fun s => Subtype.ext (by simp [mul_assoc])
        right_inv := fun s => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
    have hc' : (⟨c, h1 hc⟩ : S) ∈ S₀.subgroupOf S := hc
    exact characteristic_iff_map_le.mp h3 φ (mem_map_of_mem φ.toMonoidHom hc')
  intro g hg
  refine mem_normalizer_iff.mpr fun c => ⟨key g hg c, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

omit [Finite G] in
private theorem prop614L616_le_normalizer_inf {B S T : Subgroup G}
    (hBT : B ≤ normalizer (T : Set G)) (hBS : B ≤ normalizer (S : Set G)) :
    B ≤ normalizer ((T ⊓ normalizer (S : Set G) : Subgroup G) : Set G) :=
  (le_inf hBT (hBS.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf

private theorem prop614L616_false_of_card_lt {M B H S H₁ R : Subgroup G}
    (h : Prop614Extremal M B H S) (hH₁ : IsTwoLocal H₁) (hBH₁ : B ≤ H₁) (hH₁M : ¬ H₁ ≤ M)
    (hR : IsTwoInvariantIn B (H₁ ⊓ M) R) (hcard : Nat.card S < Nat.card R) : False := by
  obtain ⟨S₁, hRS₁, hS₁⟩ := exists_isMaxTwoInvariantIn_of_le hR
  have hlt : Nat.card S < Nat.card S₁ := hcard.trans_le (Subgroup.card_le_of_le hRS₁)
  have hS₁1 : S₁ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hlt
    have : 0 < Nat.card S := Nat.card_pos
    omega
  exact h.max H₁ S₁ ⟨hH₁, hBH₁, hH₁M, hS₁, hS₁1⟩ (Or.inl hlt)

theorem Prop614Pair.not_three_dvd_relIndex (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M) (e : (P : Subgroup G) ≃* W₃) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H S : Subgroup G}
    (h : Prop614Pair M (zpowers x ⊔ zpowers z) H S) :
    ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H := fun h3 =>
  h.not_le (le_of_three_dvd_relIndex hS hU0 hD2 hsit hsolv e hx hz h.isTwoLocal h.le h3)

theorem Prop614Extremal.isMax_self (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M) (e : (P : Subgroup G) ≃* W₃) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H S : Subgroup G}
    (h : Prop614Extremal M (zpowers x ⊔ zpowers z) H S) :
    IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S := by
  obtain ⟨⟨hSHM, hS2, hBS⟩, hSmax⟩ := h.pair.isMax
  refine ⟨⟨hSHM.trans inf_le_left, hS2, hBS⟩, fun R hR hSR => ?_⟩
  by_contra hRS
  have hSltR : S < R := lt_of_le_of_ne hSR (Ne.symm hRS)
  obtain ⟨T, hST, hT⟩ := exists_isMaxTwoInvariantIn_of_le
    (⟨hSHM.trans inf_le_right, hS2, hBS⟩ : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S)
  have hT1 : T ≠ ⊥ := fun hT1 => h.pair.ne_bot (le_bot_iff.mp (hT1 ▸ hST))
  have hTG := isMax_top_of_isMax hS hU0 hD2 hsit hsolv e hx hz hT hT1
  have hSltT : S < T := by
    refine lt_of_le_of_ne hST fun hST' => hRS ?_
    exact (hTG.2 R ⟨le_top, hR.2.1, hR.2.2⟩ (hST'.symm.le.trans hSR)).trans hST'.symm
  by_cases hH₁M : normalizer (S : Set G) ≤ M
  ·
    have hSltR₁ := prop614L616_lt_inf_normalizer hR.2.1 hSltR
    exact hSltR₁.ne (hSmax _ ⟨le_inf (inf_le_left.trans hR.1) (inf_le_right.trans hH₁M),
      hR.2.1.to_le inf_le_left, prop614L616_le_normalizer_inf hR.2.2 hBS⟩ hSltR₁.le).symm
  ·
    exact prop614L616_false_of_card_lt h ⟨S, h.pair.ne_bot, hS2, rfl⟩ hBS hH₁M
      ⟨le_inf inf_le_right (inf_le_left.trans hT.1.1), hT.1.2.1.to_le inf_le_left,
        prop614L616_le_normalizer_inf hT.1.2.2 hBS⟩
      (Subgroup.card_lt_of_lt (prop614L616_lt_inf_normalizer hT.1.2.1 hSltT))

theorem Prop614Extremal.normalizer_le_of_characteristic (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M) (e : (P : Subgroup G) ≃* W₃) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H S : Subgroup G}
    (h : Prop614Extremal M (zpowers x ⊔ zpowers z) H S) {S₀ : Subgroup G} (h1 : S₀ ≤ S)
    (h2 : S₀ ≠ ⊥) (h3 : (S₀.subgroupOf S).Characteristic) :
    normalizer (S₀ : Set G) ≤ M := by
  obtain ⟨⟨hSHM, hS2, hBS⟩, -⟩ := h.pair.isMax
  have hNN := prop614L616_normalizer_le_normalizer h1 h3
  have hH₁ : IsTwoLocal (normalizer (S₀ : Set G)) := ⟨S₀, h2, hS2.to_le h1, rfl⟩
  obtain ⟨T, hST, hT⟩ := exists_isMaxTwoInvariantIn_of_le
    (⟨hSHM.trans inf_le_right, hS2, hBS⟩ : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S)
  rcases hST.eq_or_lt with rfl | hSltT
  ·
    obtain ⟨g, hgM, hPg⟩ := exists_conj_le_normalizer_of_isMax hS hU0 hsit hsolv hx hz hT
    have hPM := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
    refine le_of_twentySeven_le_card hS hU0 hD2 hsit hsolv e hH₁ (hPg.trans hNN) ?_
      (P.isPGroup'.map _) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hgM (hPM hy)) (inv_mem hgM)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        prop614L616_card_eq_eighty_one e]
      norm_num
  ·
    by_contra hH₁M
    exact prop614L616_false_of_card_lt h hH₁ (hBS.trans hNN) hH₁M
      ⟨le_inf inf_le_right (inf_le_left.trans hT.1.1), hT.1.2.1.to_le inf_le_left,
        prop614L616_le_normalizer_inf hT.1.2.2 (hBS.trans hNN)⟩
      (Subgroup.card_lt_of_lt ((prop614L616_lt_inf_normalizer hT.1.2.1 hSltT).trans_le
        (inf_le_inf_left T hNN)))

end CFSG.LocalAnalysis.RankThreeTheoremC
