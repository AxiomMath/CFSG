module

public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerListBender
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem stdData_odd_quotient {T : StdType} (hfacts : StdTypeFacts T)
    (hiso : StdType.IsoInvariant T) {H : Type} [Group H] [Finite H] {A : Subgroup H} {n : ℕ}
    (hA : T n A) {t : H} (ht : orderOf t = 2) (hAt : A ≤ centralizer ({t} : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (A : Set H) ⊓ centralizer ({t} : Set H)),
      (S : Subgroup _).map (centralizer (A : Set H) ⊓ centralizer ({t} : Set H)).subtype =
        zpowers t)
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R)) :
    CFSG.Open.standardComponentIsStandard (A.map (QuotientGroup.mk' R)) ∧
      T n (A.map (QuotientGroup.mk' R)) ∧ orderOf (QuotientGroup.mk' R t) = 2 ∧
      QuotientGroup.mk' R t ∈
        centralizer ((A.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) : Set (H ⧸ R)) ∧
      ¬ 2 ∣ (zpowers (QuotientGroup.mk' R t)).relIndex
        (centralizer ((A.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) : Set (H ⧸ R))) ∧
      ∀ S : Sylow 2 (centralizer ((A.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) :
        Set (H ⧸ R))), Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAs, hnab, hE⟩ := hfacts n A hA
  have hE' : ∃ E : Subgroup H, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hEA, hEe, hE4⟩ := exists_four_le_of_subgroup hE
    exact ⟨E, hEA, ⟨hEe.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, hE4⟩
  set θ := QuotientGroup.mk' R
  set C := centralizer ((A.map θ : Subgroup (H ⧸ R)) : Set (H ⧸ R))
  obtain ⟨hinj, -, hθt, -, -, -, -, -, -, hstd, ⟨S₀, hS₀⟩, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab hE' ht hAt hAn hsyl R hR
  have e : A ≃* A.map θ := MulEquiv.ofBijective (θ.subgroupMap A)
    ⟨fun x y hxy => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy)),
      θ.subgroupMap_surjective A⟩
  have hsub : (zpowers (θ t)).subgroupOf C = S₀ := by
    rw [← hS₀, Subgroup.subgroupOf, comap_map_eq_self_of_injective (subtype_injective C)]
  have htC : θ t ∈ C := by
    have h : θ t ∈ (S₀ : Subgroup C).map C.subtype := by
      rw [hS₀]
      exact mem_zpowers _
    obtain ⟨x, -, hx⟩ := h
    exact hx ▸ x.2
  have hidx : ¬ 2 ∣ (zpowers (θ t)).relIndex C := by
    rw [Subgroup.relIndex, hsub]
    exact Sylow.not_dvd_index S₀
  exact ⟨hstd, hiso n _ _ e hA, hθt, htC, hidx, card_sylow_eq_two_of_relIndex hθt htC hidx⟩

@[expose] def GMSUnitarySharpKRankOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G →
    CFSG.Open.standardComponentOddCore G = ⊥ → ∀ (n : ℕ) (A : Subgroup G),
      StdUnitaryData G A n → ∀ t : G, orderOf t = 2 → t ∈ centralizer (A : Set G) →
        ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set G)) →
        SharpOutcome (fun D _ => LieModel D .PSL 3 2 (2 * n)) G A t

@[expose] def GMSSuzukiSharpKRankOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G →
    CFSG.Open.standardComponentOddCore G = ⊥ → ∀ (n : ℕ) (A : Subgroup G),
      StdSuzukiData G A n → ∀ t : G, orderOf t = 2 → t ∈ centralizer (A : Set G) →
        ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set G)) →
        SharpOutcome (fun D _ => LieModel D .PSp 2 2 n) G A t

theorem sharpOutcomeSz_oddCore_quotient (hGMS : GMSSuzukiSharpKRankOneStatement)
    {H : Type} [Group H] [Finite H] (hH : CFSG.SectionRank.IsKGroupCat H) {A : Subgroup H}
    {n : ℕ} (hA : LieModel A .twistedB2 0 2 n) {t : H} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnn : ¬ (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))).Normal) :
    SharpOutcome (fun D _ => LieModel D .PSp 2 2 n)
      (H ⧸ CFSG.Open.standardComponentOddCore H)
      (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)))
      (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H) t) := by
  have hAt : A ≤ centralizer ({t} : Set H) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htA a ha)
  obtain ⟨hstd, hT, hθt, htC, hidx, -⟩ := stdData_odd_quotient stdTypeFacts_T_Sz
    isoInvariant_T_Sz (hA : T_Sz n A) ht hAt hAn
    (exists_sylow_inf_centralizer_eq_zpowers ht htA hrank) _
    (odd_card_standardComponentOddCore H)
  exact hGMS _ (hH.quotient _) (standardComponentOddCore_quotient_eq_bot H) n _
    ⟨hstd, hnn, hT⟩ _ hθt htC hidx

section Certified

theorem gmsUnitarySharpKRankOne : GMSUnitarySharpKRankOneStatement :=
  fun _ _ _ hG hO _ _ hA _ ht htA hsyl => gmsUnitary_sharp hG hO hA ht htA hsyl

theorem gmsSuzukiSharpKRankOne : GMSSuzukiSharpKRankOneStatement :=
  fun _ _ _ hG hO _ _ hA _ ht htA hsyl => gmsSuzuki_sharp hG hO hA ht htA hsyl

end Certified

end CFSG.LocalAnalysis.EvenBN.GMSK
