module

public import CFSG.LocalAnalysis.EvenBN.GMSK.Statement
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem isKGroupCat_of_section_of_kProper {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper Catalog G) {P : Subgroup G} (hP : P ≠ ⊤) (M : Subgroup P)
    [M.Normal] : CFSG.SectionRank.IsKGroupCat (P ⧸ M) :=
  (CFSG.QuasithinUnique.isKGroupCat_of_kProper hK hP).quotient M

instance standardComponentOddCore_normal (H : Type*) [Group H] :
    (CFSG.Open.standardComponentOddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem standardComponentOddCore_eq_pPrimeCore (H : Type*) [Group H] :
    CFSG.Open.standardComponentOddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.Open.standardComponentOddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_card_standardComponentOddCore (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.Open.standardComponentOddCore H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [standardComponentOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

theorem standardComponentOddCore_quotient_eq_bot (H : Type*) [Group H] [Finite H] :
    CFSG.Open.standardComponentOddCore (H ⧸ CFSG.Open.standardComponentOddCore H) = ⊥ := by
  set O := CFSG.Open.standardComponentOddCore H
  set f := QuotientGroup.mk' O
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective O
  set W := (CFSG.Open.standardComponentOddCore (H ⧸ O)).comap f
  have hWn : W.Normal := (standardComponentOddCore_normal _).comap f
  have hWodd : Odd (Nat.card W) := by
    have h1 := relIndex_mul_card f.ker W
    rw [relIndex_ker, map_comap_eq_self_of_surjective hf] at h1
    rw [← h1]
    refine (odd_card_standardComponentOddCore _).mul ?_
    have hdvd : Nat.card ↥(f.ker ⊓ W) ∣ Nat.card O :=
      (card_dvd_of_le inf_le_left).trans (by rw [QuotientGroup.ker_mk'])
    exact (odd_card_standardComponentOddCore H).of_dvd_nat hdvd
  have hWO : W ≤ O := le_sSup ⟨hWn, hWodd⟩
  rw [eq_bot_iff]
  calc CFSG.Open.standardComponentOddCore (H ⧸ O) = W.map f :=
        (map_comap_eq_self_of_surjective hf _).symm
    _ ≤ O.map f := map_mono hWO
    _ = ⊥ := QuotientGroup.map_mk'_self O

theorem exists_sylow_inf_centralizer_eq_zpowers {H : Type*} [Group H] [Finite H]
    {A : Subgroup H} {t : H} (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set H))
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2) :
    ∃ S : Sylow 2 ↥(centralizer (A : Set H) ⊓ centralizer ({t} : Set H)),
      (S : Subgroup _).map (centralizer (A : Set H) ⊓ centralizer ({t} : Set H)).subtype =
        zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (A : Set H) ⊓ centralizer ({t} : Set H)
  have htC : zpowers t ≤ C := zpowers_le.2 ⟨htA, mem_centralizer_singleton_iff.2 rfl⟩
  have hz2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := (hz2.of_equiv (subgroupOfEquivOfLe htC).symm).exists_le_sylow
  refine ⟨S, (eq_of_le_of_card_ge ?_ ?_).symm⟩
  · intro x hx
    exact ⟨⟨x, htC hx⟩, hS hx, rfl⟩
  · rw [Nat.card_zpowers, ht]
    exact hrank _ ((map_subtype_le _).trans inf_le_left) (S.isPGroup'.map _)

theorem stdLinearData_odd_quotient {H : Type} [Group H] [Finite H] {A : Subgroup H} {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] [Fintype k] (hk : Fintype.card k = 2 ^ n)
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) k) {t : H} (ht : orderOf t = 2)
    (hAt : A ≤ centralizer ({t} : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (A : Set H) ⊓ centralizer ({t} : Set H)),
      (S : Subgroup _).map (centralizer (A : Set H) ⊓ centralizer ({t} : Set H)).subtype =
        zpowers t)
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    (hnn : ¬ (A.map (QuotientGroup.mk' R)).Normal) :
    StdLinearData (H ⧸ R) (A.map (QuotientGroup.mk' R)) n ∧
      ∀ S : Sylow 2 (centralizer ((A.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) :
        Set (H ⧸ R))), Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := two_eq_zero_of_card (K := k) (by omega) hk
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
    sl2_isSimpleGroup h2 (hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n))
  have : IsSimpleGroup A := φ.isSimpleGroup
  have hnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := k)
    exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩
  have hE : ∃ E : Subgroup H, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hE4⟩ := exists_elementaryAbelian_four h2
      (hk ▸ pow_dvd_pow 2 hn : 2 ^ 2 ∣ Fintype.card k)
    set f : Multiplicative k →* H := A.subtype.comp (φ.symm.toMonoidHom.comp (sl2Upper k))
    have hf : Function.Injective f :=
      A.subtype_injective.comp (φ.symm.injective.comp sl2Upper_injective)
    have hEf : CFSG.IsElementaryAbelian 2 (E.map f) := CFSG.IsElementaryAbelian.map f
    refine ⟨E.map f, ?_, ⟨hEf.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, by rw [card_map_of_injective hf, hE4]⟩
    rintro _ ⟨x, -, rfl⟩
    exact (φ.symm (sl2Upper k x)).2
  obtain ⟨hinj, -, hθt, -, -, -, -, -, -, hstd, ⟨S₀, hS₀⟩, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab hE ht hAt hAn hsyl R hR
  refine ⟨⟨hn, hstd, hnn, k, inferInstance, inferInstance, hk, ⟨?_⟩⟩, fun S => ?_⟩
  · refine (MulEquiv.ofBijective ((QuotientGroup.mk' R).subgroupMap A) ⟨fun x y hxy => ?_,
      (QuotientGroup.mk' R).subgroupMap_surjective A⟩).symm.trans φ
    exact Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
  · rw [Nat.card_congr (Sylow.equiv S S₀).toEquiv,
      ← card_map_of_injective (subtype_injective _), hS₀, Nat.card_zpowers, hθt]

theorem layerOutcome_oddCore_quotient (hGMS : GMSLinearStandardLayerListKRankOneStatement)
    {H : Type} [Group H] [Finite H] (hH : CFSG.SectionRank.IsKGroupCat H) {A : Subgroup H}
    {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Fintype k] (hk : Fintype.card k = 2 ^ n)
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) k) {t : H} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnn : ¬ (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))).Normal) :
    LayerOutcome (H ⧸ CFSG.Open.standardComponentOddCore H)
      (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))) n := by
  have hAt : A ≤ centralizer ({t} : Set H) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htA a ha)
  obtain ⟨hstd, hsyl⟩ := stdLinearData_odd_quotient hn hk φ ht hAt hAn
    (exists_sylow_inf_centralizer_eq_zpowers ht htA hrank) _
    (odd_card_standardComponentOddCore H) hnn
  exact hGMS _ (hH.quotient _) (standardComponentOddCore_quotient_eq_bot H) n _ hstd hsyl

end CFSG.LocalAnalysis.EvenBN.GMSK
