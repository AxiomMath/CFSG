module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bDefs
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAut
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsA6
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AutoX
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AltSix
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.RankThree.PartOne.Census3 TauCeti
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

private lemma gammaCore_le_subgroupOf {L : Type} [Group L] [Finite L]
    {X₀ P₀ Y₀ : Subgroup (MulAut L)} {K Q : Subgroup ↥X₀}
    (hQ : Q ≤ P₀.subgroupOf X₀)
    (hNorm : ∀ D : Subgroup (MulAut L), D ≤ P₀ → D ≠ ⊥ →
      X₀ ⊓ Subgroup.normalizer (D : Set (MulAut L)) ≤ Y₀) :
    gammaCore 3 1 K Q ≤ Y₀.subgroupOf X₀ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨-, R, hRQ, hR, hxR⟩
  let D : Subgroup (MulAut L) := R.map X₀.subtype
  have hDle : D ≤ P₀ := by
    rintro d ⟨r, hr, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQ (hRQ hr))
  have hDne : D ≠ ⊥ := by
    intro hbot
    have h3 : 3 ∣ Nat.card R :=
      CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three hR
    have hcardD : Nat.card D = Nat.card R :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective R X₀.subtype X₀.subtype_injective).toEquiv).symm
    have hcard1 : Nat.card D = 1 := by rw [hbot, Subgroup.card_bot]
    rw [← hcardD, hcard1] at h3
    norm_num at h3
  have hxN : (x : MulAut L) ∈ Subgroup.normalizer (D : Set (MulAut L)) := by
    have hxmap : X₀.subtype x ∈
        (Subgroup.normalizer (R : Set ↥X₀)).map X₀.subtype :=
      Subgroup.mem_map_of_mem X₀.subtype hxR
    exact (Subgroup.le_normalizer_map X₀.subtype) hxmap
  exact Subgroup.mem_subgroupOf.mpr (hNorm D hDle hDne ⟨x.2, hxN⟩)

private lemma inner_conj_data {L : Type} [Group L] (hLsimple : IsSimpleGroup L)
    (hLnonab : ∃ a b : L, a * b ≠ b * a) {X₀ : Subgroup (MulAut L)}
    (hInn : (MulAut.conj : L →* MulAut L).range ≤ X₀) :
    ∃ (K : Subgroup ↥X₀) (eK : ↥K ≃* L),
      K = (MulAut.conj : L →* MulAut L).range.subgroupOf X₀ ∧ K.Normal ∧
      IsSimpleGroup ↥K ∧ (∃ a b : ↥K, a * b ≠ b * a) ∧
      Subgroup.centralizer (K : Set ↥X₀) = ⊥ := by
  classical
  letI : IsSimpleGroup L := hLsimple
  let K : Subgroup ↥X₀ := (MulAut.conj : L →* MulAut L).range.subgroupOf X₀
  have hZL : Subgroup.center L = ⊥ := by
    rcases (inferInstance : (Subgroup.center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hLnonab
      exact hab ((isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h)) a b)
  let eK : ↥K ≃* L :=
    (Subgroup.subgroupOfEquivOfLe hInn).trans
      (MonoidHom.ofInjective
        (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.conj_injective_of_center hZL)).symm
  have hKsimple : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hKnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLnonab
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    have := congrArg eK h
    simpa using this
  have hKnormal : K.Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.conj_range_normal.subgroupOf X₀
  have hKc : Subgroup.centralizer (K : Set ↥X₀) = ⊥ := by
    have hCrange :=
      CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.centralizer_conj_range_eq_bot hZL
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hx' : (x : MulAut L) ∈ Subgroup.centralizer
        ((MulAut.conj : L →* MulAut L).range : Set (MulAut L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyK : (⟨y, hInn hy⟩ : ↥X₀) ∈ K := Subgroup.mem_subgroupOf.mpr hy
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) (⟨y, hInn hy⟩ : ↥X₀) hyK
      exact congrArg Subtype.val hcomm
    rw [hCrange] at hx'
    exact Subgroup.mem_bot.mp hx'
  exact ⟨K, eK, (show K = (MulAut.conj : L →* MulAut L).range.subgroupOf X₀ from rfl),
    hKnormal, hKsimple, hKnonab, hKc⟩

private lemma gls3_conclusion_of_aut (h : Gls3StronglyThreeEmbeddedPlus)
    {L : Type} [Group L] [Finite L] (hLsimple : IsSimpleGroup L)
    (hLnonab : ∃ a b : L, a * b ≠ b * a) {X₀ P₀ Y₀ : Subgroup (MulAut L)}
    (hInn : (MulAut.conj : L →* MulAut L).range ≤ X₀)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections ↥X₀)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 P₀ X₀)
    (hE : IsElemAbelian 3 P₀) (hPcard : Nat.card P₀ = 9)
    (hNorm : ∀ D : Subgroup (MulAut L), D ≤ P₀ → D ≠ ⊥ →
      X₀ ⊓ Subgroup.normalizer (D : Set (MulAut L)) ≤ Y₀)
    (hnotY : ¬ (MulAut.conj : L →* MulAut L).range ≤ Y₀) :
    ∃ (K : Subgroup ↥X₀) (P : Sylow 3 ↥X₀),
      K = (MulAut.conj : L →* MulAut L).range.subgroupOf X₀ ∧
      (P : Subgroup ↥X₀) = P₀.subgroupOf X₀ ∧
      Nat.card (P : Subgroup ↥X₀) = 9 ∧
      IsElemAbelian 3 (P : Subgroup ↥X₀) ∧ K.Normal ∧
      Nonempty (↥K ≃* L) ∧
      Gls3ConclusionPlus ↥X₀ K (P : Subgroup ↥X₀) := by
  classical
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨K, eK, hKdef, hKnormal, hKsimple, hKnonab, hKc⟩ :=
    inner_conj_data hLsimple hLnonab hInn
  obtain ⟨P, hPdef⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hPle : (P : Subgroup ↥X₀) ≤ P₀.subgroupOf X₀ := hPdef.le
  have hPcard9 : Nat.card (P : Subgroup ↥X₀) = 9 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSyl.le).toEquiv, hPcard]
  have hPea : IsElemAbelian 3 (P : Subgroup ↥X₀) := by
    rw [hPdef]
    exact hE.subgroupOf X₀
  have hrank : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup ↥X₀) := by
    refine CFSG.SectionRank.le_pRank (G := ↥X₀) (H := (P : Subgroup ↥X₀))
      (E := (P : Subgroup ↥X₀)) (p := 3) (by norm_num) le_rfl hPea (k := 2) ?_
    rw [hPcard9]
    norm_num
  have hYlt : Y₀.subgroupOf X₀ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hnotY
    intro x hx
    have hx' : (⟨x, hInn hx⟩ : ↥X₀) ∈ Y₀.subgroupOf X₀ := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  have hΓX : gammaCore 3 1 ⊤ (P : Subgroup ↥X₀) < ⊤ :=
    lt_of_le_of_lt (gammaCore_le_subgroupOf (K := ⊤) (Q := (P : Subgroup ↥X₀)) hPle hNorm) hYlt
  have hconc := h ↥X₀ (CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp hcat)
    K hKnormal hKsimple hKnonab hKc P hrank hΓX
  exact ⟨K, P, hKdef, hPdef, hPcard9, hPea, hKnormal, ⟨eK⟩, hconc⟩

private lemma card_dvd_gamma_mul_index {X : Type} [Group X] [Finite X]
    {K Y : Subgroup X} (hK : K.Normal) {Γ : Subgroup X} (hΓ : Γ = Y ⊓ K) :
    Nat.card Y ∣ Nat.card Γ * K.index := by
  letI : K.Normal := hK
  have hΓleY : Γ ≤ Y := hΓ.le.trans inf_le_left
  have hcard : Nat.card Y = Γ.relIndex Y * Nat.card Γ := by
    have h := Subgroup.relIndex_mul_card Γ Y
    rw [inf_of_le_left hΓleY] at h
    exact h.symm
  have hrel : Γ.relIndex Y = K.relIndex Y := by
    rw [hΓ]
    exact Subgroup.inf_relIndex_left Y K
  have hdvd : K.relIndex Y ∣ K.index := by
    rw [show K.relIndex Y = K.relIndex (Y ⊔ K) from
      (Subgroup.relIndex_sup_right Y K).symm]
    exact Subgroup.relIndex_dvd_index_of_le (le_sup_right : K ≤ Y ⊔ K)
  have hrel_dvd : Γ.relIndex Y ∣ K.index := hrel ▸ hdvd
  rw [hcard, Nat.mul_comm (Γ.relIndex Y) (Nat.card Γ)]
  exact Nat.mul_dvd_mul_left _ hrel_dvd

private lemma alt6_pow_five_image_three :
    ∀ (g : Equiv.Perm (Fin 6)), g ^ 5 = 1 → g ≠ 1 → ∀ A : Finset (Fin 6), A.card = 3 →
      A.image g ≠ A ∧ A.image g ≠ Aᶜ := by
  decide +kernel

private lemma not_five_dvd_card_gamma_of_partition {X : Type} [Group X] [Finite X]
    {K Γ : Subgroup X} (hΓK : Γ ≤ K)
    {φ : ↥K ≃* alternatingGroup (Fin 6)} {A : Finset (Fin 6)} (hAcard : A.card = 3)
    (hmem : ∀ k : ↥K, (k : X) ∈ Γ ↔
      A.image (φ k : Equiv.Perm (Fin 6)) = A ∨
        A.image (φ k : Equiv.Perm (Fin 6)) = Aᶜ) :
    ¬ 5 ∣ Nat.card Γ := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := Γ) 5 h5
  let k : ↥K := Subgroup.inclusion hΓK g
  have hkord : orderOf k = 5 := by
    rw [← hgord]
    exact orderOf_injective (Subgroup.inclusion hΓK) (Subgroup.inclusion_injective hΓK) g
  have hφord : orderOf (φ k) = 5 := by
    rw [MulEquiv.orderOf_eq, hkord]
  have hpermord : orderOf (φ k : Equiv.Perm (Fin 6)) = 5 := by
    change orderOf ((alternatingGroup (Fin 6)).subtype (φ k)) = 5
    rw [orderOf_injective (alternatingGroup (Fin 6)).subtype
      (alternatingGroup (Fin 6)).subtype_injective (φ k)]
    exact hφord
  have hpow : (φ k : Equiv.Perm (Fin 6)) ^ 5 = 1 := by
    rw [← hpermord]
    exact pow_orderOf_eq_one _
  have hne : (φ k : Equiv.Perm (Fin 6)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hpermord
    norm_num at hpermord
  have hmemk : (k : X) ∈ Γ := by
    rw [Subgroup.coe_inclusion]
    exact g.2
  have hpart := (hmem k).mp hmemk
  have hnot := alt6_pow_five_image_three
    (φ k : Equiv.Perm (Fin 6)) hpow hne A hAcard
  rcases hpart with h | h
  · exact hnot.1 h
  · exact hnot.2 h

private lemma row_A1_false {X : Type} [Group X] {K P : Subgroup X} {q : PrimePower}
    (hPcard : Nat.card P = 9) (hq3 : q.p = 3) (hv : (LieTypeIndex.A 1 q).Valid)
    (hQcard : Nat.card (P ⊓ K : Subgroup X) = q.card) : False := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hPcard]; norm_num)
  have hle : q.card ≤ 9 := by
    rw [← hQcard, ← hPcard]
    exact Subgroup.card_le_of_le inf_le_left
  have hgt := gt_nine_of_valid_A1 hq3 hv
  omega

private lemma row_twistedA_false {X : Type} [Group X] {K P : Subgroup X}
    (hPea : IsElemAbelian 3 P)
    (hQnab : ¬ (∀ a ∈ P ⊓ K, ∀ b ∈ P ⊓ K, a * b = b * a)) : False :=
  hQnab fun a ha b hb =>
    hPea.comm ((inf_le_left : P ⊓ K ≤ P) ha) ((inf_le_left : P ⊓ K ≤ P) hb)

private lemma row_reeG2_false {X : Type} [Group X] {K P E : Subgroup X} {m : ℕ}
    (hPcard : Nat.card P = 9) (hEQ : E ≤ P ⊓ K)
    (hEcard : Nat.card E = 3 ^ (2 * m + 1))
    (hv : (LieTypeIndex.reeG2 m).Valid) : False := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hPcard]; norm_num)
  have hm := one_le_of_valid_reeG2 hv
  have hcardle : Nat.card E ≤ Nat.card P :=
    Subgroup.card_le_of_le (hEQ.trans inf_le_left)
  have h27 : 27 ≤ Nat.card E := by
    rw [hEcard]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private lemma row_L2_8_false {X : Type} [Group X] {P : Subgroup X}
    (hPcard : Nat.card P = 9) (hP27 : Nat.card P = 27) : False := by
  omega

private lemma row_A6_gamma_primes {X : Type} [Group X] [Finite X] {K P : Subgroup X}
    (hΓK : gammaCore 3 1 K (P ⊓ K) ≤ K)
    {φ : ↥K ≃* alternatingGroup (Fin 6)} {A : Finset (Fin 6)} (hAcard : A.card = 3)
    (hmem : ∀ k : ↥K, (k : X) ∈ gammaCore 3 1 K (P ⊓ K) ↔
      A.image (φ k : Equiv.Perm (Fin 6)) = A ∨
        A.image (φ k : Equiv.Perm (Fin 6)) = Aᶜ)
    {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card (gammaCore 3 1 K (P ⊓ K))) : r = 2 ∨ r = 3 := by
  have hno5 := not_five_dvd_card_gamma_of_partition hΓK hAcard hmem
  have hKcard : Nat.card K = 360 := by
    rw [Nat.card_congr φ.toEquiv,
      CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.alt6_A6_card]
  have hrK : r ∣ Nat.card K := hrdvd.trans (Subgroup.card_dvd_of_le hΓK)
  have hr360 : r ∣ 360 := by rwa [hKcard] at hrK
  have h360 : r ∣ 2 ^ 3 * (3 ^ 2 * 5) := by
    rwa [show 2 ^ 3 * (3 ^ 2 * 5) = 360 by norm_num]
  rcases hr.dvd_mul.mp h360 with h2 | h35
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  rcases hr.dvd_mul.mp h35 with h3 | h5
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3))
  · exfalso
    rw [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h5] at hrdvd
    exact hno5 hrdvd

private lemma row_L34_gamma_primes {X : Type} [Group X] [Finite X] {K P : Subgroup X}
    (hΓN : gammaCore 3 1 K (P ⊓ K) =
      K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X))
    (hQcard : Nat.card (P ⊓ K : Subgroup X) = 9) {S : Subgroup X}
    (hSΓ : S ≤ gammaCore 3 1 K (P ⊓ K)) (hQS : (P ⊓ K : Subgroup X) ⊓ S = ⊥)
    (hsup : (P ⊓ K : Subgroup X) ⊔ S = gammaCore 3 1 K (P ⊓ K))
    (hQ8 : Nonempty (↥S ≃* QuaternionGroup 2))
    {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card (gammaCore 3 1 K (P ⊓ K))) : r = 2 ∨ r = 3 := by
  have hSnormal : S ≤ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) :=
    hSΓ.trans (hΓN.le.trans inf_le_right)
  have hS8 : Nat.card S = 8 := by
    obtain ⟨e⟩ := hQ8
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hΓcard : Nat.card (gammaCore 3 1 K (P ⊓ K)) = 72 := by
    rw [← hsup, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (P ⊓ K) S hSnormal (disjoint_iff.mpr hQS), hQcard, hS8]
  have hr72 : r ∣ 2 ^ 3 * 3 ^ 2 := by
    rw [show 2 ^ 3 * 3 ^ 2 = 72 by norm_num, ← hΓcard]
    exact hrdvd
  rcases hr.dvd_mul.mp hr72 with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3))

private lemma row_M11_gamma_primes {X : Type} [Group X] [Finite X] {K P : Subgroup X}
    (hQea : IsElemAbelian 3 (P ⊓ K)) (hQcard : Nat.card (P ⊓ K : Subgroup X) = 9)
    (hΓN : gammaCore 3 1 K (P ⊓ K) =
      K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X))
    {S : Subgroup X} (hSΓ : S ≤ gammaCore 3 1 K (P ⊓ K))
    (hsup : (P ⊓ K : Subgroup X) ⊔ S = gammaCore 3 1 K (P ⊓ K)) (hS16 : Nat.card S = 16)
    (hC : S ⊓ Subgroup.centralizer ((P ⊓ K : Subgroup X) : Set X) = ⊥)
    {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card (gammaCore 3 1 K (P ⊓ K))) : r = 2 ∨ r = 3 := by
  have hSnormal : S ≤ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) :=
    hSΓ.trans (hΓN.le.trans inf_le_right)
  have hQS : (P ⊓ K : Subgroup X) ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ Subgroup.centralizer ((P ⊓ K : Subgroup X) : Set X) := by
      letI : IsMulCommutative (P ⊓ K : Subgroup X) := hQea.1
      exact (Subgroup.le_centralizer (H := (P ⊓ K : Subgroup X))) hx.1
    have : x ∈ S ⊓ Subgroup.centralizer ((P ⊓ K : Subgroup X) : Set X) := ⟨hx.2, hxQ⟩
    rwa [hC] at this
  have hΓcard : Nat.card (gammaCore 3 1 K (P ⊓ K)) = 144 := by
    rw [← hsup, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (P ⊓ K) S hSnormal (disjoint_iff.mpr hQS), hQcard, hS16]
  have hr144 : r ∣ 2 ^ 4 * 3 ^ 2 := by
    rw [show 2 ^ 4 * 3 ^ 2 = 144 by norm_num, ← hΓcard]
    exact hrdvd
  rcases hr.dvd_mul.mp hr144 with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3))

private lemma gamma_primes_of_gls3 {X : Type} [Group X] [Finite X] {K P : Subgroup X}
    (hconc : Gls3ConclusionPlus X K P) (hPcard : Nat.card P = 9)
    (hPea : IsElemAbelian 3 P) {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card (gammaCore 3 1 K (P ⊓ K))) : r = 2 ∨ r = 3 := by
  obtain ⟨hΓlt, -, hrows⟩ := hconc
  have hΓK : gammaCore 3 1 K (P ⊓ K) ≤ K := hΓlt.le
  rcases hrows with
    ⟨q, hq3, ⟨hv, -⟩, -, -, -, -, hQcard⟩ |
    ⟨q, hq3, ⟨hv, -⟩, -, -, -, hQnab, -, -, -, -, -⟩ |
    ⟨m, ⟨hv, -⟩, -, -, -, E, hEQ, -, hEcard⟩ |
    ⟨-, -, -, -, -, -, hP27, -⟩ |
    ⟨⟨φ, A, hAcard, hmem⟩, -, -, -, -, -, -, -, -⟩ |
    ⟨-, ⟨k, hk⟩, -, hQea, hQcard, hΓN, S, hSΓ, hQS, hsup, hQ8, -⟩ |
    ⟨-, hKtop, hQea, hQcard, hΓN, S, hSΓ, hsup, hS16, -, hC, -⟩
  · exact (row_A1_false hPcard hq3 hv hQcard).elim
  · exact (row_twistedA_false hPea hQnab).elim
  · exact (row_reeG2_false hPcard hEQ hEcard hv).elim
  · exact (row_L2_8_false hPcard hP27).elim
  · exact row_A6_gamma_primes hΓK hAcard hmem hr hrdvd
  · exact row_L34_gamma_primes hΓN hQcard hSΓ hQS hsup hQ8 hr hrdvd
  · exact row_M11_gamma_primes hQea hQcard hΓN hSΓ hsup hS16 hC hr hrdvd

private lemma row_A6_index_primes {L : Type} [Group L] {X₀ : Subgroup (MulAut L)}
    {K : Subgroup ↥X₀} {φ : ↥K ≃* alternatingGroup (Fin 6)} (eK : ↥K ≃* L)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ K.index) : r = 2 ∨ r = 3 := by
  have hKcard : Nat.card K = 360 := by
    rw [Nat.card_congr φ.toEquiv,
      CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.alt6_A6_card]
  have eL : L ≃* alternatingGroup (Fin 6) := eK.symm.trans φ
  have hAutL : Nat.card (MulAut L) ∣ 1440 := by
    have hcongr : Nat.card (MulAut L) =
        Nat.card (MulAut (alternatingGroup (Fin 6))) :=
      Nat.card_congr (MulAut.congr eL).toEquiv
    rw [hcongr]
    exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactAutA6_holds
  have hX0dvd : Nat.card ↥X₀ ∣ 1440 := by
    have h1 : Nat.card ↥X₀ ∣ Nat.card (MulAut L) := by
      simpa using Subgroup.card_dvd_of_le (le_top : X₀ ≤ (⊤ : Subgroup (MulAut L)))
    exact h1.trans hAutL
  have hmul : K.index * Nat.card K = Nat.card ↥X₀ :=
    Subgroup.index_mul_card (G := ↥X₀) (H := K)
  have hdvd4 : K.index ∣ 4 := by
    have h := hX0dvd
    rw [← hmul, hKcard] at h
    have h' : 360 * K.index ∣ 360 * 4 := by
      rw [Nat.mul_comm 360 K.index]
      rwa [show (1440 : ℕ) = 360 * 4 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
  have hr4 : r ∣ 4 := hrdvd.trans hdvd4
  have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow (n := 2) (by simpa using hr4)
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr2)

private lemma row_L34_index_primes {X : Type} [Group X] {K : Subgroup X} {r : ℕ}
    (hr : r.Prime) (hk : ∃ k : ℕ, K.index = 2 ^ k) (hrdvd : r ∣ K.index) :
    r = 2 ∨ r = 3 := by
  obtain ⟨k, hk⟩ := hk
  have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow (by rwa [hk] at hrdvd)
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr2)

private lemma row_M11_index_primes {X : Type} [Group X] {K : Subgroup X} {r : ℕ}
    (hr : r.Prime) (hKtop : K = ⊤) (hrdvd : r ∣ K.index) : r = 2 ∨ r = 3 := by
  rw [hKtop, Subgroup.index_top] at hrdvd
  exact (hr.not_dvd_one hrdvd).elim

private lemma index_primes_of_gls3 {L : Type} [Group L] [Finite L]
    {X₀ : Subgroup (MulAut L)} {K P : Subgroup ↥X₀}
    (hconc : Gls3ConclusionPlus ↥X₀ K P) (hPcard : Nat.card P = 9)
    (hPea : IsElemAbelian 3 P) (eK : ↥K ≃* L)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ K.index) : r = 2 ∨ r = 3 := by
  obtain ⟨-, -, hrows⟩ := hconc
  rcases hrows with
    ⟨q, hq3, ⟨hv, -⟩, -, -, -, -, hQcard⟩ |
    ⟨q, hq3, ⟨hv, -⟩, -, -, -, hQnab, -, -, -, -, -⟩ |
    ⟨m, ⟨hv, -⟩, -, -, -, E, hEQ, -, hEcard⟩ |
    ⟨-, -, -, -, -, -, hP27, -⟩ |
    ⟨⟨φ, A, -, -⟩, -, -, -, -, -, -, -, -⟩ |
    ⟨-, ⟨k, hk⟩, -, -, -, -, -, -, -, -, -, -⟩ |
    ⟨-, hKtop, -, -, -, -, -, -, -, -, -, -⟩
  · exact (row_A1_false hPcard hq3 hv hQcard).elim
  · exact (row_twistedA_false hPea hQnab).elim
  · exact (row_reeG2_false hPcard hEQ hEcard hv).elim
  · exact (row_L2_8_false hPcard hP27).elim
  · exact row_A6_index_primes (φ := φ) eK hr hrdvd
  · exact row_L34_index_primes hr ⟨k, hk⟩ hrdvd
  · exact row_M11_index_primes hr hKtop hrdvd

theorem kFactE9AutTwoThree_of_gls3
    (h : Gls3StronglyThreeEmbeddedPlus) :
    KFactE9AutTwoThree := by
  classical
  intro L _ _ hLsimple hLnonab X₀ P₀ Y₀ hInn hcat hSyl hE hPcard hYX hNorm hnotY r hr hrdvd
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨K, P, hKdef, hPdef, hPcard9, hPea, hKnormal, ⟨eK⟩, hconc⟩ :=
    gls3_conclusion_of_aut h hLsimple hLnonab hInn hcat hSyl hE hPcard hNorm hnotY
  let Y' : Subgroup ↥X₀ := Y₀.subgroupOf X₀
  have hYcard : Nat.card Y' = Nat.card Y₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
  have hΓleY : gammaCore 3 1 K ((P : Subgroup ↥X₀) ⊓ K) ≤ Y' :=
    gammaCore_le_subgroupOf (K := K) (Q := (P : Subgroup ↥X₀) ⊓ K)
      (inf_le_left.trans hPdef.le) hNorm
  have hYlt : Y' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hnotY
    intro x hx
    have hx' : (⟨x, hInn hx⟩ : ↥X₀) ∈ Y' := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  have hYKlt : Y' ⊓ K < K := by
    rw [lt_iff_le_and_ne]
    refine ⟨inf_le_right, fun heq => ?_⟩
    apply hnotY
    intro x hx
    have hxK : (⟨x, hInn hx⟩ : ↥X₀) ∈ K := by
      rw [hKdef]
      exact Subgroup.mem_subgroupOf.mpr hx
    have hKY : K ≤ Y' := by rw [← heq]; exact inf_le_left
    exact Subgroup.mem_subgroupOf.mp (hKY hxK)
  have hconc' := hconc
  obtain ⟨hΓlt, hΓmax, -⟩ := hconc'
  have hΓeq : gammaCore 3 1 K ((P : Subgroup ↥X₀) ⊓ K) = Y' ⊓ K := by
    by_contra hne
    have hlt : gammaCore 3 1 K ((P : Subgroup ↥X₀) ⊓ K) < Y' ⊓ K :=
      lt_of_le_of_ne (le_inf hΓleY hΓlt.le) hne
    exact hYKlt.ne (hΓmax (Y' ⊓ K) hlt inf_le_right)
  have hdvd : r ∣ Nat.card (gammaCore 3 1 K ((P : Subgroup ↥X₀) ⊓ K)) ∨ r ∣ K.index := by
    have hprod : r ∣ Nat.card (gammaCore 3 1 K ((P : Subgroup ↥X₀) ⊓ K)) * K.index :=
      (by rwa [hYcard] : r ∣ Nat.card Y').trans
        (card_dvd_gamma_mul_index hKnormal hΓeq)
    exact hr.dvd_mul.mp hprod
  rcases hdvd with hΓ | hidx
  · exact gamma_primes_of_gls3 hconc hPcard9 hPea hr hΓ
  · exact index_primes_of_gls3 hconc hPcard9 hPea eK hr hidx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
