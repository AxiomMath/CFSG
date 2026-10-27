module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KSylowTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

@[expose] def InnerOnKAt (M : Subgroup G) : Prop :=
  ∀ E H : Subgroup G, HypCGen G M 3 E H → CaseThree M H → ∀ e ∈ E, ∃ k ∈ kSub 3 M H,
    ∀ x ∈ kSub 3 M H, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype

theorem mem_of_sylow_map_le {M Y U : Subgroup G} (hUleM : U ≤ M)
    (hYSyl : CFSG.ABGLocalTools.IsSylowOf 3 Y U)
    (hNY : Subgroup.normalizer (Y : Set G) ≤ M) {n : G}
    (hYmap : Y.map (MulAut.conj n).toMonoidHom ≤ U) : n ∈ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYSyl' : CFSG.ABGLocalTools.IsSylowOf 3 (Y.map (MulAut.conj n).toMonoidHom) U :=
    CFSG.ABGLocalTools.isSylowOf_of_card hYmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hYSyl.card_eq])
  obtain ⟨u, huU, hconju⟩ := hYSyl.exists_mem_conj hYSyl'
  have hnrm : u⁻¹ * n ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hx : (MulAut.conj n) y ∈ Y.map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      have h := (hconju ((MulAut.conj n) y)).mp hx
      convert h using 1
      rw [MulAut.conj_apply]
      group
    · intro hy
      have hx : u⁻¹ * ((MulAut.conj n) y) * u ∈ Y := by
        convert hy using 1
        rw [MulAut.conj_apply]
        group
      have hmem : (MulAut.conj n) y ∈ Y.map (MulAut.conj n).toMonoidHom :=
        (hconju ((MulAut.conj n) y)).mpr hx
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
      have hzy' : z = y := (MulAut.conj n).injective hzy
      rwa [hzy'] at hz
  have huM : u ∈ M := hUleM huU
  have hres : u⁻¹ * n ∈ M := hNY hnrm
  have hnM : n = u * (u⁻¹ * n) := by group
  rw [hnM]
  exact M.mul_mem huM hres

@[expose] def NineNineOneAt (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H →
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M q

namespace HypCGen

variable {M E H P : Subgroup G}

theorem nonempty_mulEquiv_threeStar {M H : Subgroup G} (hC3 : CaseThree M H) :
    Nonempty (threeStar (kSub 3 M H) ≃* projSL 3 (GaloisField 2 2)) :=
  nonempty_mulEquiv_projSL_of_isL34Type hC3.2.1 hC3.2.2

theorem isSylowOf_inf_kSub (h : HypCGen G M 3 E H) (hK : KNormalAt M)
    (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ kSub 3 M H) (kSub 3 M H) := by
  have hp : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet
  have hPH : CFSG.ABGLocalTools.IsSylowOf 3 P H :=
    (isSylowOf_of_NineNineOne h.maxLocal h.mem_QSet h.E_le_H hp hU hP).1
  exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPH (kSub_le 3 M H)
    (hK 3 E H h)

theorem card_inf_kSub (h : HypCGen G M 3 E H) (hC3 : CaseThree M H) (hK : KNormalAt M)
    (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) :
    Nat.card ((P ⊓ kSub 3 M H : Subgroup G)) = 9 :=
  card_eq_nine_of_isSylowOf (nonempty_mulEquiv_threeStar hC3)
    (isSylowOf_inf_kSub h hK hU hP)

theorem isElemAbelian_inf_kSub (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) :
    CFSG.Open.IsElemAbelian 3 (P ⊓ kSub 3 M H) :=
  isElemAbelian_of_isSylowOf (nonempty_mulEquiv_threeStar hC3)
    (isSylowOf_inf_kSub h hK hU hP)

theorem centralizer_le_of_mem {M E H : Subgroup G} {q : ℕ} (h : HypCGen G M q E H)
    {d : G} (hdE : d ∈ E) (hd1 : d ≠ 1) : Subgroup.centralizer ({d} : Set G) ≤ M := by
  haveI : Fact q.Prime := ⟨h.prime⟩
  have hdq : d ^ q = 1 := h.elem.2 d hdE
  have hElem : CFSG.Open.IsElemAbelian q (Subgroup.zpowers d) :=
    CFSG.Open.isElemAbelian_zpowers hdq
  have hcard : Nat.card (Subgroup.zpowers d) = q ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hdq hd1, pow_one]
  have hrank : 1 ≤ CFSG.Open.pRank q (Subgroup.zpowers d) :=
    CFSG.SectionRank.le_pRank h.prime.one_lt le_rfl hElem hcard
  have hgamma : Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
      CFSG.Open.rankThreeGamma 1 q E :=
    CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 q E (Subgroup.zpowers d)
      (Subgroup.zpowers_le.mpr hdE) hrank
  rw [← Subgroup.centralizer_closure ({d} : Set G), ← Subgroup.zpowers_eq_closure]
  exact (Subgroup.centralizer_le_normalizer (Subgroup.zpowers d : Set G)).trans
    (hgamma.trans h.gamma)

theorem pPrimeCore_map_le (h : HypCGen G M 3 E H) (hK : KNormalAt M) :
    (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype ≤ M :=
  (pPrimeCore_map_le_relPPrimeCore (p := 3) (K := kSub 3 M H) (H := H)
    (kSub_le 3 M H) (hK 3 E H h)).trans (HypCGen.relPPrimeCore_le h)


theorem centralizes_inf_kSub (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P) :
    ∀ e ∈ E, ∀ a ∈ P ⊓ kSub 3 M H, e * a * e⁻¹ = a := by
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [A, K] using isSylowOf_inf_kSub h hK hU hP
  intro e he a ha
  have heP : e ∈ P := hEP he
  have heH : e ∈ H := (hP.le heP).1
  have hKe : e ∈ Subgroup.normalizer (K : Set G) := by
    simpa [K] using hK 3 E H h heH
  have heA : ∀ x ∈ A, e * x * e⁻¹ ∈ A := by
    intro x hx
    refine ⟨P.mul_mem (P.mul_mem heP hx.1) (P.inv_mem heP), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp hKe x).mp hx.2
  obtain ⟨k, hk, hek⟩ := hI E H h hC3 e he
  have hkK : k ∈ K := hk
  have hekK : ∀ x ∈ K, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype := hek
  have he3 : e ^ 3 = 1 := h.elem.2 e he
  have hekA : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype := fun x hx => hekK x ((inf_le_right : A ≤ K) hx)
  exact (exists_mem_and_commute_of_inner (nonempty_mulEquiv_threeStar hC3) hAsyl hkK he3 heA
    hekA).2 a ha

theorem exists_ne_one_mem_inf (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P) :
    ∃ d ∈ E ⊓ (P ⊓ kSub 3 M H), d ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [A, K] using isSylowOf_inf_kSub h hK hU hP
  have hElemA : CFSG.Open.IsElemAbelian 3 A := by
    simpa [A, K] using isElemAbelian_inf_kSub h hC3 hK hU hP
  have hcent := centralizes_inf_kSub h hC3 hK hU hI hP hEP
  have hcomm : ∀ a ∈ E, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h := hcent a ha b hb
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h]
  have hElemY : CFSG.Open.IsElemAbelian 3 (E ⊔ A : Subgroup G) :=
    CFSG.Open.IsElemAbelian.sup_of_commute h.elem hElemA hcomm
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E A hcomm).1
  have hE9 : Nat.card E = 9 := by simpa using h.card
  have hA9 : Nat.card A = 9 := by
    simpa [A, K] using card_inf_kSub h hC3 hK hU hP
  by_contra hcon
  have hcon' : ∀ d, d ∈ E ⊓ A → d = 1 := by
    intro d hd
    by_contra hd1
    exact hcon ⟨d, hd, hd1⟩
  have hbot : E ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    exact hcon' d hd
  have hY81 : Nat.card (E ⊔ A : Subgroup G) = 81 := by
    rw [hbot, Subgroup.card_bot, mul_one, hE9, hA9] at hcard
    exact hcard
  have hYcard : Nat.card (E ⊔ A : Subgroup G) = 3 ^ 4 := by
    rw [hY81]; norm_num
  have hYH : E ⊔ A ≤ H :=
    sup_le h.E_le_H (le_trans inf_le_left (hP.le.trans inf_le_left))
  have h4 : 4 ≤ CFSG.Open.pRank 3 H :=
    CFSG.SectionRank.le_pRank (p := 3) (k := 4) (by norm_num) hYH hElemY hYcard
  have h3le : CFSG.Open.pRank 3 H ≤ 3 :=
    h.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num) h.not_mem_sigmaA
      h.isTwoLocal
  exact absurd h4 (by omega)

theorem normalizes_pPrimeCore_map_of_inner (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P) :
    E ⊔ (P ⊓ kSub 3 M H) ≤ Subgroup.normalizer
      ((CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  let OK : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hOKconj : ∀ k ∈ K, ∀ x ∈ OK, k * x * k⁻¹ ∈ OK := by
    intro k hk x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem K.subtype
      ((CFSG.pPrimeCore_normal (p := 3) (G := ↥K)).conj_mem n hn ⟨k, hk⟩)
  have hconjE : ∀ e' ∈ E, ∀ y ∈ OK, e' * y * e'⁻¹ ∈ OK := by
    intro e' he' y hy
    obtain ⟨k, hk, hek⟩ := hI E H h hC3 e' he'
    have hyK : y ∈ K := Subgroup.map_subtype_le _ hy
    have h1 : (k * y * k⁻¹)⁻¹ * (e' * y * e'⁻¹) ∈ OK := hek y hyK
    have h2 : k * y * k⁻¹ ∈ OK := hOKconj k hk y hy
    rw [show e' * y * e'⁻¹ =
      (k * y * k⁻¹) * ((k * y * k⁻¹)⁻¹ * (e' * y * e'⁻¹)) by group]
    exact OK.mul_mem h2 h1
  have hEnorm : E ≤ Subgroup.normalizer (OK : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjE e he x
    · intro hx
      have h := hconjE e⁻¹ (E.inv_mem he) (e * x * e⁻¹) hx
      have h' : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ = x := by group
      rwa [h'] at h
  have hAnorm : A ≤ Subgroup.normalizer (OK : Set G) := by
    intro a ha
    have haK : a ∈ K := by simpa [A] using (Subgroup.mem_inf.mp ha).2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hOKconj a haK x
    · intro hx
      have h := hOKconj a⁻¹ (K.inv_mem haK) (a * x * a⁻¹) hx
      have h' : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x := by group
      rwa [h'] at h
  exact sup_le hEnorm hAnorm

theorem exists_sylow_stepThree (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P) :
    ∃ Y U : Subgroup G,
      Y = E ⊔ (P ⊓ kSub 3 M H) ∧
      U = Y ⊔ (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype ∧
      U ≤ M ∧
      Nat.card U = Nat.card Y *
        Nat.card ((CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 Y U ∧
      Subgroup.normalizer (Y : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  let OK : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hElemA : CFSG.Open.IsElemAbelian 3 A := by
    simpa [A, K] using isElemAbelian_inf_kSub h hC3 hK hU hP
  have hcent := centralizes_inf_kSub h hC3 hK hU hI hP hEP
  have hOle : OK ≤ M := by
    simpa [OK, K] using pPrimeCore_map_le h hK
  have hYnorm : E ⊔ A ≤ Subgroup.normalizer (OK : Set G) := by
    simpa [A, K, OK] using normalizes_pPrimeCore_map_of_inner h hC3 hI hP hEP
  have hElemY : CFSG.Open.IsElemAbelian 3 (E ⊔ A) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute h.elem hElemA ?_
    intro a ha b hb
    have hh := hcent a ha b hb
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [hh]
  have hY3 : IsPGroup 3 (E ⊔ A : Subgroup G) := hElemY.isPGroup
  obtain ⟨kY, hYk⟩ := hY3.exists_card_eq
  have hOKcard : Nat.card OK = Nat.card (CFSG.pPrimeCore 3 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hOKcop : Nat.Coprime (Nat.card OK) 3 := by
    rw [hOKcard]
    exact Nat.Coprime.symm (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
  have hdisj : Disjoint OK (E ⊔ A) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hYk]
    exact hOKcop.pow_right kY
  have hYleM : E ⊔ A ≤ M :=
    sup_le h.E_le_M (le_trans inf_le_left (hP.le.trans inf_le_right))
  have hUleM : ((E ⊔ A) ⊔ OK : Subgroup G) ≤ M := sup_le hYleM hOle
  have hcardU : Nat.card (((E ⊔ A) ⊔ OK : Subgroup G)) =
      Nat.card (E ⊔ A : Subgroup G) * Nat.card OK := by
    rw [sup_comm,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer OK (E ⊔ A)
        hYnorm hdisj,
      mul_comm]
  have h3notdvd : ¬ 3 ∣ Nat.card OK :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hOKcop.symm
  have hUfac : (Nat.card (((E ⊔ A) ⊔ OK : Subgroup G))).factorization 3 = kY := by
    rw [hcardU, Nat.factorization_mul (Nat.card_pos (α := (E ⊔ A : Subgroup G))).ne'
      (Nat.card_pos (α := OK)).ne', Finsupp.add_apply, hYk,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd h3notdvd]
    simp
  have hYSyl : CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ A) ((E ⊔ A) ⊔ OK) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left (by rw [hUfac, hYk])
  have hNY : Subgroup.normalizer ((E ⊔ A : Subgroup G) : Set G) ≤ M :=
    NineNineOne.normalizer_le h.maxLocal hU h.E_le_M h.elem h.card h.gamma le_sup_left hYleM
  exact ⟨E ⊔ A, (E ⊔ A) ⊔ OK, rfl, rfl, hUleM, hcardU, hYSyl, hNY⟩

theorem exists_mem_pPrimeCore_map_of_inner (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P)
    {e : G} (he : e ∈ E) :
    ∃ (k a₀ : ↥(kSub 3 M H)),
      (a₀ : G) ∈ P ⊓ kSub 3 M H ∧
      a₀⁻¹ * (k : G) ∈ (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype ∧
      ∀ x ∈ kSub 3 M H, ((k : G) * x * (k : G)⁻¹)⁻¹ * (e * x * e⁻¹) ∈
        (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  let OK : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [A, K] using isSylowOf_inf_kSub h hK hU hP
  obtain ⟨k, hk, hek⟩ := hI E H h hC3 e he
  have heP : e ∈ P := hEP he
  have heH : e ∈ H := (hP.le heP).1
  have hKe : e ∈ Subgroup.normalizer (K : Set G) := by simpa [K] using hK 3 E H h heH
  have heA : ∀ x ∈ A, e * x * e⁻¹ ∈ A := by
    intro x hx
    refine ⟨P.mul_mem (P.mul_mem heP hx.1) (P.inv_mem heP), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp hKe x).mp hx.2
  have hekA : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈ OK := by
    intro x hx
    exact hek x (by simpa [A] using (Subgroup.mem_inf.mp hx).2)
  obtain ⟨⟨a₀, ha₀, hkO⟩, -⟩ :=
    exists_mem_and_commute_of_inner (nonempty_mulEquiv_threeStar hC3) hAsyl hk
      (h.elem.2 e he) heA hekA
  have ha₀K : a₀ ∈ K := by simpa [A] using (Subgroup.mem_inf.mp ha₀).2
  exact ⟨⟨k, hk⟩, ⟨a₀, ha₀K⟩, by simpa [A, K] using ha₀,
    by simpa [OK, K] using hkO, by simpa [OK, K] using hek⟩

theorem exists_quotient_conj_inner_eq (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P)
    {n : G}
    (hn : n ∈ Subgroup.normalizer ((P ⊓ kSub 3 M H : Subgroup G) : Set G) ⊓ kSub 3 M H)
    {e : G} (he : e ∈ E) :
    ∃ (c a : ↥(kSub 3 M H)),
      (c : G) = n * (e * n⁻¹ * e⁻¹) ∧
      (a : G) ∈ P ⊓ kSub 3 M H ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) c =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  let OK : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [A, K] using isSylowOf_inf_kSub h hK hU hP
  have hnK : n ∈ K := hn.2
  have hnN : n ∈ Subgroup.normalizer (A : Set G) := hn.1
  obtain ⟨kK, a₀K, ha₀K, hkOK, hekK⟩ :=
    exists_mem_pPrimeCore_map_of_inner h hC3 hK hU hI hP hEP he
  let k : G := kK
  have hk : k ∈ K := kK.2
  let a₀ : G := a₀K
  have ha₀ : a₀ ∈ A := by simpa [a₀, A, K] using ha₀K
  have hkO : a₀⁻¹ * k ∈ OK := by simpa [a₀, k, OK, K] using hkOK
  have hek : ∀ x ∈ K, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈ OK := by
    intro x hx
    simpa [k, OK, K] using hekK x (by simpa [K] using hx)
  have hyOK : (k * n⁻¹ * k⁻¹)⁻¹ * (e * n⁻¹ * e⁻¹) ∈ OK := hek (n⁻¹) (K.inv_mem hnK)
  have hyK : (k * n⁻¹ * k⁻¹)⁻¹ * (e * n⁻¹ * e⁻¹) ∈ K := Subgroup.map_subtype_le _ hyOK
  let yK : ↥K := ⟨(k * n⁻¹ * k⁻¹)⁻¹ * (e * n⁻¹ * e⁻¹), hyK⟩
  have hπy : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) yK = 1 :=
    (pPrimeCore_quotient_eq_one_of_mem_map (K := K) (hyK := hyK) (by simpa [OK, K] using hyOK))
  have hcK : n * (e * n⁻¹ * e⁻¹) ∈ K := by
    have h1 : n * (k * n⁻¹ * k⁻¹) ∈ K :=
      K.mul_mem hnK (K.mul_mem (K.mul_mem hk (K.inv_mem hnK)) (K.inv_mem hk))
    rw [show n * (e * n⁻¹ * e⁻¹) =
      (n * (k * n⁻¹ * k⁻¹)) * ((k * n⁻¹ * k⁻¹)⁻¹ * (e * n⁻¹ * e⁻¹)) by group]
    exact K.mul_mem h1 hyK
  let cK : ↥K := ⟨n * (e * n⁻¹ * e⁻¹), hcK⟩
  have hcEq : cK = ⟨n, hnK⟩ * (⟨k, hk⟩ * ⟨n, hnK⟩⁻¹ * ⟨k, hk⟩⁻¹) * yK := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
    dsimp [cK, yK]
    group
  have hπc : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) cK =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨n, hnK⟩ *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨n, hnK⟩)⁻¹ *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩)⁻¹ := by
    rw [hcEq, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hπy, mul_one]
    group
  have ha₀K : a₀ ∈ K := by simpa [A] using (Subgroup.mem_inf.mp ha₀).2
  let a₀K' : ↥K := ⟨a₀, ha₀K⟩
  have hπa0 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) a₀K' :=
    pPrimeCore_quotient_eq_of_mem_pPrimeCore_map ha₀K hk hkO
  let aK' : ↥K := ⟨n, hnK⟩ * a₀K' * ⟨n, hnK⟩⁻¹ * a₀K'⁻¹
  have hπc2 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) cK =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) aK' := by
    rw [hπc, hπa0]
    simp only [aK', map_mul, map_inv]
  have haA : (aK' : G) ∈ A := by
    have ha1A : n * a₀ * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnN a₀).mp ha₀
    have heq : (aK' : G) = (n * a₀ * n⁻¹) * a₀⁻¹ := by
      dsimp [aK', a₀K']
    rw [heq]
    exact A.mul_mem ha1A (A.inv_mem ha₀)
  exact ⟨cK, aK', rfl, by simpa [A, K] using haA, by simpa [K] using hπc2⟩

theorem map_conj_E_le_stepThree (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P)
    {n : G}
    (hn : n ∈ Subgroup.normalizer ((P ⊓ kSub 3 M H : Subgroup G) : Set G) ⊓ kSub 3 M H) :
    E.map (MulAut.conj n).toMonoidHom ≤
      (E ⊔ (P ⊓ kSub 3 M H)) ⊔
        (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype := by
  rintro _ ⟨e, he, rfl⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  obtain ⟨c, a, hc, ha, hπ⟩ := exists_quotient_conj_inner_eq h hC3 hK hU hI hP hEP hn he
  have haA : (a : G) ∈ A := ha
  have hmem : n * (e * n⁻¹ * e⁻¹) ∈ A ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
    rw [← hc]
    exact mem_sup_of_quotient_eq (A := A) (by simpa [A] using inf_le_right)
      haA (by simpa [K] using hπ)
  have heU : e ∈ (E ⊔ A) ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left he)
  have heq : (MulAut.conj n) e = (n * (e * n⁻¹ * e⁻¹)) * e := by
    rw [MulAut.conj_apply]
    group
  change MulAut.conj n e ∈ (E ⊔ A) ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype
  rw [heq]
  have hAle : A ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤
      (E ⊔ A) ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  exact ((E ⊔ A) ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype).mul_mem (hAle hmem) heU

theorem map_conj_stepThree (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P)
    {n : G}
    (hn : n ∈ Subgroup.normalizer ((P ⊓ kSub 3 M H : Subgroup G) : Set G) ⊓ kSub 3 M H) :
    (E ⊔ (P ⊓ kSub 3 M H)).map (MulAut.conj n).toMonoidHom ≤
      (E ⊔ (P ⊓ kSub 3 M H)) ⊔
        (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype := by
  rw [Subgroup.map_sup]
  refine sup_le (map_conj_E_le_stepThree h hC3 hK hU hI hP hEP hn) ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : n * a * n⁻¹ ∈ P ⊓ kSub 3 M H :=
    (Subgroup.mem_normalizer_iff.mp hn.1 a).mp ha
  change MulAut.conj n a ∈ (E ⊔ (P ⊓ kSub 3 M H)) ⊔
    (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype
  rw [MulAut.conj_apply]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ha')

theorem normalizer_inf_kSub_le (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P) :
    Subgroup.normalizer ((P ⊓ kSub 3 M H : Subgroup G) : Set G) ⊓ kSub 3 M H ≤ M := by
  obtain ⟨Y, U, hY, hUeq, hUleM, -, hYSyl, hNY⟩ :=
    exists_sylow_stepThree h hC3 hK hU hI hP hEP
  intro n hn
  have hYmap : Y.map (MulAut.conj n).toMonoidHom ≤ U := by
    rw [hY]
    rw [hUeq, hY]
    exact map_conj_stepThree h hC3 hK hU hI hP hEP hn
  exact mem_of_sylow_map_le hUleM hYSyl hNY hYmap

theorem gamma_inf_kSub_le (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hI : InnerOnKAt M) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P) :
    CFSG.Open.rankThreeGamma 1 3 (P ⊓ kSub 3 M H) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := P ⊓ K
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [A, K] using isSylowOf_inf_kSub h hK hU hP
  have hNA := normalizer_inf_kSub_le h hC3 hK hU hI hP hEP
  obtain ⟨d, hd, hd1⟩ := exists_ne_one_mem_inf h hC3 hK hU hI hP hEP
  have hdE : d ∈ E := hd.1
  have hdA : d ∈ A := hd.2
  have hCd : Subgroup.centralizer ({d} : Set G) ≤ M :=
    centralizer_le_of_mem h hdE hd1
  refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 A M).mpr ?_
  intro R hRA hR
  intro g hg
  obtain ⟨E₀, hE₀R, hElem₀, hcard₀⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 1) hR
  have hcard₀' : Nat.card E₀ = 3 := by simpa using hcard₀
  have hnt : Nontrivial E₀ := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcard₀']
    norm_num
  obtain ⟨a, ha1⟩ := exists_ne (1 : E₀)
  have haE₀ : (a : G) ∈ E₀ := a.2
  have haR : (a : G) ∈ R := hE₀R haE₀
  have haA : (a : G) ∈ A := hRA haR
  have ha1' : (a : G) ≠ 1 := fun hh => ha1 (Subtype.ext hh)
  have hgaR : g * (a : G) * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg (a : G)).mp haR
  have hgaA : g * (a : G) * g⁻¹ ∈ A := hRA hgaR
  have hga1 : g * (a : G) * g⁻¹ ≠ 1 := by
    intro hh
    apply ha1'
    have h2 : g⁻¹ * (g * (a : G) * g⁻¹) * g = 1 := by
      simpa using congrArg (fun z => g⁻¹ * z * g) hh
    have h3 : g⁻¹ * (g * (a : G) * g⁻¹) * g = (a : G) := by group
    exact h3.symm.trans h2
  obtain ⟨n₁, hn₁, hn₁d⟩ :=
    exists_mem_normalizer_inf_conj_eq (nonempty_mulEquiv_threeStar hC3) hAsyl hdA hd1 haA ha1'
  obtain ⟨n₂, hn₂, hn₂d⟩ :=
    exists_mem_normalizer_inf_conj_eq (nonempty_mulEquiv_threeStar hC3) hAsyl hdA hd1 hgaA hga1
  have hw : (n₂⁻¹ * g * n₁) * d * (n₂⁻¹ * g * n₁)⁻¹ = d := by
    rw [show (n₂⁻¹ * g * n₁) * d * (n₂⁻¹ * g * n₁)⁻¹ =
      n₂⁻¹ * (g * (n₁ * d * n₁⁻¹) * g⁻¹) * n₂ by group, hn₁d, ← hn₂d]
    group
  have hwC : n₂⁻¹ * g * n₁ ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    have hcomm : (n₂⁻¹ * g * n₁) * d = d * (n₂⁻¹ * g * n₁) := by
      calc (n₂⁻¹ * g * n₁) * d = ((n₂⁻¹ * g * n₁) * d * (n₂⁻¹ * g * n₁)⁻¹) *
          (n₂⁻¹ * g * n₁) := by group
        _ = d * (n₂⁻¹ * g * n₁) := by rw [hw]
    exact hcomm.symm
  have hwM : n₂⁻¹ * g * n₁ ∈ M := hCd hwC
  have hn₁M : n₁ ∈ M := hNA hn₁
  have hn₂M : n₂ ∈ M := hNA hn₂
  have hgM : g = n₂ * (n₂⁻¹ * g * n₁) * n₁⁻¹ := by group
  rw [hgM]
  exact M.mul_mem (M.mul_mem hn₂M hwM) (M.inv_mem hn₁M)

theorem fourteenFifteen_steps {M E H P : Subgroup G} (h : HypCGen G M 3 E H)
    (hC3 : CaseThree M H) (hK : KNormalAt M)
    (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3) (hI : InnerOnKAt M)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M)) (hEP : E ≤ P) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ kSub 3 M H) (kSub 3 M H) ∧
      CFSG.Open.IsElemAbelian 3 (P ⊓ kSub 3 M H) ∧
      Nat.card ((P ⊓ kSub 3 M H : Subgroup G)) = 9 ∧
      Subgroup.normalizer ((P ⊓ kSub 3 M H : Subgroup G) : Set G) ⊓ kSub 3 M H ≤ M ∧
      CFSG.Open.rankThreeGamma 1 3 (P ⊓ kSub 3 M H) ≤ M :=
  ⟨isSylowOf_inf_kSub h hK hU hP, isElemAbelian_inf_kSub h hC3 hK hU hP,
    card_inf_kSub h hC3 hK hU hP, normalizer_inf_kSub_le h hC3 hK hU hI hP hEP,
    gamma_inf_kSub_le h hC3 hK hU hI hP hEP⟩

end HypCGen


theorem fourteenFifteenOneAt_of {M : Subgroup G} (hpre : PreambleTypes M)
    (h14 : ∀ H ∈ H2StarAll M, CaseThree M H) (hK : KNormalAt M) (hU : NineNineOneAt M)
    (hI : InnerOnKAt M) : FourteenFifteenOneAt M := by
  intro q E H hdata
  have hq3 : q = 3 := eq_three_of_mem hpre hdata.mem_QSet hdata.mem
  subst q
  have hC3 : CaseThree M H := h14 H ⟨3, E, hdata.mem_QSet, hdata.mem⟩
  have hU3 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3 := hU 3 E H hdata
  haveI : Fact (Nat.Prime 3) := ⟨hdata.prime⟩
  have hEHM : E ≤ H ⊓ M := le_inf hdata.E_le_H hdata.E_le_M
  obtain ⟨P, hP, hEP⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge hEHM hdata.isPGroup
  obtain ⟨hAsyl, hAelem, hAcard, -, hΓ⟩ :=
    HypCGen.fourteenFifteen_steps hdata hC3 hK hU3 hI hP hEP
  exact ⟨P ⊓ kSub 3 M H, inf_le_right, le_trans inf_le_left (hP.le.trans inf_le_right),
    hAelem, hAcard, hΓ⟩

theorem normalizerSylowKLeAt_of {M : Subgroup G} (hpre : PreambleTypes M)
    (h14 : ∀ H ∈ H2StarAll M, CaseThree M H) (hK : KNormalAt M) (hU : NineNineOneAt M)
    (hI : InnerOnKAt M) : NormalizerSylowKLeAt M := by
  intro q E H hdata
  have hq3 : q = 3 := eq_three_of_mem hpre hdata.mem_QSet hdata.mem
  subst q
  have hC3 : CaseThree M H := h14 H ⟨3, E, hdata.mem_QSet, hdata.mem⟩
  have hU3 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3 := hU 3 E H hdata
  haveI : Fact (Nat.Prime 3) := ⟨hdata.prime⟩
  have hEHM : E ≤ H ⊓ M := le_inf hdata.E_le_H hdata.E_le_M
  obtain ⟨P, hP, hEP⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge hEHM hdata.isPGroup
  obtain ⟨hAsyl, -, -, hNA, -⟩ :=
    HypCGen.fourteenFifteen_steps hdata hC3 hK hU3 hI hP hEP
  exact ⟨P ⊓ kSub 3 M H, hAsyl, hNA⟩

theorem agl81FourteenFifteen_of_print_inputs
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M ∧
        FourteenFifteenNormAt M ∧ KNormalAt M ∧ PLayerNotLeAt M ∧ NineNineOneAt M ∧
        InnerOnKAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_inputs ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hch, h1, h2, hN, hK, hL, hU, hI⟩ := h G hC M hM hσ
  have h14 := caseThree_of_cases hpre hch h1 h2
  exact ⟨hpre, hch, h1, h2, fourteenFifteenOneAt_of hpre h14 hK hU hI, hN, hK, hL,
    normalizerSylowKLeAt_of hpre h14 hK hU hI⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
