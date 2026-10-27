module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34ConfigR
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KQuotFix

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_range_conjQuotAction
    {M E H A : Subgroup G} (h : HypCGen G M 3 E H)
    (hC3 : CaseThree M H) (hK : KNormalAt M) (hL : PLayerNotLeAt M)
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (kSub 3 M H))
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {Y : Subgroup G}
    (hYH : Y ≤ H) (hYM : Y ≤ M) :
    Group.IsSolvable ↥(((conjQuotAction H (kSub 3 M H)
      (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) (kSub_le 3 M H) (hK 3 E H h)).comp
        (Subgroup.inclusion hYH)).range) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N
  let ψ : ↥Y →* MulAut (↥K ⧸ N) :=
    (conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h)).comp (Subgroup.inclusion hYH)
  let Abar : Subgroup (↥K ⧸ N) := (A.subgroupOf K).map π
  haveI : N.Normal := CFSG.pPrimeCore_normal (p := 3) (G := ↥K)
  have hψA : ∀ y : ↥Y, Abar.map (ψ y).toMonoidHom = Abar := by
    intro y
    simpa [ψ, K, N, π, Abar, Subgroup.coe_inclusion] using
      HypCGen.conjQuotAction_map_aStar_eq h hC3 hK hL hA hNA
        (x := (Subgroup.inclusion hYH y)) (hYM y.2)
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card ψ.range → r = 2 ∨ r = 3 := by
    intro r hr hrd
    by_contra hnot
    have hr2 : r ≠ 2 := fun h2 => hnot (Or.inl h2)
    have hr3 : r ≠ 3 := fun h3 => hnot (Or.inr h3)
    have hr5 : 5 ≤ r := by
      obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
      have h2 : 2 ≤ r := hr.two_le
      omega
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' r hrd
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp x.2
    have hxq : ψ y ^ r = 1 := by
      have hord : orderOf (ψ y) = r := by
        rw [hy]
        rwa [Subgroup.orderOf_coe]
      rw [← hord]
      exact pow_orderOf_eq_one (ψ y)
    have hxq' : conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h)
        (Subgroup.inclusion hYH y) ^ r = 1 := by
      simpa [ψ] using hxq
    have hα1 : conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h)
        (Subgroup.inclusion hYH y) = 1 :=
      HypCGen.conjQuotAction_eq_one_of_pow_eq_one h hC3 hK hL hA hNA
        (x := Subgroup.inclusion hYH y) (hYM y.2) hr hr5 hxq'
    have hψy : ψ y = 1 := by
      simpa [ψ, K, N] using hα1
    have hx1 : x = 1 := by
      apply Subtype.ext
      change (x : MulAut (↥K ⧸ N)) = 1
      rw [← hy]
      exact hψy
    rw [hx1] at hxord
    exact hr.ne_one (by simpa using hxord.symm)
  have hsub : (Nat.card ψ.range).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro r hr
    obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
    rcases hprime r hrp hrd with h2 | h3
    · simp [h2]
    · simp [h3]
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    ((Finset.card_le_card hsub).trans (by decide))

private theorem normalizer_quotientCentralizer_inf {M H A : Subgroup G}
    (h : HypCGen G M 3 A H) (hK : KNormalAt M) :
    H ⊓ M ≤ Subgroup.normalizer
      ((quotientCentralizer H (kSub 3 M H) (CFSG.pPrimeCore 3 ↥(kSub 3 M H))
        (kSub_le 3 M H) (hK 3 A H h) ⊓ M : Subgroup G) : Set G) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let X : Subgroup G := quotientCentralizer H K N (kSub_le 3 M H) (hK 3 A H h)
  let Z0 : Subgroup G := X ⊓ M
  change H ⊓ M ≤ Subgroup.normalizer (Z0 : Set G)
  have hXH : X ≤ H := quotientCentralizer_le H K N (kSub_le 3 M H) (hK 3 A H h)
  have hZ0conj : ∀ {g z : G}, g ∈ H ⊓ M → z ∈ Z0 → g * z * g⁻¹ ∈ Z0 := by
    intro g z hg hz
    refine ⟨?_, M.mul_mem (M.mul_mem hg.2 hz.2) (M.inv_mem hg.2)⟩
    obtain ⟨n, hn, hker⟩ :=
      (mem_quotientCentralizer N (kSub_le 3 M H) (hK 3 A H h)).mp hz.1
    let gH : ↥H := ⟨g, hg.1⟩
    have hconj : conjQuotAction H K N (kSub_le 3 M H) (hK 3 A H h) (gH * n * gH⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hker]
      simp
    refine (mem_quotientCentralizer N (kSub_le 3 M H) (hK 3 A H h)).mpr
      ⟨gH * n * gH⁻¹, ?_, hconj⟩
    simp [gH, hn]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact fun hz => hZ0conj hg hz
  · intro hz
    have h := hZ0conj (g := g⁻¹) ⟨H.inv_mem hg.1, M.inv_mem hg.2⟩ hz
    have heq : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rwa [heq] at h

private theorem normal_sylowTwo_quotientCentralizer {M H A T Z0 : Subgroup G}
    (hZ0norm : H ⊓ M ≤ Subgroup.normalizer (Z0 : Set G)) (hZ0HM : Z0 ≤ H ⊓ M)
    (hSeq : T ⊓ Z0 = CFSG.Open.pCoreOf 2 (A ⊔ T) ⊓ Z0) :
    let Z := Z0 ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)
    let S := T ⊓ Z0
    (S.subgroupOf Z).Normal := by
  dsimp only
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  let Z : Subgroup G := Z0 ⊓ Subgroup.normalizer (R : Set G)
  let S : Subgroup G := T ⊓ Z0
  change (S.subgroupOf Z).Normal
  have hSZ : S ≤ Z := by
    intro s hs
    change s ∈ T ⊓ Z0 at hs
    rw [hSeq] at hs
    exact ⟨hs.2, Subgroup.le_normalizer (H := R) hs.1⟩
  have hSZconj : ∀ {z s : G}, z ∈ Z → s ∈ S → z * s * z⁻¹ ∈ S := by
    intro z s hz hs
    change s ∈ T ⊓ Z0 at hs
    change z * s * z⁻¹ ∈ T ⊓ Z0
    rw [hSeq] at hs ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp hz.2 s).mp hs.1, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hZ0norm (hZ0HM hz.1)) s).mp hs.2
  have hSZnorm : Z ≤ Subgroup.normalizer (S : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · exact fun hs => hSZconj hz hs
    · intro hs
      have h := hSZconj (Z.inv_mem hz) hs
      have heq : z⁻¹ * (z * s * z⁻¹) * (z⁻¹)⁻¹ = s := by group
      rwa [heq] at h
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSZ).mpr hSZnorm

private theorem isSolvable_quotientCentralizer_inf_normalizer
    {M H A : Subgroup G} (h : HypCGen G M 3 A H)
    (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M) (hK : KNormalAt M)
    (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    Group.IsSolvable ↥(quotientCentralizer H (kSub 3 M H)
      (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) (kSub_le 3 M H) (hK 3 A H h) ⊓ M ⊓
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let X : Subgroup G := quotientCentralizer H K N (kSub_le 3 M H) (hK 3 A H h)
  let Z0 : Subgroup G := X ⊓ M
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  let Z : Subgroup G := Z0 ⊓ Subgroup.normalizer (R : Set G)
  let S : Subgroup G := T ⊓ Z0
  have hAH : A ≤ H := hAK.trans (kSub_le 3 M H)
  have hXH : X ≤ H := quotientCentralizer_le H K N (kSub_le 3 M H) (hK 3 A H h)
  have hZ0HM : Z0 ≤ H ⊓ M := le_inf (inf_le_left.trans hXH) inf_le_right
  have hHMnorm : H ⊓ M ≤ Subgroup.normalizer (Z0 : Set G) := by
    simpa [Z0, X, K, N] using normalizer_quotientCentralizer_inf h hK
  have hS_sylow_Z0 : CFSG.ABGLocalTools.IsSylowOf 2 S Z0 :=
    hT.inf_of_le_normalizer hZ0HM hHMnorm
  have hRleT : R ≤ T := h.pCoreOf_sup_le_of_isSylowOf hAH hT
  have hOleR : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ R :=
    h.pPrimeCore_kSub_le_pCoreOf hC3 hTwo hK hAH hT
  have hSleR : S ≤ R := by
    intro s hs
    refine mem_pCoreOf_sup_of_forall_commutator_mem (A := A) (T := T) hT.isPGroup
      (h.pCoreOf_sup_le_of_isSylowOf hAH hT)
      (h.sylowTwo_le_normalizer_sup_pCoreOf hC3 hTwo hK hL hAK hNA hT) hs.1 ?_
    intro a ha
    exact hOleR (commutator_mem_map_of_mem_quotientCentralizer N (kSub_le 3 M H)
      (hK 3 A H h) hs.2.1 (hAK ha))
  have hSeq : S = R ⊓ Z0 := by
    refine le_antisymm (fun s hs => ⟨hSleR hs, hs.2⟩) (fun s hs => ⟨hRleT hs.1, hs.2⟩)
  have hSZ : S ≤ Z := by
    intro s hs
    exact ⟨hs.2, Subgroup.le_normalizer (H := R) (hSleR hs)⟩
  have hS_sylow_Z : CFSG.ABGLocalTools.IsSylowOf 2 S Z :=
    hS_sylow_Z0.of_le hSZ inf_le_left
  have hSnorm : (S.subgroupOf Z).Normal := by
    have := normal_sylowTwo_quotientCentralizer hHMnorm hZ0HM hSeq
    simpa [Z, S, Z0, R, K, N] using this
  have hS2 : IsPGroup 2 S := hT.isPGroup.to_le (fun x hx => hx.1)
  have hSsolv : Group.IsSolvable ↥S := by
    haveI : Group.IsNilpotent ↥S := hS2.isNilpotent
    infer_instance
  have hqodd : Odd (Nat.card (↥Z ⧸ S.subgroupOf Z)) := by
    have hnot2 : ¬ 2 ∣ S.relIndex Z :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hS_sylow_Z).2.2
    rw [← Subgroup.index_eq_card]
    change Odd (S.relIndex Z)
    rw [← Nat.not_even_iff_odd]
    exact fun heven => hnot2 (even_iff_two_dvd.mp heven)
  have hQsolv : Group.IsSolvable (↥Z ⧸ S.subgroupOf Z) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hqodd
  haveI : (S.subgroupOf Z).Normal := hSnorm
  haveI : Group.IsSolvable ↥(S.subgroupOf Z) := by
    haveI : Group.IsSolvable ↥S := hSsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hSZ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSZ).injective
  haveI : Group.IsSolvable (↥Z ⧸ S.subgroupOf Z) := hQsolv
  change Group.IsSolvable ↥Z
  exact Group.isSolvable_of_subgroup_quotient (S.subgroupOf Z)
variable {M H A : Subgroup G}

theorem HypCGen.isSolvable_inf_normalizer_pCoreOf
    (h : HypCGen G M 3 A H) (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M) (hK : KNormalAt M)
    (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    Group.IsSolvable ↥(H ⊓ M ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  let Y : Subgroup G := H ⊓ M ⊓ Subgroup.normalizer (R : Set G)
  have hYH : Y ≤ H := inf_le_left.trans inf_le_left
  have hYM : Y ≤ M := inf_le_left.trans inf_le_right
  let ψ : ↥Y →* MulAut (↥K ⧸ N) :=
    (conjQuotAction H K N (kSub_le 3 M H) (hK 3 A H h)).comp (Subgroup.inclusion hYH)
  have hA : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [K] using h.isSylowOf_three_E hC3 hAK
  have hrange : Group.IsSolvable ↥ψ.range := by
    have := isSolvable_range_conjQuotAction h hC3 hK hL hA hNA hYH hYM
    simpa [ψ, K, N] using this
  let X : Subgroup G := quotientCentralizer H K N (kSub_le 3 M H) (hK 3 A H h)
  let Z0 : Subgroup G := X ⊓ M
  let Z : Subgroup G := Z0 ⊓ Subgroup.normalizer (R : Set G)
  have hZsolv : Group.IsSolvable ↥Z := by
    have := isSolvable_quotientCentralizer_inf_normalizer h hC3 hTwo hK hL hAK hNA hT
    simpa [Z, Z0, X, K, N, R] using this
  have hkerMap : ψ.ker.map Y.subtype = Z := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy1 : ψ y = 1 := by simpa [MonoidHom.mem_ker] using hy
      refine ⟨⟨?_, y.2.1.2⟩, y.2.2⟩
      refine (mem_quotientCentralizer N (kSub_le 3 M H) (hK 3 A H h)).mpr
        ⟨Subgroup.inclusion hYH y, ?_, ?_⟩
      · simp [Subgroup.coe_inclusion]
      · simpa [ψ, K, N] using hy1
    · rintro ⟨hgX, hgN⟩
      have hgH : g ∈ H := quotientCentralizer_le H K N (kSub_le 3 M H) (hK 3 A H h) hgX.1
      have hgM : g ∈ M := hgX.2
      let y : ↥Y := ⟨g, ⟨⟨hgH, hgM⟩, hgN⟩⟩
      refine ⟨y, ?_, rfl⟩
      change ψ y = 1
      obtain ⟨n, hn, hker⟩ :=
        (mem_quotientCentralizer N (kSub_le 3 M H) (hK 3 A H h)).mp hgX.1
      have hincl : (Subgroup.inclusion hYH y : ↥H) = n := Subtype.ext (by simpa [y] using hn.symm)
      simpa [ψ, K, N, hincl] using hker
  let e : ↥ψ.ker ≃* ↥Z :=
    (Subgroup.equivMapOfInjective ψ.ker Y.subtype Y.subtype_injective).trans
      (MulEquiv.subgroupCongr hkerMap)
  have hkerSolv : Group.IsSolvable ↥ψ.ker := by
    haveI : Group.IsSolvable ↥Z := hZsolv
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Group.IsSolvable ↥ψ.ker := hkerSolv
  haveI : Group.IsSolvable ↥ψ.range := hrange
  have hker_le : ψ.rangeRestrict.ker ≤ ψ.ker.subtype.range := by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]
  exact solvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict hker_le

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
