module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ShapeShear
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Lem44Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem l28lem42_comm {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite G] in
theorem l28lem42_zpow_emod {e : G} (he : e ^ 3 = 1) (k : ℤ) : e ^ k = e ^ (k % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
  rw [zpow_add, zpow_mul, show e ^ (3 : ℤ) = 1 by exact_mod_cast he, one_zpow, mul_one]

omit [Finite G] in
theorem l28lem42_centralizer_inv (u : G) :
    centralizer ({u⁻¹} : Set G) = centralizer ({u} : Set G) := by
  ext g
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : Commute g u⁻¹⁻¹ := Commute.inv_right (show Commute g u⁻¹ from h)
    rw [inv_inv] at h'
    exact h'
  · intro h
    exact Commute.inv_right (show Commute g u from h)

theorem l28lem42_conj_eq {A : Subgroup G} (hA : Nat.card A ≤ 2) {a d : G} (ha : a ∈ A)
    (hd : d * a * d⁻¹ ∈ A) : d * a * d⁻¹ = a := by
  by_contra hne
  have h1 : (1 : G) ≠ a := by
    rintro rfl
    exact hne (by simp)
  have h2 : (1 : G) ≠ d * a * d⁻¹ := by
    intro h
    apply h1
    have : a = d⁻¹ * (d * a * d⁻¹) * d := by group
    rw [← h] at this
    simpa using this.symm
  have h3 : 2 < (A : Set G).ncard :=
    (Set.two_lt_ncard (Set.toFinite _)).mpr ⟨1, A.one_mem, a, ha, _, hd, h1, h2, Ne.symm hne⟩
  have h4 : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
  omega

theorem l28_three_le_pRank {P : Subgroup G} (hZc : Nat.card (L28Z P) = 3 ^ 2)
    (hZel : IsElemAbelian 3 (L28Z P)) {y : G} (hyP : y ∈ P) (hy3 : y ^ 3 = 1)
    (hyZ : y ∉ L28Z P) : 3 ≤ CFSG.Open.pRank 3 (centralizer ({y} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ e ∈ L28Z P, e * y = y * e := fun e he => (l28z_comm he hyP).symm
  have hel : IsElemAbelian 3 (zpowers y) := by
    refine ⟨inferInstance, fun a ha => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hcard : Nat.card ↥(L28Z P ⊔ zpowers y) = 3 ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three _ hy3 hyZ hcomm, hZc]
    ring
  have hE : IsElemAbelian 3 (L28Z P ⊔ zpowers y) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hZel hel
      (fun e he => by
        rw [mem_centralizer_iff]
        intro a ha
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
        exact (Commute.zpow_right (show Commute e y from hcomm e he) k).eq.symm)
  refine le_pRank_of_elemAbelian_card ?_ hE hcard
  refine sup_le (fun e he => mem_centralizer_singleton_iff.mpr (hcomm e he)) ?_
  exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

theorem l28_lemma42_of_shear (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hR : L28Prop34 3 P J x) (hSh : L28Shear 3 (P : Subgroup G)) {U : Subgroup G}
    (hV : L28InV 3 P x U) : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M := by
  intro u huU hux
  by_contra hCu
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hUx : U ⊓ L28Z (P : Subgroup G) = zpowers x := l28plane_inf_center hgen hR hV
  obtain ⟨hxP, ⟨hxM, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  obtain ⟨-, hZc, -, -, -⟩ := id hR
  obtain ⟨hUQ, hUel, hUc, hxU, -⟩ := id hV
  obtain ⟨hZel, hshear⟩ := id hSh
  have hUP : U ≤ (P : Subgroup G) := hUQ.trans inf_le_left
  have hUM : U ≤ M := hUP.trans hPM
  have hxZ : zpowers x ≤ L28Z (P : Subgroup G) := hUx.ge.trans inf_le_right
  have hnotZ : ∀ y ∈ U, y ∉ zpowers x → y ∉ L28Z (P : Subgroup G) := by
    intro y hyU hyx hyZ
    have hy : y ∈ U ⊓ L28Z (P : Subgroup G) := ⟨hyU, hyZ⟩
    rw [hUx] at hy
    exact hyx hy
  have hu3 : u ^ 3 = 1 := hUel.2 u huU
  have hcommU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => l28lem42_comm hUel ha hb
  have hLOw : ∀ w ∈ U, w ∉ zpowers x → ¬ centralizer ({w} : Set G) ≤ M →
      IsLargeObstruction 3 M w := fun w hwU hwx hCw =>
    ⟨hUM hwU, fun h => hwx (h ▸ one_mem _), hUel.2 w hwU,
      l28_three_le_pRank hZc hZel (hUP hwU) (hUel.2 w hwU) (hnotZ w hwU hwx), hCw⟩
  have hshearLO : ∀ w ∈ U, w ∉ zpowers x → IsLargeObstruction 3 M w → ∀ l : ℤ,
      IsLargeObstruction 3 M (w * x ^ l) := by
    intro w hwU hwx hw l
    obtain ⟨q, hqP, hq⟩ := hshear w (hUP hwU) (hUel.2 w hwU) (hnotZ w hwU hwx) (x ^ l)
      (hxZ (zpow_mem (mem_zpowers x) l))
    have h := hw.conj (hPM hqP)
    rwa [MulAut.conj_apply, hq] at h
  have hUsup : zpowers u ⊔ zpowers x = U := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr huU) (zpowers_le.mpr hxU)) ?_
    rw [sup_comm, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers x) hu3
      hux (fun e he => hcommU e (zpowers_le.mpr hxU he) u huU), Nat.card_zpowers,
      orderOf_eq_prime hx3 hx1, hUc]
    norm_num
  have hLO : ∀ y ∈ U, y ∉ zpowers x → IsLargeObstruction 3 M y := by
    intro y hyU hyx
    have hy' : y ∈ zpowers u ⊔ zpowers x := by rw [hUsup]; exact hyU
    obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp (fun t ht c hc =>
      hcommU t (zpowers_le.mpr huU ht) c (zpowers_le.mpr hxU hc)) hy'
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hc
    rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
    · exfalso
      apply hyx
      rw [l28lem42_zpow_emod hu3 m, h, zpow_zero, one_mul]
      exact zpow_mem (mem_zpowers x) l
    · rw [l28lem42_zpow_emod hu3 m, h, zpow_one]
      exact hshearLO u huU hux (hLOw u huU hux hCu) l
    · have hu2 : u ^ (2 : ℤ) = u⁻¹ := by
        rw [zpow_two]
        refine eq_inv_of_mul_eq_one_left ?_
        calc u * u * u = u ^ 3 := (pow_three' u).symm
          _ = 1 := hu3
      rw [l28lem42_zpow_emod hu3 m, h, hu2]
      have hinx : u⁻¹ ∉ zpowers x := fun hi => hux (by simpa using (zpowers x).inv_mem hi)
      refine hshearLO u⁻¹ (U.inv_mem huU) hinx (hLOw u⁻¹ (U.inv_mem huU) hinx ?_) l
      rw [l28lem42_centralizer_inv]
      exact hCu
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 M
  have hcop : Nat.Coprime 3 (Nat.card T₀) := by
    obtain ⟨b, hb⟩ := hT₀2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hgood : ∀ y ∈ U, y ≠ 1 →
      T₀ ⊓ centralizer ({y} : Set G) ≤ centralizer ({x} : Set G) := by
    intro y hyU hy1
    by_cases hyx : y ∈ zpowers x
    ·
      have hy3 : y ^ 3 = 1 := hUel.2 y hyU
      have hyz : zpowers y = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyx) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy3 hy1,
          orderOf_eq_prime hx3 hx1])
      have hxy : x ∈ zpowers y := by rw [hyz]; exact mem_zpowers x
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxy
      intro a ha
      have hay : a * y = y * a := mem_centralizer_singleton_iff.mp ha.2
      rw [mem_centralizer_singleton_iff, ← hj]
      exact (Commute.zpow_right (show Commute a y from hay) j).eq
    · have hcard := card_pCore_inf_centralizer_le_two hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3
        hE1 hE3 hp hM (hLO y hyU hyx)
      intro a ha
      have hxC : x ∈ centralizer ({y} : Set G) :=
        mem_centralizer_singleton_iff.mpr (hcommU x hxU y hyU)
      have hxa : x * a * x⁻¹ ∈ T₀ ⊓ centralizer ({y} : Set G) :=
        ⟨(mem_normalizer_iff.mp (hMT₀ hxM) a).mp ha.1,
          (mem_normalizer_iff.mp (Subgroup.le_normalizer hxC) a).mp ha.2⟩
      have hax := l28lem42_conj_eq hcard ha hxa
      rw [mem_centralizer_singleton_iff]
      calc a * x = (x * a * x⁻¹) * x := by rw [hax]
        _ = x * a := by group
  have hT₀C : T₀ ≤ centralizer ({x} : Set G) :=
    CFSG.LocalAnalysis.RankFourTheoremC.le_of_forall_inf_centralizer_le_plane Nat.prime_three hUel
      hUc (fun d hd => hMT₀ (hUM hd)) hcop hgood
  have hxT : x ∈ T₀ := hS.charTwo M hM.1.1
    ⟨hxM, mem_centralizer_iff.mpr fun t ht => mem_centralizer_singleton_iff.mp (hT₀C ht)⟩
  obtain ⟨k, hk⟩ := hT₀2 ⟨x, hxT⟩
  have h2 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hcoprime : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  exact hx1 (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_one (hcoprime.gcd_eq_one ▸ Nat.dvd_gcd h3 h2)))

theorem GL83GenericPrimeThreeL28Lemma42.of_prop34S (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) (h : GL83GenericPrimeThreeL28Prop34S G) :
    GL83GenericPrimeThreeL28Lemma42 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ hR U hV
  subst hp3
  have hRS := h 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  exact l28_lemma42_of_shear hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hgen
    hR (L28Shape.toShear hR.2.1 hRS.2) hV

end CFSG.LocalAnalysis.RankThreeTheoremC
