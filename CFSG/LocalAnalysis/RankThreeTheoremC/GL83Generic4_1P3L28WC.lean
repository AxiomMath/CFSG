module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28WCDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ShapeShear
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l28_exists_inverting (hK : L28SylowInversion) {P : Sylow 3 G} {M : Subgroup G}
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧
      ∀ a ∈ (P : Subgroup G) ⊓ J, a ^ 3 = 1 → n * a * n⁻¹ = a⁻¹ := by
  obtain ⟨S, φ, hinj, hφS, -, hlift⟩ :=
    r1s_normalizer_data hgen hJ.le_centralizer hJ.centralizer_le
  obtain ⟨n', hn'N, hn'inv⟩ := hK _ (r1sBar_isL28 hJ) S
  obtain ⟨n, hnC, hnN, hnact⟩ := hlift n' hn'N
  refine ⟨n, hnC, hnN, fun a ha ha3 => ?_⟩
  have hna : n * a * n⁻¹ ∈ (P : Subgroup G) ⊓ J := (mem_normalizer_iff.mp hnN a).mp ha
  have h1 := hnact ⟨a, ha⟩ ⟨_, hna⟩ rfl
  have h3 : (φ ⟨a, ha⟩) ^ 3 = 1 := by
    rw [← map_pow]
    exact (congrArg φ (Subtype.ext ha3)).trans (map_one φ)
  have h2 : φ ⟨_, hna⟩ = φ ⟨a⁻¹, inv_mem ha⟩ := by
    rw [h1, hn'inv _ (hφS _) h3]
    exact (map_inv φ ⟨a, ha⟩).symm
  exact congrArg Subtype.val (hinj h2)

theorem l28wc_false_of_noncentral (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) (hZc : Nat.card (L28Z (P : Subgroup G)) = 3 ^ 2)
    (hshear : L28Shear 3 (P : Subgroup G)) {y : G} (hyP : y ∈ (P : Subgroup G))
    (hyLO : IsLargeObstruction 3 M y) (hyZ : y ∉ L28Z (P : Subgroup G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hZel, hsh⟩ := hshear
  obtain ⟨-, -, hy3, -, -⟩ := id hyLO
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ L28Z (P : Subgroup G), z ≠ 1 := by
    by_contra hno'
    push Not at hno'
    have : L28Z (P : Subgroup G) = ⊥ := eq_bot_iff.mpr fun z hz => mem_bot.mpr (hno' z hz)
    rw [this, Subgroup.card_bot] at hZc
    omega
  obtain ⟨q, hqP, hq⟩ := hsh y hyP hy3 hyZ z hz
  have hzP : z ∈ (P : Subgroup G) := l28Z_le _ hz
  have hyz' : y * z = z * y := l28z_comm hz hyP
  have hqz : q * z * q⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr (l28z_comm hz hqP)
  have hyz : y ∉ zpowers z := fun h => hyZ (zpowers_le.mpr hz h)
  exact false_of_coset_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hyLO
    (hPM hzP) hz1 (hZel.2 z hz) hyz hyz'.symm (hPM hqP) (by rw [hq, hyz']) hqz

theorem l28wc_of_central (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hInv : L28SylowInversion) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G))
    (hZc : Nat.card (L28Z (P : Subgroup G)) = 3 ^ 2)
    (hZel : IsElemAbelian 3 (L28Z (P : Subgroup G)))
    (hZ3 : ∀ t ∈ (P : Subgroup G) ⊓ J, t ^ 3 = 1 → t ∈ L28Z (P : Subgroup G)) {y : G}
    (hyLO : IsLargeObstruction 3 M y) (hyZ : y ∈ L28Z (P : Subgroup G)) :
    y ∈ zpowers x ∨ y ∈ J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, hxLO, -, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  have hTc : Nat.card T = 3 ^ 2 := (l28_T_data hS hU0 hE1 hp hM hgen hJ).2.2
  obtain ⟨u', hu'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥T) 3 (by rw [hTc]; exact ⟨3, by norm_num⟩)
  set u : G := (u' : G) with hu
  have huT : u ∈ T := u'.2
  have huo : orderOf u = 3 := by rw [hu, Subgroup.orderOf_coe]; exact hu'
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at huo; omega
  have hu3 : u ^ 3 = 1 := by rw [← huo]; exact pow_orderOf_eq_one u
  have huZ : u ∈ L28Z (P : Subgroup G) := hZ3 u huT hu3
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    mem_l28Z_of_comm hxP fun g' hg' => mem_centralizer_singleton_iff.mp (hPC hg')
  have hxu : x ∉ zpowers u := fun h => hxJ (zpowers_le.mpr huT.2 h)
  have hux : u * x = x * u := l28z_comm hxZ huT.1
  obtain ⟨hDel, hDc⟩ := plane_zpowers_sup (x := x) (k := u) hx3 hu1 hu3 hxu hux
  have hZeq : L28Z (P : Subgroup G) = zpowers u ⊔ zpowers x := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr huZ) (zpowers_le.mpr hxZ)) ?_).symm
    rw [hDc, hZc]
  have hKz : ∀ t ∈ zpowers u, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_zpow (show Commute u x from hux) i j).eq
  obtain ⟨k, hk, v, hv, hyeq⟩ := u3l42_decomp hKz (hZeq ▸ hyZ)
  by_cases hk1 : k = 1
  · left
    rw [hyeq, hk1, one_mul]
    exact hv
  by_cases hv1 : v = 1
  · right
    rw [hyeq, hv1, mul_one]
    exact (zpowers_le.mpr huT.2) hk
  exfalso
  obtain ⟨n, hnC, hnN, hninv⟩ := l28_exists_inverting hInv hgen hJ
  have hnx : n * x * n⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hnC)
  have hnu : n * u * n⁻¹ = u⁻¹ := hninv u huT hu3
  have hmap : ∀ m : G, m * u * m⁻¹ ∈ zpowers u → m * x * m⁻¹ ∈ zpowers x →
      ∀ w ∈ zpowers u ⊔ zpowers x, m * w * m⁻¹ ∈ zpowers u ⊔ zpowers x := by
    intro m hmu hmx w hw
    obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp hKz hw
    have h1 : m * t * m⁻¹ ∈ zpowers u := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
      have h := map_zpow (MulAut.conj m) u i
      simp only [MulAut.conj_apply] at h
      rw [h]
      exact zpow_mem hmu i
    have h2 : m * c * m⁻¹ ∈ zpowers x := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
      have h := map_zpow (MulAut.conj m) x j
      simp only [MulAut.conj_apply] at h
      rw [h]
      exact zpow_mem hmx j
    rw [show m * (t * c) * m⁻¹ = (m * t * m⁻¹) * (m * c * m⁻¹) by group]
    exact Subgroup.mul_mem _ (mem_sup_left h1) (mem_sup_right h2)
  have hnZ : n ∈ normalizer ((L28Z (P : Subgroup G) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro w
    rw [hZeq]
    refine ⟨hmap n (by rw [hnu]; exact inv_mem (mem_zpowers u))
      (by rw [hnx]; exact mem_zpowers x) w, fun hw => ?_⟩
    have hnu' : n⁻¹ * u * n⁻¹⁻¹ ∈ zpowers u := by
      have : n⁻¹ * u * n⁻¹⁻¹ = u⁻¹ := by
        rw [inv_inv]
        have h : n⁻¹ * (n * u * n⁻¹) * n = u := by group
        rw [hnu] at h
        calc n⁻¹ * u * n = (n⁻¹ * u⁻¹ * n)⁻¹ := by group
          _ = u⁻¹ := by rw [h]
      rw [this]
      exact inv_mem (mem_zpowers u)
    have hnx' : n⁻¹ * x * n⁻¹⁻¹ ∈ zpowers x := by
      have : n⁻¹ * x * n⁻¹⁻¹ = x := by
        rw [inv_inv]
        have h : n⁻¹ * (n * x * n⁻¹) * n = x := by group
        rwa [hnx] at h
      rw [this]
      exact mem_zpowers x
    have := hmap n⁻¹ hnu' hnx' _ hw
    rwa [show n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w by group] at this
  have hnM : n ∈ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM
    (elementary_isPGroup 3 _ hZel) ((l28Z_le _).trans hPM)
    (le_pRank_of_elemAbelian_card le_rfl hZel hZc) hnZ
  have hkT : k ∈ T := (zpowers_le.mpr huT) hk
  have hk3 : k ^ 3 = 1 := hZel.2 k (zpowers_le.mpr huZ hk)
  have hxk : x ∉ zpowers k := fun h => hxJ (zpowers_le.mpr hkT.2 h)
  have hkx : k * x = x * k := l28z_comm hxZ hkT.1
  have hyD : y ∈ zpowers k ⊔ zpowers x := by
    rw [hyeq]
    exact Subgroup.mul_mem _ (mem_sup_left (mem_zpowers k)) (mem_sup_right hv)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hyk : y ∉ zpowers k := fun h => by
    have hv' : v ∈ zpowers k := by
      rw [hyeq] at h
      simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers k)) h
    have hcx : zpowers v = zpowers x := p34_zpowers_eq_of_mem hxo hv hv1
    have hxv : x ∈ zpowers v := by
      rw [hcx]
      exact mem_zpowers x
    exact hxk (zpowers_le.mpr hv' hxv)
  have hyx : y ∉ zpowers x := fun h => by
    have hk' : k ∈ zpowers x := by
      rw [hyeq] at h
      simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hv)
    have hcx : zpowers k = zpowers x := p34_zpowers_eq_of_mem hxo hk' hk1
    have hxk' : x ∈ zpowers k := by
      rw [hcx]
      exact mem_zpowers x
    exact hxk hxk'
  exact false_of_mixed_pair hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hxLO
    (hPM hkT.1) hk1 hk3 hxk hkx hnM hnx (hninv k hkT hk3) hyD hyk hyx hyLO

theorem l28_prop34_weakClosure (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hInv : L28SylowInversion) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G))
    (hZc : Nat.card (L28Z (P : Subgroup G)) = 3 ^ 2)
    (hZ3 : ∀ t ∈ (P : Subgroup G) ⊓ J, t ^ 3 = 1 → t ∈ L28Z (P : Subgroup G))
    (hshape : L28Shape 3 (P : Subgroup G)) :
    ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom ≤ J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, hxLO, -, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  have hshear := hshape.toShear hZc
  intro g hg
  have hyP : g * x * g⁻¹ ∈ (P : Subgroup G) := hg ⟨x, mem_zpowers x, rfl⟩
  have hyLO : IsLargeObstruction 3 M (g * x * g⁻¹) :=
    isLargeObstruction_conj_of_map_le hS hU0 hp hM hxP hxLO hg
  have hconj : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hconj]
  by_cases hyZ : g * x * g⁻¹ ∈ L28Z (P : Subgroup G)
  · rcases l28wc_of_central hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hInv hp hM hgen
      hJ hPC hZc hshear.1 hZ3 hyLO hyZ with hyx | hyJ
    · left
      exact p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hyx hyLO.2.1
    · right
      exact zpowers_le.mpr hyJ
  · exact (l28wc_false_of_noncentral hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM
      hZc hshear hyP hyLO hyZ).elim

theorem GL83GenericPrimeThreeL28Prop34S.of_nowc (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) (hInv : L28SylowInversion)
    (h : GL83GenericPrimeThreeL28Prop34SNoWC G) : GL83GenericPrimeThreeL28Prop34S G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsL28Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨⟨hPC, hZc, hZ3, hout⟩, hshape⟩ :=
    h 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  exact ⟨⟨hPC, hZc, hZ3, l28_prop34_weakClosure hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1
    hE3 hInv hp hM hgen hJ hPC hZc hZ3 hshape, hout⟩, hshape⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
