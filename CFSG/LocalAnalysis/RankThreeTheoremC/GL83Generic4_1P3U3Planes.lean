module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SecondPoint
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ShapeShear
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlaneLines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem u3_center_le_commutator {T : Subgroup G} (hc : Nat.card T = 3 ^ 3)
    (hnc : ¬ IsMulCommutative T) : (center ↥T).map T.subtype ≤ ⁅T, T⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcZ : Nat.card (center ↥T) = 3 := u3plane_card_center hc hnc
  have hq : Nat.card (↥T ⧸ center ↥T) = 3 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥T)
    rw [hc, hcZ] at h
    omega
  have hqc : IsMulCommutative (↥T ⧸ center ↥T) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hab : ∃ a b : ↥T, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    exact hnc ⟨⟨fun a b => hall a b⟩⟩
  obtain ⟨a, b, hab⟩ := hab
  have hcomm : a * b * a⁻¹ * b⁻¹ ∈ center ↥T := by
    rw [← QuotientGroup.ker_mk' (center ↥T), MonoidHom.mem_ker]
    have h := hqc.is_comm.comm (QuotientGroup.mk' (center ↥T) a) (QuotientGroup.mk' (center ↥T) b)
    simp only [map_mul, map_inv]
    rw [h]
    group
  have hne : a * b * a⁻¹ * b⁻¹ ≠ 1 := fun h => hab (by
    have : a * b = b * a := by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h, one_mul]
    exact this)
  have hgen : (center ↥T) = Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcomm) ?_).symm
    rw [hcZ, Nat.card_zpowers]
    have hdvd : orderOf (a * b * a⁻¹ * b⁻¹) ∣ 3 := by
      rw [← hcZ]
      exact Subgroup.orderOf_dvd_natCard _ hcomm
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · rw [h]
  intro z hz
  obtain ⟨z', hz', rfl⟩ := hz
  rw [hgen] at hz'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz'
  have hmem : ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) ∈ ⁅T, T⁆ := by
    have h := Subgroup.commutator_mem_commutator a.2 b.2
    rwa [commutatorElement_def] at h
  rw [← hj]
  show (((a * b * a⁻¹ * b⁻¹ : ↥T) ^ j : ↥T) : G) ∈ ⁅T, T⁆
  rw [Subgroup.coe_zpow]
  exact Subgroup.zpow_mem _ hmem j

theorem u3_normalizer_le (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {T : Subgroup G} (hTM : T ≤ M)
    (hexp : ∀ t ∈ T, t ^ 3 = 1) (hc : Nat.card T = 3 ^ 3) (hnc : ¬ IsMulCommutative T) :
    normalizer (T : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcZ : Nat.card (center ↥T) = 3 := u3plane_card_center hc hnc
  set A : Subgroup G := (center ↥T).map T.subtype with hA
  have hAcard : Nat.card A = 3 := by
    rw [hA, Subgroup.card_map_of_injective T.subtype_injective, hcZ]
  have hAT : ∀ z ∈ A, z ∈ T := fun z ⟨z', _, h⟩ => h ▸ z'.2
  have hAc : ∀ a ∈ A, ∀ t ∈ T, a * t = t * a := fun a ⟨a', ha', h⟩ t ht => by
    rw [← h]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp ha' ⟨t, ht⟩).symm)
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : A = ⊥ := eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hno z hz)
    rw [this, Subgroup.card_bot] at hAcard
    omega
  obtain ⟨b, hbT, hbA⟩ : ∃ b ∈ T, b ∉ A := by
    by_contra hno
    push Not at hno
    have h1 := Subgroup.card_le_of_le (fun t ht => hno t ht : T ≤ A)
    rw [hc, hAcard] at h1
    omega
  have haA' : zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  obtain ⟨hel, hcard⟩ := plane_zpowers_sup (x := b) (k := a) (hexp b hbT) ha1
    (hexp a (hAT a haA)) (fun h => hbA (haA' h)) (hAc a haA b hbT)
  have hle : zpowers a ⊔ zpowers b ≤ T :=
    sup_le (Subgroup.zpowers_le.mpr (hAT a haA)) (Subgroup.zpowers_le.mpr hbT)
  exact normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM (IsPGroup.of_card hc) hTM
    (le_pRank_of_elemAbelian_card hle hel hcard)

theorem u3_false_of_second_point {P : Sylow 3 G} {x z : G} {J : Subgroup G}
    (hR1 : U3Prop34 3 P J x)
    (hz : z ∈ (center ↥((P : Subgroup G) ⊓ J)).map ((P : Subgroup G) ⊓ J).subtype) (hz1 : z ≠ 1)
    (hcases : SecondPointAbel (P : Subgroup G) z ∨ (∃ J' : Subgroup G, U3Prop34 3 P J' z) ∨
      ∃ J' : Subgroup G, L28Prop34S 3 P J' z) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPC, hcard, hexp, hnc, ⟨Z, hZc, hxZ, hZcomm, hTZ, hPeq⟩, -⟩ := hR1
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  have hTP : T ≤ (P : Subgroup G) := inf_le_left
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Z) ⟨b, hb⟩)
  have hAmem : ∀ a ∈ (center ↥T).map T.subtype, ∃ a' : ↥T, a' ∈ center ↥T ∧ (a' : G) = a :=
    fun a ⟨a', ha', h⟩ => ⟨a', ha', h⟩
  have hcentral : ∀ a ∈ (center ↥T).map T.subtype, ∀ g ∈ (P : Subgroup G), g * a = a * g := by
    intro a ha g hg
    obtain ⟨a', ha'c, rfl⟩ := hAmem a ha
    rw [hPeq] at hg
    obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp hZcomm hg
    have h1 : t * (a' : G) = (a' : G) * t :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp ha'c ⟨t, ht⟩)
    have h2 : (a' : G) * c = c * (a' : G) := hZcomm _ a'.2 c hc
    calc t * c * (a' : G) = t * (c * (a' : G)) := mul_assoc _ _ _
      _ = t * ((a' : G) * c) := by rw [h2]
      _ = (t * (a' : G)) * c := (mul_assoc _ _ _).symm
      _ = ((a' : G) * t) * c := by rw [h1]
      _ = (a' : G) * (t * c) := mul_assoc _ _ _
  have hzP : ∀ g ∈ (P : Subgroup G), g * z = z * g := hcentral z hz
  have hzT : z ∈ T := by
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2
  rcases hcases with ⟨K₀, hK₀P, hK₀el, hK₀c, hzK₀, hK₀z, hΩ, -⟩ | ⟨J', hR'⟩ | ⟨J', hR'⟩
  ·
    have hzo : z ^ 3 = 1 := hexp _ hzT
    have hKz : K₀ ≤ centralizer ((zpowers z : Subgroup G) : Set G) := fun k hk => by
      rw [mem_centralizer_iff]
      intro a ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
      exact ((Commute.zpow_right (show Commute k z from hK₀z k hk) j).eq).symm
    have hEel : IsElemAbelian 3 (K₀ ⊔ zpowers z) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hK₀el
        (CFSG.AGLEmbedding.isElemAbelian_zpowers hzo) hKz
    have hTE : ∀ t ∈ T, t ∈ K₀ ⊔ zpowers z := fun t ht =>
      hΩ t ⟨hTP ht, mem_centralizer_singleton_iff.mpr (hzP t (hTP ht))⟩ (hexp t ht)
    exact hnc ⟨⟨fun a b => Subtype.ext (by
      have h := congrArg Subtype.val (hEel.1.is_comm.comm (⟨a, hTE a a.2⟩ :
        ↥(K₀ ⊔ zpowers z)) ⟨b, hTE b b.2⟩)
      exact h)⟩⟩
  ·
    obtain ⟨-, -, -, -, ⟨Z', hZ'c, hzZ', hZ'comm, hTZ', hPeq'⟩, -⟩ := hR'
    have hZ'ab : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Z') ⟨b, hb⟩)
    have hPmem : ∀ g ∈ (P : Subgroup G), g ∈ ((P : Subgroup G) ⊓ J') ⊔ Z' := fun g hg => by
      rw [hPeq'] at hg
      exact hg
    have hcomm : ⁅(P : Subgroup G), (P : Subgroup G)⁆ ≤ (P : Subgroup G) ⊓ J' :=
      Subgroup.commutator_le.mpr fun a ha b hb => u3l42_commutator_mem hZ'comm hZ'ab
        (hPmem a ha) (hPmem b hb)
    have hzcomm : z ∈ ⁅(P : Subgroup G), (P : Subgroup G)⁆ :=
      (Subgroup.commutator_mono hTP hTP) (u3_center_le_commutator hcard hnc hz)
    have : z ∈ ((P : Subgroup G) ⊓ J') ⊓ Z' := ⟨hcomm hzcomm, hzZ'⟩
    rw [hTZ', Subgroup.mem_bot] at this
    exact hz1 this
  ·
    have hP5 : Nat.card (P : Subgroup G) = 3 ^ 5 := hR'.2.1
    have hZP : Nat.card (L28Z (P : Subgroup G)) = 3 ^ 2 := hR'.1.2.1
    have hdisj : Disjoint T Z := disjoint_iff.mpr hTZ
    have hZN : Z ≤ normalizer (T : Set G) := fun c hc =>
      Subgroup.centralizer_le_normalizer (T : Set G)
        (mem_centralizer_iff.mpr fun t ht => hZcomm t ht c hc)
    have hcardP : Nat.card (P : Subgroup G) = Nat.card T * Nat.card Z := by
      rw [hPeq]
      exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T Z hZN hdisj
    have hZc9 : Nat.card Z = 3 ^ 2 := by
      rw [hP5, hcard] at hcardP
      omega
    set A : Subgroup G := (center ↥T).map T.subtype with hA
    have hAcard : Nat.card A = 3 := by
      rw [hA, Subgroup.card_map_of_injective T.subtype_injective, u3plane_card_center hcard hnc]
    have hAT : A ≤ T := fun a ha => by
      obtain ⟨a', -, rfl⟩ := hAmem a ha
      exact a'.2
    have hAZ : Z ≤ normalizer (A : Set G) := fun c hc =>
      Subgroup.centralizer_le_normalizer (A : Set G)
        (mem_centralizer_iff.mpr fun a ha => hZcomm a (hAT ha) c hc)
    have hAZcard : Nat.card (A ⊔ Z : Subgroup G) = Nat.card A * Nat.card Z :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A Z hAZ
        (Disjoint.mono_left hAT hdisj)
    have hZP' : ∀ c ∈ Z, ∀ g ∈ (P : Subgroup G), g * c = c * g := by
      intro c hc g hg
      rw [hPeq] at hg
      obtain ⟨t, ht, d, hd, rfl⟩ := u3l42_decomp hZcomm hg
      have h1 : t * c = c * t := hZcomm t ht c hc
      have h2 : d * c = c * d := hZab d hd c hc
      calc t * d * c = t * (d * c) := mul_assoc _ _ _
        _ = t * (c * d) := by rw [h2]
        _ = (t * c) * d := (mul_assoc _ _ _).symm
        _ = (c * t) * d := by rw [h1]
        _ = c * (t * d) := mul_assoc _ _ _
    have hle : A ⊔ Z ≤ L28Z (P : Subgroup G) := sup_le
      (fun a ha => mem_l28Z_of_comm (hTP (hAT ha)) (hcentral a ha))
      (fun c hc => mem_l28Z_of_comm (by rw [hPeq]; exact Subgroup.mem_sup_right hc)
        (hZP' c hc))
    have h27 := Subgroup.card_le_of_le hle
    rw [hAZcard, hAcard, hZc9, hZP] at h27
    omega

theorem u3_lemma42_of_planes (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore)
    (hAct : KFactA6SylowAction) (hUAct : KFactU3SylowInversion)
    (hA34 : GL83GenericPrimeThreeA6Prop34 G) (hU34 : GL83GenericPrimeThreeU3Fusion G)
    (hE34 : GL83GenericPrimeThreeL28Prop34S G) (hp : 3 ∈ rankThreeSigmaA G)
    (hIH : LargerPrimesUnique G 3) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J)
    (hR1 : U3Prop34 3 P J x) :
    ∀ u ∈ u3VPlane (P : Subgroup G) J x, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro u huU hux
  by_contra hCu
  have hR1' := hR1
  obtain ⟨hxP, hxLO, -, hrk⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPC, hcard, hexp, hnc, ⟨Z, hZc, hxZ, hZcomm, hTZ, hPeq⟩, -⟩ := hR1
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  have hTP : T ≤ (P : Subgroup G) := inf_le_left
  have hrkP : CFSG.Open.pRank 3 (P : Subgroup G) = 3 := by
    rwa [inf_of_le_left hPC] at hrk
  have hPx : ∀ g ∈ (P : Subgroup G), g * x = x * g := fun g hg =>
    mem_centralizer_singleton_iff.mp (hPC hg)
  have hxT : x ∉ T := fun hxT => hx1 (by
    have : x ∈ T ⊓ Z := ⟨hxT, hxZ⟩
    rwa [hTZ, mem_bot] at this)
  have hxJ : x ∉ J := fun h => hxT ⟨hxP, h⟩
  obtain ⟨hUel, -, hUP, -, -, -⟩ := u3plane_facts hgen hR1' hxJ
  set A : Subgroup G := (center ↥T).map T.subtype with hA
  have hAmem : ∀ a ∈ A, ∃ a' : ↥T, a' ∈ center ↥T ∧ (a' : G) = a := fun a ⟨a', ha', h⟩ =>
    ⟨a', ha', h⟩
  have hAT : ∀ a ∈ A, a ∈ T := fun a ha => by
    obtain ⟨a', -, rfl⟩ := hAmem a ha
    exact a'.2
  have hAx : ∀ a ∈ A, a * x = x * a := fun a ha => mem_centralizer_singleton_iff.mp
    (hPC (hTP (hAT a ha)))
  have hAcentral : ∀ a ∈ A, ∀ g ∈ (P : Subgroup G), g * a = a * g := by
    intro a ha g hg
    obtain ⟨a', ha'c, rfl⟩ := hAmem a ha
    rw [hPeq] at hg
    obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp hZcomm hg
    have h1 : t * (a' : G) = (a' : G) * t :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp ha'c ⟨t, ht⟩)
    have h2 : (a' : G) * c = c * (a' : G) := hZcomm _ a'.2 c hc
    calc t * c * (a' : G) = t * (c * (a' : G)) := mul_assoc _ _ _
      _ = t * ((a' : G) * c) := by rw [h2]
      _ = (t * (a' : G)) * c := (mul_assoc _ _ _).symm
      _ = ((a' : G) * t) * c := by rw [h1]
      _ = (a' : G) * (t * c) := mul_assoc _ _ _
  obtain ⟨a, haA, c, hc, hu⟩ := u3l42_decomp (T := A) (Z := zpowers x) (fun a ha c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute a x from hAx a ha) j).eq) huU
  have hu1 : u ≠ 1 := fun h => hux (h ▸ one_mem _)
  have hu3 : u ^ 3 = 1 := hUel.2 u huU
  have huP : u ∈ (P : Subgroup G) := hUP huU
  have hPCu : (P : Subgroup G) ≤ centralizer ({u} : Set G) := fun g hg => by
    refine mem_centralizer_singleton_iff.mpr ?_
    have hcx : g * c = c * g := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
      exact (Commute.zpow_right (show Commute g x from hPx g hg) j).eq
    rw [hu]
    calc g * (a * c) = (g * a) * c := (mul_assoc _ _ _).symm
      _ = (a * g) * c := by rw [hAcentral a haA g hg]
      _ = a * (g * c) := mul_assoc _ _ _
      _ = a * (c * g) := by rw [hcx]
      _ = (a * c) * g := (mul_assoc _ _ _).symm
  obtain ⟨Q, hQsyl, hPQ, hQM⟩ := exists_sylow_through3 hS hU0 hp hM P.isPGroup'
    (by rw [hrkP]; norm_num) hPM hPCu
  have hQeq : Q = (P : Subgroup G) := P.3 hQsyl.isPGroup hPQ
  have hinf : (P : Subgroup G) ⊓ centralizer ({u} : Set G) = (P : Subgroup G) :=
    inf_of_le_left hPCu
  have hLO : IsLargeObstruction 3 M u :=
    ⟨hPM huP, hu1, hu3, (le_of_eq hrkP.symm).trans (pRank_mono 3 (by norm_num) hPCu), hCu⟩
  have hugen : IsGenericPoint 3 P M u := by
    refine ⟨huP, hLO, ?_, ?_⟩
    · rw [hinf, ← hQeq]
      exact hQsyl
    · rw [hinf]
      exact hrkP
  by_cases ha1 : a = 1
  · exact hux (by rw [hu, ha1, one_mul]; exact hc)
  have ha3 : a ^ 3 = 1 := hexp a (hAT a haA)
  have hxa : x ∉ zpowers a := fun h => hxT (zpowers_le.mpr (hAT a haA) h)
  by_cases hc1 : c = 1
  ·
    have hua : u = a := by rw [hu, hc1, mul_one]
    have hfail : ¬ rankThreeGamma 1 3 (P : Subgroup G) ≤ M := u3l42_not_gamma_le huP hu1 hu3 hCu
    exact u3_false_of_second_point hR1' (hua ▸ haA) hu1
      (second_point_cases hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hKT hSig hL hA1 hAct hA34 hU34 hE34 hp
        hIH hM hfail hugen)
  ·
    obtain ⟨n, hnC, hnN, hninv⟩ := u3_exists_inverting hUAct hgen hJ
    have hnM : n ∈ M := u3_normalizer_le hS hU0 hp hM (hTP.trans hPM) hexp hcard hnc hnN
    have hnx : n * x * n⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp hnC)
    have hyD : u ∈ zpowers a ⊔ zpowers x := by
      rw [hu]
      exact Subgroup.mul_mem _ (mem_sup_left (mem_zpowers a)) (mem_sup_right hc)
    have hyk : u ∉ zpowers a := fun h => by
      have hc' : c ∈ zpowers a := by
        rw [hu] at h
        simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers a)) h
      have hcx : zpowers c = zpowers x :=
        p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hc hc1
      have hxc : x ∈ zpowers c := by
        rw [hcx]
        exact mem_zpowers x
      exact hxa (zpowers_le.mpr hc' hxc)
    exact false_of_mixed_pair hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hxLO
      (hPM (hTP (hAT a haA))) ha1 ha3 hxa (hAx a haA) hnM hnx (hninv a haA) hyD hyk hux hLO

end CFSG.LocalAnalysis.RankThreeTheoremC
