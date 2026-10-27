module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieL27
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem centralizer_rightConjugate (A : Subgroup G) (k : G) :
    centralizer (rightConjugate A k : Set G) = rightConjugate (centralizer (A : Set G)) k := by
  ext x
  rw [mem_rightConjugate_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h a ha
    have hmem : k⁻¹ * a * k ∈ (rightConjugate A k : Set G) := by
      rw [SetLike.mem_coe, mem_rightConjugate_iff]
      simpa [mul_assoc] using ha
    have := h _ hmem
    calc a * (k * x * k⁻¹) = k * ((k⁻¹ * a * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * a * k)) * k⁻¹ := by rw [this]
      _ = k * x * k⁻¹ * a := by group
  · intro h y hy
    rw [SetLike.mem_coe, mem_rightConjugate_iff] at hy
    have := h _ hy
    calc y * x = k⁻¹ * ((k * y * k⁻¹) * (k * x * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k := by rw [this]
      _ = x * y := by group

theorem mem_normalizer_rightConjugate_iff' (Q : Subgroup G) (g x : G) :
    x ∈ normalizer (rightConjugate Q g : Set G) ↔ g * x * g⁻¹ ∈ normalizer (Q : Set G) := by
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_eq_self_iff, rightConjugate_mul]
  constructor
  · intro h
    rw [← rightConjugate_mul, h, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  · intro h
    rw [show g * x = g * x * g⁻¹ * g by group, ← rightConjugate_mul, h]

theorem isSylowOf_rightConjugate [Finite G] {P K : Subgroup G} (h : IsSylowOf 2 P K) (g : G) :
    IsSylowOf 2 (rightConjugate P g) (rightConjugate K g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_map_hom h (MulAut.conj g⁻¹).toMonoidHom

theorem isElemAbelian_rightConjugate' {E : Subgroup G} (hE : IsElemAbelian 2 E) (g : G) :
    IsElemAbelian 2 (rightConjugate E g) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    rw [mem_rightConjugate_iff] at ha hb
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    simp only [coe_mul] at h ⊢
    have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
        _ = g * (b * a) * g⁻¹ := by group
    simpa using this
  · rw [mem_rightConjugate_iff] at hx
    have h := hE.2 _ hx
    rw [conj_pow] at h
    simpa using h

theorem mem_normalizer_rightConjugate_of_tight [Finite G] {A T : Subgroup G}
    (hstd : standardComponentIsStandard A) {g : G}
    (hTK : T ≤ rightConjugate (centralizer (A : Set G)) g) (heven : Even (Nat.card T)) {a : G}
    (haN : a ∈ normalizer (T : Set G)) : a ∈ normalizer (rightConjugate A g : Set G) := by
  rw [mem_normalizer_rightConjugate_iff', ← hstd.2.2.2.1]
  by_contra hy
  have hodd := hstd.2.2.1 (g * a * g⁻¹) hy
  set K := centralizer (A : Set G)
  have hle : T.map (MulAut.conj g).toMonoidHom ≤
      K ⊓ K.map (MulAut.conj (g * a * g⁻¹)).toMonoidHom := by
    rintro x ⟨t, ht, rfl⟩
    have htK : g * t * g⁻¹ ∈ K := (mem_rightConjugate_iff _ _ _).mp (hTK ht)
    refine mem_inf.mpr ⟨htK, ?_⟩
    have ht' : a⁻¹ * t * a ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem haN) t).mp ht
      simpa using this
    have hK' : g * (a⁻¹ * t * a) * g⁻¹ ∈ K := (mem_rightConjugate_iff _ _ _).mp (hTK ht')
    refine ⟨_, hK', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h2 : 2 ∣ Nat.card (T.map (MulAut.conj g).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact even_iff_two_dvd.mp heven
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le hle)))

theorem mem_centralizer_of_mem_sup_of_isSylowOf [Finite G] {B T : Subgroup G}
    (hTs : IsSylowOf 2 T (centralizer (B : Set G))) (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {a : G} (ha : a ∈ B ⊔ centralizer (B : Set G)) (haN : a ∈ normalizer (T : Set G))
    (ha2 : a ^ 2 = 1) : a ∈ centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer ha
  set Kc := centralizer (B : Set G)
  have hTK : T ≤ Kc := hTs.le
  have hbT : ∀ t ∈ T, b * t = t * b := fun t ht => mem_centralizer_iff.mp (hTK ht) b hb
  have hbc : b * c = c * b := (mem_centralizer_iff.mp hc b hb)
  have hbC : b ∈ centralizer (T : Set G) := mem_centralizer_iff.mpr fun t ht => (hbT t ht).symm
  have hcN : c ∈ normalizer (T : Set G) := by
    have := mul_mem (inv_mem (centralizer_le_normalizer _ hbC)) haN
    rwa [inv_mul_cancel_left] at this
  set N := Kc ⊓ normalizer (T : Set G)
  set C := Kc ⊓ centralizer (T : Set G)
  have hTC : T ≤ C := le_inf hTK fun x hx => mem_centralizer_iff.mpr fun y hy => hTab y hy x hx
  have hCN : C ≤ N := inf_le_inf_left _ (centralizer_le_normalizer _)
  have hNK : N ≤ Kc := inf_le_left
  have hnorm : (C.subgroupOf N).Normal := by
    rw [normal_subgroupOf_iff hCN]
    intro x y hx hy
    obtain ⟨hxK, hxC⟩ := mem_inf.mp hx
    obtain ⟨hyK, hyN⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hyK hxK) (inv_mem hyK), ?_⟩
    rw [mem_centralizer_iff]
    intro t ht
    have ht' : y⁻¹ * t * y ∈ T := by simpa using (mem_normalizer_iff.mp (inv_mem hyN) t).mp ht
    have h1 := mem_centralizer_iff.mp hxC _ ht'
    calc t * (y * x * y⁻¹) = y * ((y⁻¹ * t * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * t * y)) * y⁻¹ := by rw [h1]
      _ = y * x * y⁻¹ * t := by group
  have hidx : Odd (C.subgroupOf N).index := by
    have hdvd : C.relIndex N ∣ T.relIndex Kc := by
      rw [← relIndex_mul_relIndex T N Kc (hTC.trans hCN) hNK,
        ← relIndex_mul_relIndex T C N hTC hCN]
      exact (dvd_mul_left _ _).mul_right _
    have hodd : ¬ 2 ∣ T.relIndex Kc := (isSylowOf_iff.mp hTs).2.2
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h2 => hodd (h2.trans hdvd)
  have hcm := Subgroup.pow_index_mem (C.subgroupOf N) (⟨c, mem_inf.mpr ⟨hc, hcN⟩⟩ : N)
  rw [mem_subgroupOf] at hcm
  have hcmC : c ^ (C.subgroupOf N).index ∈ centralizer (T : Set G) := by
    have h : c ^ (C.subgroupOf N).index ∈ C := by simpa using hcm
    exact (mem_inf.mp h).2
  have ham : (b * c) ^ (C.subgroupOf N).index = b * c := by
    obtain ⟨s, hs⟩ := hidx
    rw [hs, pow_succ, pow_mul, ha2, one_pow, one_mul]
  rw [← ham, (Commute.mul_pow hbc _)]
  exact mul_mem (pow_mem hbC _) hcmC

theorem eq_one_of_sq_of_odd {H : Type*} [Group H] {Z : Subgroup H} (hZ : Odd (Nat.card Z))
    {m : H} (hm : m ∈ Z) (h2 : m ^ 2 = 1) : m = 1 := by
  have hdvd1 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hdvd2 : orderOf m ∣ Nat.card Z := by
    have := orderOf_dvd_natCard (⟨m, hm⟩ : Z)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime 2 (Nat.card Z) := Nat.coprime_two_left.2 hZ
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)

theorem exists_involution_lift [Finite G] {A T : Subgroup G} {P : Type} [Group P]
    (π : ↥A →* P) (hπ : Function.Surjective π) (hker : π.ker = center A)
    (hZ : Odd (Nat.card (center A))) (hTA : T ≤ A) (hT : IsElemAbelian 2 T) {abar : P}
    (ha2 : abar ^ 2 = 1) (haN : abar ∈ normalizer (imgIn π T : Set P))
    (haC : abar ∉ centralizer (imgIn π T : Set P)) :
    ∃ a ∈ A, a ^ 2 = 1 ∧ a ∈ normalizer (T : Set G) ∧ a ∉ centralizer (T : Set G) := by
  obtain ⟨a₀, rfl⟩ := hπ abar
  obtain ⟨k, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a₀).ne'
  set a : A := a₀ ^ r with ha_def
  have hπa : π a = π a₀ := by
    rw [ha_def, map_pow]
    obtain ⟨s, rfl⟩ := hr
    rw [pow_succ, pow_mul, ha2, one_pow, one_mul]
  have ha2' : a ^ 2 = 1 := by
    have hz : a ^ 2 ∈ center A := by
      rw [← hker, MonoidHom.mem_ker, map_pow, hπa, ha2]
    have h1 : (a ^ 2) ^ (2 ^ k) = 1 := by
      rw [ha_def, ← pow_mul, ← pow_mul, show r * (2 * 2 ^ k) = orderOf a₀ * 2 by rw [hor]; ring,
        pow_mul, pow_orderOf_eq_one, one_pow]
    have hdvd1 : orderOf (a ^ 2) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have hdvd2 : orderOf (a ^ 2) ∣ Nat.card (center A) := by
      have := orderOf_dvd_natCard (⟨a ^ 2, hz⟩ : center A)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (center A)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZ)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  have haG2 : (a : G) ^ 2 = 1 := by simpa using congrArg Subtype.val ha2'
  set Z := (center A).map A.subtype
  have hZodd : Odd (Nat.card Z) := by rwa [card_map_of_injective A.subtype_injective]
  have hZN : Z ≤ normalizer (T : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro t ht
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨t, hTA ht⟩)
    simpa using this
  have hfwd : ∀ t ∈ T, (a : G) * t * (a : G)⁻¹ ∈ T := by
    intro t ht
    have h1 : π (a * ⟨t, hTA ht⟩ * a⁻¹) ∈ imgIn π T := by
      rw [map_mul, map_mul, map_inv, hπa]
      exact (mem_normalizer_iff.mp haN _).mp (mem_imgIn_of π (m := ⟨t, hTA ht⟩) ht)
    obtain ⟨t', ht'T, ht'⟩ := mem_imgIn.mp h1
    have hz : t'⁻¹ * (a * ⟨t, hTA ht⟩ * a⁻¹) ∈ center A := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ht', inv_mul_cancel]
    have hmem : (a : G) * t * (a : G)⁻¹ ∈ T ⊔ Z := by
      have e : (a : G) * t * (a : G)⁻¹ =
          (t' : G) * ((t'⁻¹ * (a * ⟨t, hTA ht⟩ * a⁻¹) : A) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact mul_mem (mem_sup_left ht'T) (mem_sup_right ⟨_, hz, rfl⟩)
    refine mem_of_two_element_of_mem_sup hZN hZodd hmem (k := 1) ?_
    rw [pow_one, conj_pow, hT.2 t ht]
    group
  have haNT : (a : G) ∈ normalizer (T : Set G) := by
    rw [mem_normalizer_iff]
    intro t
    refine ⟨hfwd t, fun ht => ?_⟩
    have hainv : (a : G)⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, haG2]
    have := hfwd _ ht
    rwa [hainv, show (a : G) * ((a : G) * t * a) * a = ((a : G) * a) * t * ((a : G) * a) by
      simp only [mul_assoc], ← sq, haG2, one_mul, mul_one] at this
  refine ⟨a, a.2, haG2, haNT, fun haCT => haC ?_⟩
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨t, htT, rfl⟩ := mem_imgIn.mp hv
  rw [← hπa, ← map_mul, ← map_mul]
  exact congrArg π (Subtype.ext (mem_centralizer_iff.mp haCT _ htT))

theorem rankTwoOddLieStandard_of (hI : OddLieInputs) (hHRD : ModelHighestRootData)
    (h3 : Section3Config) (h32 : Lemma32) : RankTwoStandard.RankTwoOddLieStandard := by
  intro G _ _ A hRT hO hT
  obtain ⟨hL, hA5, hA6, -⟩ := hT
  have hstd := hRT.standard
  have hAq : Open.IsQuasisimple A := hstd.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hK
  have h31 : Hyp31 A := ⟨hstd, hypII_of_oddLieType hI hHRD A hAq hL, hO,
    by have := hRT.rank; omega, hRT.not_normal⟩
  obtain ⟨g, hg, R, T, hR, hTs, hTN, hRN, -, hTt, hRt⟩ := h3 G A h31
  have hRe : IsElemAbelian 2 R := h32 G A h31 R hR
  have hKg : Odd (Nat.card (K ⊓ rightConjugate K g : Subgroup G)) :=
    hstd.tightlyEmbedded_centralizer.2 g fun h => hg (hstd.2.2.2.1 ▸ h)
  have hR4 : 4 ≤ Nat.card R := by
    obtain ⟨E, hEK, -, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two K
    have h1 : Nat.card E ∣ Nat.card K := card_dvd_of_le hEK
    rw [hEc] at h1
    have hdvd : 2 ^ 2 ∣ Nat.card K := (Nat.pow_dvd_pow 2 hRT.rank).trans h1
    have hle : 2 ≤ (Nat.card K).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
    rw [hR.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Nat.card K).factorization 2 := Nat.pow_le_pow_right (by norm_num) hle
  have hT4 : 4 ≤ Nat.card T := by
    rw [hTs.card_eq, rightConjugate_card, ← hR.card_eq]
    exact hR4
  have hTe : IsElemAbelian 2 T := by
    have h1 : IsSylowOf 2 (rightConjugate T g⁻¹) K := by
      have := isSylowOf_rightConjugate hTs g⁻¹
      rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    have h2 := isElemAbelian_rightConjugate' (h32 G A h31 _ h1) g
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h2
  have hTC : T ⊓ centralizer (A : Set G) = ⊥ :=
    two_subgroup_of_odd_eq_bot _ _ hTs.isPGroup.to_inf_left hKg
      (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, hTs.le (mem_inf.mp hx).1⟩)
  have hRC : R ⊓ centralizer (rightConjugate A g : Set G) = ⊥ := by
    rw [centralizer_rightConjugate]
    exact two_subgroup_of_odd_eq_bot _ _ hR.isPGroup.to_inf_left hKg
      (fun x hx => mem_inf.mpr ⟨hR.le (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩)
  obtain ⟨X, hX⟩ := Hyp46.exists_of ⟨hTe, hT4, hTN, hTC⟩ hTt
  obtain ⟨hZodd, p, f, hpF, -, hf, hq, ⟨eA⟩, -, hTle⟩ := hX.as76b_4_9_general hI hHRD hAq hL
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have h7 : p ^ f = 7 := by
    rcases (by simpa using hq : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) with h5 | h7 | h9
    · obtain ⟨e5⟩ := (CFSG.LinearGroups.five_field_linear_two_alternating_five_model
        (GaloisField p f) (by rw [hcardF, h5])).1
      exact (hA5 ⟨eA.trans e5⟩).elim
    · exact h7
    · have : Fintype (GaloisField p f) := Fintype.ofFinite _
      open CFSG.LocalAnalysis.ComponentInitial in
      obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
        (GaloisField p f) (by rw [← Nat.card_eq_fintype_card, hcardF, h9])
      exact (hA6 ⟨eA.trans e6⟩).elim
  have hTA : T ≤ A := hTle (by omega)
  obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h7
  let eA7 : ↥A ⧸ center ↥A ≃* PSL(2, ZMod 7) :=
    eA.trans (CFSG.GorensteinWalter.psl2RingEquiv (GaloisField.equivZmodP 7).toRingEquiv)
  let π : ↥A →* PSL(2, ZMod 7) := eA7.toMonoidHom.comp (QuotientGroup.mk' (center A))
  have hπs : Function.Surjective π := eA7.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = center A := by
    ext x
    rw [MonoidHom.mem_ker]
    change eA7 (QuotientGroup.mk' (center A) x) = 1 ↔ _
    rw [map_eq_one_iff _ eA7.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hinj : ∀ m : A, (m : G) ∈ T → π m = 1 → m = 1 := fun m hmT hm1 =>
    eq_one_of_sq_of_odd hZodd (hπk ▸ hm1 : m ∈ center A)
      (Subtype.ext (by simpa using hTe.2 _ hmT))
  obtain ⟨-, abar, habar2, habarN, habarC⟩ := psl27_elemAbelian (isElemAbelian_imgIn π hTe)
    (by rw [card_imgIn π hTA hinj]; exact hT4)
  obtain ⟨a, haA, ha2, haN, haC⟩ :=
    exists_involution_lift π hπs hπk hZodd hTA hTe habar2 habarN habarC
  have heven : Even (Nat.card T) := by
    rcases hTs.isPGroup.card_eq_or_dvd with h1 | h2
    · omega
    · exact even_iff_two_dvd.mpr h2
  have haNg := mem_normalizer_rightConjugate_of_tight hstd hTs.le heven haN
  set Ag := rightConjugate A g with hAg
  let eAg : ↥A ≃* ↥Ag :=
    A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hAgq : Open.IsQuasisimple Ag := isQuasisimple_of_mulEquiv eAg hAq
  let eQ : ↥A ⧸ center ↥A ≃* ↥Ag ⧸ center ↥Ag :=
    QuotientGroup.congr (center A) (center Ag) eAg (map_center_mulEquiv eAg)
  have hLg : CFSG.Blueprint.OddLieType (↥Ag ⧸ center ↥Ag) := oddLieType_of_equiv eQ hL
  obtain ⟨X', hX'⟩ := Hyp46.exists_of ⟨hRe, hR4, hRN, hRC⟩ hRt
  obtain ⟨hZgodd, p', f', hp'F, -, hf', -, ⟨eAg'⟩, -, hRle⟩ :=
    hX'.as76b_4_9_general hI hHRD hAgq hLg
  have hne5 : p' ^ f' ≠ 5 := by
    intro h5
    have hc1 : Nat.card (↥Ag ⧸ center ↥Ag) = 168 := by
      rw [← Nat.card_congr eQ.toEquiv, Nat.card_congr eA7.toEquiv, card_psl27]
    have hF : Nat.card (GaloisField p' f') = 5 := by rw [GaloisField.card p' f' (by omega), h5]
    have hc2 : Nat.card PSL(2, GaloisField p' f') = 60 := by
      rw [CFSG.GorensteinWalter.psl2_card_formula _ (isOddPrimePower_of_odd (by rw [hF]; decide)),
        hF]
      norm_num
    have := Nat.card_congr eAg'.toEquiv
    omega
  have hRAg : R ≤ Ag := hRle hne5
  have haR : ∀ r ∈ R, a * r = r * a := fun r hr => mem_centralizer_iff.mp (hR.le hr) a haA
  have hainner :=
    mem_sup_centralizer_of_psl27 hAgq.1 (eQ.symm.trans eA7) hZgodd hRAg hRe hR4 haNg haR
  have hTsg : IsSylowOf 2 T (centralizer (Ag : Set G)) := by
    rw [hAg, centralizer_rightConjugate]
    exact hTs
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact haC (mem_centralizer_of_mem_sup_of_isSylowOf hTsg hTab hainner haN ha2)

end CFSG.ComponentClassification.RankTwoOddLie
