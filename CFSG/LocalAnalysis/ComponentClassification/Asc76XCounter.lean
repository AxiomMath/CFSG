module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTransfer
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma24
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma23

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

@[expose] def Conc4 {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, (∀ J ∈ Ω, (∀ g : G, J ≠ rightConjugate K g) → ⁅K, J⁆ = ⊥) ∧
    (K.Normal ∨ (IsSzOrU3 (normalClosure (K : Set G)) ∧
      ∀ R : Subgroup G, IsSylowOf 2 R K → IsSylowOf 2 R (normalClosure (K : Set G))))

theorem asc76Theorem4_iff : Asc76Theorem4 ↔
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Sec3Setting Ω → Conc4 Ω :=
  Iff.rfl

structure MinCounter {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) : Prop where
  setting : Sec3Setting Ω
  not_conc : ¬ Conc4 Ω
  ih : ∀ (G' : Type) [Group G'] [Finite G'] (Ω' : Set (Subgroup G')), Sec3Setting Ω' →
    Nat.card G' < Nat.card G ∨ (Nat.card G' = Nat.card G ∧ Ω'.ncard < Ω.ncard) → Conc4 Ω'

theorem asc76Theorem4_of_forall_not_minCounter
    (h : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), ¬ MinCounter Ω) :
    Asc76Theorem4 := by
  rw [asc76Theorem4_iff]
  suffices H : ∀ n m : ℕ, ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
      Nat.card G = n → Ω.ncard = m → Sec3Setting Ω → Conc4 Ω by
    intro G _ _ Ω hΩ
    exact H _ _ G Ω rfl rfl hΩ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G _ _ Ω hn hm hΩ
  by_contra hc
  refine h G Ω ⟨hΩ, hc, fun G' _ _ Ω' hΩ' hlt => ?_⟩
  rcases hlt with hlt | ⟨heq, hlt⟩
  · exact ihn _ (hn ▸ hlt) _ G' Ω' rfl rfl hΩ'
  · exact ihm _ (hm ▸ hlt) G' Ω' (heq.trans hn) rfl hΩ'

@[expose] def perp {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Set (Subgroup G) :=
  {J | J ∈ Ω ∧ Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G))}

@[expose] def Lemma22Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K J T R : Subgroup G), TightlyEmbedded K →
    TightlyEmbedded J → Odd (Nat.card (K ⊓ J : Subgroup G)) →
    (Nat.card K).factorization 2 = (Nat.card J).factorization 2 →
    IsSylowOf 2 T (J ⊓ normalizer (K : Set G)) → T ≠ ⊥ → IsSylowOf 2 R K →
    T ≤ normalizer (R : Set G) → 1 < Open.pRank 2 K → 1 < Open.pRank 2 J →
    IsSylowOf 2 T J → ⁅T, oUpperTwoPrime K⁆ ≤ oddCoreIn K ∨ IsElemAbelian 2 T

theorem lemma22Four_of (h : Asc76Lemma22) : Lemma22Four := by
  intro G _ _ K J T R hK hJ hKJ hfac hT hT1 hR hTR hmK hmJ
  exact (h G K J T R hK hJ hKJ hfac hT hT1 hR hTR hmK hmJ).2.2.2.1

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_isSylowOf {p : ℕ} [Fact p.Prime] {M P Q : Subgroup G}
    (hP : IsSylowOf p P M) (hQ : IsSylowOf p Q M) : ∃ m ∈ M, Q = rightConjugate P m := by
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) Q' P'
  refine ⟨m, m.2, ?_⟩
  ext x
  rw [mem_rightConjugate_iff]
  have hP' : ((P' : Subgroup M) : Set M) = MulAut.conj m • ((Q' : Subgroup M) : Set M) := by
    rw [← hm, Sylow.coe_subgroup_smul]
    rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨m * y * m⁻¹, ?_, by simp⟩
    have : m * y * m⁻¹ ∈ ((P' : Subgroup M) : Set M) := by
      rw [hP']
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    exact this
  · rintro ⟨y, hy, hyx⟩
    have hxM : x ∈ M := by
      have h1 : (m : G) * x * (m : G)⁻¹ ∈ M := hyx ▸ y.2
      have : x = (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * m := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem m.2) h1) m.2
    have hy' : y ∈ ((P' : Subgroup M) : Set M) := hy
    rw [hP'] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    refine ⟨z, hz, ?_⟩
    have : (z : G) = (m : G)⁻¹ * y * m := by
      rw [← hzy]
      simp only [MulAut.smul_def, MulAut.conj_apply, coe_mul, coe_inv]
      group
    show (z : G) = x
    rw [this, show (y : G) = m * x * (m : G)⁻¹ from hyx]
    group

theorem exists_mul_mem_normalizer {J O R : Subgroup G}
    (hO : Odd (Nat.card O)) (hR : IsPGroup 2 R) (hRO : R ≤ normalizer (O : Set G))
    (hcomm : ⁅J, R⁆ ≤ O) {j : G} (hj : j ∈ J) : ∃ o ∈ O, o * j ∈ normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := R ⊔ O with hM
  have hinf : R ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := hR ⟨x, (mem_inf.mp hx).1⟩
    have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf x ∣ Nat.card O := orderOf_dvd_natCard O (mem_inf.mp hx).2
    have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hO)
    rw [mem_bot]
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hprod := card_sup_mul_card_inf hRO
  rw [hinf, card_bot, mul_one] at hprod
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR
  have hfac : (Nat.card M).factorization 2 = a := by
    rw [hM, hprod, ha, Nat.factorization_mul (by positivity) hO.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hO.not_two_dvd_nat, add_zero,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hRM : IsSylowOf 2 R M := isSylowOf_iff_card.mpr ⟨le_sup_left, by rw [hfac, ha]⟩
  have hRjM : rightConjugate R j⁻¹ ≤ M := by
    intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have hc : ⁅j, j⁻¹ * x * j⁆ ∈ O := hcomm (commutator_mem_commutator hj hx)
    have hx' : x = ⁅j, j⁻¹ * x * j⁆ * (j⁻¹ * x * j) := by
      rw [commutatorElement_def]
      group
    rw [hx']
    exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
  have hRjsyl : IsSylowOf 2 (rightConjugate R j⁻¹) M :=
    isSylowOf_iff_card.mpr ⟨hRjM, by rw [rightConjugate_card, hfac, ha]⟩
  obtain ⟨m, hmM, hm⟩ := exists_conj_of_isSylowOf hRM hRjsyl
  have hmM' : m ∈ ((R : Set G) * (O : Set G)) := by
    rw [← coe_mul_of_left_le_normalizer_right R O hRO]
    exact hmM
  obtain ⟨r, hr, o, ho, rfl⟩ := hmM'
  simp only at hm
  have h1 : rightConjugate R (r * o) = rightConjugate R o := by
    rw [← rightConjugate_mul, (rightConjugate_eq_self_iff R r).mpr (le_normalizer hr)]
  have h2 : rightConjugate R (j⁻¹ * o⁻¹) = R := by
    rw [← rightConjugate_mul, hm, h1, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  refine ⟨o, ho, ?_⟩
  have h3 := inv_mem ((rightConjugate_eq_self_iff R _).mp h2)
  rwa [mul_inv_rev, inv_inv, inv_inv] at h3

omit [Finite G] in
theorem exists_isSylowOf_le {p : ℕ} [Fact p.Prime] {M P : Subgroup G} (hPM : P ≤ M)
    (hP : IsPGroup p P) : ∃ S : Subgroup G, IsSylowOf p S M ∧ P ≤ S := by
  obtain ⟨Q, hQ⟩ := (hP.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  refine ⟨_, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPM hx⟩, hQ hx, rfl⟩⟩

theorem isSylowOf_of_le {p : ℕ} [Fact p.Prime] {P A B : Subgroup G} (hPA : P ≤ A) (hAB : A ≤ B)
    (hP : IsSylowOf p P B) : IsSylowOf p P A := by
  rw [isSylowOf_iff_card] at hP ⊢
  refine ⟨hPA, ?_⟩
  rw [hP.2]
  congr 1
  apply le_antisymm
  · have h := card_dvd_of_le hPA
    rw [hP.2] at h
    exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (card_dvd_of_le hAB) p

theorem isSylowOf_inf {p : ℕ} [Fact p.Prime] {M N S : Subgroup G} (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hS : IsSylowOf p S M) : IsSylowOf p (S ⊓ N) N := by
  rw [isSylowOf_iff_card] at hS ⊢
  refine ⟨inf_le_right, ?_⟩
  have hSN : S ≤ normalizer (N : Set G) := hS.1.trans hMN
  have hprod := card_sup_mul_card_inf hSN
  have hSp : IsPGroup p S := IsPGroup.of_card hS.2
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hSp.to_le (inf_le_left : S ⊓ N ≤ S))
  set a := (Nat.card M).factorization p
  have h1 : (Nat.card (S ⊔ N : Subgroup G)).factorization p = a := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (card_dvd_of_le (sup_le hS.1 hNM)) p
    · have h := card_dvd_of_le (le_sup_left : S ≤ S ⊔ N)
      rw [hS.2] at h
      exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h
  have h2 := congrArg (fun n => n.factorization p) hprod
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Finsupp.add_apply, h1, hS.2, hb, Nat.Prime.factorization_pow Fact.out,
    Nat.Prime.factorization_pow Fact.out, Finsupp.single_eq_same, Finsupp.single_eq_same] at h2
  rw [hb]
  congr 1
  omega

theorem oddCore_map_mulEquiv' {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.oddCore_normal X).map _ e.surjective,
      by rw [card_map_of_injective e.injective]
         exact CFSG.ComponentClassification.OddCore.odd_card X⟩
  · have hle : (CFSG.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.oddCore X :=
      le_sSup ⟨(CFSG.oddCore_normal Y).map _ e.symm.surjective,
        by rw [card_map_of_injective e.symm.injective]
           exact CFSG.ComponentClassification.OddCore.odd_card Y⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

theorem normalizer_le_normalizer_oddCoreIn (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer ((oddCoreIn X : Subgroup G) : Set G) := by
  intro n hn
  have key : ∀ g ∈ normalizer (X : Set G), rightConjugate (oddCoreIn X) g = oddCoreIn X := by
    intro g hg
    set f : G →* G := (MulAut.conj g⁻¹).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj g⁻¹).injective
    set e : X ≃* rightConjugate X g := X.equivMapOfInjective f hf
    have hcomm : (rightConjugate X g).subtype.comp e.toMonoidHom = f.comp X.subtype := by
      ext h
      rfl
    have h1 : oddCoreIn (rightConjugate X g) = rightConjugate (oddCoreIn X) g := by
      change (CFSG.oddCore _).map _ = _
      rw [← oddCore_map_mulEquiv' e, Subgroup.map_map, hcomm, rightConjugate, oddCoreIn,
        Subgroup.map_map]
      rfl
    rw [← h1, (rightConjugate_eq_self_iff X g).mpr hg]
  exact (rightConjugate_eq_self_iff _ n).mp (key n hn)

@[expose] def actKer (K : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ normalizer (K : Set G) ∧ ∀ k ∈ K, ⁅y, k⁆ ∈ oddCoreIn K}
  one_mem' := ⟨one_mem _, fun k _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun k hk => ?_⟩
    have e : ⁅a * b, k⁆ = (a * ⁅b, k⁆ * a⁻¹) * ⁅a, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn K ha) _).mp
      (hb' k hk)) (ha' k hk)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun k hk => ?_⟩
    have e : ⁅a⁻¹, k⁆ = a⁻¹ * ⁅a, k⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn K (inv_mem ha)) _).mp
      (inv_mem (ha' k hk))

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_normalizer_of_fourGroup (hΩ : Sec3Setting Ω) {L E O : Subgroup G} (hL : L ∈ Ω)
    (hEL : E ≤ L) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) (hO : Odd (Nat.card O))
    (hEO : E ≤ normalizer (O : Set G)) : O ≤ normalizer (L : Set G) := by
  have hpow : ∀ e : E, e ^ 2 = 1 := fun e => Subtype.ext (by simpa using hE.2 _ e.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two E O hpow (by rw [hE4]; norm_num) hO.not_two_dvd_nat hEO
  rw [hgen]
  refine iSup_le fun e => iSup_le fun he1 => ?_
  have he2 : orderOf (e : G) = 2 := by
    rw [orderOf_coe]
    exact orderOf_eq_prime (hpow e) he1
  exact inf_le_right.trans (hΩ.centralizer_le_normalizer hL (hEL e.2) he2)

theorem sylow_ne_bot (hΩ : Sec3Setting Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) : R ≠ ⊥ := by
  intro h
  have := (hΩ.rank K hK R hR).2
  apply this
  rw [h]
  exact ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [(mem_bot).mp hx, one_pow]⟩

theorem exists_sylow_normalized {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) :
    ∃ R : Subgroup G, IsSylowOf 2 R K ∧ T ≤ normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : K ⊔ T ≤ normalizer (K : Set G) := sup_le le_normalizer hTK
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_le (le_sup_right : T ≤ K ⊔ T) hT
  refine ⟨S ⊓ K, isSylowOf_inf le_sup_left hY hS, fun t ht => ?_⟩
  have htS : t ∈ S := hTS ht
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxS, hxK⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨S.mul_mem (S.mul_mem htS hxS) (S.inv_mem htS),
      (mem_normalizer_iff.mp (hTK ht) x).mp hxK⟩
  · intro hx
    obtain ⟨hxS, hxK⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp (hTK ht) x).mpr hxK⟩
    have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [this]
    exact S.mul_mem (S.mul_mem (S.inv_mem htS) hxS) htS

theorem even_inf_normalizer_symm (hΩ : Sec3Setting Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hne : J ≠ K) (h : Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G))) :
    Even (Nat.card (K ⊓ normalizer (J : Set G) : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTK⟩ := hΩ.sylow K hK J hJ (Ne.symm hne) h
  have hT1 := hΩ.sylow_ne_bot hJ hT
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (isSylowOf_iff_card.mp hT).2
  have hTJ : T ≤ J := (isSylowOf_iff_card.mp hT).1
  obtain ⟨R, hR, hTR⟩ := exists_sylow_normalized hT2 hTK
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (isSylowOf_iff_card.mp hR).2
  have hRK : R ≤ K := (isSylowOf_iff_card.mp hR).1
  have hR1 := hΩ.sylow_ne_bot hK hR
  have hP : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hR2 hTR
  have hPN : T ⊔ R ≤ normalizer (R : Set G) := sup_le hTR le_normalizer
  have hc := inf_center_ne_bot' hP le_sup_right hPN hR1
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  obtain ⟨hrR, hrP⟩ := mem_inf.mp hr
  have hrC := (mem_inf.mp hrP).2
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrJ : r ∈ normalizer (J : Set G) := by
    have hJr := hΩ.eq_of_pGroup_le hJ (hΩ.conj_mem J hJ r) hT2 hT1 hTJ (fun t ht => by
      rw [mem_rightConjugate_iff]
      have hc := mem_centralizer_iff.mp hrC t (mem_sup_left ht)
      rw [← hc, mul_inv_cancel_right]
      exact hTJ ht)
    exact (rightConjugate_eq_self_iff J r).mp hJr.symm
  obtain ⟨k, hk⟩ := hR2 ⟨r, hrR⟩
  have hk' : r ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact even_card_of_two_element (mem_inf.mpr ⟨hRK hrR, hrJ⟩) hr1' hk'

theorem commutator_sylow_le (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J T : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) (hT : IsSylowOf 2 T J)
    (hTK : T ≤ normalizer (K : Set G)) : ⁅T, K⁆ ≤ oddCoreIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (isSylowOf_iff_card.mp hT).2
  have hTJ : T ≤ J := (isSylowOf_iff_card.mp hT).1
  obtain ⟨R, hR, hTR⟩ := exists_sylow_normalized hT2 hTK
  obtain ⟨EK, hEK, hEKe, hEK4⟩ := hΩ.exists_fourGroup hK
  obtain ⟨EJ, hEJ, hEJe, hEJ4⟩ := hΩ.exists_fourGroup hJ
  have h := h22 G K J T R (hΩ.tightlyEmbedded hK) (hΩ.tightlyEmbedded hJ)
    (hΩ.twoPart K hK J hJ (Ne.symm hne)).2 (hΩ.twoPart K hK J hJ (Ne.symm hne)).1
    (isSylowOf_of_le (le_inf hTJ hTK) inf_le_left hT) (hΩ.sylow_ne_bot hJ hT) hR hTR
    (one_lt_pRank_of_fourGroup hEK hEKe hEK4) (one_lt_pRank_of_fourGroup hEJ hEJe hEJ4) hT
  rcases h with h | h
  · rwa [hΩ.perfect K hK] at h
  · exact absurd h (hΩ.rank J hJ T hT).2

theorem lemma35 (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hne : J ≠ K) (h : Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G))) :
    J ≤ normalizer (K : Set G) ∧ ⁅J, K⁆ ≤ oddCoreIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJN : J ≤ normalizer (K : Set G) := by
    obtain ⟨R, hR, hRJ⟩ := hΩ.sylow J hJ K hK hne (hΩ.even_inf_normalizer_symm hK hJ hne h)
    have hR2 : IsPGroup 2 R := IsPGroup.of_card (isSylowOf_iff_card.mp hR).2
    have hRK : R ≤ K := (isSylowOf_iff_card.mp hR).1
    have hcomm : ⁅J, R⁆ ≤ oddCoreIn J := by
      rw [commutator_comm]
      exact hΩ.commutator_sylow_le h22 hJ hK (Ne.symm hne) hR hRJ
    have hRO : R ≤ normalizer ((oddCoreIn J : Subgroup G) : Set G) :=
      hRJ.trans (normalizer_le_normalizer_oddCoreIn J)
    obtain ⟨E, hER, hE, hE4⟩ := exists_fourGroup_le (hΩ.rank K hK R hR).1
    have hOK : oddCoreIn J ≤ normalizer (K : Set G) :=
      hΩ.le_normalizer_of_fourGroup hK (hER.trans hRK) hE hE4 (odd_card_oddCoreIn J)
        (hER.trans hRO)
    intro j hj
    obtain ⟨o, ho, hoj⟩ := exists_mul_mem_normalizer (odd_card_oddCoreIn J) hR2 hRO hcomm hj
    have h1 : o * j ∈ normalizer (K : Set G) :=
      hΩ.normalizer_le_normalizer hK hR2 (hΩ.sylow_ne_bot hK hR) hRK hoj
    have : j = o⁻¹ * (o * j) := by group
    rw [this]
    exact mul_mem (inv_mem (hOK ho)) h1
  refine ⟨hJN, ?_⟩
  have hJA : J ≤ actKer K := by
    rw [← hΩ.perfect J hJ]
    refine (closure_le _).mpr fun x hx => ?_
    obtain ⟨hxJ, k, hxk⟩ := hx
    obtain ⟨T, hT, hxT⟩ := exists_isSylowOf_le ((zpowers_le).mpr hxJ)
      (isPGroup_zpowers_of_two_element hxk)
    have hTJ : T ≤ J := (isSylowOf_iff_card.mp hT).1
    have hc := hΩ.commutator_sylow_le h22 hK hJ hne hT (hTJ.trans hJN)
    refine ⟨hJN hxJ, fun y hy => hc (commutator_mem_commutator (hxT (mem_zpowers x)) hy)⟩
  rw [commutator_le]
  intro j hj k hk
  exact (hJA hj).2 k hk

end CFSG.ComponentClassification.Asc76.Sec3Setting
