module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineFinish
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem centralizer_map_le_of_odd {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {P : Subgroup X} (hP : IsPGroup 2 P) :
    Subgroup.centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) ≤
      (Subgroup.centralizer (P : Set X)).map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro q hq
  let α : P →* MulAut X := MulAut.conj.comp P.subtype
  have hNα : ∀ a : P, ∀ n ∈ N, α a n ∈ N := fun a n hn =>
    (inferInstance : N.Normal).conj_mem n hn a
  have hcop : ¬ 2 ∣ Nat.card N := fun h =>
    (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have hfix : q ∈ {q : X ⧸ N | ∀ a : P,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα a q = q} := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    have h := Subgroup.mem_centralizer_iff.mp hq (QuotientGroup.mk' N (a : X)) ⟨a, a.2, rfl⟩
    change ((((a : X) * x * (a : X)⁻¹ : X)) : X ⧸ N) = (x : X ⧸ N)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change QuotientGroup.mk' N (a : X) * (x : X ⧸ N) * (QuotientGroup.mk' N (a : X))⁻¹ =
      (x : X ⧸ N)
    rw [h, mul_inv_cancel_right]
  rw [CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hP α N hNα hcop] at hfix
  obtain ⟨c, hc, rfl⟩ := hfix
  refine ⟨c, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
  have h : (a : X) * c * a⁻¹ = c := hc ⟨a, ha⟩
  calc a * c = (a * c * a⁻¹) * a := by group
    _ = c * a := by rw [h]

theorem exists_pow_two_element {Y : Type*} [Group Y] (f : X →* Y) (c : X) {j : ℕ}
    (hj : f c ^ (2 ^ j) = 1) : ∃ m : ℕ, (∃ k : ℕ, (c ^ m) ^ (2 ^ k) = 1) ∧ f (c ^ m) = f c := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop : m.Coprime (orderOf (f c)) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
    rw [hi]
    exact Nat.Coprime.pow_right i (Nat.coprime_two_right.mpr hm)
  obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨m * m', ⟨k, ?_⟩, ?_⟩
  · rw [← pow_mul, show m * m' * 2 ^ k = 2 ^ k * m * m' by ring, pow_mul, ← hkm,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_mul, hm']

omit [Finite X] in
theorem isPGroup_zpowers_of_pow {z : X} {k : ℕ} (hk : z ^ (2 ^ k) = 1) :
    IsPGroup 2 (Subgroup.zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])

theorem mem_of_isSylowOf_of_isMulCommutative {P K : Subgroup X} (hP : IsSylowOf 2 P K)
    (hK : IsMulCommutative K) {z : X} (hz : z ∈ K) {k : ℕ} (hk : z ^ (2 ^ k) = 1) : z ∈ P := by
  obtain ⟨c, hc, hle⟩ := exists_rightConjugate_le_of_isSylowOf hP (isPGroup_zpowers_of_pow hk)
    (Subgroup.zpowers_le.mpr hz)
  have h := hle (conj_mem_rightConjugate (Subgroup.mem_zpowers z) c)
  have hcz : c * z = z * c := congrArg Subtype.val (hK.is_comm.comm ⟨c, hc⟩ ⟨z, hz⟩)
  have hz' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group
  rwa [hz'] at h

omit [Finite X] in
theorem mk_eq_one_of_odd {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {P : Subgroup X}
    (hP : IsPGroup 2 P) {x : X} (hx : x ∈ P) (h1 : QuotientGroup.mk' N x = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact eq_one_of_two_pow_of_odd ((QuotientGroup.eq_one_iff x).mp h1) hN
    (congrArg Subtype.val hk)

theorem odd_card_oddCore_map (A : Subgroup X) :
    Odd (Nat.card ((CFSG.oddCore A).map A.subtype)) := by
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact odd_card_oddCore A

structure Pre49 (A T S Q H : Subgroup X) : Prop where
  sylowFrame : SylowFrame A T S
  hyp43 : Hyp43 A T Q H
  top : A ⊔ T = ⊤
  quasisimple : IsQuasisimple A
  pRank_lt : 1 < pRank 2 T
  not_le : ¬ A ≤ H
  rank : pRank 2 (centerOf A ⊓ Subgroup.centralizer (T : Set X)) ≤ pRank 2 T
  none : ∀ a ∈ A, (∃ k : ℕ, a ^ (2 ^ k) = 1) → a ∈ Subgroup.centralizer (T : Set X) →
    a ∈ centerOf A

namespace Pre49

variable {A T S Q H : Subgroup X}

theorem frame (p : Pre49 A T S Q H) : Frame A T := p.sylowFrame.toFrame

theorem normal (p : Pre49 A T S Q H) : (⊤ : Subgroup X) ≤ Subgroup.normalizer (A : Set X) := by
  rw [← p.top]
  exact sup_le Subgroup.le_normalizer p.frame.le_normalizer

theorem oddCore_normal (p : Pre49 A T S Q H) : ((CFSG.oddCore A).map A.subtype).Normal := by
  have : (CFSG.oddCore A).Characteristic := OddCore.characteristic A
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro x _
  exact mem_normalizer_map_of_characteristic (CFSG.oddCore A) (p.normal (Subgroup.mem_top x))

theorem oddCore_le (p : Pre49 A T S Q H) : (CFSG.oddCore A).map A.subtype ≤ H := by
  obtain ⟨E, hET, hE4, hEel⟩ := exists_four_le p.pRank_lt
  have : ((CFSG.oddCore A).map A.subtype).Normal := p.oddCore_normal
  have hON : E ≤ Subgroup.normalizer
      (((CFSG.oddCore A).map A.subtype : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  apply le_of_centralizers_le hE4 hEel hON (odd_card_oddCore_map A)
  intro e he he1
  exact (inf_le_inf_right _ ((Subgroup.map_subtype_le _).trans le_sup_left)).trans
    (p.hyp43.centralizer_le p.frame (hET he) he1)

theorem oddCore_ne_top (p : Pre49 A T S Q H) : CFSG.oddCore A ≠ ⊤ := by
  intro htop
  apply p.not_le
  intro a ha
  apply p.oddCore_le
  exact ⟨⟨a, ha⟩, htop ▸ Subgroup.mem_top _, rfl⟩

variable {N : Subgroup X} [N.Normal]

theorem quasisimple_quotient (p : Pre49 A T S Q H)
    (hN : N = (CFSG.oddCore A).map A.subtype) : IsQuasisimple (A.map (QuotientGroup.mk' N)) := by
  set f := (QuotientGroup.mk' N).comp A.subtype
  have hker : f.ker ≠ ⊤ := by
    intro htop
    apply p.oddCore_ne_top
    rw [eq_top_iff]
    intro a _
    have ha : f a = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top a)
    have h1 : (a : X) ∈ N := (QuotientGroup.eq_one_iff _).mp ha
    rw [hN] at h1
    obtain ⟨b, hb, hba⟩ := h1
    rwa [← Subtype.ext hba]
  have hq := Quasisimple.range_quasisimple_of_ker_ne_top p.quasisimple f hker
  have hrange : f.range = A.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact Components.quasisimple_of_equiv (MulEquiv.subgroupCongr hrange).symm hq

omit [Finite X] in
theorem ker_subgroupMap (hN : N = (CFSG.oddCore A).map A.subtype) :
    ((QuotientGroup.mk' N).subgroupMap A).ker = CFSG.oddCore A := by
  ext a
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change ((a : X) : X ⧸ N) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, hN]
  constructor
  · rintro ⟨b, hb, hba⟩
    rwa [← Subtype.ext hba]
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem oddCore_quotient (hN : N = (CFSG.oddCore A).map A.subtype) :
    CFSG.oddCore (A.map (QuotientGroup.mk' N)) = ⊥ := by
  set ρ := (QuotientGroup.mk' N).subgroupMap A
  have hρ : Function.Surjective ρ := (QuotientGroup.mk' N).subgroupMap_surjective A
  have hker : ρ.ker = CFSG.oddCore A := ker_subgroupMap hN
  have hle := comap_oddCore_le ρ hρ (by rw [hker]; exact odd_card_oddCore A)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := hρ x
  have ha : a ∈ CFSG.oddCore A := hle hx
  rw [← hker] at ha
  exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp ha)

theorem not_le_quotient (p : Pre49 A T S Q H) (hN : N = (CFSG.oddCore A).map A.subtype) :
    ¬ A.map (QuotientGroup.mk' N) ≤ H.map (QuotientGroup.mk' N) := by
  intro hle
  apply p.not_le
  intro a ha
  have h1 : a ∈ H ⊔ N := mk_mem_map_iff.mp (hle (Subgroup.mem_map_of_mem _ ha))
  have hNH : N ≤ H := by rw [hN]; exact p.oddCore_le
  rwa [sup_eq_left.mpr hNH] at h1

theorem exists_lift (p : Pre49 A T S Q H) (hN : N = (CFSG.oddCore A).map A.subtype)
    {x : X ⧸ N} (hxA : x ∈ A.map (QuotientGroup.mk' N)) {j : ℕ} (hxj : x ^ (2 ^ j) = 1)
    (hxC : x ∈ Subgroup.centralizer ((T.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
      Set (X ⧸ N))) :
    ∃ a ∈ A, (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧ a ∈ Subgroup.centralizer (T : Set X) ∧
      QuotientGroup.mk' N a = x := by
  have hodd : Odd (Nat.card N) := by rw [hN]; exact odd_card_oddCore_map A
  obtain ⟨c, hcC, rfl⟩ := centralizer_map_le_of_odd hodd p.frame.isPGroup hxC
  have hcA : c ∈ A := by
    have h1 : c ∈ A ⊔ N := mk_mem_map_iff.mp hxA
    have hNA : N ≤ A := by rw [hN]; exact Subgroup.map_subtype_le _
    rwa [sup_eq_left.mpr hNA] at h1
  obtain ⟨m, hm2, hmx⟩ := exists_pow_two_element (QuotientGroup.mk' N) c hxj
  exact ⟨c ^ m, A.pow_mem hcA m, hm2, Subgroup.pow_mem _ hcC m, hmx⟩

theorem none_quotient (p : Pre49 A T S Q H) (hN : N = (CFSG.oddCore A).map A.subtype) :
    ∀ x ∈ A.map (QuotientGroup.mk' N), (∃ k : ℕ, x ^ (2 ^ k) = 1) →
      x ∈ Subgroup.centralizer ((T.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
        Set (X ⧸ N)) → x ∈ centerOf (A.map (QuotientGroup.mk' N)) := by
  rintro x hxA ⟨j, hj⟩ hxC
  obtain ⟨a, haA, ha2, haC, rfl⟩ := p.exists_lift hN hxA hj hxC
  have haZ := p.none a haA ha2 haC
  refine ⟨hxA, Subgroup.mem_centralizer_iff.mpr ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp haZ.2 b hb]

theorem central (p : Pre49 A T S Q H) {z : X}
    (hz : z ∈ centerOf A ⊓ Subgroup.centralizer (T : Set X)) (x : X) : x * z = z * x := by
  have hx : x ∈ A ⊔ T := p.top ▸ Subgroup.mem_top x
  have hxm : x ∈ (A : Set X) * (T : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A T p.frame.le_normalizer]
    exact hx
  obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.mp hxm
  have hza : a * z = z * a := Subgroup.mem_centralizer_iff.mp hz.1.2 a ha
  have hzt : t * z = z * t := Subgroup.mem_centralizer_iff.mp hz.2 t ht
  calc a * t * z = a * (t * z) := by group
    _ = a * (z * t) := by rw [hzt]
    _ = (a * z) * t := by group
    _ = (z * a) * t := by rw [hza]
    _ = z * (a * t) := by group

theorem rank_quotient (p : Pre49 A T S Q H) (hN : N = (CFSG.oddCore A).map A.subtype) :
    pRank 2 (centerOf (A.map (QuotientGroup.mk' N)) ⊓ Subgroup.centralizer
      ((T.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N))) ≤
      pRank 2 (T.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N
  set K := centerOf A ⊓ Subgroup.centralizer (T : Set X) with hK
  have hodd : Odd (Nat.card N) := by rw [hN]; exact odd_card_oddCore_map A
  have hKn : K.Normal := ⟨fun z hz x => by rw [p.central hz x, mul_inv_cancel_right]; exact hz⟩
  have hKcomm : IsMulCommutative K := ⟨⟨fun a b => Subtype.ext (p.central b.2 a)⟩⟩
  have hPsyl : IsSylowOf 2 (S ⊓ K) K :=
    p.sylowFrame.sylow.inf_of_le_normalizer (by rw [p.top]; exact le_top)
      (by rw [p.top, Subgroup.normalizer_eq_top])
  have hP2 : IsPGroup 2 (S ⊓ K : Subgroup X) := p.sylowFrame.sylow.isPGroup.to_inf_left
  obtain ⟨E, hEle, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two
    (centerOf (A.map π) ⊓ Subgroup.centralizer ((T.map π : Subgroup (X ⧸ N)) : Set (X ⧸ N)))
  have hEP : E ≤ (S ⊓ K).map π := by
    intro x hx
    have hx' := hEle hx
    obtain ⟨a, haA, ⟨k, hk⟩, haC, rfl⟩ := p.exists_lift hN hx'.1.1 (j := 1)
      (by rw [pow_one]; exact hEel.2 _ hx) hx'.2
    have haZ := p.none a haA ⟨k, hk⟩ haC
    exact Subgroup.mem_map_of_mem π
      (mem_of_isSylowOf_of_isMulCommutative hPsyl hKcomm ⟨haZ, haC⟩ hk)
  have h1 := CFSG.SectionRank.le_pRank one_lt_two hEP hEel hEcard
  rw [pRank_map_eq_of_ker π fun x hx h1 => mk_eq_one_of_odd hodd hP2 hx h1] at h1
  rw [pRank_map_eq_of_ker π fun t ht h1 => mk_eq_one_of_odd hodd p.frame.isPGroup ht h1]
  exact h1.trans ((CFSG.SectionRank.pRank_mono one_lt_two inf_le_right).trans p.rank)

theorem core49 (p : Pre49 A T S Q H) (hN : N = (CFSG.oddCore A).map A.subtype) :
    Core49 (A.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N))
      (S.map (QuotientGroup.mk' N)) (Q.map (QuotientGroup.mk' N))
      (H.map (QuotientGroup.mk' N)) := by
  have hNA : N ≤ A := by rw [hN]; exact Subgroup.map_subtype_le _
  have hodd : Odd (Nat.card N) := by rw [hN]; exact odd_card_oddCore_map A
  exact
    { sylowFrame := p.sylowFrame.map_odd p.top N hNA hodd
      hyp43 := Hyp43.map_odd p.frame p.hyp43 p.top N hNA hodd
      top := by
        rw [← Subgroup.map_sup, p.top,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      quasisimple := p.quasisimple_quotient hN
      oddCore := oddCore_quotient hN
      pRank_lt := by
        rw [pRank_map_eq_of_ker _ fun t ht h1 => mk_eq_one_of_odd hodd p.frame.isPGroup ht h1]
        exact p.pRank_lt
      not_le := p.not_le_quotient hN
      rank := p.rank_quotient hN
      none := p.none_quotient hN }

theorem false (p : Pre49 A T S Q H) (h48 : Theorem48Statement) : False := by
  have : ((CFSG.oddCore A).map A.subtype).Normal := p.oddCore_normal
  exact (p.core49 rfl).false h48

end Pre49

end CFSG.ComponentClassification.AschbacherTheorem3
