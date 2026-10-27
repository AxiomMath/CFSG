module

public import CFSG.GH74.GLS.C3.Layer1.BkL92
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Small
public import CFSG.GH74.GLS.C3.Layer1.St1Thm5

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
open CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.C3.Layer1.Back
open scoped Pointwise commutatorElement

section Pure

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_complement_zpowers {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) {x : G}
    (hxA : x ∈ A) (hx2 : orderOf x = 2) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ A₀ ⊓ zpowers x = ⊥ ∧ Nat.card ↥A₀ * 2 = Nat.card ↥A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : ↥A := ⟨x, hxA⟩ with hx'
  have hcomm : ∀ a b : ↥A, a * b = b * a := fun a b => hA.toIsMulCommutative.is_comm.comm a b
  obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 2 ↥A (zpowers x')
  refine ⟨C.map A.subtype, Subgroup.map_subtype_le C, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨⟨c, hc, rfl⟩, hgx⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgx
    have hcx : c ∈ zpowers x' := ⟨j, Subtype.ext (by simpa [hx'] using hj)⟩
    have h1 : c ∈ zpowers x' ⊓ C := ⟨hcx, hc⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _
  · have hdisj : Disjoint (zpowers x') C := hC.disjoint
    have hnorm : zpowers x' ≤ normalizer (C : Set ↥A) := by
      intro h _
      rw [Subgroup.mem_normalizer_iff]
      intro c
      rw [show h * c * h⁻¹ = c by rw [hcomm h c]; group]
    have hmul : ((zpowers x' : Subgroup ↥A) : Set ↥A) * (C : Set ↥A) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm, hC.sup_eq_top]
      rfl
    have hcompl : Subgroup.IsComplement' (zpowers x') C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
    have hcard := hcompl.card_mul_card
    have hz : Nat.card ↥(zpowers x') = 2 := by
      rw [Nat.card_zpowers, hx', Subgroup.orderOf_mk, hx2]
    rw [hz] at hcard
    rw [Subgroup.card_map_of_injective A.subtype_injective, mul_comm]
    exact hcard

theorem inf_le_zpowers_of_pRank_one {A C : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) {x : G}
    (hxA : x ∈ A) (hxC : x ∈ C) (hx2 : orderOf x = 2) (hC1 : CFSG.pRank 2 ↥C = 1) :
    A ⊓ C ≤ zpowers x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup G := A ⊓ C with hE
  have hsq : ∀ a ∈ E, a ^ 2 = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha.1
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨a, ha.1⟩ : ↥A) ⟨b, hb.1⟩)
  have hEel : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hsq⟩
  have hpg : IsPGroup 2 ↥E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hsq g g.2⟩
  obtain ⟨r, hr⟩ := hpg.exists_card_eq
  have hrk : r ≤ CFSG.pRank 2 ↥C := by
    rw [CFSG.GH74.GLS.TwoThin.pRank_two_subgroup_eq_open]
    exact CFSG.SectionRank.le_pRank one_lt_two inf_le_right hEel hr
  rw [hC1] at hrk
  have hZE : zpowers x ≤ E := zpowers_le.2 ⟨hxA, hxC⟩
  have hZcard : Nat.card ↥(zpowers x) = 2 := by rw [Nat.card_zpowers, hx2]
  have hEc : Nat.card ↥E ≤ 2 := by
    rw [hr]
    calc 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 2 := by norm_num
  have hEeq : zpowers x = E := Subgroup.eq_of_le_of_card_ge hZE (by rw [hZcard]; exact hEc)
  exact hEeq.ge


omit [Finite G] in
theorem mem_normalizer_sup_zpowers {E : Subgroup G} {y k : G} (hk : k ∈ normalizer (E : Set G))
    (hky : k * y * k⁻¹ = y) : k ∈ normalizer ((E ⊔ zpowers y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have hmapE : E.map (MulAut.conj k).toMonoidHom = E := by
    ext g
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hk e).1 he
    · intro hg
      refine ⟨k⁻¹ * g * k, ?_, ?_⟩
      swap
      · show k * (k⁻¹ * g * k) * k⁻¹ = g
        group
      · refine (Subgroup.mem_normalizer_iff.1 hk (k⁻¹ * g * k)).2 ?_
        rw [show k * (k⁻¹ * g * k) * k⁻¹ = g by group]
        exact hg
  have hmapZ : (zpowers y).map (MulAut.conj k).toMonoidHom = zpowers y := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hky]
  have hmapQ : (E ⊔ zpowers y).map (MulAut.conj k).toMonoidHom = E ⊔ zpowers y := by
    rw [Subgroup.map_sup, hmapE, hmapZ]
  intro h
  constructor
  · intro hh
    have : (MulAut.conj k).toMonoidHom h ∈ (E ⊔ zpowers y).map (MulAut.conj k).toMonoidHom :=
      ⟨h, hh, rfl⟩
    rw [hmapQ] at this
    simpa [MulAut.conj_apply] using this
  · intro hh
    have : k * h * k⁻¹ ∈ (E ⊔ zpowers y).map (MulAut.conj k).toMonoidHom := by
      rw [hmapQ]
      exact hh
    obtain ⟨q, hq, hqh⟩ := this
    have : q = h := (MulAut.conj k).injective (by simpa [MulAut.conj_apply] using hqh)
    rw [← this]
    exact hq

theorem gammaIn_le_gammaK {x : G} {K : Subgroup G} (hK : K ≤ centralizer ({x} : Set G))
    {A A₀ : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) (hxA : x ∈ A) (hx2 : orderOf x = 2)
    (hA₀ : A₀ ≤ A) (hA₀x : A₀ ⊓ zpowers x = ⊥) : gammaIn K A₀ ≤ gammaK 2 A 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine iSup_le fun E => iSup_le fun hEA₀ => iSup_le fun hE1 => ?_
  have hEA : E ≤ A := hEA₀.trans hA₀
  have hEne : E ≠ ⊥ := by
    rintro rfl
    rw [Back.pRank_bot_eq_zero] at hE1
    omega
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    apply hEne
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    exact hcon ⟨g, hg, hg1⟩
  have hsqA : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
  set Q : Subgroup G := E ⊔ zpowers x with hQ
  have hQA : Q ≤ A := sup_le hEA (zpowers_le.2 hxA)
  have hQel : CFSG.Open.IsElemAbelian 2 Q := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcommA a (hQA a.2) b (hQA b.2))⟩⟩, fun a ha => hsqA a (hQA ha)⟩
  have hpg : IsPGroup 2 ↥Q := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hsqA g (hQA g.2)⟩
  obtain ⟨r, hr⟩ := hpg.exists_card_eq
  have hZ : Nat.card ↥(zpowers x) = 2 := by rw [Nat.card_zpowers, hx2]
  have hZQ : zpowers x ≤ Q := le_sup_right
  have heQ : e ∈ Q := Subgroup.mem_sup_left he
  have hex : e ∉ zpowers x := by
    intro h
    have : e ∈ A₀ ⊓ zpowers x := ⟨hEA₀ he, h⟩
    rw [hA₀x, Subgroup.mem_bot] at this
    exact he1 this
  have hQ2 : 2 < Nat.card ↥Q := by
    have hle : 2 ≤ Nat.card ↥Q := hZ ▸ Subgroup.card_le_of_le hZQ
    by_contra hcon
    have h2 : Nat.card ↥Q = 2 := by omega
    have heq : zpowers x = Q := Subgroup.eq_of_le_of_card_ge hZQ (by rw [hZ, h2])
    exact hex (heq ▸ heQ)
  have hr2 : 2 ≤ r := by
    by_contra hcon
    have : r ≤ 1 := by omega
    have : 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hQrank : 2 ≤ CFSG.pRank 2 ↥Q := by
    rw [CFSG.GH74.GLS.TwoThin.pRank_two_subgroup_eq_open]
    exact hr2.trans (CFSG.SectionRank.le_pRank one_lt_two le_rfl hQel hr)
  refine le_iSup_of_le Q (le_iSup_of_le hQA (le_iSup_of_le hQrank ?_))
  intro k hk
  obtain ⟨hkE, hkK⟩ := hk
  have hkx : k * x * k⁻¹ = x := by
    have := mem_centralizer_singleton_iff.1 (hK hkK)
    rw [this]
    group
  exact mem_normalizer_sup_zpowers hkE hkx

end Pure

section Hbot

variable {G : Type} [Group G] [Finite G]

theorem inf_CMK_eq_bot_of_complement {x : G} {K : Subgroup G} (hxC : x ∈ CxK x K)
    (hx2 : orderOf x = 2) (hC1 : CFSG.pRank 2 ↥(CxK x K) = 1) {A A₀ : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A) (hxA : x ∈ A) (hAC : A ≤ centralizer ({x} : Set G))
    (hA₀A : A₀ ≤ A) (hA₀x : A₀ ⊓ zpowers x = ⊥) :
    A₀ ⊓ CMK (normalizer (K : Set G)) K = ⊥ := by
  have hAC1 : A ⊓ CxK x K ≤ zpowers x := inf_le_zpowers_of_pRank_one hA hxA hxC hx2 hC1
  rw [eq_bot_iff]
  rintro a ⟨haA₀, haCMK⟩
  have haCxK : a ∈ CxK x K := ⟨hAC (hA₀A haA₀), (Subgroup.mem_inf.1 haCMK).2⟩
  have h1 : a ∈ A₀ ⊓ zpowers x := ⟨haA₀, hAC1 ⟨hA₀A haA₀, haCxK⟩⟩
  rw [hA₀x] at h1
  exact h1

end Hbot

section Main

variable {G : Type} [Group G] [Finite G]

theorem b_ivk_6_1_L29_aux
    {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (hL29 : HasL2Model (kBar K) (fun q => q = 9)) (hC1 : pRank 2 ↥(CxK x K) = 1)
    {A : Subgroup G} (hAN : A ≤ NxK x K) (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hcard : Nat.card ↥A = 2 ^ 4) (hxA : x ∈ A) : K ≤ gammaK 2 A 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := hpair.1
  have hKC : K ≤ centralizer ({x} : Set G) := hpair.2.1
  have hAM : A ≤ normalizer (K : Set G) := hAN.trans inf_le_right
  have hAC : A ≤ centralizer ({x} : Set G) := hAN.trans inf_le_left
  have hLn := hLn_normalizer K
  have hodd : HasL2Model (kBar K) Odd := by
    obtain ⟨p, f, hp, hf, hP, hL⟩ := hL29
    exact ⟨p, f, hp, hf, by rw [show p ^ f = 9 from hP]; decide, hL⟩
  obtain ⟨A₀, hA₀A, hA₀x, hA₀card⟩ := exists_complement_zpowers hA hxA hx2
  have hA₀8 : Nat.card ↥A₀ = 8 := by
    have : Nat.card ↥A = 16 := by rw [hcard]; norm_num
    omega
  have hA₀M : A₀ ≤ normalizer (K : Set G) := hA₀A.trans hAM
  have hbot := inf_CMK_eq_bot_of_complement hpair.x_mem_CxK hx2 hC1 hA hxA hAC hA₀A hA₀x
  have hψ := actV_injective hLn hA₀M hbot
  have hsqA : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
  have hA₀el : CFSG.IsElementaryAbelian 2 ↥A₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A₀).2
      ⟨⟨⟨fun a b => Subtype.ext (hcommA a (hA₀A a.2) b (hA₀A b.2))⟩⟩,
        fun a ha => hsqA a (hA₀A ha)⟩
  have hA₀2 : IsPGroup 2 ↥A₀ := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hsqA g (hA₀A g.2)⟩
  have hA₀rank : 2 ≤ pRank 2 ↥A₀ := by
    have h3 : 3 ≤ pRank 2 ↥A₀ :=
      le_pRank_of_elem le_rfl hA₀el (k := 3) (by rw [hA₀8]; norm_num)
    omega
  have e : ↥A₀ ≃* ↥(actV hLn A₀ hA₀M).range := MonoidHom.ofInjective hψ
  have hW2 : IsPGroup 2 ↥(actV hLn A₀ hA₀M).range :=
    hA₀2.of_surjective (actV hLn A₀ hA₀M).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have : Finite ↥(actV hLn A₀ hA₀M).range := Finite.of_equiv _ e.toEquiv
  have hWr : 2 ≤ CFSG.pRank 2 ↥(actV hLn A₀ hA₀M).range := by
    rw [← pRank_two_eq_of_mulEquiv e]
    exact hA₀rank
  have hΓW : gammaAut (kBar K) (actV hLn A₀ hA₀M).range = ⊤ := by
    by_contra hne
    have h4 := (CFSG.GH74.GLS.IVK.Proofs2.b_ivk_6 (kBar K) (actV hLn A₀ hA₀M).range
      (Or.inl hodd) hW2 hWr hne).2.1.2
    rw [← Nat.card_congr e.toEquiv, hA₀8] at h4
    omega
  have hle := gammaAut_le_barImg hLn hA₀M hψ
  rw [hΓW] at hle
  have htop : barImg K (gammaIn K A₀) = ⊤ := top_le_iff.1 hle
  have hKin : K ≤ gammaIn K A₀ :=
    le_of_barImg_eq_top (pPrimeCoreOf_le_gammaIn hLn hA₀M hA₀rank) htop
  exact hKin.trans (gammaIn_le_gammaK hKC hA hxA hx2 hA₀A hA₀x)

end Main

end CFSG.GH74.GLS.IVK.Proofs2
