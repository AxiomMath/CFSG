module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFiveBar
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Conj

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open scoped Pointwise

namespace RankOne

section Solvable

theorem isSolvable_of_isCyclic_sylow {X : Type*} [Group X] [Finite X] (P : Sylow 2 X)
    (hP : IsCyclic P) : Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨hnormal, hodd, hindex, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement P hP
  have hs1 : Group.IsSolvable (CFSG.pPrimeCore 2 X) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : (CFSG.pPrimeCore 2 X).Normal := hnormal
  have hs2 : Group.IsSolvable (X ⧸ CFSG.pPrimeCore 2 X) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hq : IsPGroup 2 (X ⧸ CFSG.pPrimeCore 2 X) :=
      IsPGroup.of_card (n := n) (by rw [← Subgroup.index_eq_card, hindex, hn])
    have := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (CFSG.pPrimeCore 2 X)

variable {G : Type*} [Group G]

theorem isSolvable_of_isSylowOf_isCyclic [Finite G] {P K : Subgroup G} (hP : IsSylowOf 2 P K)
    (hc : IsCyclic P) : Group.IsSolvable K := by
  obtain ⟨R, rfl⟩ := hP
  refine isSolvable_of_isCyclic_sylow R ?_
  exact isCyclic_of_surjective
    ((R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem isSolvable_sup_of_le_normalizer {H N : Subgroup G} (hHN : H ≤ normalizer (N : Set G))
    (hH : Group.IsSolvable H) (hN : Group.IsSolvable N) :
    Group.IsSolvable (H ⊔ N : Subgroup G) := by
  set L := H ⊔ N with hL
  have hNL : N ≤ L := le_sup_right
  have hHL : H ≤ L := le_sup_left
  have hn : (N.subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNL).mpr (sup_le hHN le_normalizer)
  have : Group.IsSolvable (N.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hNL).toMonoidHom)
      (subgroupOfEquivOfLe hNL).injective
  have : Group.IsSolvable (L ⧸ N.subgroupOf L) := by
    let f : H →* L ⧸ N.subgroupOf L := (QuotientGroup.mk' _).comp (Subgroup.inclusion hHL)
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf L) z
      have hl : (l : G) ∈ (H : Set G) * (N : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right H N hHN]
        exact l.2
      obtain ⟨h, hh, n, hn', hhn⟩ := Set.mem_mul.mp hl
      refine ⟨⟨h, hh⟩, ?_⟩
      change QuotientGroup.mk' (N.subgroupOf L) (Subgroup.inclusion hHL ⟨h, hh⟩) = _
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      rw [mem_subgroupOf]
      have : ((Subgroup.inclusion hHL ⟨h, hh⟩)⁻¹ * l : L) = (n : G) := by
        change h⁻¹ * (l : G) = n
        rw [← hhn]
        group
      rw [this]
      exact hn'
    exact Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient (N.subgroupOf L)

end Solvable

section Shapes

variable {X : Type} [Group X] [Finite X]

theorem isCyclic_of_le_isDihedral {P Z : Subgroup X}
    (hP : AschbacherTheorem3.IsDihedralTwoGroup P) (hZP : Z ≤ P) (hZ : ¬ HasFourGroup Z) :
    IsCyclic Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := hP
  have hcard : Nat.card P = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← pow_succ']
    congr 1
    omega
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hcard
  have hY : AschbacherKnownGroup.HasDihedralSylowTwo P := by
    have htop : IsPGroup 2 (⊤ : Subgroup P) := hP2.of_equiv Subgroup.topEquiv.symm
    let S₀ : Sylow 2 P := htop.toSylow (by rw [index_top]; norm_num)
    refine ⟨S₀, n, hn, ⟨?_⟩⟩
    exact (MulEquiv.subgroupCongr (IsPGroup.toSylow_coe htop _)).trans (Subgroup.topEquiv.trans e)
  have hZ2 : IsPGroup 2 (Z.subgroupOf P) := hP2.to_subgroup _
  have hr : CFSG.Open.pRank 2 (Z.subgroupOf P) ≤ 1 := by
    by_contra h
    obtain ⟨E, hEZ, hE, hE4⟩ := hasFourGroup_of_one_lt_pRank (X := Z.subgroupOf P) (by omega)
    apply hZ
    refine ⟨E.map P.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hEZ hx
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hE x hx)
    · rw [card_map_of_injective P.subtype_injective, hE4]
  have hc := AschbacherTheorem5.Involution.isCyclic_of_pRank_le_one_of_dihedral hY hZ2 hr
  exact isCyclic_of_surjective (subgroupOfEquivOfLe hZP).toMonoidHom (MulEquiv.surjective _)

end Shapes

theorem hasFourGroup_of_isSylowOf {G : Type} [Group G] [Finite G] {P L : Subgroup G}
    (hP : IsSylowOf 2 P L) (h4 : HasFourGroup L) : HasFourGroup P := by
  obtain ⟨E, hEL, hE, hE4⟩ := h4
  obtain ⟨c, -, hc⟩ :=
    AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hP (isPGroup_of_sq_eq_one hE) hEL
  exact (hasFourGroup_rightConjugate_iff.mpr ⟨E, le_rfl, hE, hE4⟩).mono hc

section Bar

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barHom {Q P : Subgroup G} (hPN : P ≤ normalizer (Q : Set G)) :
    P →* bar Q P :=
  ((toBar Q).comp (Subgroup.inclusion hPN)).codRestrict (bar Q P) fun p =>
    toBar_mem_bar Q (h := Subgroup.inclusion hPN p) p.2

theorem barHom_bijective {Q P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (Q : Set G)) : Function.Bijective (barHom hPN) := by
  refine ⟨fun p q hpq => ?_, fun x => ?_⟩
  · have h := congrArg Subtype.val hpq
    have h' := toBar_injOn_of_isPGroup (D := Q) hP (u := Subgroup.inclusion hPN p)
      (v := Subgroup.inclusion hPN q) p.2 q.2 h
    exact Subgroup.inclusion_injective hPN h'
  · obtain ⟨h, hhP, hx⟩ := (mem_bar_iff Q P x).mp x.2
    refine ⟨⟨h, hhP⟩, Subtype.ext ?_⟩
    rw [← hx]
    rfl

@[expose] noncomputable def barEquiv {Q P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (Q : Set G)) : P ≃* bar Q P :=
  MulEquiv.ofBijective (barHom hPN) (barHom_bijective hP hPN)

theorem mul_comm_of_bar {Q P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (Q : Set G))
    (h : ∀ x ∈ bar Q P, ∀ y ∈ bar Q P, x * y = y * x) {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    a * b = b * a := by
  set e := barEquiv hP hPN
  have h1 : e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ :=
    Subtype.ext (h _ (e ⟨a, ha⟩).2 _ (e ⟨b, hb⟩).2)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (e.injective h1)

end Bar

section Elementary

variable {G : Type*} [Group G]

theorem two_dvd_card_of_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    2 ∣ Nat.card P := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rcases n with _ | n
  · exact absurd (Subgroup.eq_bot_of_card_eq P (by rw [hn, pow_zero])) hP1
  · rw [hn, pow_succ]
    exact dvd_mul_left 2 _

theorem eq_one_of_mem_of_mem [Finite G] {P O : Subgroup G} (hP : IsPGroup 2 P)
    (hO : Odd (Nat.card O)) {x : G} (hxP : x ∈ P) (hxO : x ∈ O) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk x hxO]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem commute_of_inf_eq_bot {X Y : Subgroup G} (hXY : X ≤ normalizer (Y : Set G))
    (hYX : Y ≤ normalizer (X : Set G)) (h : X ⊓ Y = ⊥) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) :
    x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ X := by
    have : y * x⁻¹ * y⁻¹ ∈ X := (mem_normalizer_iff.mp (hYX hy) x⁻¹).mp (inv_mem hx)
    simpa [mul_assoc] using mul_mem hx this
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ Y :=
    mul_mem ((mem_normalizer_iff.mp (hXY hx) y).mp hy) (inv_mem hy)
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [← mem_bot, ← h]
    exact mem_inf.mpr ⟨h1, h2⟩
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

end Elementary

end RankOne

end CFSG.ComponentClassification.Asc75T4
