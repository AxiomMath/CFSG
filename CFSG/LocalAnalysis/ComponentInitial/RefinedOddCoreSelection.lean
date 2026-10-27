module

public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.ComponentInitial.RankOneCentralizerStandardOrQuaternion

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.Assembly (IsComponentOf IsElemAbelian)
open CFSG.Assembly.ComponentType (IsTwoPComponent)

variable {G : Type*} [Group G]

@[expose] def RefinedMaxima (J A : Subgroup G) : Prop :=
  (∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G, IsComponentOf Q (centralizer ({t} : Set G)) →
    (center Q).index ≤ (center J).index) ∧
  (∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G, IsComponentOf Q (centralizer ({t} : Set G)) →
    IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
    (center Q).index = (center J).index →
      (CFSG.Assembly.oddCore Q).index ≤ (CFSG.Assembly.oddCore J).index) ∧
  ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G, IsComponentOf Q (centralizer ({t} : Set G)) →
    IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
    (center Q).index = (center J).index →
    (CFSG.Assembly.oddCore Q).index = (CFSG.Assembly.oddCore J).index →
    ∀ B : Subgroup G, B ≤ centralizer (Q : Set G) → IsElemAbelian 2 B → t ∈ B →
      Nat.card B ≤ Nat.card A

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.Assembly.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [assembly_oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

theorem index_oddCore_le_of_surjective {L J : Type*} [Group L] [Group J] [Finite L] [Finite J]
    {δ : L →* J} (hδ : Function.Surjective δ) :
    (CFSG.Assembly.oddCore J).index ≤ (CFSG.Assembly.oddCore L).index := by
  have himage : (CFSG.Assembly.oddCore L).map δ ≤ CFSG.Assembly.oddCore J := by
    refine le_sSup ⟨(CFSG.Assembly.oddCore_normal L).map δ hδ, ?_⟩
    exact Odd.of_dvd_nat (odd_card_oddCore L) (Subgroup.card_map_dvd _ _)
  let φ : L →* J ⧸ CFSG.Assembly.oddCore J := (QuotientGroup.mk' (CFSG.Assembly.oddCore J)).comp δ
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hδ
  have hker : CFSG.Assembly.oddCore L ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact himage ⟨x, hx, rfl⟩
  calc (CFSG.Assembly.oddCore J).index = Nat.card (J ⧸ CFSG.Assembly.oddCore J) := index_eq_card _
    _ = φ.ker.index := by rw [index_ker, MonoidHom.range_eq_top.2 hφ, card_top]
    _ ≤ (CFSG.Assembly.oddCore L).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) (index_dvd_of_le hker)

theorem exists_involution_of_isQuasisimple [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) : ∃ t ∈ L, orderOf t = 2 := by
  have hq := (AssemblyBPredicates.isQuasisimple_iff_native L).1 hL
  have heven : Even (Nat.card L) := by
    by_contra hodd
    exact not_isSolvable_of_isQuasisimple hq
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.1 hodd))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 (even_iff_two_dvd.1 heven)
  exact ⟨t, t.2, by rw [Subgroup.orderOf_coe, ht]⟩

theorem pRank_eq_one_of_card_le_two [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L)
    (hle : ∀ E : Subgroup G, E ≤ L → IsElemAbelian 2 E → Nat.card E ≤ 2) :
    CFSG.Assembly.pRank 2 L = 1 := by
  obtain ⟨t, htL, ht⟩ := exists_involution_of_isQuasisimple hL
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  refine pRank_eq_of_forall_card_le one_lt_two (zpowers_le.mpr htL)
    (isElemAbelian_iff_isElementaryAbelian.mpr (IsElementaryAbelian.zpowers_of_pow_eq_one ht2))
    (by rw [Nat.card_zpowers, ht, pow_one]) fun E hEL hE => ?_
  rw [pow_one]
  exact hle E hEL hE

theorem odd_card_ker_of_index_oddCore_eq {L J : Type*} [Group L] [Group J] [Finite L] [Finite J]
    {δ : L →* J} (hδ : Function.Surjective δ)
    (he : (CFSG.Assembly.oddCore L).index = (CFSG.Assembly.oddCore J).index) :
    Odd (Nat.card δ.ker) := by
  have h1 := (CFSG.Assembly.oddCore L).card_mul_index
  have h2 := (CFSG.Assembly.oddCore J).card_mul_index
  have h3 := δ.ker.card_mul_index
  have h4 : δ.ker.index = Nat.card J := by
    rw [index_ker, MonoidHom.range_eq_top.2 hδ, card_top]
  have he0 : 0 < (CFSG.Assembly.oddCore J).index :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have h5 : Nat.card δ.ker * Nat.card (CFSG.Assembly.oddCore J) =
      Nat.card (CFSG.Assembly.oddCore L) := by
    apply Nat.eq_of_mul_eq_mul_right he0
    calc Nat.card δ.ker * Nat.card (CFSG.Assembly.oddCore J) *
          (CFSG.Assembly.oddCore J).index =
        Nat.card δ.ker * Nat.card J := by rw [mul_assoc, h2]
      _ = Nat.card L := by rw [← h4, h3]
      _ = Nat.card (CFSG.Assembly.oddCore L) * (CFSG.Assembly.oddCore J).index := by
        rw [← he, h1]
  exact Odd.of_dvd_nat (odd_card_oddCore L) (Dvd.intro _ h5)

theorem card_le_of_quotient_odd [Finite G] {L : Subgroup G} {J : Type*} [Group J] [Finite J]
    {δ : L →* J} (hδ : Function.Surjective δ) (hodd : Odd (Nat.card δ.ker))
    {E : Subgroup J} (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 2 ^ CFSG.Assembly.pRank 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : L ⧸ δ.ker ≃* J := QuotientGroup.quotientKerEquivOfSurjective δ hδ
  have hE₁ : IsElemAbelian 2 (E.map q.symm.toMonoidHom) :=
    isElemAbelian_iff_isElementaryAbelian.mpr (IsElementaryAbelian.map _)
  have hcard : Nat.card (E.map q.symm.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective q.symm.injective
  have hle := card_le_pow_pRank_of_le (H := ⊤) le_top hE₁
  have hq : CFSG.Assembly.pRank 2 (⊤ : Subgroup (L ⧸ δ.ker)) ≤ CFSG.Assembly.pRank 2 L := by
    have h1 : CFSG.Open.pRank 2 (⊤ : Subgroup (L ⧸ δ.ker)) = CFSG.Open.pRank 2 (⊤ : Subgroup L) :=
      CFSG.SectionRank.pRank_quotient_eq δ.ker fun h => (Nat.not_even_iff_odd.2 hodd)
        (even_iff_two_dvd.2 h)
    have h2 := CFSG.SectionRank.pRank_le_map one_lt_two L.subtype L.subtype_injective ⊤
    rw [← MonoidHom.range_eq_map, range_subtype] at h2
    exact h1.le.trans h2
  rw [← hcard]
  exact hle.trans (Nat.pow_le_pow_right two_pos hq)

theorem diagonal_odd_core_rank_one [Finite G] {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) {J L A : Subgroup G}
    (hL : IsComponentOf L (centralizer ({b} : Set G)))
    (hLp : IsTwoPComponent (L.subgroupOf (centralizer ({b} : Set G))))
    (hLa : conjSub a⁻¹ L ≠ L) (hset : (J : Set G) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g})
    {δ : L →* J} (hδ : ∀ x : L, (δ x : G) = x * (a⁻¹ * x * a)) (hδs : Function.Surjective δ)
    (hiso : Nonempty (J ⧸ center J ≃* L ⧸ center L)) (hJq : CFSG.Assembly.IsQuasisimple J)
    (hA : A ≤ centralizer (J : Set G)) (hAe : IsElemAbelian 2 A) (haA : a ∈ A) (hbA : b ∈ A)
    (hmax : RefinedMaxima J A) :
    (CFSG.Assembly.oddCore L).index = (CFSG.Assembly.oddCore J).index ∧
      Odd (Nat.card δ.ker) ∧ CFSG.Assembly.pRank 2 J = 1 ∧ CFSG.Assembly.pRank 2 L = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : (center L).index = (center J).index := by
    obtain ⟨e⟩ := hiso
    rw [index_eq_card, index_eq_card]
    exact (Nat.card_congr e.toEquiv).symm
  have he : (CFSG.Assembly.oddCore L).index = (CFSG.Assembly.oddCore J).index :=
    le_antisymm (hmax.2.1 b hb L hL hLp hd) (index_oddCore_le_of_surjective hδs)
  have hodd : Odd (Nat.card δ.ker) := odd_card_ker_of_index_oddCore_eq hδs he
  set H := centralizer ({b} : Set G) with hHdef
  have haH : a ∈ H := Subgroup.mem_centralizer_singleton_iff.2 hab
  set a' : H := ⟨a, haH⟩ with ha'def
  have ha' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hL' : CFSG.IsComponent (L.subgroupOf H) :=
    (isComponentOf_iff_isComponent_subgroupOf hL.1).1 hL
  have hconjL : (conjSub a'⁻¹ (L.subgroupOf H)).map H.subtype = conjSub a⁻¹ L := by
    rw [map_subtype_conjSub, Subgroup.map_subgroupOf_eq_of_le hL.1]
    rfl
  have hLa' : conjSub a'⁻¹ (L.subgroupOf H) ≠ L.subgroupOf H := fun h =>
    hLa (by rw [← hconjL, h, Subgroup.map_subgroupOf_eq_of_le hL.1])
  obtain ⟨hJ'set, -, -, -, -, -, -, -, -, -, -, hAfacts⟩ :=
    diagonal_component_centralizer_index_two hL' hLa' ha'
  have hAc : IsMulCommutative A := hAe.1
  have hAH : A ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (hAc.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hA'CJ : A.subgroupOf H ≤ centralizer
      ((swapDiag (commutator_conjSub_eq_bot hL' hLa')).range : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x₀, hx₀, rfl⟩ := (Set.ext_iff.1 hJ'set y).1 hy
    have hyJ : ((x₀ * (a'⁻¹ * x₀ * a') : H) : G) ∈ J := by
      rw [← SetLike.mem_coe, hset]
      exact ⟨x₀, hx₀, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hA (Subgroup.mem_subgroupOf.1 hx)) _ hyJ)
  have hAe' : IsElementaryAbelian 2 A := isElemAbelian_iff_isElementaryAbelian.mp hAe
  have hA'e : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  obtain ⟨-, hB⟩ := hAfacts (A.subgroupOf H) hA'CJ hA'e haA
  have hA2 : 2 ≤ Nat.card A := by
    have h := orderOf_dvd_natCard (⟨a, haA⟩ : A)
    rw [Subgroup.orderOf_mk, ha] at h
    exact Nat.le_of_dvd Nat.card_pos h
  have hbot : A.subgroupOf H ⊓ centralizer ((L.subgroupOf H ⊔ conjSub a'⁻¹ (L.subgroupOf H) :
      Subgroup H) : Set H) ⊓ conjSub a'⁻¹ (L.subgroupOf H) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨⟨huA, -⟩, huLa⟩ := hu
    have huLa' : (u : G) ∈ conjSub a⁻¹ L := by
      rw [← hconjL]
      exact ⟨u, huLa, rfl⟩
    obtain ⟨x, hxL, hxu⟩ := huLa'
    have hua : (u : G) * a = a * u :=
      congrArg Subtype.val (hAc.is_comm.comm ⟨u, huA⟩ ⟨a, haA⟩)
    have hxu' : x = u := by
      have h1 : a⁻¹ * x * a = u := by simpa [MulAut.conj_apply] using hxu
      calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
        _ = a * u * a⁻¹ := by rw [h1]
        _ = u := by rw [← hua, mul_inv_cancel_right]
    have huL : (u : G) ∈ L := hxu' ▸ hxL
    have hu2 : (u : G) ^ 2 = 1 := hAe.2 _ huA
    have hker : (⟨u, huL⟩ : L) ∈ δ.ker := by
      rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      rw [hδ, Subgroup.coe_one]
      calc (u : G) * (a⁻¹ * u * a) = (u : G) * (a⁻¹ * (a * u)) := by rw [mul_assoc a⁻¹, hua]
        _ = (u : G) ^ 2 := by rw [inv_mul_cancel_left, pow_two]
        _ = 1 := hu2
    have hord : orderOf (⟨⟨u, huL⟩, hker⟩ : δ.ker) = 1 := by
      have h1 : orderOf (⟨⟨u, huL⟩, hker⟩ : δ.ker) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact Subtype.ext (Subtype.ext (by simpa using hu2))
      exact Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h1
        (orderOf_dvd_natCard _)
    rw [orderOf_eq_one_iff] at hord
    have : (u : G) = 1 := congrArg (fun z : δ.ker => ((z : L) : G)) hord
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hLbound : ∀ E : Subgroup G, E ≤ L → IsElemAbelian 2 E → Nat.card E ≤ 2 := by
    intro E hEL hE
    have hEe : IsElementaryAbelian 2 E := isElemAbelian_iff_isElementaryAbelian.mp hE
    have hBLa : conjSub a⁻¹ E ≤ conjSub a⁻¹ L := Subgroup.map_mono hEL
    have hBH : conjSub a⁻¹ E ≤ H := hBLa.trans (isComponentOf_conjSub_of_mem hL (inv_mem haH)).1
    have hB'le : (conjSub a⁻¹ E).subgroupOf H ≤ conjSub a'⁻¹ (L.subgroupOf H) := by
      intro x hx
      have hx' : (x : G) ∈ conjSub a⁻¹ L := hBLa hx
      rw [← hconjL] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rw [← Subtype.ext hyx]
      exact hy
    have hBe : IsElementaryAbelian 2 (conjSub a⁻¹ E) := IsElementaryAbelian.map _
    have hB'e : IsElementaryAbelian 2 ((conjSub a⁻¹ E).subgroupOf H) :=
      IsElementaryAbelian.subgroupOf hBH
    obtain ⟨hEC, hEe', hEcard⟩ := hB _ hB'le hB'e (by rw [hbot]; exact bot_le)
    set F : Subgroup G := (A.subgroupOf H ⊓ centralizer ((L.subgroupOf H ⊔
      conjSub a'⁻¹ (L.subgroupOf H) : Subgroup H) : Set H) ⊔
        (conjSub a⁻¹ E).subgroupOf H).map H.subtype with hFdef
    have hFC : F ≤ centralizer (L : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := Subgroup.mem_centralizer_iff.1 (hEC hy) ⟨l, hL.1 hl⟩
        (Subgroup.mem_subgroupOf.2 hl)
      exact congrArg Subtype.val this
    have hFe : IsElemAbelian 2 F := by
      have : IsElementaryAbelian 2 ↥(A.subgroupOf H ⊓ centralizer ((L.subgroupOf H ⊔
          conjSub a'⁻¹ (L.subgroupOf H) : Subgroup H) : Set H) ⊔
            (conjSub a⁻¹ E).subgroupOf H) := hEe'
      exact isElemAbelian_iff_isElementaryAbelian.mpr (IsElementaryAbelian.map _)
    have hbF : b ∈ F := by
      refine ⟨⟨b, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩, mem_sup_left ⟨hbA,
        Subgroup.mem_centralizer_iff.2 fun y _ =>
          Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)⟩, rfl⟩
    have hFcard : Nat.card F = Nat.card A * Nat.card E / 2 := by
      rw [hFdef, Subgroup.card_map_of_injective H.subtype_injective, hEcard, hbot,
        Subgroup.card_bot, mul_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv, card_conjSub]
    have hle := hmax.2.2 b hb L hL hLp hd he F hFC hFe hbF
    rw [hFcard] at hle
    by_contra hlt
    have h3 : Nat.card A * 3 ≤ Nat.card A * Nat.card E := Nat.mul_le_mul_left _ (by omega)
    have h4 := Nat.div_le_div_right (c := 2) h3
    omega
  have hL1 : CFSG.Assembly.pRank 2 L = 1 := pRank_eq_one_of_card_le_two hL.2.2 hLbound
  refine ⟨he, hodd, pRank_eq_one_of_card_le_two hJq fun E hEJ hE => ?_, hL1⟩
  have hEe : IsElementaryAbelian 2 E := isElemAbelian_iff_isElementaryAbelian.mp hE
  have h1 := card_le_of_quotient_odd hδs hodd (IsElementaryAbelian.subgroupOf (H := E) hEJ)
  rw [hL1, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv] at h1
  exact h1

theorem exists_refined_selection {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    ∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G, IsComponentOf J (centralizer ({a} : Set G)) ∧
      IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))) ∧
      ∃ A : Subgroup G, A ≤ centralizer (J : Set G) ∧ IsElemAbelian 2 A ∧ a ∈ A ∧
        RefinedMaxima J A := by
  obtain ⟨a₀, ha₀, J₀, hJ₀p, hJ₀, -, hmax₀, -, -⟩ :=
    local_B_maximal_component_commuting_involution_propagation hC hpump hK hcomp hB
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let S₂ := {p : G × Subgroup G // orderOf p.1 = 2 ∧
    IsComponentOf p.2 (centralizer ({p.1} : Set G)) ∧
    IsTwoPComponent (p.2.subgroupOf (centralizer ({p.1} : Set G))) ∧
    (center p.2).index = (center J₀).index}
  have : Nonempty S₂ := ⟨⟨(a₀, J₀), ha₀, hJ₀, hJ₀p, rfl⟩⟩
  obtain ⟨⟨⟨t₁, Q₁⟩, ht₁, hQ₁, hQ₁p, hQ₁d⟩, hmax₁⟩ :=
    Finite.exists_max (fun p : S₂ => (CFSG.Assembly.oddCore p.1.2).index)
  let S₃ := {p : G × Subgroup G × Subgroup G // orderOf p.1 = 2 ∧
    IsComponentOf p.2.1 (centralizer ({p.1} : Set G)) ∧
    IsTwoPComponent (p.2.1.subgroupOf (centralizer ({p.1} : Set G))) ∧
    (center p.2.1).index = (center J₀).index ∧
    (CFSG.Assembly.oddCore p.2.1).index = (CFSG.Assembly.oddCore Q₁).index ∧
    p.2.2 ≤ centralizer (p.2.1 : Set G) ∧ IsElemAbelian 2 p.2.2 ∧ p.1 ∈ p.2.2}
  have ht₁C : t₁ ∈ centralizer (Q₁ : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hQ₁.1 hq)
  have ht₁2 : t₁ ^ 2 = 1 := ht₁ ▸ pow_orderOf_eq_one t₁
  have : Nonempty S₃ := ⟨⟨(t₁, Q₁, zpowers t₁), ht₁, hQ₁, hQ₁p, hQ₁d, rfl,
    zpowers_le.mpr ht₁C, isElemAbelian_iff_isElementaryAbelian.mpr
      (IsElementaryAbelian.zpowers_of_pow_eq_one ht₁2), mem_zpowers t₁⟩⟩
  obtain ⟨⟨⟨a, J, A⟩, ha, hJ, hJp, hJd, hJe, hAC, hAe, haA⟩, hmax₃⟩ :=
    Finite.exists_max (fun p : S₃ => Nat.card p.1.2.2)
  refine ⟨a, ha, J, hJ, hJp, A, hAC, hAe, haA, fun t ht Q hQ => ?_,
    fun t ht Q hQ hQp hQd => ?_, fun t ht Q hQ hQp hQd hQe B hBC hBe htB => ?_⟩
  · exact hJd ▸ hmax₀ t ht Q hQ
  · exact hJe ▸ hmax₁ ⟨(t, Q), ht, hQ, hQp, hQd.trans hJd⟩
  · exact hmax₃ ⟨(t, Q, B), ht, hQ, hQp, hQd.trans hJd, hQe.trans hJe, hBC, hBe, htB⟩

theorem mem_of_central_involution [Finite G] {a : G} (ha : orderOf a = 2) {J A : Subgroup G}
    (hJ : IsComponentOf J (centralizer ({a} : Set G)))
    (hJp : IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))))
    (hAC : A ≤ centralizer (J : Set G)) (hAe : IsElemAbelian 2 A) (haA : a ∈ A)
    (hmax : RefinedMaxima J A) {c : G} (hcJ : c ∈ J) (hcC : c ∈ centralizer (J : Set G))
    (hc : orderOf c = 2) : c ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : c ^ 2 = 1 := hc ▸ pow_orderOf_eq_one c
  have : IsElementaryAbelian 2 A := isElemAbelian_iff_isElementaryAbelian.mp hAe
  have : IsElementaryAbelian 2 (zpowers c) := IsElementaryAbelian.zpowers_of_pow_eq_one hc2
  have hcA : zpowers c ≤ centralizer (A : Set G) := zpowers_le.mpr <|
    Subgroup.mem_centralizer_iff.2 fun x hx => (Subgroup.mem_centralizer_iff.1 (hAC hx) c hcJ).symm
  have hsup : IsElemAbelian 2 (A ⊔ zpowers c) :=
    isElemAbelian_iff_isElementaryAbelian.mpr (IsElementaryAbelian.sup_of_le_centralizer hcA)
  have hle := hmax.2.2 a ha J hJ hJp rfl rfl (A ⊔ zpowers c)
    (sup_le hAC (zpowers_le.mpr hcC)) hsup (mem_sup_left haA)
  have heq : A = A ⊔ zpowers c := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [heq]
  exact mem_sup_right (mem_zpowers c)

theorem refined_odd_core_index_selection_diagonal_rank_one {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    ∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G, IsComponentOf J (centralizer ({a} : Set G)) ∧
      IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))) ∧
      ∃ A : Subgroup G, A ≤ centralizer (J : Set G) ∧ IsElemAbelian 2 A ∧ a ∈ A ∧
        RefinedMaxima J A ∧
        (∀ c ∈ J, c ∈ centralizer (J : Set G) → orderOf c = 2 → c ∈ A) ∧
        ∀ b ∈ A, b ≠ 1 → ∃ L : Subgroup G, IsComponentOf L (centralizer ({b} : Set G)) ∧
          IsTwoPComponent (L.subgroupOf (centralizer ({b} : Set G))) ∧
          (L = J ∨ (conjSub a⁻¹ L ≠ L ∧ (J : Set G) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g} ∧
            Nonempty (J ⧸ center J ≃* L ⧸ center L) ∧
            (CFSG.Assembly.oddCore L).index = (CFSG.Assembly.oddCore J).index ∧
            (∃ δ : L →* J, (∀ x : L, (δ x : G) = x * (a⁻¹ * x * a)) ∧
              Function.Surjective δ ∧ Odd (Nat.card δ.ker)) ∧
            CFSG.Assembly.pRank 2 J = 1 ∧ CFSG.Assembly.pRank 2 L = 1)) := by
  obtain ⟨a, ha, J, hJ, hJp, A, hAC, hAe, haA, hmax⟩ :=
    exists_refined_selection hC hpump hK hcomp hB
  refine ⟨a, ha, J, hJ, hJp, A, hAC, hAe, haA, hmax,
    fun c hcJ hcC hc => mem_of_central_involution ha hJ hJp hAC hAe haA hmax hcJ hcC hc,
    fun b hbA hb1 => ?_⟩
  have hb : orderOf b = 2 := orderOf_eq_prime (hAe.2 b hbA) hb1
  have hab : a * b = b * a := congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩)
  have hJb : J ≤ centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hAC hbA) x hx)
  obtain ⟨L, hL, hLp, -, hcases⟩ :=
    exists_correspondence_of_commuting_involution hC hpump hK hB ha hJ hJp hmax.1 hb hab hJb
  refine ⟨L, hL, hLp, ?_⟩
  rcases hcases with rfl | ⟨hLa, hset, ⟨δ, hδ, hδs, -⟩, hiso, -⟩
  · exact Or.inl rfl
  · obtain ⟨he, hodd, hJ1, hL1⟩ := diagonal_odd_core_rank_one ha hb hab hL hLp hLa hset hδ hδs
      hiso hJ.2.2 hAC hAe haA hbA hmax
    exact Or.inr ⟨hLa, hset, hiso, he, ⟨δ, hδ, hδs, hodd⟩, hJ1, hL1⟩

end CFSG.LocalAnalysis.ComponentInitial
