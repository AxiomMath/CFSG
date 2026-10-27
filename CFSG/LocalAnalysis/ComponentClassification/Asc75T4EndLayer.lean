module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Dihedral
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionRankOne
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4CaseII

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsQuaternionTwoGroup)
open CFSG.ComponentClassification.AschbacherKnownGroup (HasDihedralSylowTwo)
open scoped Pointwise

section NoFour

variable {X : Type} [Group X] [Finite X]

theorem not_hasFourGroup_of_isCyclic_or_quaternion {P : Subgroup X}
    (h : IsCyclic P ∨ IsQuaternionTwoGroup P) : ¬ HasFourGroup P := by
  intro h4
  obtain ⟨u, huP, w, hwP, hu, hw, hu1, hw1, huw, -⟩ := h4.exists_commute
  have hu' : (⟨u, huP⟩ : P) ^ 2 = 1 := Subtype.ext (by simpa using hu)
  have hw' : (⟨w, hwP⟩ : P) ^ 2 = 1 := Subtype.ext (by simpa using hw)
  have hu1' : (⟨u, huP⟩ : P) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hw1' : (⟨w, hwP⟩ : P) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  rcases h with hcyc | ⟨n, hn, ⟨e⟩⟩
  · exact huw (congrArg Subtype.val
      (AschbacherKnownGroup.FactsL2.eq_of_sq_eq_one_of_isCyclic hu' hw' hu1' hw1'))
  · have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    have hord : ∀ x : P, x ^ 2 = 1 → x ≠ 1 → orderOf (e x) = 2 := fun x hx hx1 => by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hx hx1
    have h1 := CFSG.DisconnectedInvolutionGraph.Helpers.quaternion_unique_involution (2 ^ (n - 2))
      ⟨e ⟨u, huP⟩, hord _ hu' hu1'⟩ ⟨e ⟨w, hwP⟩, hord _ hw' hw1'⟩
    have h2 : e ⟨u, huP⟩ = e ⟨w, hwP⟩ := congrArg Subtype.val h1
    exact huw (congrArg Subtype.val (e.injective h2))

end NoFour

variable {G : Type} [Group G] [Finite G]

theorem hasFourGroup_bar_of_le {Q Y : Subgroup G} (hYN : Y ≤ normalizer (Q : Set G))
    (h : HasFourGroup Y) : HasFourGroup (bar Q Y) := by
  obtain ⟨E, hEY, hE, hE4⟩ := h
  have hE2 : IsPGroup 2 E := isPGroup_of_sq_eq_one hE
  refine ⟨bar Q E, bar_mono Q hEY, ?_, by rw [card_bar_of_isPGroup hE2 (hEY.trans hYN), hE4]⟩
  intro z hz
  obtain ⟨x, hxE, rfl⟩ := (mem_bar_iff Q E z).mp hz
  rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hE x hxE), map_one]

noncomputable def barTwoPrimeLayerInEquiv (Q : Subgroup G) :
    twoPrimeLayerIn Q ⧸ CFSG.Assembly.oddCore (twoPrimeLayerIn Q) ≃*
      bar Q (twoPrimeLayerIn Q) := by
  have hKN : twoPrimeLayerIn Q ≤ normalizer (Q : Set G) :=
    (twoPrimeLayerIn_le Q).trans le_normalizer
  let φ : twoPrimeLayerIn Q →* bar Q (twoPrimeLayerIn Q) :=
    ((toBar Q).comp (inclusion hKN)).codRestrict _ fun k => toBar_mem_bar Q k.2
  have hφ : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := (mem_bar_iff Q _ z).mp hz
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ.ker = CFSG.Assembly.oddCore (twoPrimeLayerIn Q) := by
    ext k
    rw [MonoidHom.mem_ker, ← oddCoreIn_subgroupOf, mem_subgroupOf, oddCoreIn_twoPrimeLayerIn]
    constructor
    · intro h
      have h1 : toBar Q (inclusion hKN k) = 1 := congrArg Subtype.val h
      rw [toBar_eq_one_iff] at h1
      exact h1
    · intro h
      apply Subtype.ext
      show toBar Q (inclusion hKN k) = 1
      rw [toBar_eq_one_iff]
      exact h
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem layer_bar_twoPrimeLayerIn (Q : Subgroup G) :
    CFSG.layer (bar Q (twoPrimeLayerIn Q)) = ⊤ := by
  rw [← layer_map_mulEquiv (barTwoPrimeLayerInEquiv Q),
    show CFSG.layer (twoPrimeLayerIn Q ⧸ CFSG.Assembly.oddCore (twoPrimeLayerIn Q)) = ⊤ from
      isSemisimpleQ_twoPrimeLayerIn Q]
  exact map_top_of_surjective _ (barTwoPrimeLayerInEquiv Q).surjective

theorem oddCore_bar_twoPrimeLayerIn (Q : Subgroup G) :
    CFSG.Assembly.oddCore (bar Q (twoPrimeLayerIn Q)) = ⊥ :=
  oddCore_bar_eq_bot (twoPrimeLayerIn_le Q)
    (le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn Q))

theorem HasFourGroup.of_bar_of_le {Q Y : Subgroup G} (hYN : Y ≤ normalizer (Q : Set G))
    (h : HasFourGroup (bar Q Y)) : HasFourGroup Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEY, hE, hE4⟩ := h
  set F : Subgroup G :=
    (E.comap (toBar Q) ⊓ Y.subgroupOf (normalizer (Q : Set G))).map (normalizer (Q : Set G)).subtype
  have hFY : F ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_inf.mp hx).2
  have hFN : F ≤ normalizer (Q : Set G) := hFY.trans hYN
  have hFE : bar Q F = E := by
    apply le_antisymm
    · intro z hz
      obtain ⟨x, hxF, rfl⟩ := (mem_bar_iff Q F z).mp hz
      obtain ⟨y, hy, hyx⟩ := hxF
      rw [show x = y from Subtype.ext hyx.symm]
      exact (mem_inf.mp hy).1
    · intro e he
      obtain ⟨y, hyY, hy⟩ := (mem_bar_iff Q Y e).mp (hEY he)
      exact (mem_bar_iff Q F e).mpr ⟨y, ⟨y, mem_inf.mpr ⟨by rw [mem_comap, hy]; exact he, hyY⟩,
        rfl⟩, hy⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 F
  have hPE : bar Q P = E := by
    have h1 := isSylowOf_bar (D := Q) hP hFN
    rw [hFE] at h1
    exact (h1.eq_of_le h1.le le_rfl (isPGroup_of_sq_eq_one hE)).symm
  have h4 : HasFourGroup (bar Q P) := hPE ▸ ⟨E, le_rfl, hE, hE4⟩
  exact (HasFourGroup.of_bar hP.isPGroup h4).mono (hP.le.trans hFY)

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem hasFourGroup_bar : HasFourGroup (bar Q (twoPrimeLayerIn Q)) :=
  hasFourGroup_bar_of_le ((twoPrimeLayerIn_le Q).trans le_normalizer) hS.four

theorem exists_isDihedral_sylow (hC : linkedClass Q = {Q}) (hodd : ¬ OddNormalizerOverlaps Q) :
    ∃ R : Subgroup (Bar Q), IsSylowOf 2 R (bar Q Q) ∧ IsDihedralTwoGroup R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, heven⟩ : ∃ g : G, g ∉ normalizer (Q : Set G) ∧
      ¬ Odd (Nat.card (rightConjugate Q g ⊓ normalizer (Q : Set G) : Subgroup G)) := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hodd h
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (rightConjugate Q g ⊓ normalizer (Q : Set G))
  have hT1 : T ≠ ⊥ := by
    intro hbot
    apply heven
    have h1 := hT.card_eq
    rw [hbot, card_bot] at h1
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have h3 : (Nat.card (rightConjugate Q g ⊓ normalizer (Q : Set G) : Subgroup G)).factorization
        2 = 0 := by
      have := congrArg (fun m => m.factorization 2) h1
      simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at this
      exact this.symm
    omega
  obtain ⟨S, hS', hTS, -, ⟨-, hR, -⟩⟩ := hS.thm3RankOne_of_linkedClass_eq hC hg hT hT1
  have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
  have hQTN : Q ⊔ T ≤ normalizer (Q : Set G) := sup_le le_normalizer hTH
  have hRs : IsSylowOf 2 (bar Q S ⊓ bar Q Q) (bar Q Q) := by
    have h1 := isSylowOf_bar (D := Q) hS' hQTN
    rw [bar_sup le_normalizer hTH] at h1
    exact h1.inf_of_le_normalizer le_sup_left
      (sup_le le_normalizer (bar_le_normalizer hTH le_normalizer))
  refine ⟨_, hRs, ?_⟩
  have h4 : HasFourGroup (bar Q S ⊓ bar Q Q) := by
    obtain ⟨E, hEQ, hE, hE4⟩ := hS.hasFourGroup_bar.mono (bar_mono Q (twoPrimeLayerIn_le Q))
    obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hRs
      (isPGroup_of_sq_eq_one hE) hEQ
    exact (hasFourGroup_rightConjugate_iff.mpr ⟨E, le_rfl, hE, hE4⟩).mono hc
  rcases hR with h | h | h
  · exact absurd h4 (not_hasFourGroup_of_isCyclic_or_quaternion (Or.inl h))
  · exact absurd h4 (not_hasFourGroup_of_isCyclic_or_quaternion (Or.inr h))
  · exact h

theorem hasDihedralSylowTwo_bar (hC : linkedClass Q = {Q}) (hodd : ¬ OddNormalizerOverlaps Q) :
    HasDihedralSylowTwo (bar Q (twoPrimeLayerIn Q)) := by
  obtain ⟨R, hR, hRd⟩ := hS.exists_isDihedral_sylow hC hodd
  exact hasDihedralSylowTwo_of_le hR hRd (bar_mono Q (twoPrimeLayerIn_le Q)) hS.hasFourGroup_bar

theorem isSimpleGroup_bar (hC : linkedClass Q = {Q}) (hodd : ¬ OddNormalizerOverlaps Q) :
    IsSimpleGroup (bar Q (twoPrimeLayerIn Q)) :=
  isSimpleGroup_of_layer_eq_top (layer_bar_twoPrimeLayerIn Q) (oddCore_bar_twoPrimeLayerIn Q)
    (hS.hasDihedralSylowTwo_bar hC hodd)

theorem inf_centralizer_bar_eq_bot (hC : linkedClass Q = {Q}) (hodd : ¬ OddNormalizerOverlaps Q) :
    bar Q Q ⊓ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hRd⟩ := hS.exists_isDihedral_sylow hC hodd
  have : IsSimpleGroup (bar Q (twoPrimeLayerIn Q)) := hS.isSimpleGroup_bar hC hodd
  set L := bar Q (twoPrimeLayerIn Q)
  set C := bar Q Q ⊓ centralizer (L : Set (Bar Q))
  have hLQ : L ≤ bar Q Q := bar_mono Q (twoPrimeLayerIn_le Q)
  have hQL : bar Q Q ≤ normalizer (L : Set (Bar Q)) :=
    bar_le_normalizer (le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn Q))
      ((twoPrimeLayerIn_le Q).trans le_normalizer)
  have hCn : NormalIn C (bar Q Q) := by
    refine normalIn_of_le_normalizer inf_le_left fun x hx => ?_
    refine inf_normalizer_le_normalizer_inf _ _ (mem_inf.mpr ⟨le_normalizer hx, ?_⟩)
    have hxL := hQL hx
    have key : ∀ z : Bar Q, z ∈ normalizer (L : Set (Bar Q)) → ∀ y : Bar Q,
        y ∈ centralizer (L : Set (Bar Q)) → z * y * z⁻¹ ∈ centralizer (L : Set (Bar Q)) :=
      fun z hz y hy => by
      rw [mem_centralizer_iff]
      intro l hl
      have hl' : z⁻¹ * l * z⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (inv_mem hz) l).mp hl
      have h1 := mem_centralizer_iff.mp hy _ hl'
      rw [inv_inv] at h1
      calc l * (z * y * z⁻¹) = z * ((z⁻¹ * l * z) * y) * z⁻¹ := by group
        _ = z * (y * (z⁻¹ * l * z)) * z⁻¹ := by rw [h1]
        _ = z * y * z⁻¹ * l := by group
    rw [mem_normalizer_iff]
    intro y
    constructor
    · exact key x hxL y
    · intro hy
      have := key x⁻¹ (inv_mem hxL) _ hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this
  have hCL : C ⊓ L = ⊥ := by
    have hZ : (C ⊓ L).subgroupOf L ≤ center L := fun x hx => by
      rw [mem_center_iff]
      intro y
      have hx' := (mem_inf.mp (mem_inf.mp hx).1).2
      exact Subtype.ext (mem_centralizer_iff.mp hx' y y.2)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have hxL := (mem_inf.mp hx).2
      have h1 := hZ (show (⟨x, hxL⟩ : L) ∈ (C ⊓ L).subgroupOf L from hx)
      rw [hbot, mem_bot] at h1
      rw [mem_bot]
      exact congrArg Subtype.val h1
    · exfalso
      let _ : CommGroup L := Group.commGroupOfCenterEqTop htop
      have hp := IsSimpleGroup.prime_card (α := L)
      obtain ⟨E, hEL, -, hE4⟩ := hS.hasFourGroup_bar
      have h4 : 4 ∣ Nat.card L := by
        rw [← hE4, ← Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv]
        exact card_subgroup_dvd_card _
      have h2 := (Nat.Prime.eq_one_or_self_of_dvd hp 2 ((show 2 ∣ 4 by norm_num).trans h4))
      have h4' := (Nat.Prime.eq_one_or_self_of_dvd hp 4 h4)
      omega
  have hCodd : Odd (Nat.card C) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨⟨c, hcC⟩, hc2⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp hev)
    rw [Subgroup.orderOf_mk] at hc2
    have hc2' : c ^ 2 = 1 := by rw [← hc2]; exact pow_orderOf_eq_one c
    have hc1 : c ≠ 1 := fun h => by rw [h, orderOf_one] at hc2; norm_num at hc2
    obtain ⟨V, hVL, hV, hV4⟩ := hS.hasFourGroup_bar
    have hcV : c ∉ V := fun h => by
      have : c ∈ C ⊓ L := mem_inf.mpr ⟨hcC, hVL h⟩
      rw [hCL, mem_bot] at this
      exact hc1 this
    have hcent : zpowers c ≤ centralizer (V : Set (Bar Q)) := (zpowers_le).mpr
      ((centralizer_le hVL) (mem_inf.mp hcC).2)
    have hN : zpowers c ≤ normalizer (V : Set (Bar Q)) := hcent.trans (centralizer_le_normalizer _)
    have hsq : ∀ x ∈ zpowers c ⊔ V, x ^ 2 = 1 := by
      intro x hx
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hN] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
      have hab : Commute a b := (mem_centralizer_iff.mp (hcent ha) b hb).symm
      rw [hab.mul_pow, sq_eq_one_of_mem_zpowers hc2' ha, hV b hb, one_mul]
    have hle := card_le_four_of_sq_eq_one hR hRd
      (sup_le ((zpowers_le).mpr (mem_inf.mp hcC).1) (hVL.trans hLQ)) hsq
      (fun a ha b hb => mul_comm_of_sq_eq_one hsq ha hb)
    have h8 := card_sup_mul_card_inf hN
    have hinf : zpowers c ⊓ V = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxc, hxV⟩ := mem_inf.mp hx
      rcases eq_one_or_eq_of_mem_zpowers hc2' hc1 hxc with rfl | rfl
      · exact one_mem _
      · exact absurd hxV hcV
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hc2' hc1, hV4] at h8
    omega
  have h := le_oddCoreIn hCn hCodd
  rw [eq_bot_iff]
  intro x hx
  have h1 := h hx
  rw [mem_oddCoreIn_iff] at h1
  obtain ⟨hxQ, hxO⟩ := h1
  have h0 : CFSG.oddCore (bar Q Q) = ⊥ := oddCore_bar_eq_bot le_rfl le_normalizer
  have hxO' : (⟨x, hxQ⟩ : bar Q Q) ∈ CFSG.oddCore (bar Q Q) := hxO
  rw [h0, mem_bot] at hxO'
  rw [mem_bot]
  exact congrArg Subtype.val hxO'

theorem hasCyclicSylowTwo_inf_centralizer (hC : linkedClass Q = {Q})
    (hodd : ¬ OddNormalizerOverlaps Q) {g : G} (hg : g ∉ normalizer (Q : Set G)) {u : G}
    (huQg : u ∈ rightConjugate Q g) (huN : u ∈ normalizer (Q : Set G)) (hu : u ^ 2 = 1)
    (hu1 : u ≠ 1) :
    CFSG.ComponentClassification.AschbacherKnownGroup.HasCyclicSylowTwo
      (bar Q (twoPrimeLayerIn Q) ⊓ centralizer ({toBar Q ⟨u, huN⟩} : Set (Bar Q)) :
        Subgroup (Bar Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hRd⟩ := hS.exists_isDihedral_sylow hC hodd
  set ū := toBar Q ⟨u, huN⟩
  set Y := bar Q (twoPrimeLayerIn Q) ⊓ centralizer ({ū} : Set (Bar Q))
  have hKN : twoPrimeLayerIn Q ≤ normalizer (Q : Set G) :=
    (twoPrimeLayerIn_le Q).trans le_normalizer
  have hlift : Y ≤ bar Q (twoPrimeLayerIn Q ⊓ centralizer ({u} : Set G)) := by
    intro z hz
    obtain ⟨hzL, hzC⟩ := mem_inf.mp hz
    obtain ⟨y, hyK, rfl⟩ := (mem_bar_iff Q _ z).mp hzL
    have hOn : twoPrimeLayerIn Q ≤ normalizer (oddCoreIn Q : Set G) :=
      hKN.trans (normalizer_le_normalizer_oddCoreIn Q)
    have huO : u ∈ normalizer (oddCoreIn Q : Set G) := normalizer_le_normalizer_oddCoreIn Q huN
    have hc : ∀ t ∈ zpowers u, t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ oddCoreIn Q := by
      intro t ht
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
      have hcomm : toBar Q ⟨u, huN⟩ * toBar Q y = toBar Q y * toBar Q ⟨u, huN⟩ :=
        mem_centralizer_iff.mp hzC _ rfl
      have hcomm' : Commute (toBar Q ⟨u, huN⟩ ^ i) (toBar Q y) := (Commute.zpow_left hcomm i)
      have h1 : toBar Q ((⟨u, huN⟩ : normalizer (Q : Set G)) ^ i * y *
          ((⟨u, huN⟩ : normalizer (Q : Set G)) ^ i)⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, hcomm'.eq]
        group
      rw [toBar_eq_one_iff] at h1
      simp only [coe_mul, coe_inv, SubgroupClass.coe_zpow] at h1
      exact h1
    obtain ⟨c, hcC, hcO⟩ := exists_mem_centralizer_of_commutator
      (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hu)) (odd_card_oddCoreIn Q)
      ((zpowers_le).mpr huO) (hOn hyK) hc
    have hcK : c ∈ twoPrimeLayerIn Q := by
      have : c = (y : G) * (c⁻¹ * y)⁻¹ := by group
      rw [this]
      exact mul_mem hyK (inv_mem (oddCoreIn_le_twoPrimeLayerIn Q hcO))
    have hcu : c ∈ centralizer ({u} : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact mem_centralizer_iff.mp hcC u (mem_zpowers u)
    refine (mem_bar_iff Q _ _).mpr ⟨⟨c, hKN hcK⟩, mem_inf.mpr ⟨hcK, hcu⟩, ?_⟩
    rw [eq_comm, ← mul_inv_eq_one, ← map_inv, ← map_mul, toBar_eq_one_iff]
    have : (y : G) * c⁻¹ = c * (c⁻¹ * y) * c⁻¹ := by group
    show (y : G) * c⁻¹ ∈ oddCoreIn Q
    rw [this]
    exact (mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn Q (hKN hcK)) _).mp hcO
  by_contra hcyc
  have h4 : HasFourGroup Y := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Y))
    have hnc : ¬ IsCyclic (P : Subgroup Y) := fun h => hcyc ⟨P, h⟩
    let e : (P : Subgroup Y) ≃* (P : Subgroup Y).map Y.subtype :=
      (P : Subgroup Y).equivMapOfInjective Y.subtype Y.subtype_injective
    have hYQ : Y ≤ bar Q Q := inf_le_left.trans (bar_mono Q (twoPrimeLayerIn_le Q))
    rcases isCyclic_or_dihedral_of_isSylowOf hR hRd ((map_subtype_le _).trans hYQ)
        (P.isPGroup'.map Y.subtype) with h | ⟨k, hk, ⟨f⟩⟩
    · exact absurd ((MulEquiv.isCyclic e).mpr h) hnc
    · have hev : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
      obtain ⟨a, b, ha, hb, ha1, hb1, hab, hc, -, -⟩ :=
        AschbacherKnownGroup.FactsL2.dihedral_exists_commuting_involutions hev
          (by positivity) 1 (one_pow 2)
      have hmem : ∀ x : DihedralGroup (2 ^ k),
          ((f.symm x : (P : Subgroup Y).map Y.subtype) : Bar Q) ∈ Y :=
        fun x => map_subtype_le _ (f.symm x).2
      have hinj : ∀ x y : DihedralGroup (2 ^ k),
          ((f.symm x : (P : Subgroup Y).map Y.subtype) : Bar Q) = (f.symm y : _) → x = y :=
        fun x y h => f.symm.injective (Subtype.ext h)
      refine hasFourGroup_of_commute (hmem a) (hmem b) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← coe_pow, ← map_pow, ha, map_one, coe_one]
      · rw [← coe_pow, ← map_pow, hb, map_one, coe_one]
      · intro h
        exact ha1 (hinj a 1 (by rw [h, map_one, coe_one]))
      · intro h
        exact hb1 (hinj b 1 (by rw [h, map_one, coe_one]))
      · exact fun h => hab (hinj a b h)
      · rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, hc]
  have h4' := HasFourGroup.of_bar_of_le
    (inf_le_left.trans hKN : twoPrimeLayerIn Q ⊓ centralizer ({u} : Set G) ≤ _) (h4.mono hlift)
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu hu1
  have hCN := centralizer_le_of_involution (rightConjugate_tightlyEmbedded Q hS.tight g) huQg hu2
  exact hS.not_hasFourGroup_inf_normalizer hC hg
    (h4'.mono (inf_le_inf (twoPrimeLayerIn_le Q) hCN))

end MainSetting

end CFSG.ComponentClassification.Asc75T4
