module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementPrime
public import CFSG.CharacterTheory.Semidihedral.EscapingCentralizer

public section

open scoped Pointwise

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.Semidihedral.PrimeOrderCyclicConfinementLift
  (original_prime_order_cyclic_normalizer_confinement_extends_to_every_element
    original_trivial_intersections_give_exact_normalizer_of_nontrivial_odd_core)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem stationary_confinement_of_escaping_centralizer
    (hEsc : EscapingCentralizer.EscapingCentralizerStatement.{0})
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : allLocalPrimeStationaryCovers t s) :
    (∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ C t) ∧
    (∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ C t) ∧
    (∀ g : G, g ∉ C t →
      (N t).map (C t).subtype ⊓ ((N t).map (C t).subtype).map (MulAut.conj g).toMonoidHom =
        ⊥) ∧
    (N t ≠ ⊥ → Subgroup.normalizer (((N t).map (C t).subtype : Subgroup G) : Set G) = C t) := by
  classical
  set Na := (N t).map (C t).subtype with hNadef
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hNaodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have hprime : ∀ a ∈ Na, ∀ r : ℕ, r.Prime → orderOf a = r →
      Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ C t := fun a ha r hr har =>
    prime_order_normalizer_le hEsc hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab
      hcentral hnc p f hp hpodd hf hq hmodel hcov ha (har ▸ hr)
  have hall :=
    original_prime_order_cyclic_normalizer_confinement_extends_to_every_element Na (C t) hprime
  have hnorm : ∀ u ∈ Na, u ≠ 1 → Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ C t :=
    fun u hu hu1 => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hall u hu hu1
      exact h
  have hcent : ∀ u ∈ Na, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ C t :=
    fun u hu hu1 => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := hall u hu hu1
      exact h
  obtain ⟨hJN, hJimage, hJY, -⟩ := localCentralizingLayer_facts n hn S0 f0 hG t s ht hnonab
    hcentral hnc p f hp hpodd hf hq.le hmodel hcov
  have hJnorm : ∀ w ∈ Na, (localCentralizingLayer t).map (C t).subtype ≤
      Subgroup.normalizer (Subgroup.zpowers w : Set G) := fun w hw j hj =>
    mem_normalizer_zpowers_of_commute (layer_commute_odd_core t _ hJN hj hw)
  have hTI : ∀ g : G, g ∉ C t → Na ⊓ Na.map (MulAut.conj g).toMonoidHom = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    rintro v ⟨hvN, w, hwN, hwv⟩
    rw [Subgroup.mem_bot]
    by_contra hv1
    change (MulAut.conj g) w = v at hwv
    set e := MulAut.conj g with hedef
    have htw : t * w = w * t := (Subgroup.mem_centralizer_singleton_iff.mp (hNaC hwN)).symm
    have htv : t * v = v * t := (Subgroup.mem_centralizer_singleton_iff.mp (hNaC hvN)).symm
    have hetv : e t * v = v * e t := by
      rw [← hwv, ← map_mul, ← map_mul, htw]
    have hetC : e t ∈ C t :=
      hcent v hvN hv1 (Subgroup.mem_centralizer_singleton_iff.mpr hetv)
    have het2 : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht
    have htne : t ≠ e t := by
      intro h
      apply hg
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have h' : t = g * t * g⁻¹ := h
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [← h']
    set A := Subgroup.normalizer (Subgroup.zpowers v : Set G) with hAdef
    have hVA : Subgroup.closure ({t, e t} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact mem_normalizer_zpowers_of_commute htv
      · exact mem_normalizer_zpowers_of_commute hetv
    obtain ⟨hsimple', hnonab', hcentral', hnc', -, -, -, -, hmodel'⟩ :=
      OrderedPairLocalTransport.original_layer_hypotheses_transport e t hnonab hcentral hnc
        p f hp hpodd hf hq.le hmodel
    let := hsimple'
    have hcovert := cover_of_layer_le t A _ hJY hJimage (hJnorm v hvN)
    have hcoverw := cover_of_layer_le t (Subgroup.normalizer (Subgroup.zpowers w : Set G)) _
      hJY hJimage (hJnorm w hwN)
    have htrans := PerfectLayerNormalization.isomorphism_transports_original_subgroup_local_cover
      e t _ hcoverw
    have hAmap : (Subgroup.normalizer (Subgroup.zpowers w : Set G)).map e.toMonoidHom = A := by
      rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
      change Subgroup.normalizer (Subgroup.zpowers (e w) : Set G) = A
      rw [hwv]
    rw [hAmap] at htrans
    have hbot :=
      TwoCoverOddCore.two_commuting_involution_local_layer_covers_force_trivial_subgroup_odd_core
        G hGnonab hrecognition n hn S0 f0 t (e t) ht het2 hetC htne hnonab hcentral hnc
        p f hp hpodd hf hq.le hmodel hnonab' hcentral' hnc' p f hp hpodd hf hq.le hmodel'
        A hVA hcovert htrans
    have hvodd : Odd (orderOf v) := hNaodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Na hvN)
    have hvR : v ∈ (CFSG.pPrimeCore 2 A).map A.subtype :=
      le_ambient_core_of_normal_odd A (Subgroup.zpowers v) Subgroup.le_normalizer le_rfl
        (by rw [Nat.card_zpowers]; exact hvodd) (Subgroup.mem_zpowers v)
    rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at hvR
    exact hv1 hvR
  refine ⟨hnorm, hcent, hTI, fun hN => ?_⟩
  have hNa : Na ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hxa : (x : G) ∈ Na := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hxa
    exact Subtype.ext hxa
  exact (original_trivial_intersections_give_exact_normalizer_of_nontrivial_odd_core
    Na (C t) hNa hTI
    (StationaryOddLocalization.actual_centralizer_core_normalized t (C t) le_rfl)).2.2

theorem stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t s) :
    (∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ C t) ∧
    (∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ C t) ∧
    (∀ g : G, g ∉ C t →
      (N t).map (C t).subtype ⊓ ((N t).map (C t).subtype).map (MulAut.conj g).toMonoidHom =
        ⊥) ∧
    (N t ≠ ⊥ → Subgroup.normalizer (((N t).map (C t).subtype : Subgroup G) : Set G) = C t) :=
  stationary_confinement_of_escaping_centralizer
    EscapingCentralizer.escapingCentralizerStatement_holds.{0} hGnonab hrecognition n hn S0 f0
    t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov

end CFSG.Semidihedral.StationaryConfinement
