module

public import CFSG.CharacterTheory.Semidihedral.StationarySevenNineSupport
public import CFSG.CharacterTheory.Semidihedral.EscapingLocalEigensubgroups
public import CFSG.CharacterTheory.Semidihedral.Principal.ConfinedInvertedOddSubgroup
public import CFSG.CharacterTheory.Semidihedral.StationaryLayerCoverSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterSevenNineOrders

public section

open scoped Pointwise

namespace CFSG.Semidihedral.StationarySevenNine

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers

@[expose] def StationaryConfinementStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S0 : Sylow 2 G) (_f0 : SemidihedralGroup n ≃* S0)
      (t s : G), orderOf t = 2 → orderOf s = 2 → s ∈ C t → t ≠ s →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t s →
    (∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ C t) ∧
    (∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ C t) ∧
    (∀ g : G, g ∉ C t →
      (N t).map (C t).subtype ⊓ ((N t).map (C t).subtype).map (MulAut.conj g).toMonoidHom =
        ⊥) ∧
    (N t ≠ ⊥ → Subgroup.normalizer (((N t).map (C t).subtype : Subgroup G) : Set G) = C t)

@[expose] def StationaryFixedFactorStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S0 : Sylow 2 G) (_f0 : SemidihedralGroup n ≃* S0)
      (t s : G), orderOf t = 2 → orderOf s = 2 → s ∈ C t → t ≠ s →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t s →
    let qe := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let Na := (N t).map (C t).subtype
    let Ya := Y.map (C t).subtype
    let Ja := J.map (C t).subtype
    let Ea := (J ⊓ N t).map (C t).subtype
    let A₀ := Na ⊓ Subgroup.centralizer ({s} : Set G)
    let D := C t ⊓ Subgroup.centralizer ({s} : Set G)
    let R := (CFSG.pPrimeCore 2 D).map D.subtype
    let M := Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G)
    ∃ U W : Subgroup G,
      (∀ x : G, x ∈ U ↔ x ∈ Na ∧ s * x * s⁻¹ = x⁻¹) ∧
      (∀ x : G, x ∈ W ↔ x ∈ Ja ⊓ Subgroup.centralizer ({s} : Set G) ∧ Odd (orderOf x)) ∧
      U ≤ Na ∧ IsMulCommutative U ∧ (U.subgroupOf Na).Characteristic ∧
      Nat.Coprime (Nat.card U) (U.relIndex Na) ∧ (U.subgroupOf Na).Normal ∧
      U ⊔ A₀ = Na ∧ U ⊓ A₀ = ⊥ ∧ Nat.card U = A₀.relIndex Na ∧
      Subgroup.normalizer (Na : Set G) ≤ Subgroup.normalizer (U : Set G) ∧
      IsCyclic A₀ ∧ Nat.card A₀ ∣ qe / 2 ∧
      W ⊓ A₀ = ⊥ ∧ (∀ w ∈ W, ∀ a ∈ A₀, Commute w a) ∧ W ⊔ A₀ = R ⊓ Ya ∧
      W ⊔ A₀ ≤ M ∧ M ≤ Subgroup.normalizer ((W ⊔ A₀ : Subgroup G) : Set G) ∧
      (∀ a ∈ A₀, a ≠ 1 → U ⊓ Subgroup.centralizer ({a} : Set G) = ⊥) ∧
      (U ≠ ⊥ → A₀ ≠ ⊥ → ∀ a ∈ A₀, a ≠ 1 → ∀ x ∈ U, a * x * a⁻¹ = x → x = 1) ∧
      Ea ≤ U ⊓ (Subgroup.center Na).map Na.subtype ∧
      (Ea ≠ ⊥ → p ^ f = 9 ∧ Nat.card Ea = 3 ∧ A₀ = ⊥ ∧ Na = U ∧
        IsMulCommutative Na ∧ ∀ x ∈ Na, s * x * s⁻¹ = x⁻¹)

theorem seven_nine_core_of_confined_fixed_factor
    {G : Type} [Group G] [Finite G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : p ^ f = 7 ∨ p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hconf : ∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ C t)
    (U : Subgroup G)
    (hUmem : ∀ x : G, x ∈ U ↔ x ∈ (N t).map (C t).subtype ∧
      (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x⁻¹)
    (hUcard : Nat.card U = ((N t).map (C t).subtype ⊓
      Subgroup.centralizer ({(fS (s n) : G)} : Set G)).relIndex ((N t).map (C t).subtype))
    (hUnorm : Subgroup.normalizer (((N t).map (C t).subtype : Subgroup G) : Set G) ≤
      Subgroup.normalizer (U : Set G))
    (hA₀cyc : IsCyclic ((N t).map (C t).subtype ⊓
      Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G))
    (hA₀dvd : Nat.card ((N t).map (C t).subtype ⊓
      Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G) ∣
        (if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) / 2)
    (hEU : ((EscapingLocalEigensubgroups.localCentralizingLayer t) ⊓ N t).map (C t).subtype ≤
      U) :
    let s₀ : G := fS (s n)
    let e : ℤ := if p ^ f = 7 then -1 else 1
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Na := (N t).map (C t).subtype
    let Ja := J.map (C t).subtype
    let A₀ := Na ⊓ Subgroup.centralizer ({s₀} : Set G)
    let JS := Ja ⊔ Subgroup.zpowers s₀
    let a₀ := Nat.card A₀
    n = 5 ∧ (∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ E = ⊥ ∧ Na = A₀ ∧ IsCyclic Na ∧
      Nat.card Na = a₀ ∧ (a₀ : ℤ) ∣ ((p ^ f : ℕ) + e) / 2 ∧
      (p ^ f = 7 → a₀ = 1 ∨ a₀ = 3) ∧ (p ^ f = 9 → a₀ = 1 ∨ a₀ = 5) ∧
      (∃ φ : J ≃* T₀, ∀ x : J, (φ x : H t) = nu t x) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (T₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (Y = J ⊔ N t ∧ J ⊓ N t = ⊥ ∧ ∀ x ∈ J, ∀ y ∈ N t, Commute x y) ∧
      (JS ⊔ Na = C t ∧ JS ⊓ Na = ⊥ ∧ ∀ x ∈ JS, ∀ y ∈ Na, Commute x y) ∧
      N t ≤ Subgroup.center (C t) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (a : Fˣ), Nat.card F = p ^ f ∧
        ¬ IsSquare a ∧ Nonempty (JS ≃* MatrixCoverData.M F a)) ∧
      (p ^ f = 7 → Nat.card G = 2328480 * a₀ ∨ Nat.card G = 1876896 * a₀) ∧
      (p ^ f = 9 → Nat.card G = 8514720 * a₀ ∨ Nat.card G = 6441120 * a₀ ∨
        Nat.card G = 7236000 * a₀) := by
  intro s₀ e T₀ Y H₀ J E Na Ja A₀ JS a₀
  have : Fintype G := Fintype.ofFinite G
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  obtain ⟨hn5, hCcard, -, hX, hbdvd⟩ :=
    CFSG.Semidihedral.Principal.perfect_local_parameter_seven_nine_exact_order_alternatives n hn
      S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  set CN : Subgroup (N t) := ((Subgroup.centralizer {s₀}).comap (C t).subtype).subgroupOf (N t)
    with hCN
  obtain ⟨hcardA, hindexA⟩ := fixed_core_card_index t s₀
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hNacard : Nat.card Na = Nat.card (N t) :=
    Subgroup.card_map_of_injective (C t).subtype_injective
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have hUNa : U ≤ Na := fun x hx => ((hUmem x).mp hx).1
  have hUodd : Odd (Nat.card U) :=
    (hNacard ▸ hNodd : Odd (Nat.card Na)).of_dvd_nat (Subgroup.card_dvd_of_le hUNa)
  have hCNa : C t ≤ Subgroup.normalizer (Na : Set G) :=
    le_normalizer_map_of_normal (C t) (N t) inferInstance
  have hUnormal : (U.subgroupOf (C t)).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hUnorm (hCNa c.2)) (x : G)).mp hx
  obtain ⟨-, hcop⟩ :=
    Principal.confined_normal_inverted_odd_subgroup_primes_do_not_divide_centralizer_index
    n hn S fS t ht U (hUNa.trans hNaC) hUodd hUnormal (fun x hx => ((hUmem x).mp hx).2)
    (fun u hu hu1 => hconf u (hUNa hu) hu1)
  have hbU : CN.index = Nat.card U := hindexA.trans hUcard.symm
  have hU1 : Nat.card U = 1 := by
    apply Nat.Coprime.eq_one_of_dvd hcop
    rw [← hbU]
    exact (dvd_pow_self _ two_ne_zero).trans hbdvd
  have hUbot : U = ⊥ := Subgroup.card_eq_one.mp hU1
  have hUtriv : ∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ → x = 1 := by
    intro x hx hxs
    have hxU : x ∈ U := (hUmem x).mpr ⟨hx, hxs⟩
    rw [hUbot] at hxU
    exact Subgroup.mem_bot.mp hxU
  have hrel1 : A₀.relIndex Na = 1 := by
    rw [← hU1]
    exact hUcard.symm
  have hNaA : Na = A₀ := le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) inf_le_left
  have hEbot : E = ⊥ := by
    have h : E.map (C t).subtype = ⊥ := by
      rw [← le_bot_iff, ← hUbot]
      exact hEU
    exact (Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective).mp h
  have hNacyc : IsCyclic Na := by
    rw [hNaA]
    exact hA₀cyc
  have hdvd3 : p ^ f = 7 → a₀ ∣ 3 := by
    intro h
    have h3 : (if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) / 2 = 3 := by
      rw [h]
      decide
    exact h3 ▸ hA₀dvd
  have hdvd5 : p ^ f = 9 → a₀ ∣ 5 := by
    intro h
    have h5 : (if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) / 2 = 5 := by
      rw [h]
      decide
    exact h5 ▸ hA₀dvd
  have hdvdZ : (a₀ : ℤ) ∣ ((p ^ f : ℕ) + e) / 2 := by
    rcases hq with h | h
    · have hval : (((p ^ f : ℕ) : ℤ) + e) / 2 = 3 := by
        show (((p ^ f : ℕ) : ℤ) + (if p ^ f = 7 then -1 else 1)) / 2 = 3
        rw [h]
        norm_num
      rw [hval]
      exact_mod_cast hdvd3 h
    · have hval : (((p ^ f : ℕ) : ℤ) + e) / 2 = 5 := by
        show (((p ^ f : ℕ) : ℤ) + (if p ^ f = 7 then -1 else 1)) / 2 = 5
        rw [h]
        norm_num
      rw [hval]
      exact_mod_cast hdvd5 h
  have ha7 : p ^ f = 7 → a₀ = 1 ∨ a₀ = 3 := fun h =>
    (Nat.dvd_prime Nat.prime_three).mp (hdvd3 h)
  have ha9 : p ^ f = 9 → a₀ = 1 ∨ a₀ = 5 := fun h =>
    (Nat.dvd_prime Nat.prime_five).mp (hdvd5 h)
  have hq5 : 5 ≤ p ^ f := by rcases hq with h | h <;> omega
  obtain ⟨-, hJnormal, -, -, hJN, hY, -, -, -, -, ⟨φ', hφ'⟩, -,
      ⟨F, hF, hFfin, eta, -, hFcard, -, -, -, -⟩, -, -, -⟩ :=
    (Local.all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
      n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq5 hmodel).1
      (EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage t s₀ hcov)
  have hJT : ∃ φ : J ≃* T₀, ∀ x : J, (φ x : H t) = nu t x := by
    have hEJ : E.subgroupOf J = ⊥ := by
      rw [hEbot]
      exact Subgroup.bot_subgroupOf _
    let μ : J →* T₀ := φ'.toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf J))
    have hμinj : Function.Injective μ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : QuotientGroup.mk' (E.subgroupOf J) x = 1 := by
        apply φ'.injective
        rw [map_one]
        exact hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hEJ] at h1
      exact Subgroup.mem_bot.mp h1
    exact ⟨MulEquiv.ofBijective μ ⟨hμinj, φ'.surjective.comp (QuotientGroup.mk'_surjective _)⟩,
      fun x => hφ' x⟩
  have hJcent : J ≤ Subgroup.centralizer (N t : Set (C t)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN
  have hJNcomm : ∀ x ∈ J, ∀ y ∈ N t, Commute x y := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hJcent hx)) y hy).symm
  obtain ⟨hNZK, hJindex, -, -, -, -, -⟩ := actual_quotient_inputs n hn S fS hG t ht2
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ ActualSimpleLayerLocalPackage.J t :=
    simple_le_index_two _ _ hJindex hnonab
  have hYK : Y ≤ K t := by
    have h1 : T₀ ≤ T t := by
      rw [← barKappa_preimage_J t hNZK]
      exact Subgroup.comap_mono hLJ
    have h2 : Y ≤ ((K t).map (nu t)).comap (nu t) := Subgroup.comap_mono h1
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    exact h2.trans (sup_le le_rfl (le_sup_left.trans hNZK))
  set sC : C t := ⟨s₀, hsC⟩ with hsCdef
  have hsC2 : orderOf sC = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hs2
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hsY : sC ∉ Y := fun h =>
    actual_noncentral_involution_not_mem_K n hn S fS hG t ht2 sC hsC2 hsCt (hYK h)
  have hYindex : Y.index = 2 := by
    have h1 : Y.index = T₀.index :=
      Subgroup.index_comap_of_surjective T₀ (QuotientGroup.mk'_surjective _)
    have hT₀card : Nat.card T₀ = p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr eta.toEquiv, GorensteinWalter.sl2_card_formula, hFcard]
    have hH : Nat.card (C t) = Nat.card (H t) * Nat.card (N t) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (N t)
    have hab : Nat.card CN * CN.index = Nat.card (N t) := Subgroup.card_mul_index CN
    have h2 : Nat.card T₀ * T₀.index = Nat.card (H t) := Subgroup.card_mul_index T₀
    have hNpos : 0 < Nat.card (N t) := Nat.card_pos
    have hqpos : 0 < p ^ f * ((p ^ f) ^ 2 - 1) := by
      apply Nat.mul_pos (by omega)
      have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    have hHcard : Nat.card (H t) = 2 * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
      apply Nat.eq_of_mul_eq_mul_right hNpos
      rw [← hH, hCcard, ← hab]
      ring
    rw [h1]
    rw [hT₀card, hHcard] at h2
    have h3 : (p ^ f * ((p ^ f) ^ 2 - 1)) * T₀.index = (p ^ f * ((p ^ f) ^ 2 - 1)) * 2 := by
      rw [h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left hqpos h3
  have hsN : ∀ y ∈ N t, sC * y = y * sC := by
    intro y hy
    have hyA : (y : G) ∈ A₀ := by
      rw [← hNaA]
      exact ⟨y, hy, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyA.2
    exact Subtype.ext h.symm
  have hNcomm : ∀ a ∈ N t, ∀ b ∈ N t, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.isMulCommutative (α := Na)).is_comm.comm
      ⟨(a : G), a, ha, rfl⟩ ⟨(b : G), b, hb, rfl⟩
    have h' : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val h
    exact Subtype.ext h'
  obtain ⟨hsup, hinf, hcomm, hcenter, hJSC, hbij⟩ :=
    central_product_of_index_two (C t) J (N t) Y inferInstance hJnormal hY hEbot hJcent
      hYindex sC hsC2 hsY hsN hNcomm
  obtain ⟨F', hF', hF'fin, A, rho, data⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have hA1 : Nat.card A = 1 := by
    have hodd := data.field_group_odd
    have hdvd := data.field_group_dvd
    rcases CFSG.Semidihedral.Principal.prime_pow_seven_or_nine hp hf hq with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Nat.dvd_one.mp hdvd
    · have hle := Nat.le_of_dvd (by norm_num) hdvd
      obtain ⟨k, hk⟩ := hodd
      interval_cases h : Nat.card A <;> omega
  have hAsub : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
  have hfixodd : Odd (Nat.card (MatrixCover.FixedField F' A)) := by
    rw [data.fixed_field_card]
    exact hpodd.pow
  obtain ⟨a, ha⟩ := exists_nonsquare_unit_of_odd_card (MatrixCover.FixedField F' A) hfixodd
  obtain ⟨ha', Ψ, -, -, -⟩ := data.every_coefficient a ha
  have hJSM : Nonempty (JS ≃* MatrixCoverData.M F' (MatrixCover.fixedUnit F' A a)) := by
    let e1 : JS ≃* JS.subgroupOf (C t) := (Subgroup.subgroupOfEquivOfLe hJSC).symm
    let e2 : JS.subgroupOf (C t) ≃* H t := MulEquiv.ofBijective _ hbij
    let e4 : MatrixCoverData.M F' (MatrixCover.fixedUnit F' A a) ≃*
        MatrixCover.MatrixFieldModel F' A a :=
      MulEquiv.ofBijective _ (semidirectProduct_inl_bijective_of_subsingleton _)
    exact ⟨e1.trans (e2.trans (Ψ.symm.trans e4.symm))⟩
  have hb1 : CN.index = 1 := hbU.trans hU1
  have hord7 : p ^ f = 7 → Nat.card G = 2328480 * a₀ ∨ Nat.card G = 1876896 * a₀ := by
    intro h7
    rcases hX with ⟨-, h | h⟩ | ⟨h9, -⟩
    · left
      have h' := congrArg Prod.fst h
      simp only at h'
      rw [h', hb1, hcardA]
      ring
    · right
      have h' := congrArg Prod.fst h
      simp only at h'
      rw [h', hb1, hcardA]
      ring
    · omega
  have hord9 : p ^ f = 9 → Nat.card G = 8514720 * a₀ ∨ Nat.card G = 6441120 * a₀ ∨
      Nat.card G = 7236000 * a₀ := by
    intro h9
    rcases hX with ⟨h7, -⟩ | ⟨-, h | h | h⟩
    · omega
    · left
      have h' := congrArg Prod.fst h
      simp only at h'
      rw [h', hb1, hcardA]
      ring
    · right; left
      have h' := congrArg Prod.fst h
      simp only at h'
      rw [h', hb1, hcardA]
      ring
    · right; right
      have h' := congrArg Prod.fst h
      simp only at h'
      rw [h', hb1, hcardA]
      ring
  refine ⟨hn5, hUtriv, hEbot, hNaA, hNacyc, by rw [hNaA], hdvdZ, ha7, ha9, hJT,
    ⟨F, hF, hFfin, hFcard, ⟨eta⟩⟩, ⟨hY, hEbot, hJNcomm⟩, ⟨hsup, hinf, hcomm⟩, hcenter,
    ⟨F', hF', hF'fin, MatrixCover.fixedUnit F' A a, data.field_card, ha', hJSM⟩, hord7, hord9⟩

theorem stationary_all_prime_seven_nine_odd_core_is_cyclic_and_central_of_confinement
    (hconfine : StationaryConfinementStatement) (hfixed : StationaryFixedFactorStatement)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : p ^ f = 7 ∨ p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G)) :
    let s₀ : G := fS (s n)
    let e : ℤ := if p ^ f = 7 then -1 else 1
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Na := (N t).map (C t).subtype
    let Ja := J.map (C t).subtype
    let A₀ := Na ⊓ Subgroup.centralizer ({s₀} : Set G)
    let JS := Ja ⊔ Subgroup.zpowers s₀
    let a₀ := Nat.card A₀
    n = 5 ∧ (∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ E = ⊥ ∧ Na = A₀ ∧ IsCyclic Na ∧
      Nat.card Na = a₀ ∧ (a₀ : ℤ) ∣ ((p ^ f : ℕ) + e) / 2 ∧
      (p ^ f = 7 → a₀ = 1 ∨ a₀ = 3) ∧ (p ^ f = 9 → a₀ = 1 ∨ a₀ = 5) ∧
      (∃ φ : J ≃* T₀, ∀ x : J, (φ x : H t) = nu t x) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (T₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (Y = J ⊔ N t ∧ J ⊓ N t = ⊥ ∧ ∀ x ∈ J, ∀ y ∈ N t, Commute x y) ∧
      (JS ⊔ Na = C t ∧ JS ⊓ Na = ⊥ ∧ ∀ x ∈ JS, ∀ y ∈ Na, Commute x y) ∧
      N t ≤ Subgroup.center (C t) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (a : Fˣ), Nat.card F = p ^ f ∧
        ¬ IsSquare a ∧ Nonempty (JS ≃* MatrixCoverData.M F a)) ∧
      (p ^ f = 7 → Nat.card G = 2328480 * a₀ ∨ Nat.card G = 1876896 * a₀) ∧
      (p ^ f = 9 → Nat.card G = 8514720 * a₀ ∨ Nat.card G = 6441120 * a₀ ∨
        Nat.card G = 7236000 * a₀) := by
  have : Group.IsPerfect G := StationaryLayerCover.isPerfect_of_nonabelian hGnonab
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hq5 : 5 < p ^ f := by rcases hq with h | h <;> omega
  obtain ⟨-, hconf, -, -⟩ := hconfine G hGnonab hrecognition n hn S fS t (fS (s n)) ht2 hs2 hsC
    (Ne.symm hst) hnonab hcentral hnc p f hp hpodd hf hq5 hmodel hcov
  obtain ⟨U, -, hUmem, -, -, -, -, -, -, -, -, hUcard, hUnorm, hA₀cyc, hA₀dvd, -, -, -, -, -, -,
      -, hEU, -⟩ := hfixed G hGnonab hrecognition n hn S fS t (fS (s n)) ht2 hs2 hsC
    (Ne.symm hst) hnonab hcentral hnc p f hp hpodd hf hq5 hmodel hcov
  exact seven_nine_core_of_confined_fixed_factor n hn S fS t ht hnonab hcentral hnc p f hp hpodd
    hf hq hmodel hcov hconf U hUmem hUcard hUnorm hA₀cyc hA₀dvd (hEU.trans inf_le_left)

end CFSG.Semidihedral.StationarySevenNine
