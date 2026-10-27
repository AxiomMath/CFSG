module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LieType.Seitz
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift
open scoped commutatorElement


section TwoLocal

variable {X : Type} [Group X] [Finite X]

theorem le_twoLocalRank_of_pair {K C : Subgroup X} (hC : IsElemAbelian 3 C)
    (hCK : C ≤ Subgroup.centralizer (K : Set X)) {E P : Subgroup ↥K} (hE : IsElemAbelian 3 E)
    (hdisj : E ⊓ Subgroup.center ↥K = ⊥) (hP : P ≠ ⊥) (hP2 : IsPGroup 2 ↥P)
    (hEN : E ≤ Subgroup.normalizer (P : Set ↥K)) :
    CFSG.Open.pRank 3 E + CFSG.Open.pRank 3 C ≤ GLATwoLocalRank 3 X := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨e, he⟩ := i271_exists_card_eq hp hE
  obtain ⟨c, hc⟩ := i271_exists_card_eq hp hC
  have her : CFSG.Open.pRank 3 E = e := i271_pRank_eq hp hE he
  have hcr : CFSG.Open.pRank 3 C = c := i271_pRank_eq hp hC hc
  set P' : Subgroup X := P.map K.subtype with hP'
  set E' : Subgroup X := E.map K.subtype with hE'
  have hE'K : E' ≤ K := Subgroup.map_subtype_le E
  have hE'el : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE K.subtype
  have hE'card : Nat.card E' = 3 ^ e := by
    rw [hE', Subgroup.card_map_of_injective K.subtype_injective, he]
  have hcomm : ∀ x ∈ E', ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hCK hy) x (hE'K hx)
  have hdisj' : E' ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, hyE, rfl⟩, hxC⟩
    have hyz : y ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hCK hxC) z z.2)
    have h1 : y ∈ E ⊓ Subgroup.center ↥K := ⟨hyE, hyz⟩
    rw [hdisj, Subgroup.mem_bot] at h1
    rw [h1, Subgroup.mem_bot]
    rfl
  have hTel : IsElemAbelian 3 (E' ⊔ C) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx, u, hu, hxu⟩ := i224_mem_sup_of_comm hcomm a.2
      obtain ⟨x', hx', u', hu', hxu'⟩ := i224_mem_sup_of_comm hcomm b.2
      apply Subtype.ext
      change (a : X) * b = b * a
      rw [hxu, hxu']
      have e1 : ∀ s ∈ E', ∀ t ∈ E', s * t = t * s := fun s hs t ht =>
        congrArg Subtype.val (hE'el.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
      have e2 : ∀ s ∈ C, ∀ t ∈ C, s * t = t * s := fun s hs t ht =>
        congrArg Subtype.val (hC.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
      calc x * u * (x' * u') = x * (u * x') * u' := by group
        _ = x * (x' * u) * u' := by rw [← hcomm x' hx' u hu]
        _ = (x * x') * (u * u') := by group
        _ = (x' * x) * (u' * u) := by rw [e1 x hx x' hx', e2 u hu u' hu']
        _ = x' * (x * u') * u := by group
        _ = x' * (u' * x) * u := by rw [hcomm x hx u' hu']
        _ = x' * u' * (x * u) := by group
    · obtain ⟨x, hx, u, hu, rfl⟩ := i224_mem_sup_of_comm hcomm hy
      have hxp : x ^ 3 = 1 := hE'el.2 x hx
      have hup : u ^ 3 = 1 := hC.2 u hu
      have e1 : Commute x u := hcomm x hx u hu
      rw [e1.mul_pow, hxp, hup, one_mul]
  have hTcard : Nat.card ↥(E' ⊔ C) = 3 ^ (e + c) := by
    rw [i224_card_sup hcomm hdisj', hE'card, hc, pow_add]
  have hTN : E' ⊔ C ≤ Subgroup.normalizer (P' : Set X) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.le_normalizer_map K.subtype ⟨y, hEN hy, rfl⟩
    · intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hcen : ∀ z : X, z ∈ P' → u * z * u⁻¹ = z := by
        rintro _ ⟨z, -, rfl⟩
        have := Subgroup.mem_centralizer_iff.1 (hCK hu) (z : X) z.2
        calc u * (z : X) * u⁻¹ = (z : X) * u * u⁻¹ := by rw [← this]
          _ = (z : X) := by group
      constructor
      · intro hy
        rw [hcen y hy]
        exact hy
      · intro hy
        have h1 : u * y * u⁻¹ = y := by
          have h := hcen _ hy
          calc u * y * u⁻¹ = u⁻¹ * (u * (u * y * u⁻¹) * u⁻¹) * u := by group
            _ = u⁻¹ * (u * y * u⁻¹) * u := by rw [h]
            _ = y := by group
        rw [h1] at hy
        exact hy
  have hP'ne : P' ≠ ⊥ := by
    intro h0
    exact hP ((Subgroup.map_eq_bot_iff_of_injective P K.subtype_injective).1 h0)
  have hP'2 : IsPGroup 2 ↥P' :=
    hP2.of_equiv (Subgroup.equivMapOfInjective P K.subtype K.subtype_injective)
  have hle := le_glaTwoLocalRank_of_le_normalizer (p := 3) (by norm_num) hP'ne hP'2 hTel hTN hTcard
  rw [her, hcr]
  exact hle

end TwoLocal

@[expose] def IsE6FourIndex : TauCeti.LieTypeIndex → Prop
  | .E6 q => IsTwoPow q 2
  | _ => False

@[expose] def IsE6EightIndex : TauCeti.LieTypeIndex → Prop
  | .E6 q => IsTwoPow q 3
  | _ => False

@[expose] def IsRankFourIndex : TauCeti.LieTypeIndex → Prop
  | .F4 q => IsTwoPow q 2
  | .E6 q => IsTwoPow q 1 ∨ IsTwoPow q 3
  | _ => False

@[expose] def IsOutThreePrimeIndex : TauCeti.LieTypeIndex → Prop
  | .F4 q => IsTwoPow q 2
  | .E6 q => IsTwoPow q 1
  | _ => False

@[expose] def rho2318 : TauCeti.LieTypeIndex → ℕ
  | .A r _ => r - 1
  | .twistedA r _ => r - 2
  | .F4 _ => 4
  | .E6 q => if q.p = 2 ∧ q.exponent = 2 then 5 else 4
  | .E7 _ => 6
  | .E8 _ => 6
  | _ => 0

theorem gen2318Index_evenScope {d : TauCeti.LieTypeIndex} (hd : Gen2318Index d) :
    Seitz2313Cover.EvenScope d := by
  cases d with
  | A r q =>
    obtain ⟨⟨hq2, -⟩, n, hn2, hrn⟩ := hd
    have : 9 ≤ r + 1 := by
      rw [hrn]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact ⟨hq2, by omega⟩
  | twistedA r q =>
    obtain ⟨hq13, n, hn3, hrn⟩ := hd
    refine ⟨?_, by omega⟩
    rcases hq13 with ⟨hq2, -⟩ | ⟨hq2, -⟩ <;> exact hq2
  | F4 q => exact hd.1
  | E6 q => rcases hd with ⟨hq2, -⟩ | ⟨hq2, -⟩ | ⟨hq2, -⟩ <;> exact hq2
  | E7 q => rcases hd with ⟨hq2, -⟩ | ⟨hq2, -⟩ <;> exact hq2
  | E8 q => rcases hd with ⟨hq2, -⟩ | ⟨hq2, -⟩ | ⟨hq2, -⟩ <;> exact hq2
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

theorem four_le_rho2318 {d : TauCeti.LieTypeIndex} (hd : Gen2318Index d) : 4 ≤ rho2318 d := by
  cases d with
  | A r q =>
    obtain ⟨⟨hq2, -⟩, n, hn2, hrn⟩ := hd
    have : 9 ≤ r + 1 := by
      rw [hrn]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    simp only [rho2318]
    omega
  | twistedA r q =>
    obtain ⟨hq13, n, hn3, hrn⟩ := hd
    simp only [rho2318]
    omega
  | F4 q => simp [rho2318]
  | E6 q => simp only [rho2318]; split_ifs <;> omega
  | E7 q => simp [rho2318]
  | E8 q => simp [rho2318]
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

theorem gen2318_trichotomy {d : TauCeti.LieTypeIndex} (hd : Gen2318Index d) :
    6 ≤ rho2318 d ∨ IsRankFourIndex d ∨ IsE6FourIndex d := by
  cases d with
  | A r q =>
    obtain ⟨⟨hq2, -⟩, n, hn2, hrn⟩ := hd
    have : 9 ≤ r + 1 := by
      rw [hrn]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    left
    simp only [rho2318]
    omega
  | twistedA r q =>
    obtain ⟨hq13, n, hn3, hrn⟩ := hd
    left
    simp only [rho2318]
    omega
  | F4 q => exact Or.inr (Or.inl hd)
  | E6 q =>
    rcases hd with h | h | h
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
  | E7 q => left; simp [rho2318]
  | E8 q => left; simp [rho2318]
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

theorem rho2318_E6Four {d : TauCeti.LieTypeIndex} (h : IsE6FourIndex d) : rho2318 d = 5 := by
  cases d <;> simp_all [IsE6FourIndex, rho2318, IsTwoPow]

theorem isRankFour_split {d : TauCeti.LieTypeIndex} (h : IsRankFourIndex d) :
    IsOutThreePrimeIndex d ∨ IsE6EightIndex d := by
  cases d <;> simp_all [IsRankFourIndex, IsOutThreePrimeIndex, IsE6EightIndex]
  all_goals tauto

@[expose] def Gen2318TwoLocal : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    Gen2318Index d.1 → Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
        rho2318 d.1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
        E ≤ Subgroup.normalizer (P : Set K)

@[expose] def Star2313Even : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), Gen2318Index d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D →
      ∃ E : Subgroup (MulAut S), E ≤ D ∧ E.relIndex D ≤ 9 ∧
        ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U

@[expose] def Gen2318OutThreePrime : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsOutThreePrimeIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → E ≤ (MulAut.conj : S →* MulAut S).range

@[expose] def Gen2318RankFour : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsRankFourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 3 ^ 4 →
      E ≤ (MulAut.conj : S →* MulAut S).range →
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U

@[expose] def Gen2318E64Core : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsE6FourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A → 5 ≤ CFSG.Open.pRank 3 A →
      ∃ E : Subgroup (MulAut S), E ≤ A ∧ 4 ≤ CFSG.Open.pRank 3 E ∧
        ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U

@[expose] def Gen2318E68Outer : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → CFSG.Open.IsElemAbelian 3 B →
      B ≤ Subgroup.normalizer (K : Set X) → GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B →
      B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ → IsLieQuot ↥K IsE6EightIndex →
        ¬ InducesInnerIn B K →
        5 ≤ CFSG.Open.pRank 3 B ∧ K ≤ gammaPrimeIn 3 4 B K

section Main

theorem gen2318_of_inputs (hGA : CFSG.Open.GriessAllModelsStatement) (hStar : Star2313Even)
    (hTL : Gen2318TwoLocal) (hOut : Gen2318OutThreePrime) (hRank4 : Gen2318RankFour)
    (hE64 : Gen2318E64Core) (hE68 : Gen2318E68Outer) : Gen2318 := by
  classical
  intro X _ _ hXK K B hKc hBel hBN hrk hC hLie
  have hq : CFSG.Open.IsQuasisimple ↥K := hKc.2.2
  have hperf : commutator ↥K = ⊤ := hq.1
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := odd_center_gen2318 hGA hq hLie
  obtain ⟨d, hd, ⟨e⟩⟩ := hLie
  by_cases hout : IsE6EightIndex d.1 ∧ ¬ InducesInnerIn B K
  · exact hE68 X hXK K B hKc hBel hBN hrk hC ⟨d, hout.1, ⟨e⟩⟩ hout.2
  have hs : Seitz2313Cover.EvenScope d.1 := gen2318Index_evenScope hd
  have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hBel inf_le_left
  have hc1 : 1 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    one_le_pRank_centralizer Nat.prime_three hBel hC
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn Nat.prime_three hBel hBN
  have hm := pRank_eq_add_autOrderIn Nat.prime_three hBel hBN hr
  obtain ⟨EK, PK, hEKel, hdisj, hρ, hPK0, hPK2, hEKN⟩ := hTL ↥K hq d hd ⟨e⟩
  have h2 := le_twoLocalRank_of_pair hCel inf_le_right hEKel hdisj hPK0 hPK2 hEKN
  have h4 := four_le_rho2318 hd
  have hrρ : rho2318 d.1 ≤ r := by omega
  refine ⟨by omega, ?_⟩
  have hAcard : Nat.card (autImage B K) = 3 ^ r := (card_autImage hperf).trans hr
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hBel
  obtain ⟨m, E₀, hE₀A, hE₀el, hE₀card, hm4, U, hU0, hU2, hUinv⟩ :
      ∃ (m : ℕ) (E₀ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))), E₀ ≤ autImage B K ∧
        IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ m ∧ 4 ≤ m ∧
        ∃ U : Subgroup (↥K ⧸ Subgroup.center ↥K), U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
          ∀ φ ∈ E₀, ∀ u ∈ U, φ u ∈ U := by
    rcases gen2318_trichotomy hd with hlarge | hrk4 | he64
    ·
      obtain ⟨E₀, hE₀A, hrel, U, hU0, hU2, hUinv⟩ := hStar _ d hd ⟨e⟩ (autImage B K) hAel
      have hE₀el : IsElemAbelian 3 E₀ := i271_isElemAbelian_of_le hAel hE₀A
      obtain ⟨m, hm'⟩ := i271_exists_card_eq Nat.prime_three hE₀el
      have h1 := Subgroup.relIndex_mul_card E₀ (autImage B K)
      rw [inf_of_le_left hE₀A, hm', hAcard] at h1
      have h3 : 3 ^ r ≤ 3 ^ (m + 2) := by
        calc 3 ^ r = E₀.relIndex (autImage B K) * 3 ^ m := h1.symm
          _ ≤ 9 * 3 ^ m := Nat.mul_le_mul_right _ hrel
          _ = 3 ^ (m + 2) := by ring
      have h5 : r ≤ m + 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h3
      exact ⟨m, E₀, hE₀A, hE₀el, hm', by omega, U, hU0, hU2, hUinv⟩
    ·
      have hinner : autImage B K ≤ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
          MulAut (↥K ⧸ Subgroup.center ↥K)).range := by
        rcases isRankFour_split hrk4 with hout3 | he68
        · exact hOut _ d hout3 ⟨e⟩ _ hAel
        · refine autImage_le_range_conj ?_
          by_contra hninn
          exact hout ⟨he68, hninn⟩
      obtain ⟨A', hA'le, hA'card⟩ := exists_sub_card_pow Nat.prime_three hAcard (k := 4)
        (by omega)
      have hA'el : IsElemAbelian 3 A' := i271_isElemAbelian_of_le hAel hA'le
      obtain ⟨U, hU0, hU2, hUinv⟩ := hRank4 _ d hrk4 ⟨e⟩ A' hA'el hA'card (hA'le.trans hinner)
      exact ⟨4, A', hA'le, hA'el, hA'card, le_rfl, U, hU0, hU2, hUinv⟩
    ·
      have h5 : 5 ≤ r := by
        have := rho2318_E6Four he64
        omega
      have hrank : 5 ≤ CFSG.Open.pRank 3 (autImage B K) := by
        rw [i271_pRank_eq Nat.prime_three hAel hAcard]
        exact h5
      obtain ⟨E₀, hE₀A, hE₀rank, U, hU0, hU2, hUinv⟩ := hE64 _ d he64 ⟨e⟩ (autImage B K) hAel hrank
      have hE₀el : IsElemAbelian 3 E₀ := i271_isElemAbelian_of_le hAel hE₀A
      obtain ⟨m, hm'⟩ := i271_exists_card_eq Nat.prime_three hE₀el
      have hmr : CFSG.Open.pRank 3 E₀ = m := i271_pRank_eq Nat.prime_three hE₀el hm'
      exact ⟨m, E₀, hE₀A, hE₀el, hm', by omega, U, hU0, hU2, hUinv⟩
  exact le_gammaPrime_of_seitz seitz2313Even_holds hperf hBel hodd hs e hE₀A hE₀el hE₀card
    (by omega) (by omega) ⟨U, hU0, hU2, hUinv⟩

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
