module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimewiseScalarInvolutionSupport
public import CFSG.GroupTheory.PrimeCommutatorSupport

public section

open scoped Pointwise commutatorElement

namespace CFSG.Semidihedral.Principal.PrimewiseScalar

open CFSG.SolvableHall CFSG.OddInversion

variable {M : Type*} [Group M] [Finite M]

theorem hall_structure (N : Subgroup M) (hNsolv : Group.IsSolvable N) (hNodd : Odd (Nat.card N))
    {s : M} (hsN : s ∈ Subgroup.normalizer (N : Set M)) (hs : orderOf s = 2)
    (hall : Nat.Coprime (Nat.card (N ⊓ Subgroup.centralizer ({s} : Set M) : Subgroup M))
      ((N ⊓ Subgroup.centralizer ({s} : Set M)).relIndex N)) :
    ∃ V : Subgroup M, (V : Set M) = invertedSet N s ∧ V ≤ N ∧ (V.subgroupOf N).Normal ∧
      V ⊔ (N ⊓ Subgroup.centralizer ({s} : Set M)) = N ∧
      V ⊓ (N ⊓ Subgroup.centralizer ({s} : Set M)) = ⊥ ∧
      Nat.card V = (N ⊓ Subgroup.centralizer ({s} : Set M)).relIndex N := by
  classical
  let _ := zpowersConjAction N hsN
  set A := N ⊓ Subgroup.centralizer ({s} : Set M) with hAdef
  have hAN : A ≤ N := inf_le_left
  set u : Subgroup.zpowers s := ⟨s, Subgroup.mem_zpowers s⟩ with hudef
  have hgen : ∀ v : Subgroup.zpowers s, v ∈ Subgroup.zpowers u := by
    rintro ⟨v, hv⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ⟨k, Subtype.ext (by simp [hudef])⟩
  have hu : orderOf u = 2 := by rw [hudef, Subgroup.orderOf_mk, hs]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)
  obtain ⟨hJn, -, hJT, -, -, hcardJ, -, hHall⟩ :=
    solvable_prime_commutator_prime_support (P := Subgroup.zpowers s) (A := N) u hgen hu hNsolv hp
  set J := commutatorAction (A := Subgroup.zpowers s) (G := N) with hJdef
  set C := fixedPointSubgroup (Subgroup.zpowers s) N with hCdef
  have hC : C = A.subgroupOf N := by
    ext x
    rw [hCdef, mem_fixedPointSubgroup_iff hsN hs, Subgroup.mem_subgroupOf, hAdef,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      calc (x : M) * s = s * x * s⁻¹ * s := by rw [h]
        _ = s * x := by group
    · rintro ⟨-, h⟩
      rw [← h]
      group
  have hCcard : Nat.card C = Nat.card A := by
    rw [hC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hCidx : C.index = A.relIndex N := by rw [hC]; rfl
  obtain ⟨hJC1, hJC2⟩ := hHall (by rw [hCcard, hCidx]; exact hall)
  set V := J.map N.subtype with hVdef
  have hVN : V ≤ N := Subgroup.map_subtype_le J
  have hVsub : V.subgroupOf N = J :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective J
  have hCmap : C.map N.subtype = A := by rw [hC]; exact Subgroup.map_subgroupOf_eq_of_le hAN
  have htop : (⊤ : Subgroup N).map N.subtype = N := by
    ext x
    exact ⟨fun ⟨y, _, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩⟩
  have hVA : V ⊔ A = N := by
    rw [hVdef, ← hCmap, ← Subgroup.map_sup, hJC2, htop]
  have hVA' : V ⊓ A = ⊥ := by
    rw [hVdef, ← hCmap, ← Subgroup.map_inf_eq _ _ _ Subtype.val_injective, hJC1, Subgroup.map_bot]
  have hVcard : Nat.card V = A.relIndex N := by
    rw [hVdef, Subgroup.card_map_of_injective Subtype.val_injective, hcardJ, hJC1,
      Subgroup.card_bot, mul_one, hCidx]
  have hUV : invertedSet N s ⊆ (V : Set M) := by
    intro x hx
    obtain ⟨d, hdJ, hd⟩ := exists_sq_eq_of_mem_invertedSet hNodd hx
    have hdinvN : d⁻¹ ∈ N := N.inv_mem hdJ.1
    have hgenmem : (⟨x, hx.1⟩ : N) ∈ J := by
      rw [hJdef, commutatorAction_eq_closure]
      apply Subgroup.subset_closure
      refine ⟨u, ⟨d⁻¹, hdinvN⟩, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, zpowersConjAction_smul_coe, hudef]
      have h1 : s * d⁻¹ * s⁻¹ = d := by
        rw [← conj_inv, hdJ.2, inv_inv]
      rw [h1, inv_inv, ← sq, hd]
    exact ⟨⟨x, hx.1⟩, hgenmem, rfl⟩
  have hUcard : Nat.card (invertedSet N s) = A.relIndex N := by
    have hsNotN : s ∉ N := notMem_of_odd_card hNodd hs
    obtain ⟨-, -, h⟩ := odd_inversion_coset_count hNodd hsN hsNotN hs
    rw [h, hAdef, Subgroup.inf_relIndex_left]
  have hVU : (V : Set M) = invertedSet N s := by
    symm
    apply Set.eq_of_subset_of_ncard_le hUV _ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hUcard, SetLike.coe_sort_coe, hVcard]
  refine ⟨V, hVU, hVN, ?_, hVA, hVA', hVcard⟩
  rw [hVsub]
  exact hJn

theorem hall_full (N : Subgroup M) (hNsolv : Group.IsSolvable N) (hNodd : Odd (Nat.card N))
    {s : M} (hsN : s ∈ Subgroup.normalizer (N : Set M)) (hs : orderOf s = 2)
    (hall : Nat.Coprime (Nat.card (N ⊓ Subgroup.centralizer ({s} : Set M) : Subgroup M))
      ((N ⊓ Subgroup.centralizer ({s} : Set M)).relIndex N)) :
    ∃ V : Subgroup M, (V : Set M) = invertedSet N s ∧ V = ⁅N, Subgroup.zpowers s⁆ ∧ V ≤ N ∧
      IsMulCommutative V ∧ (V.subgroupOf N).Characteristic ∧
      Nat.Coprime (Nat.card V) (V.relIndex N) ∧ (V.subgroupOf N).Normal ∧
      V ⊔ (N ⊓ Subgroup.centralizer ({s} : Set M)) = N ∧
      V ⊓ (N ⊓ Subgroup.centralizer ({s} : Set M)) = ⊥ ∧
      V ⊓ Subgroup.centralizer ({s} : Set M) = ⊥ ∧
      Nat.card V = (N ⊓ Subgroup.centralizer ({s} : Set M)).relIndex N ∧
      (∀ W : Subgroup M, W ≤ N → (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card V) →
        W ≤ V) ∧
      (∀ W : Subgroup M, W ≤ N → (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card V) →
        Nat.Coprime (W.relIndex N) (Nat.card V) → W = V) ∧
      Subgroup.normalizer (N : Set M) ≤ Subgroup.normalizer (V : Set M) := by
  classical
  obtain ⟨V, hVU, hVN, hVn, hVA, hVA', hVcard⟩ := hall_structure N hNsolv hNodd hsN hs hall
  set A := N ⊓ Subgroup.centralizer ({s} : Set M) with hAdef
  have hAN : A ≤ N := inf_le_left
  have hss : s⁻¹ = s := inv_eq_self_of_orderOf_two hs
  have hinv : ∀ x ∈ V, s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have : x ∈ invertedSet N s := by rw [← hVU]; exact hx
    exact this.2
  have hcomm : IsMulCommutative V := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have h1 := hinv _ (V.mul_mem x.2 y.2)
    rw [show s * ((x : M) * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) by group, hinv _ x.2,
      hinv _ y.2, mul_inv_rev] at h1
    have h2 := congrArg (fun z => z⁻¹) h1
    simp only [mul_inv_rev, inv_inv] at h2
    change (x : M) * y = y * x
    exact h2.symm
  have hcardN : Nat.card N = Nat.card V * Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (H := A) (K := N)
    rw [inf_eq_left.mpr hAN, ← hVcard] at h1
    rw [← h1, mul_comm]
  have hVidx : V.relIndex N = Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (H := V) (K := N)
    rw [inf_eq_left.mpr hVN, hcardN] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1]; ring)
  have hVhall : Nat.Coprime (Nat.card V) (V.relIndex N) := by
    rw [hVcard, hVidx]
    exact hall.symm
  have hpi : ∀ W : Subgroup M, W ≤ N → (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card V) →
      W ≤ V := by
    intro W hWN hW
    set J' := V.subgroupOf N
    set W' := W.subgroupOf N
    have h1 : J'.relIndex (W' ⊔ J') = J'.relIndex W' := Subgroup.relIndex_sup_right W' J'
    have h2 : J'.relIndex (W' ⊔ J') ∣ J'.index := Subgroup.relIndex_dvd_index_of_le le_sup_right
    have h3 : J'.relIndex W' ∣ Nat.card W' := Subgroup.relIndex_dvd_card J' W'
    have hW'card : Nat.card W' = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv
    have hJ'idx : J'.index = Nat.card A := hVidx
    have hd1 : J'.relIndex W' = 1 := by
      by_contra hne
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqW : q ∣ Nat.card W := hW'card ▸ hqd.trans h3
      have h5 : J'.relIndex W' ∣ J'.index := h1 ▸ h2
      have hqA : q ∣ Nat.card A := hJ'idx ▸ hqd.trans h5
      have hqV : q ∣ Nat.card V := hW q hq hqW
      have h4 : q ∣ Nat.gcd (Nat.card A) (A.relIndex N) := Nat.dvd_gcd hqA (hVcard ▸ hqV)
      rw [hall.gcd_eq_one] at h4
      exact hq.not_dvd_one h4
    intro x hx
    have hxW' : (⟨x, hWN hx⟩ : N) ∈ W' := hx
    have hle : W' ≤ J' := Subgroup.relIndex_eq_one.mp hd1
    exact hle hxW'
  have huniq : ∀ W : Subgroup M, W ≤ N →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card V) →
      Nat.Coprime (W.relIndex N) (Nat.card V) → W = V := by
    intro W hWN hW hWcop
    have hWV := hpi W hWN hW
    apply Subgroup.eq_of_le_of_card_ge hWV
    have h1 := Subgroup.relIndex_mul_card (H := W) (K := N)
    rw [inf_eq_left.mpr hWN] at h1
    have h2 : Nat.card V ∣ W.relIndex N * Nat.card W := by
      rw [h1]
      exact Subgroup.card_dvd_of_le hVN
    exact Nat.le_of_dvd Nat.card_pos (hWcop.symm.dvd_of_dvd_mul_left h2)
  have hchar : (V.subgroupOf N).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ
    set W := ((V.subgroupOf N).map φ.toMonoidHom).map N.subtype
    have hWN : W ≤ N := Subgroup.map_subtype_le _
    have hWcard : Nat.card W = Nat.card V := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective,
        Subgroup.card_map_of_injective φ.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
    have hWV : W ≤ V := hpi W hWN (fun q _ hq => hWcard ▸ hq)
    intro x hx
    have : (x : M) ∈ W := ⟨x, hx, rfl⟩
    exact hWV this
  have hnorm : Subgroup.normalizer (N : Set M) ≤ Subgroup.normalizer (V : Set M) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    let φ := N.normalizerMonoidHom ⟨g, hg⟩
    have hfix : (V.subgroupOf N).comap φ.toMonoidHom = V.subgroupOf N := hchar.fixed φ
    have hφ : ∀ y : N, ((φ y : N) : M) = g * y * g⁻¹ := fun y => rfl
    constructor
    · intro hx
      have hxN : x ∈ N := hVN hx
      have h1 : (⟨x, hxN⟩ : N) ∈ (V.subgroupOf N).comap φ.toMonoidHom := by rw [hfix]; exact hx
      have h2 : φ ⟨x, hxN⟩ ∈ V.subgroupOf N := h1
      rw [Subgroup.mem_subgroupOf, hφ] at h2
      exact h2
    · intro hx
      have hxN : x ∈ N := (Subgroup.mem_normalizer_iff.mp hg x).mpr (hVN hx)
      have h1 : (⟨x, hxN⟩ : N) ∈ (V.subgroupOf N).comap φ.toMonoidHom := by
        change φ ⟨x, hxN⟩ ∈ V.subgroupOf N
        rw [Subgroup.mem_subgroupOf, hφ]
        exact hx
      rw [hfix] at h1
      exact h1
  have hVc : V ⊓ Subgroup.centralizer ({s} : Set M) = ⊥ := by
    rw [← hVA', hAdef, ← inf_assoc, inf_eq_left.mpr hVN]
  have hVB : V = ⁅N, Subgroup.zpowers s⁆ := by
    apply le_antisymm
    · intro x hx
      have hxU : x ∈ invertedSet N s := by rw [← hVU]; exact hx
      obtain ⟨d, hdJ, hd⟩ := exists_sq_eq_of_mem_invertedSet hNodd hxU
      have hcomm' : ⁅d, s⁆ = x := by
        rw [commutatorElement_def, ← hd, sq]
        have h1 : s * d⁻¹ * s⁻¹ = d := by rw [← conj_inv, hdJ.2, inv_inv]
        calc d * s * d⁻¹ * s⁻¹ = d * (s * d⁻¹ * s⁻¹) := by group
          _ = d * d := by rw [h1]
      rw [← hcomm']
      exact Subgroup.commutator_mem_commutator hdJ.1 (Subgroup.mem_zpowers s)
    · rw [Subgroup.commutator_le]
      intro n hn g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rcases zpow_eq_one_or_self hs k with h | h
      · rw [h, commutatorElement_one_right]
        exact V.one_mem
      · rw [h, ← SetLike.mem_coe, hVU]
        rw [commutatorElement_def]
        have := mul_conj_inv_mem_invertedSet hs hsN hn
        rw [show n * s * n⁻¹ * s⁻¹ = n * (s * n * s⁻¹)⁻¹ by group]
        exact this
  exact ⟨V, hVU, hVB, hVN, hcomm, hchar, hVhall, hVn, hVA, hVA', hVc, hVcard, hpi, huniq, hnorm⟩

theorem card_eq_of_isHallSubgroup_singleton {G : Type*} [Group G] [Finite G] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (H : Subgroup G) (hH : IsHallSubgroup {(⟨ℓ, hℓ⟩ : Nat.Primes)} H) :
    Nat.card H = ℓ ^ (Nat.card G).factorization ℓ := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card H = ℓ ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {q} hq hqd => by
      have := hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqd
      simpa using congrArg Subtype.val this)⟩
  have hidx : ¬ ℓ ∣ H.index := fun h => hH.p_in_pi_of_p_dvd_index ⟨ℓ, hℓ⟩ h rfl
  have hG := H.card_mul_index
  rw [← hG, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero, hk,
    hℓ.factorization_pow, Finsupp.single_eq_same]

@[expose] def IsSylowOf (N : Subgroup M) (ℓ : ℕ) (P : Subgroup M) : Prop :=
  ∃ Q : Sylow ℓ N, (Q : Subgroup N).map N.subtype = P

theorem exists_invariant_sylow_le (N : Subgroup M) (hNsolv : Group.IsSolvable N)
    (hNodd : Odd (Nat.card N)) {s : M} (hsN : s ∈ Subgroup.normalizer (N : Set M))
    (hs : orderOf s = 2) {ℓ : ℕ} (hℓ : ℓ.Prime) (K : Subgroup M) (hKN : K ≤ N)
    (hK : IsPGroup ℓ K) (hKinv : ∀ x ∈ K, s * x * s⁻¹ ∈ K) :
    ∃ P : Subgroup M, IsSylowOf N ℓ P ∧ (∀ x ∈ P, s * x * s⁻¹ ∈ P) ∧ K ≤ P := by
  classical
  let _ := zpowersConjAction N hsN
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)
  have hA2 : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_eq_two hs, pow_one])
  set K' := K.subgroupOf N
  have hK'π : IsPiSubgroup {(⟨ℓ, hℓ⟩ : Nat.Primes)} K' := by
    intro q hq
    have hcard : Nat.card K' = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
    rw [hcard] at hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
    rw [hk] at hq
    have := (Nat.prime_dvd_prime_iff_eq q.2 hℓ).mp (q.2.dvd_of_dvd_pow hq)
    exact Subtype.ext this
  have hK'inv : ∀ g : Subgroup.zpowers s, ∀ x ∈ K', g • x ∈ K' :=
    smul_mem_of_conj_mem hsN hs (fun x hx => hKinv x hx)
  obtain ⟨P', hP'hall, hP'inv, hKP'⟩ := coprime_invariant_hall_containment hA2 hp hNsolv
    {(⟨ℓ, hℓ⟩ : Nat.Primes)} K' hK'π hK'inv
  have hP'card := card_eq_of_isHallSubgroup_singleton hℓ P' hP'hall
  refine ⟨P'.map N.subtype, ⟨Sylow.ofCard P' hP'card, by rw [Sylow.coe_ofCard]⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := hP'inv ⟨s, Subgroup.mem_zpowers s⟩ x hx
    exact ⟨_, h1, rfl⟩
  · intro x hx
    exact ⟨⟨x, hKN hx⟩, hKP' hx, rfl⟩

theorem exists_conj_of_invariant_sylow (N : Subgroup M) (hNodd : Odd (Nat.card N)) {s : M}
    (hsN : s ∈ Subgroup.normalizer (N : Set M)) (hs : orderOf s = 2) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {P P₁ : Subgroup M} (hP : IsSylowOf N ℓ P) (hP₁ : IsSylowOf N ℓ P₁)
    (hPinv : ∀ x ∈ P, s * x * s⁻¹ ∈ P) (hP₁inv : ∀ x ∈ P₁, s * x * s⁻¹ ∈ P₁) :
    ∃ c ∈ N, s * c * s⁻¹ = c ∧ ∀ y : M, y ∈ P₁ ↔ c * y * c⁻¹ ∈ P := by
  classical
  let _ := zpowersConjAction N hsN
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)
  have hA2 : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_eq_two hs, pow_one])
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q₁, rfl⟩ := hP₁
  have hinvN : ∀ (R : Sylow ℓ N), (∀ x ∈ (R : Subgroup N).map N.subtype,
      s * x * s⁻¹ ∈ (R : Subgroup N).map N.subtype) →
      ∀ g : Subgroup.zpowers s, ∀ x ∈ (R : Subgroup N), g • x ∈ (R : Subgroup N) := by
    intro R hR
    refine smul_mem_of_conj_mem hsN hs (fun x hx => ?_)
    obtain ⟨y, hy, hyx⟩ := hR x ⟨x, hx, rfl⟩
    have : y = ⟨s * (x : M) * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN x).mp x.2⟩ :=
      Subtype.ext hyx
    rw [← this]
    exact hy
  obtain ⟨c, hc, hcQ⟩ := coprime_invariant_sylow_conjugacy hA2 hp Q Q₁
    (hinvN Q hPinv) (hinvN Q₁ hP₁inv)
  have hcs : s * (c : M) * s⁻¹ = c := (mem_fixedPointSubgroup_iff hsN hs c).mp hc
  refine ⟨c, c.2, hcs, fun y => ?_⟩
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hcQ] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  · intro hy
    obtain ⟨w, hw, hwy⟩ := hy
    have hyN : y ∈ N := by
      have h1 : (c : M)⁻¹ * (w : M) * c ∈ N := N.mul_mem (N.mul_mem (N.inv_mem c.2) w.2) c.2
      rw [show (w : M) = c * y * (c : M)⁻¹ from hwy,
        show (c : M)⁻¹ * (c * y * (c : M)⁻¹) * c = y by group] at h1
      exact h1
    have hmem : (⟨y, hyN⟩ : N) ∈ (Q : Subgroup N).map (MulAut.conj c⁻¹).toMonoidHom := by
      refine ⟨w, hw, Subtype.ext ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, inv_inv]
      rw [show (w : M) = c * y * (c : M)⁻¹ from hwy]
      group
    rw [hcQ] at hmem
    exact ⟨⟨y, hyN⟩, hmem, rfl⟩

omit [Finite M] in
theorem conj_comm_s {s c y : M} (hc : s * c * s⁻¹ = c) :
    s * (c * y * c⁻¹) * s⁻¹ = c * (s * y * s⁻¹) * c⁻¹ := by
  calc s * (c * y * c⁻¹) * s⁻¹ = (s * c * s⁻¹) * (s * y * s⁻¹) * (s * c * s⁻¹)⁻¹ := by group
    _ = c * (s * y * s⁻¹) * c⁻¹ := by rw [hc]

theorem card_isSylowOf {N : Subgroup M} {ℓ : ℕ} [Fact ℓ.Prime] {P : Subgroup M}
    (hP : IsSylowOf N ℓ P) : Nat.card P = ℓ ^ (Nat.card N).factorization ℓ := by
  obtain ⟨Q, rfl⟩ := hP
  rw [Subgroup.card_map_of_injective Subtype.val_injective, Sylow.card_eq_multiplicity]

omit [Finite M] in
theorem le_of_isSylowOf {N : Subgroup M} {ℓ : ℕ} {P : Subgroup M} (hP : IsSylowOf N ℓ P) :
    P ≤ N := by
  obtain ⟨Q, rfl⟩ := hP
  exact Subgroup.map_subtype_le _

omit [Finite M] in
theorem card_eq_card_mul_relIndex (N K : Subgroup M) (hKN : K ≤ N) :
    Nat.card N = Nat.card K * K.relIndex N := by
  have h := Subgroup.relIndex_mul_card (H := K) (K := N)
  rw [inf_eq_left.mpr hKN] at h
  rw [← h, mul_comm]

theorem scalar_of_hall (N : Subgroup M) (hNsolv : Group.IsSolvable N) (hNodd : Odd (Nat.card N))
    {s : M} (hsN : s ∈ Subgroup.normalizer (N : Set M)) (hs : orderOf s = 2)
    (hall : Nat.Coprime (Nat.card (N ⊓ Subgroup.centralizer ({s} : Set M) : Subgroup M))
      ((N ⊓ Subgroup.centralizer ({s} : Set M)).relIndex N))
    {ℓ : ℕ} (hℓ : ℓ.Prime) {P : Subgroup M} (hP : IsSylowOf N ℓ P)
    (hPinv : ∀ x ∈ P, s * x * s⁻¹ ∈ P) :
    (∀ x ∈ P, s * x * s⁻¹ = x) ∨ (∀ x ∈ P, s * x * s⁻¹ = x⁻¹) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set A := N ⊓ Subgroup.centralizer ({s} : Set M) with hAdef
  have hAN : A ≤ N := inf_le_left
  have hPN := le_of_isSylowOf hP
  have hAfix : ∀ x ∈ A, s * x * s⁻¹ = x := by
    intro x hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    rw [← h]
    group
  by_cases hℓA : ℓ ∣ Nat.card A
  · left
    obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow ℓ A))
    set K := (R : Subgroup A).map A.subtype with hK
    have hKA : K ≤ A := Subgroup.map_subtype_le _
    have hKp : IsPGroup ℓ K := R.isPGroup'.map A.subtype
    have hKinv : ∀ x ∈ K, s * x * s⁻¹ ∈ K := fun x hx => by rw [hAfix x (hKA hx)]; exact hx
    obtain ⟨P₁, hP₁, hP₁inv, hKP₁⟩ :=
      exists_invariant_sylow_le N hNsolv hNodd hsN hs hℓ K (hKA.trans hAN) hKp hKinv
    have hidx : ¬ ℓ ∣ A.relIndex N := by
      intro h
      have h1 : ℓ ∣ Nat.gcd (Nat.card A) (A.relIndex N) := Nat.dvd_gcd hℓA h
      rw [hall.gcd_eq_one] at h1
      exact hℓ.not_dvd_one h1
    have hKcard : Nat.card K = Nat.card P₁ := by
      rw [card_isSylowOf hP₁, hK, Subgroup.card_map_of_injective Subtype.val_injective,
        Sylow.card_eq_multiplicity, card_eq_card_mul_relIndex N A hAN,
        Nat.factorization_mul Nat.card_pos.ne' (by
          intro h0; rw [h0] at hidx; exact hidx (dvd_zero ℓ)),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    have hKeq : K = P₁ := Subgroup.eq_of_le_of_card_ge hKP₁ hKcard.ge
    have hP₁A : P₁ ≤ A := hKeq ▸ hKA
    obtain ⟨c, -, hc, hcP⟩ :=
      exists_conj_of_invariant_sylow N hNodd hsN hs hℓ hP₁ hP hP₁inv hPinv
    intro y hy
    have h1 := hAfix _ (hP₁A ((hcP y).mp hy))
    rw [conj_comm_s hc] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · right
    have hPA : P ⊓ A = ⊥ := by
      rw [← Subgroup.card_eq_one]
      by_contra hne
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqP : q ∣ Nat.card P := hqd.trans (Subgroup.card_dvd_of_le inf_le_left)
      rw [card_isSylowOf hP] at hqP
      have hqℓ : q = ℓ := (Nat.prime_dvd_prime_iff_eq hq hℓ).mp (hq.dvd_of_dvd_pow hqP)
      exact hℓA (hqℓ ▸ hqd.trans (Subgroup.card_dvd_of_le inf_le_right))
    have hss : s⁻¹ = s := inv_eq_self_of_orderOf_two hs
    have hsP : s ∈ Subgroup.normalizer (P : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hPinv x, fun hx => ?_⟩
      have h1 := hPinv _ hx
      rwa [show s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ by group,
        show s * s = 1 by rw [← sq, ← hs, pow_orderOf_eq_one], inv_one, one_mul,
        mul_one] at h1
    have hPodd : Odd (Nat.card P) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hPN)
    obtain ⟨hbij, -, -⟩ := odd_involution_product_decomposition hPodd hs hsP
    intro x hx
    obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := hbij.surjOn hx
    have hc1 : c = 1 := by
      have : c ∈ P ⊓ A := by
        refine ⟨(Subgroup.mem_inf.mp hc).1, hPN (Subgroup.mem_inf.mp hc).1,
          (Subgroup.mem_inf.mp hc).2⟩
      rw [hPA] at this
      exact this
    simp only at hcj
    rw [hc1, one_mul] at hcj
    rw [← hcj]
    exact hj.2

theorem hall_of_scalar (N : Subgroup M) (hNsolv : Group.IsSolvable N) (hNodd : Odd (Nat.card N))
    {s : M} (hsN : s ∈ Subgroup.normalizer (N : Set M)) (hs : orderOf s = 2)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card N → ∃ P : Subgroup M, IsSylowOf N ℓ P ∧
      (∀ x ∈ P, s * x * s⁻¹ ∈ P) ∧
      ((∀ x ∈ P, s * x * s⁻¹ = x) ∨ (∀ x ∈ P, s * x * s⁻¹ = x⁻¹))) :
    Nat.Coprime (Nat.card (N ⊓ Subgroup.centralizer ({s} : Set M) : Subgroup M))
      ((N ⊓ Subgroup.centralizer ({s} : Set M)).relIndex N) := by
  classical
  set A := N ⊓ Subgroup.centralizer ({s} : Set M) with hAdef
  have hAN : A ≤ N := inf_le_left
  have hAfix : ∀ x ∈ A, s * x * s⁻¹ = x := by
    intro x hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    rw [← h]
    group
  by_contra hnot
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hnot
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓA : ℓ ∣ Nat.card A := hℓd.trans (Nat.gcd_dvd_left _ _)
  have hℓI : ℓ ∣ A.relIndex N := hℓd.trans (Nat.gcd_dvd_right _ _)
  have hℓN : ℓ ∣ Nat.card N := hℓA.trans (Subgroup.card_dvd_of_le hAN)
  obtain ⟨P, hP, hPinv, hPs⟩ := h ℓ hℓ hℓN
  have hPN := le_of_isSylowOf hP
  rcases hPs with hcent | hinv
  ·
    have hPA : P ≤ A := fun x hx => ⟨hPN hx, Subgroup.mem_centralizer_singleton_iff.mpr (by
      have h1 := hcent x hx
      calc x * s = s * x * s⁻¹ * s := by rw [h1]
        _ = s * x := by group)⟩
    have h1 : ℓ ^ (Nat.card N).factorization ℓ ∣ Nat.card A := by
      rw [← card_isSylowOf hP]
      exact Subgroup.card_dvd_of_le hPA
    have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
    have hI0 : A.relIndex N ≠ 0 := by
      intro h0
      rw [card_eq_card_mul_relIndex N A hAN, h0, mul_zero] at hℓN
      exact Nat.card_pos.ne' (by
        rw [card_eq_card_mul_relIndex N A hAN, h0, mul_zero])
    have h2 := (hℓ.pow_dvd_iff_le_factorization hA0).mp h1
    rw [card_eq_card_mul_relIndex N A hAN, Nat.factorization_mul hA0 hI0,
      Finsupp.add_apply] at h2
    have h3 : 0 < (A.relIndex N).factorization ℓ := hℓ.factorization_pos_of_dvd hI0 hℓI
    omega
  ·
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) ℓ hℓA
    set K := Subgroup.zpowers (x : M) with hK
    have hKA : K ≤ A := Subgroup.zpowers_le.mpr x.2
    have hKp : IsPGroup ℓ K := IsPGroup.of_card (n := 1) (by
      rw [hK, Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
    have hKinv : ∀ y ∈ K, s * y * s⁻¹ ∈ K := fun y hy => by rw [hAfix y (hKA hy)]; exact hy
    obtain ⟨P₁, hP₁, hP₁inv, hKP₁⟩ :=
      exists_invariant_sylow_le N hNsolv hNodd hsN hs hℓ K (hKA.trans hAN) hKp hKinv
    obtain ⟨c, -, hc, hcP⟩ :=
      exists_conj_of_invariant_sylow N hNodd hsN hs hℓ hP hP₁ hPinv hP₁inv
    have hxP₁ : (x : M) ∈ P₁ := hKP₁ (Subgroup.mem_zpowers _)
    have h1 := hinv _ ((hcP x).mp hxP₁)
    rw [conj_comm_s hc, hAfix x x.2, conj_inv] at h1
    have h2 : (x : M) = (x : M)⁻¹ := mul_left_cancel (mul_right_cancel h1)
    have h3 : (x : M) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h2]
      exact mul_inv_cancel _
    have h4 : orderOf x ∣ 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h3
    rw [hx] at h4
    have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h4
    rw [hℓ2] at hℓN
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hℓN)

theorem hall_of_complement (N : Subgroup M) {s : M} (V : Subgroup M) (hVN : V ≤ N)
    (hVn : (V.subgroupOf N).Normal)
    (hVA : V ⊔ (N ⊓ Subgroup.centralizer ({s} : Set M)) = N)
    (hVA' : V ⊓ (N ⊓ Subgroup.centralizer ({s} : Set M)) = ⊥)
    (hVhall : Nat.Coprime (Nat.card V) (V.relIndex N)) :
    Nat.Coprime (Nat.card (N ⊓ Subgroup.centralizer ({s} : Set M) : Subgroup M))
      ((N ⊓ Subgroup.centralizer ({s} : Set M)).relIndex N) := by
  set A := N ⊓ Subgroup.centralizer ({s} : Set M) with hAdef
  have hAN : A ≤ N := inf_le_left
  set V' := V.subgroupOf N
  set A' := A.subgroupOf N
  have hsup : A' ⊔ V' = ⊤ := by
    apply Subgroup.map_injective (f := N.subtype) Subtype.val_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAN,
      Subgroup.map_subgroupOf_eq_of_le hVN, sup_comm, hVA]
    ext x
    exact ⟨fun hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩, fun ⟨y, _, hy⟩ => hy ▸ y.2⟩
  have hinf : V' ⊓ A' = ⊥ := by
    apply Subgroup.map_injective (f := N.subtype) Subtype.val_injective
    rw [Subgroup.map_inf_eq _ _ _ Subtype.val_injective, Subgroup.map_subgroupOf_eq_of_le hAN,
      Subgroup.map_subgroupOf_eq_of_le hVN, hVA', Subgroup.map_bot]
  have h1 : V'.relIndex (A' ⊔ V') = V'.relIndex A' := Subgroup.relIndex_sup_right A' V'
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 : V'.relIndex A' = Nat.card A' := by
    rw [Subgroup.relIndex, show V'.subgroupOf A' = ⊥ by
      rw [← Subgroup.inf_subgroupOf_right, hinf, Subgroup.bot_subgroupOf], Subgroup.index_bot]
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hVidx : V.relIndex N = Nat.card A := by
    change V'.index = _
    rw [h1, h2, hA'card]
  have hNV := card_eq_card_mul_relIndex N V hVN
  have hNA := card_eq_card_mul_relIndex N A hAN
  have hAidx : A.relIndex N = Nat.card V := by
    rw [hVidx] at hNV
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A))
    rw [← hNA, hNV, mul_comm]
  rw [hAidx, ← hVidx]
  exact hVhall.symm

theorem solvable_odd_primewise_scalar_involution_has_characteristic_inverted_complement
    (N : Subgroup M) (hNsolv : Group.IsSolvable N) (hNodd : Odd (Nat.card N)) (s : M)
    (hsN : s ∈ Subgroup.normalizer (N : Set M)) (hs : orderOf s = 2) :
    let A := N ⊓ Subgroup.centralizer ({s} : Set M)
    let U := invertedSet N s
    let B := ⁅N, Subgroup.zpowers s⁆
    let invariant : Subgroup M → Prop := fun P => ∀ x ∈ P, s * x * s⁻¹ ∈ P
    let scalar : Subgroup M → Prop := fun P =>
      (∀ x ∈ P, s * x * s⁻¹ = x) ∨ (∀ x ∈ P, s * x * s⁻¹ = x⁻¹)
    let hall : Prop := Nat.Coprime (Nat.card A) (A.relIndex N)
    ((∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card N →
        ∃ P : Subgroup M, IsSylowOf N ℓ P ∧ invariant P ∧ scalar P) ↔ hall) ∧
    (hall ↔ ∃ V : Subgroup M, (V : Set M) = U ∧ V = B ∧ V ≤ N ∧ IsMulCommutative V ∧
      (V.subgroupOf N).Characteristic ∧ Nat.Coprime (Nat.card V) (V.relIndex N) ∧
      (V.subgroupOf N).Normal ∧ V ⊔ A = N ∧ V ⊓ A = ⊥ ∧
      V ⊓ Subgroup.centralizer ({s} : Set M) = ⊥) ∧
    (hall →
      (∀ ℓ : ℕ, ℓ.Prime → ∀ P : Subgroup M, IsSylowOf N ℓ P → invariant P → scalar P) ∧
      Nat.card U = A.relIndex N ∧
      ∃ V : Subgroup M, (V : Set M) = U ∧
        (∀ W : Subgroup M, W ≤ N → (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card V) →
          W ≤ V) ∧
        (∀ W : Subgroup M, W ≤ N → (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card V) →
          Nat.Coprime (W.relIndex N) (Nat.card V) → W = V) ∧
        Subgroup.normalizer (N : Set M) ≤ Subgroup.normalizer (V : Set M)) := by
  intro A U B invariant scalar hall
  have hscalar : hall → ∀ ℓ : ℕ, ℓ.Prime → ∀ P : Subgroup M, IsSylowOf N ℓ P → invariant P →
      scalar P := fun h ℓ hℓ P hP hPinv => scalar_of_hall N hNsolv hNodd hsN hs h hℓ hP hPinv
  refine ⟨⟨hall_of_scalar N hNsolv hNodd hsN hs, fun h ℓ hℓ _ => ?_⟩, ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨P, hP, hPinv, -⟩ := exists_invariant_sylow_le N hNsolv hNodd hsN hs hℓ ⊥ bot_le
      (IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero]))
      (fun x hx => by rw [Subgroup.mem_bot] at hx ⊢; rw [hx]; group)
    exact ⟨P, hP, hPinv, hscalar h ℓ hℓ P hP hPinv⟩
  · obtain ⟨V, hVU, hVB, hVN, hcomm, hchar, hVhall, hVn, hVA, hVA', hVc, -, -, -, -⟩ :=
      hall_full N hNsolv hNodd hsN hs h
    exact ⟨V, hVU, hVB, hVN, hcomm, hchar, hVhall, hVn, hVA, hVA', hVc⟩
  · rintro ⟨V, -, -, hVN, -, -, hVhall, hVn, hVA, hVA', -⟩
    exact hall_of_complement N V hVN hVn hVA hVA' hVhall
  · intro h
    obtain ⟨V, hVU, -, -, -, -, -, -, -, -, -, hVcard, hpi, huniq, hnorm⟩ :=
      hall_full N hNsolv hNodd hsN hs h
    refine ⟨hscalar h, ?_, V, hVU, hpi, huniq, hnorm⟩
    rw [← hVcard]
    change Nat.card (invertedSet N s) = Nat.card V
    rw [← hVU]
    rfl

end CFSG.Semidihedral.Principal.PrimewiseScalar
