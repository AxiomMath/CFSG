module

public import CFSG.Sporadic.Th.Max3.AltNine
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

private def altRep2A : alternatingGroup (Fin 9) :=
  ⟨altRep2, mem_alternatingGroup.mpr sign_altRep2⟩

private theorem two_mul_card_centralizer_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    (g : alternatingGroup α)
    (h : ∃ s : Perm α, s * (g : Perm α) = (g : Perm α) * s ∧ s ∉ alternatingGroup α) :
    2 * Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup α))) =
      Nat.card (Subgroup.centralizer ({(g : Perm α)} : Set (Perm α))) := by
  classical
  obtain ⟨s, hs, hso⟩ := h
  let H : Subgroup (Perm α) := Subgroup.centralizer ({(g : Perm α)} : Set (Perm α))
  let φ : H →* ℤˣ := (Equiv.Perm.sign).comp H.subtype
  have hsH : s ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact hs
  have hs2 : Equiv.Perm.sign s = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hh | hh
    · exact absurd (mem_alternatingGroup.mpr hh) hso
    · exact hh
  have hphi : φ ⟨s, hsH⟩ = -1 := hs2
  have hindex : φ.ker.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and']
    refine ⟨⟨s, hsH⟩, ?_, ?_⟩
    · simp only [MonoidHom.mem_ker]
      rw [hphi]
      decide
    · intro b
      rcases Int.units_eq_one_or (φ b) with hb | hb
      · exact Or.inr (by rw [MonoidHom.mem_ker]; exact hb)
      · exact Or.inl (by rw [MonoidHom.mem_ker, map_mul, hphi, hb]; decide)
  have hH : Nat.card H = Nat.card φ.ker * 2 := by
    rw [← Subgroup.card_mul_index (H := φ.ker), hindex]
  have hkerCard : Nat.card φ.ker =
      Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup α))) := by
    apply Nat.card_congr
    refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro x
      have hxker : φ x = 1 := x.2
      have hxH : (x.1 : Perm α) * (g : Perm α) = (g : Perm α) * (x.1 : Perm α) :=
        Subgroup.mem_centralizer_singleton_iff.mp x.1.2
      exact
        ⟨⟨(x.1 : Perm α), mem_alternatingGroup.mpr hxker⟩,
          Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxH)⟩
    · intro y
      have hyC : y.1 * g = g * y.1 := Subgroup.mem_centralizer_singleton_iff.mp y.2
      exact
        ⟨⟨(y.1 : Perm α),
            Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext_iff.mp hyC)⟩,
          by
            rw [MonoidHom.mem_ker]
            exact mem_alternatingGroup.mp y.1.2⟩
    · intro x; rfl
    · intro y; rfl
  rw [hH, hkerCard]
  ring

private theorem exists_odd_commute_of_sq_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    {x : Perm α} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ s : Perm α, s * x = x * s ∧ s ∉ alternatingGroup α := by
  have hxx : ∀ y, x (x y) = y := by
    intro y
    have h := congrArg (fun p : Perm α => p y) hx
    simpa [pow_two] using h
  obtain ⟨a, hxa⟩ : ∃ a, x a ≠ a := by
    by_contra h
    push Not at h
    exact hx1 (Equiv.ext fun a => by simpa using h a)
  have hcomm : swap a (x a) * x = x * swap a (x a) := by
    ext c
    by_cases hca : c = a
    · subst c; simp [hxx]
    · by_cases hcb : c = x a
      · subst c; simp [hxx]
      · have h1 : x c ≠ a := by
          intro h
          exact hcb (by
            calc c = x (x c) := (hxx c).symm
              _ = x a := congrArg x h)
        have h2 : x c ≠ x a := fun h => hca (x.injective h)
        rw [mul_apply, mul_apply, Equiv.swap_apply_of_ne_of_ne hca hcb,
          Equiv.swap_apply_of_ne_of_ne h1 h2]
  refine ⟨swap a (x a), hcomm, ?_⟩
  intro hmem
  rw [mem_alternatingGroup] at hmem
  rw [Equiv.Perm.sign_swap (Ne.symm hxa)] at hmem
  exact absurd hmem (by decide)

private theorem nat_card_centralizer_perm_sq_one {α : Type*} [Fintype α] [DecidableEq α]
    {x : Perm α} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (Perm α))) =
      Nat.factorial (Fintype.card α - 2 * x.cycleType.card) * 2 ^ x.cycleType.card *
        Nat.factorial x.cycleType.card := by
  have hct : x.cycleType = Multiset.replicate x.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hx
  have hk : x.cycleType.card ≠ 0 := fun h => hx1 (Equiv.Perm.card_cycleType_eq_zero.mp h)
  rw [Equiv.Perm.nat_card_centralizer, hct]
  simp only [Multiset.sum_replicate, Multiset.prod_replicate, Multiset.toFinset_replicate, hk,
    ↓reduceIte, Finset.mem_singleton, Finset.prod_singleton, Multiset.count_replicate_self,
    Multiset.card_replicate]
  ring_nf

private theorem exists_swap_mul_swap_of_cycleType {c : Perm (Fin 9)}
    (hc : c.cycleType = ({2,2} : Multiset ℕ)) :
    ∃ a b e f : Fin 9, c = swap a b * swap e f := by
  have h2 : (2:ℕ) ∈ c.cycleType := by rw [hc]; simp
  obtain ⟨d, τ, hdc, hd, hdcyc, hdsupp⟩ := Equiv.Perm.mem_cycleType_iff.mp h2
  have hdct : d.cycleType = ({2} : Multiset ℕ) := by
    rw [hdcyc.cycleType, hdsupp]
  have hτ : τ.cycleType = ({2} : Multiset ℕ) := by
    have h1 : d.cycleType + τ.cycleType = ({2,2} : Multiset ℕ) := by
      rw [← Equiv.Perm.Disjoint.cycleType_mul hd, ← hdc, hc]
    rw [hdct] at h1
    exact add_left_cancel h1
  have hdswap : d.IsSwap := Equiv.Perm.card_support_eq_two.mp hdsupp
  have hτswap : τ.IsSwap := Equiv.Perm.isSwap_iff_cycleType.mpr hτ
  obtain ⟨a, b, _hab, rfl⟩ := hdswap
  obtain ⟨e, f, _hef, rfl⟩ := hτswap
  exact ⟨a, b, e, f, hdc⟩

private theorem sq_eq_one_of_cycleType {c : Perm (Fin 9)}
    (hc : c.cycleType = ({2,2} : Multiset ℕ)) : c * c = 1 := by
  have h := (Equiv.Perm.pow_prime_eq_one_iff (σ := c) (p := 2)).mpr (by rw [hc]; simp)
  simpa [pow_two] using h

private theorem support_card_of_cycleType {c : Perm (Fin 9)}
    (hc : c.cycleType = ({2,2} : Multiset ℕ)) : c.support.card = 4 := by
  rw [← Equiv.Perm.sum_cycleType, hc]
  rfl

private def type22CommutingList : Finset (Perm (Fin 9)) :=
  ((Finset.univ : Finset (Fin 9 × Fin 9 × Fin 9 × Fin 9)).filter (fun t =>
      let p := swap t.1 t.2.1 * swap t.2.2.1 t.2.2.2
      p * p = 1 ∧ p.support.card = 4 ∧ p * altRep2 = altRep2 * p)).image
    (fun t => swap t.1 t.2.1 * swap t.2.2.1 t.2.2.2)

private theorem type22CommutingList_card : type22CommutingList.card = 38 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem mem_type22CommutingList {c : Perm (Fin 9)}
    (hc : c.cycleType = ({2,2} : Multiset ℕ)) (hcomm : c * altRep2 = altRep2 * c) :
    c ∈ type22CommutingList := by
  obtain ⟨a, b, e, f, hceq⟩ := exists_swap_mul_swap_of_cycleType hc
  have hsq : (swap a b * swap e f) * (swap a b * swap e f) = 1 := by
    rw [← hceq]; exact sq_eq_one_of_cycleType hc
  have hsupp : (swap a b * swap e f).support.card = 4 := by
    rw [← hceq]; exact support_card_of_cycleType hc
  have hcom : (swap a b * swap e f) * altRep2 = altRep2 * (swap a b * swap e f) := by
    rw [← hceq]; exact hcomm
  refine Finset.mem_image.mpr ⟨(a, b, e, f), ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsq, hsupp, hcom⟩
  · exact hceq.symm

private theorem ncard_type22_commuting_conj (g x : alternatingGroup (Fin 9)) :
    Set.ncard {c : alternatingGroup (Fin 9) |
        c ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set (alternatingGroup (Fin 9))) ∧
        (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)} =
    Set.ncard {c : alternatingGroup (Fin 9) |
        c ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 9))) ∧
        (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)} := by
  apply Nat.card_congr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨c, hcC, hcct⟩
    have hc : c * (g * x * g⁻¹) = (g * x * g⁻¹) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcC
    refine ⟨g⁻¹ * c * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * c * g * x = g⁻¹ * (c * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * c) * g := by rw [hc]
        _ = x * (g⁻¹ * c * g) := by group
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hconj := Equiv.Perm.cycleType_conj (σ := (c : Perm (Fin 9)))
        (τ := ((g : Perm (Fin 9)))⁻¹)
      simp only [inv_inv] at hconj
      rw [hconj, hcct]
  · rintro ⟨c, hcC, hcct⟩
    have hc : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    refine ⟨g * c * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
        _ = g * (x * c) * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [Equiv.Perm.cycleType_conj, hcct]
  · rintro ⟨c, _⟩; exact Subtype.ext (by group)
  · rintro ⟨c, _⟩; exact Subtype.ext (by group)

private theorem ncard_type22_commuting_altRep2_le :
    Set.ncard {c : alternatingGroup (Fin 9) |
        c ∈ Subgroup.centralizer ({altRep2A} : Set (alternatingGroup (Fin 9))) ∧
        (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)} ≤ 38 := by
  have hsub : ((fun c : alternatingGroup (Fin 9) => (c : Perm (Fin 9))) ''
      {c : alternatingGroup (Fin 9) |
        c ∈ Subgroup.centralizer ({altRep2A} : Set (alternatingGroup (Fin 9))) ∧
        (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)}) ⊆
      (type22CommutingList : Set (Perm (Fin 9))) := by
    rintro p ⟨c, hc, rfl⟩
    refine mem_type22CommutingList hc.2 ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hc.1
    simpa only [Subgroup.coe_mul, altRep2A] using Subtype.ext_iff.mp this
  calc Set.ncard {c : alternatingGroup (Fin 9) |
          c ∈ Subgroup.centralizer ({altRep2A} : Set (alternatingGroup (Fin 9))) ∧
          (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)}
      = Set.ncard ((fun c : alternatingGroup (Fin 9) => (c : Perm (Fin 9))) ''
          {c : alternatingGroup (Fin 9) |
            c ∈ Subgroup.centralizer ({altRep2A} : Set (alternatingGroup (Fin 9))) ∧
            (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)}) :=
        (Set.ncard_image_of_injective _ Subtype.coe_injective).symm
    _ ≤ Set.ncard (type22CommutingList : Set (Perm (Fin 9))) := Set.ncard_le_ncard hsub
    _ = type22CommutingList.card := Set.ncard_coe_finset type22CommutingList
    _ = 38 := type22CommutingList_card

private theorem cycleType_eq_22_of_card_centralizer_eq_480_A9
    (x : alternatingGroup (Fin 9)) (hx : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 9)))) = 480) :
    (x : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ) := by
  have hxP : (x : Perm (Fin 9)) ^ 2 = 1 := by
    simpa using congrArg (fun y : alternatingGroup (Fin 9) => (y : Perm (Fin 9))) hx
  have hxP1 : (x : Perm (Fin 9)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨s, hs, hso⟩ := exists_odd_commute_of_sq_eq_one hxP hxP1
  have hhalf := two_mul_card_centralizer_alternatingGroup x ⟨s, hs, hso⟩
  rw [hC, nat_card_centralizer_perm_sq_one hxP hxP1] at hhalf
  have hsum : (x : Perm (Fin 9)).cycleType.sum = 2 * (x : Perm (Fin 9)).cycleType.card := by
    rw [Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hxP, Multiset.sum_replicate,
      Multiset.card_replicate, smul_eq_mul]
    exact Nat.mul_comm _ _
  have hle : 2 * (x : Perm (Fin 9)).cycleType.card ≤ 9 := by
    rw [← hsum, Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hk : (x : Perm (Fin 9)).cycleType.card ≠ 0 := fun h =>
    hxP1 (Equiv.Perm.card_cycleType_eq_zero.mp h)
  have hk1 : 1 ≤ (x : Perm (Fin 9)).cycleType.card := Nat.one_le_iff_ne_zero.mpr hk
  have hk4 : (x : Perm (Fin 9)).cycleType.card ≤ 4 := by omega
  have hcases : (x : Perm (Fin 9)).cycleType.card = 1 ∨
      (x : Perm (Fin 9)).cycleType.card = 2 ∨
      (x : Perm (Fin 9)).cycleType.card = 3 ∨
      (x : Perm (Fin 9)).cycleType.card = 4 := by omega
  have hk2 : (x : Perm (Fin 9)).cycleType.card = 2 := by
    rcases hcases with h | h | h | h
    · rw [h] at hhalf; norm_num [Nat.factorial] at hhalf
    · exact h
    · rw [h] at hhalf; norm_num [Nat.factorial] at hhalf
    · rw [h] at hhalf; norm_num [Nat.factorial] at hhalf
  rw [Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hxP, hk2]
  rfl

theorem not_card_centralizer_A8 (x : alternatingGroup (Fin 8)) (hx : x ^ 2 = 1) (hx1 : x ≠ 1) :
    Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 8)))) ≠ 480 := by
  intro h480
  have hxP : (x : Perm (Fin 8)) ^ 2 = 1 := by
    simpa using congrArg (fun y : alternatingGroup (Fin 8) => (y : Perm (Fin 8))) hx
  have hxP1 : (x : Perm (Fin 8)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨s, hs, hso⟩ := exists_odd_commute_of_sq_eq_one hxP hxP1
  have hhalf := two_mul_card_centralizer_alternatingGroup x ⟨s, hs, hso⟩
  rw [h480, nat_card_centralizer_perm_sq_one hxP hxP1] at hhalf
  have hsum : (x : Perm (Fin 8)).cycleType.sum = 2 * (x : Perm (Fin 8)).cycleType.card := by
    rw [Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hxP, Multiset.sum_replicate,
      Multiset.card_replicate, smul_eq_mul]
    exact Nat.mul_comm _ _
  have hle : 2 * (x : Perm (Fin 8)).cycleType.card ≤ 8 := by
    rw [← hsum, Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hk : (x : Perm (Fin 8)).cycleType.card ≠ 0 := fun h =>
    hxP1 (Equiv.Perm.card_cycleType_eq_zero.mp h)
  have hk1 : 1 ≤ (x : Perm (Fin 8)).cycleType.card := Nat.one_le_iff_ne_zero.mpr hk
  have hk4 : (x : Perm (Fin 8)).cycleType.card ≤ 4 := by omega
  have hcases : (x : Perm (Fin 8)).cycleType.card = 1 ∨
      (x : Perm (Fin 8)).cycleType.card = 2 ∨
      (x : Perm (Fin 8)).cycleType.card = 3 ∨
      (x : Perm (Fin 8)).cycleType.card = 4 := by omega
  rcases hcases with h | h | h | h <;> rw [h] at hhalf <;> norm_num [Nat.factorial] at hhalf

theorem card_involutions_A9_le (x : alternatingGroup (Fin 9)) (hx : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hC : Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 9)))) = 480) :
    Set.ncard {c : alternatingGroup (Fin 9) |
      c ∈ centralizer ({x} : Set (alternatingGroup (Fin 9))) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
        Nat.card (centralizer ({c} : Set (alternatingGroup (Fin 9)))) = 480} ≤ 38 := by
  have hxct : (x : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ) :=
    cycleType_eq_22_of_card_centralizer_eq_480_A9 x hx hx1 hC
  have hsub : {c : alternatingGroup (Fin 9) |
        c ∈ centralizer ({x} : Set (alternatingGroup (Fin 9))) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
          Nat.card (centralizer ({c} : Set (alternatingGroup (Fin 9)))) = 480} ⊆
      {c : alternatingGroup (Fin 9) |
        c ∈ centralizer ({x} : Set (alternatingGroup (Fin 9))) ∧
        (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)} := by
    rintro c ⟨hcC, hc2, hc1, hccard⟩
    exact ⟨hcC, cycleType_eq_22_of_card_centralizer_eq_480_A9 c hc2 hc1 hccard⟩
  obtain ⟨g, hg⟩ : ∃ g : alternatingGroup (Fin 9), g * x * g⁻¹ = altRep2A := by
    have hord : orderOf (x : Perm (Fin 9)) = 2 := by
      rw [← Equiv.Perm.lcm_cycleType, hxct]; rfl
    obtain ⟨g, hgA, hg | hg⟩ :=
      CFSG.Sporadic.Th.Max3.exists_conj_eq_of_orderOf_eq_two x.2 hord
    · exact ⟨⟨g, hgA⟩, Subtype.ext hg⟩
    · exfalso
      have h1 : (g * (x : Perm (Fin 9)) * g⁻¹).cycleType = (x : Perm (Fin 9)).cycleType :=
        Equiv.Perm.cycleType_conj
      rw [hg, CFSG.Sporadic.Th.Max3.cycleType_altRep4] at h1
      rw [hxct] at h1
      exact absurd (congrArg Multiset.card h1) (by norm_num)
  have htrans := ncard_type22_commuting_conj g x
  rw [hg] at htrans
  calc Set.ncard {c : alternatingGroup (Fin 9) |
        c ∈ centralizer ({x} : Set (alternatingGroup (Fin 9))) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
          Nat.card (centralizer ({c} : Set (alternatingGroup (Fin 9)))) = 480}
      ≤ Set.ncard {c : alternatingGroup (Fin 9) |
          c ∈ centralizer ({x} : Set (alternatingGroup (Fin 9))) ∧
          (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)} := Set.ncard_le_ncard hsub
    _ = Set.ncard {c : alternatingGroup (Fin 9) |
          c ∈ centralizer ({altRep2A} : Set (alternatingGroup (Fin 9))) ∧
          (c : Perm (Fin 9)).cycleType = ({2,2} : Multiset ℕ)} := htrans.symm
    _ ≤ 38 := ncard_type22_commuting_altRep2_le

end CFSG.EvenSporadicStandard.HNRecog.Harada
