module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem exists_two_group_lift {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center X)
    (hZ : Nat.card (Subgroup.center X) = 3) {E T' : Subgroup Y} (hT : T' ≠ ⊥)
    (hT2 : IsPGroup 2 T') (hE : E ≤ Subgroup.normalizer (T' : Set Y)) :
    ∃ T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ E.comap π ≤ Subgroup.normalizer (T : Set X) := by
  have : Finite Y := Finite.of_surjective π hπ
  set Ť : Subgroup X := T'.comap π with hŤ
  have hZŤ : Subgroup.center X ≤ Ť := by
    intro z hz
    have : π z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
    show π z ∈ T'
    rw [this]
    exact T'.one_mem
  set N : Subgroup Ť := (Subgroup.center X).subgroupOf Ť with hN
  have hNcard : Nat.card N = 3 := by
    rw [hN, ← hZ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZŤ).toEquiv
  have hNcen : ∀ n : Ť, n ∈ N → ∀ g : Ť, g * n = n * g := fun n hn g => by
    have hc : (n : X) ∈ Subgroup.center X := hn
    exact Subtype.ext (Subgroup.mem_center_iff.1 hc (g : X))
  have hNnormal : N.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by rw [hNcen n hn g, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact hn⟩
  let φ : Ť →* T' := (π.comp Ť.subtype).codRestrict T' fun x => x.2
  have hφker : φ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hN, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hφsurj : Function.Surjective φ := by
    intro t
    obtain ⟨x, hx⟩ := hπ t
    exact ⟨⟨x, by show π x ∈ T'; rw [hx]; exact t.2⟩, Subtype.ext hx⟩
  have hindex : N.index = Nat.card T' := by
    rw [← hφker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφsurj, Subgroup.card_top]
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hindex, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = 2 ^ k := by
    rw [← hH.symm.index_eq_card, hindex, hk]
  have hH2 : IsPGroup 2 H := IsPGroup.of_card hHcard
  have hmem : ∀ x : Ť, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ H := by
    rintro x ⟨n, hn⟩
    obtain ⟨⟨⟨z, hz⟩, ⟨h, hh⟩⟩, hzh⟩ := (Subgroup.isComplement'_def.1 hH).2 x
    change z * h = x at hzh
    have hcomm : Commute z h := hNcen z hz h |>.symm
    have h1 : z ^ 2 ^ n * h ^ 2 ^ n = 1 := by rw [← hcomm.mul_pow, hzh, hn]
    have h2 : z ^ 2 ^ n ∈ H := by
      have : z ^ 2 ^ n = (h ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact H.inv_mem (H.pow_mem hh _)
    have h3 : z ^ 2 ^ n = 1 := by
      have := Subgroup.disjoint_def.1 hH.disjoint (N.pow_mem hz _) h2
      exact this
    have h4 : z = 1 := by
      have h5 : z ^ 3 = 1 := by
        have := pow_card_eq_one' (G := N) (x := ⟨z, hz⟩)
        rw [hNcard] at this
        exact congrArg Subtype.val this
      have h6 := orderOf_dvd_of_pow_eq_one h3
      have h7 := orderOf_dvd_of_pow_eq_one h5
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)) h6 h7)
    rw [h4, one_mul] at hzh
    rw [← hzh]
    exact hh
  refine ⟨H.map Ť.subtype, ?_, hH2.map _, ?_⟩
  · intro h0
    have hH1 : H = ⊥ := (Subgroup.map_eq_bot_iff_of_injective H Ť.subtype_injective).1 h0
    apply hT
    have : Nat.card T' = 1 := by
      rw [hk, ← hHcard, hH1]
      exact Subgroup.card_bot
    exact Subgroup.eq_bot_of_card_eq _ this
  ·
    have one : ∀ e : X, π e ∈ Subgroup.normalizer (T' : Set Y) → ∀ t ∈ H.map Ť.subtype,
        e * t * e⁻¹ ∈ H.map Ť.subtype := by
      rintro e he _ ⟨t, ht, rfl⟩
      have hy : e * (t : X) * e⁻¹ ∈ Ť := by
        show π (e * (t : X) * e⁻¹) ∈ T'
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 he _).1 t.2
      obtain ⟨n, hn⟩ := hH2 ⟨t, ht⟩
      have hn' : (t : X) ^ 2 ^ n = 1 := by
        have := congrArg (fun x : H => ((x : Ť) : X)) hn
        simpa using this
      have hm : (⟨e * (t : X) * e⁻¹, hy⟩ : Ť) ∈ H := by
        refine hmem _ ⟨n, Subtype.ext ?_⟩
        change (e * (t : X) * e⁻¹) ^ 2 ^ n = 1
        rw [conj_pow, hn']
        group
      exact ⟨_, hm, rfl⟩
    intro e he
    have heE : π e ∈ Subgroup.normalizer (T' : Set Y) := hE he
    have heE' : π e⁻¹ ∈ Subgroup.normalizer (T' : Set Y) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ heE
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => one e heE y hy, fun hy => ?_⟩
    have := one e⁻¹ heE' _ hy
    simpa [mul_assoc] using this

end CFSG.HardMathSupport.Solomon.Coordinator
