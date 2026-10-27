module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

theorem perfect_hom_trivial {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    [Group.IsSolvable B] (f : A →* B) (a : A) : f a = 1 := by
  by_contra h
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Nontrivial f.range := ⟨⟨⟨f a, a, rfl⟩, 1, fun h' => h (congrArg Subtype.val h')⟩⟩
  exact Group.IsPerfect.not_isSolvable f.range inferInstance

theorem simple_hom_trivial {S Ω : Type*} [Group S] [IsSimpleGroup S] [Finite S] [Finite Ω]
    {m : ℕ} (hS : m.factorial < Nat.card S) (hΩ : Nat.card Ω ≤ m) (θ : S →* Equiv.Perm Ω)
    (s : S) : θ s = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker with h | h
  · exfalso
    have hinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff _).1 h
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm] at h1
    exact absurd (lt_of_lt_of_le hS (h1.trans (Nat.factorial_le hΩ))) (lt_irrefl _)
  · have hs : s ∈ θ.ker := h ▸ Subgroup.mem_top s
    exact hs

theorem simple_action_trivial {S Ω : Type*} [Group S] [IsSimpleGroup S] [Finite S]
    [MulAction S Ω] [Finite Ω] {m : ℕ} (hS : m.factorial < Nat.card S) (hΩ : Nat.card Ω ≤ m)
    (s : S) (x : Ω) : s • x = x := by
  have := simple_hom_trivial hS hΩ (MulAction.toPermHom S Ω) s
  simpa using congrArg (fun p => p x) this

structure Quot2Data {C Y : Type*} [Group C] [Group Y] (φ : C →* Y) (D : Subgroup Y) : Prop where
  D_le : D ≤ φ.range
  range_le : φ.range ≤ normalizer (D : Set Y)
  simple : IsSimpleGroup D
  noncomm : ∃ a b : D, a * b ≠ b * a
  index_two : ∃ k : ℕ, Nat.card φ.range = Nat.card D * 2 ^ k
  ker_two : ∃ m : ℕ, Nat.card φ.ker = 2 ^ m
  big : (Nat.card φ.ker).factorial < Nat.card D

section Basic

variable {C Y : Type*} [Group C] [Group Y] [Finite C] {φ : C →* Y} {D : Subgroup Y}

omit [Finite C] in
theorem card_eq_card_map_mul_card_ker (φ : C →* Y) (K : Subgroup C) :
    Nat.card K = Nat.card (K.map φ) * Nat.card (φ.ker.subgroupOf K) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.domRestrict K).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (φ.domRestrict K)).toEquiv,
    MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h1
  exact h1

local instance finite_range_of_finite (φ : C →* Y) : Finite φ.range :=
  Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective

theorem card_ker_subgroupOf_le (φ : C →* Y) (K : Subgroup C) :
    Nat.card (φ.ker.subgroupOf K) ≤ Nat.card φ.ker :=
  Nat.card_le_card_of_injective (fun x => ⟨(x : K).1, Subgroup.mem_subgroupOf.1 x.2⟩)
    (fun _ _ hab => Subtype.ext (Subtype.ext (congrArg (fun z : φ.ker => (z : C)) hab)))

theorem Quot2Data.finite (h : Quot2Data φ D) : Finite D :=
  Finite.of_injective (Subgroup.inclusion h.D_le) (Subgroup.inclusion_injective _)

omit [Finite C] in
theorem Quot2Data.normal_subgroupOf (h : Quot2Data φ D) : (D.subgroupOf φ.range).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.D_le).2 h.range_le

theorem Quot2Data.isPGroup_quot (h : Quot2Data φ D) [(D.subgroupOf φ.range).Normal] :
    IsPGroup 2 (φ.range ⧸ D.subgroupOf φ.range) := by
  have := h.finite
  obtain ⟨k, hk⟩ := h.index_two
  have hQcard : Nat.card (φ.range ⧸ D.subgroupOf φ.range) = 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf φ.range)
    have h2 : Nat.card (D.subgroupOf φ.range) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.D_le).toEquiv
    rw [h2, hk] at h1
    have hpos : 0 < Nat.card D := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card hQcard

theorem Quot2Data.map_le (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K) :
    K.map φ ≤ D := by
  have := h.normal_subgroupOf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (φ.range ⧸ D.subgroupOf φ.range) := h.isPGroup_quot.isNilpotent
  have : Group.IsSolvable (φ.range ⧸ D.subgroupOf φ.range) := inferInstance
  let ψ : K →* φ.range ⧸ D.subgroupOf φ.range :=
    (QuotientGroup.mk' (D.subgroupOf φ.range)).comp (φ.rangeRestrict.comp K.subtype)
  rintro _ ⟨k, hk, rfl⟩
  have h1 := perfect_hom_trivial ψ ⟨k, hk⟩
  have h2 : φ.rangeRestrict k ∈ D.subgroupOf φ.range := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

theorem Quot2Data.mem_of_odd (h : Quot2Data φ D) {c : C} (hodd : Odd (orderOf c)) : φ c ∈ D := by
  have := h.normal_subgroupOf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : C →* φ.range ⧸ D.subgroupOf φ.range :=
    (QuotientGroup.mk' (D.subgroupOf φ.range)).comp φ.rangeRestrict
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 h.isPGroup_quot) (ψ c)
  have hdvd : orderOf (ψ c) ∣ orderOf c := orderOf_map_dvd ψ c
  have hj0 : j = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf (ψ c) := by
      rw [hj]
      exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have h2 : φ.rangeRestrict c ∈ D.subgroupOf φ.range := (QuotientGroup.eq_one_iff _).1 hj
  exact h2

theorem Quot2Data.map_eq (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K)
    (hc : Nat.card K = Nat.card D) : K.map φ = D := by
  have := h.finite
  have := h.simple
  have hle := h.map_le hK
  have : Finite (K.map φ) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  set H' : Subgroup D := (K.map φ).subgroupOf D with hH'
  have hcard := card_eq_card_map_mul_card_ker φ K
  have hH'card : Nat.card H' = Nat.card (K.map φ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx := Subgroup.card_eq_card_quotient_mul_card_subgroup H'
  have hq : Nat.card (D ⧸ H') = Nat.card (φ.ker.subgroupOf K) := by
    have hpos : 0 < Nat.card (K.map φ) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (D ⧸ H') * Nat.card (K.map φ) = Nat.card D := by rw [← hH'card, ← hidx]
      _ = Nat.card K := hc.symm
      _ = Nat.card (K.map φ) * Nat.card (φ.ker.subgroupOf K) := hcard
      _ = Nat.card (φ.ker.subgroupOf K) * Nat.card (K.map φ) := mul_comm _ _
  have hle_n : Nat.card (D ⧸ H') ≤ Nat.card φ.ker := hq ▸ card_ker_subgroupOf_le φ K
  have hH'top : H' = ⊤ := by
    rw [eq_top_iff]
    intro s _
    have h1 := simple_action_trivial (S := D) (Ω := D ⧸ H') h.big hle_n s ((1 : D) : D ⧸ H')
    have h2 : ((s * 1 : D) : D ⧸ H') = ((1 : D) : D ⧸ H') := h1
    rw [QuotientGroup.eq] at h2
    simpa using h2
  refine le_antisymm hle fun d hd => ?_
  have : (⟨d, hd⟩ : D) ∈ H' := hH'top ▸ Subgroup.mem_top _
  exact this

theorem Quot2Data.eq_one_of_map_eq_one (h : Quot2Data φ D) {K : Subgroup C}
    (hK : Group.IsPerfect K) (hc : Nat.card K = Nat.card D) {k : C} (hk : k ∈ K) (hφ : φ k = 1) :
    k = 1 := by
  have := h.finite
  have e := card_eq_card_map_mul_card_ker φ K
  rw [h.map_eq hK hc, hc] at e
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h1 : Nat.card (φ.ker.subgroupOf K) = 1 := by
    have : Nat.card D * Nat.card (φ.ker.subgroupOf K) = Nat.card D * 1 := by rw [← e, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h2 := Subgroup.card_eq_one.1 h1
  have : (⟨k, hk⟩ : K) ∈ φ.ker.subgroupOf K := Subgroup.mem_subgroupOf.2 hφ
  rw [h2, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

@[expose] noncomputable def Quot2Data.restrictEquiv (h : Quot2Data φ D) {K : Subgroup C}
    (hK : Group.IsPerfect K) (hc : Nat.card K = Nat.card D) : K ≃* D :=
  MulEquiv.ofBijective ((φ.domRestrict K).codRestrict D
    (fun k => h.map_le hK ⟨k, k.2, rfl⟩))
    ⟨fun a b hab => by
      have h1 : φ (a : C) = φ (b : C) := congrArg Subtype.val hab
      have h2 : ((a : C)⁻¹ * (b : C)) ∈ K := K.mul_mem (K.inv_mem a.2) b.2
      have h3 := h.eq_one_of_map_eq_one hK hc h2 (by rw [map_mul, map_inv, h1, inv_mul_cancel])
      exact Subtype.ext (inv_mul_eq_one.1 h3),
    fun d => by
      obtain ⟨k, hk, hkd⟩ := (h.map_eq hK hc ▸ d.2 : (d : Y) ∈ K.map φ)
      exact ⟨⟨k, hk⟩, Subtype.ext hkd⟩⟩

theorem Quot2Data.restrictEquiv_apply (h : Quot2Data φ D) {K : Subgroup C}
    (hK : Group.IsPerfect K) (hc : Nat.card K = Nat.card D) (k : K) :
    ((h.restrictEquiv hK hc k : D) : Y) = φ (k : C) := rfl

theorem Quot2Data.isSimpleGroup (h : Quot2Data φ D) {K : Subgroup C}
    (hK : Group.IsPerfect K) (hc : Nat.card K = Nat.card D) : IsSimpleGroup K := by
  have := h.simple
  exact (h.restrictEquiv hK hc).isSimpleGroup

theorem Quot2Data.comm_ker (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K)
    (hc : Nat.card K = Nat.card D) {k n : C} (hk : k ∈ K) (hn : n ∈ φ.ker) : k * n = n * k := by
  have := h.isSimpleGroup hK hc
  let θ : K →* Equiv.Perm φ.ker :=
    (MulAut.toPerm φ.ker).comp (MulAut.conjNormal.comp K.subtype)
  have h1 := simple_hom_trivial (S := K) (Ω := φ.ker) (m := Nat.card φ.ker)
    (hc ▸ h.big) le_rfl θ ⟨k, hk⟩
  have h2 := congrArg (fun p : Equiv.Perm φ.ker => ((p ⟨n, hn⟩ : φ.ker) : C)) h1
  have h3 : k * n * k⁻¹ = n := (MulAut.conjNormal_apply k ⟨n, hn⟩).symm.trans h2
  exact mul_inv_eq_iff_eq_mul.1 h3

theorem Quot2Data.exists_mul_ker (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K)
    (hc : Nat.card K = Nat.card D) {c : C} (hcD : φ c ∈ D) :
    ∃ k ∈ K, ∃ n ∈ φ.ker, c = k * n := by
  obtain ⟨k, hk, hkc⟩ := (h.map_eq hK hc ▸ hcD : φ c ∈ K.map φ)
  refine ⟨k, hk, k⁻¹ * c, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hkc, inv_mul_cancel]

omit [Finite C] in
theorem Quot2Data.isPGroup_ker (h : Quot2Data φ D) : IsPGroup 2 φ.ker := by
  obtain ⟨m, hm⟩ := h.ker_two
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card hm

theorem Quot2Data.odd_mem (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K)
    (hc : Nat.card K = Nat.card D) {c : C} (hodd : Odd (orderOf c)) : c ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := h.exists_mul_ker hK hc (h.mem_of_odd hodd)
  have hkn : Commute k n := h.comm_ker hK hc hk hn
  set m := orderOf (k * n) with hm
  have h1 : k ^ m * n ^ m = 1 := by rw [← hkn.mul_pow]; exact pow_orderOf_eq_one _
  have h2 : n ^ m = (k ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : n ^ m = 1 := by
    refine h.eq_one_of_map_eq_one hK hc ?_ ?_
    · rw [h2]; exact K.inv_mem (K.pow_mem hk m)
    · rw [map_pow, (MonoidHom.mem_ker.1 hn), one_pow]
  have h4 : orderOf n ∣ m := orderOf_dvd_of_pow_eq_one h3
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 h.isPGroup_ker) ⟨n, hn⟩
  have hj' : orderOf n = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
  have hj0 : j = 0 := by
    by_contra hne
    have : 2 ∣ orderOf n := by rw [hj']; exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (this.trans h4))
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
  rw [hj', mul_one]
  exact hk

theorem Quot2Data.le_of_perfect (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K)
    (hc : Nat.card K = Nat.card D) {K' : Subgroup C} (hK' : Group.IsPerfect K') : K' ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup C := D.comap φ with hE
  have hKE : K ≤ E := fun k hk => h.map_le hK ⟨k, hk, rfl⟩
  have hK'E : K' ≤ E := fun k hk => h.map_le hK' ⟨k, hk, rfl⟩
  have hkerE : φ.ker ≤ E := Subgroup.ker_le_comap φ D
  have hnE : (K.subgroupOf E).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k₀, hk₀, n, hn, hg⟩ := h.exists_mul_ker hK hc g.2
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hcomm : n * (x : C) = (x : C) * n := (h.comm_ker hK hc hx hn).symm
    have h1 : n * (x : C) * n⁻¹ = x := mul_inv_eq_iff_eq_mul.2 hcomm
    have h2 : ((g * x * g⁻¹ : E) : C) = k₀ * ((x : C)) * k₀⁻¹ := by
      show (g : C) * (x : C) * (g : C)⁻¹ = _
      rw [hg]
      calc k₀ * n * (x : C) * (k₀ * n)⁻¹ = k₀ * (n * (x : C) * n⁻¹) * k₀⁻¹ := by group
        _ = _ := by rw [h1]
    rw [h2]
    exact K.mul_mem (K.mul_mem hk₀ hx) (K.inv_mem hk₀)
  have : Finite φ.ker := inferInstance
  have : Group.IsNilpotent φ.ker := h.isPGroup_ker.isNilpotent
  let ρ : φ.ker →* E ⧸ K.subgroupOf E :=
    (QuotientGroup.mk' (K.subgroupOf E)).comp (Subgroup.inclusion hkerE)
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk, n, hn, hx⟩ := h.exists_mul_ker hK hc x.2
    refine ⟨⟨n, hn⟩, ?_⟩
    show QuotientGroup.mk (⟨n, hkerE hn⟩ : E) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    show ((⟨n, hkerE hn⟩ : E)⁻¹ * x : E) ∈ K.subgroupOf E
    rw [Subgroup.mem_subgroupOf]
    show n⁻¹ * (x : C) ∈ K
    rw [hx, h.comm_ker hK hc hk hn, inv_mul_cancel_left]
    exact hk
  have : Group.IsSolvable (E ⧸ K.subgroupOf E) := Group.isSolvable_of_surjective hρ
  let σ : K' →* E ⧸ K.subgroupOf E :=
    (QuotientGroup.mk' (K.subgroupOf E)).comp (Subgroup.inclusion hK'E)
  intro k' hk'
  have h1 := perfect_hom_trivial σ ⟨k', hk'⟩
  have h2 : Subgroup.inclusion hK'E ⟨k', hk'⟩ ∈ K.subgroupOf E := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

theorem Quot2Data.eq_of_perfect (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K)
    (hc : Nat.card K = Nat.card D) {K' : Subgroup C} (hK' : Group.IsPerfect K')
    (hc' : Nat.card K' = Nat.card D) : K' = K :=
  Subgroup.eq_of_le_of_card_ge (h.le_of_perfect hK hc hK') (by rw [hc, hc'])

theorem Quot2Data.normal (h : Quot2Data φ D) {K : Subgroup C} (hK : Group.IsPerfect K)
    (hc : Nat.card K = Nat.card D) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have := hK
  have hperf : Group.IsPerfect (K.map (MulAut.conj g).toMonoidHom) := Group.IsPerfect.map _
  have hcard : Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card D := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  have h1 := h.eq_of_perfect hK hc hperf hcard
  rw [← h1]
  exact ⟨n, hn, rfl⟩

theorem Quot2Data.mem_ker_of_centralizes (h : Quot2Data φ D) {K : Subgroup C}
    (hK : Group.IsPerfect K) (hc : Nat.card K = Nat.card D)
    (hY : ∀ y ∈ φ.range, (∀ d ∈ D, y * d = d * y) → y = 1) {c : C}
    (hcK : ∀ k ∈ K, c * k = k * c) : c ∈ φ.ker := by
  rw [MonoidHom.mem_ker]
  refine hY _ ⟨c, rfl⟩ fun d hd => ?_
  obtain ⟨k, hk, rfl⟩ := (h.map_eq hK hc ▸ hd : d ∈ K.map φ)
  rw [← map_mul, ← map_mul, hcK k hk]

end Basic

end CFSG.EvenSporadicStandard.Solomon78
