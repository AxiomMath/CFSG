module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type*} [Group G]

theorem padicValNat_card_eq_of_normalizer_le {p : ℕ} [Fact p.Prime] {K L : Subgroup G} [Finite K]
    (hLK : L ≤ K) (T : Sylow p ↥L)
    (hN : ∀ n ∈ K, n ∈ Subgroup.normalizer
      (((T : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) → n ∈ L) :
    padicValNat p (Nat.card ↥K) = padicValNat p (Nat.card ↥(T : Subgroup ↥L)) := by
  classical
  let T' : Subgroup G := (T : Subgroup ↥L).map L.subtype
  have hT'K : T' ≤ K := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact hLK y.2
  let T'' : Subgroup ↥K := T'.subgroupOf K
  have hT''p : IsPGroup p T'' :=
    (T.isPGroup'.map L.subtype).comap_subtype (K := K)
  obtain ⟨S, hT''S⟩ := hT''p.exists_le_sylow
  have hT''eqS : T'' = S := by
    by_contra hne
    have hltS : T'' < (S : Subgroup ↥K) := lt_of_le_of_ne hT''S hne
    let P : Subgroup ↥S := T''.subgroupOf (S : Subgroup ↥K)
    have hPtop : P < ⊤ := by
      rw [lt_top_iff_ne_top]
      change T''.subgroupOf (S : Subgroup ↥K) ≠ ⊤
      intro h
      rw [Subgroup.subgroupOf_eq_top] at h
      exact hne (le_antisymm h hT''S).symm
    haveI : Finite ↥S := inferInstance
    haveI : Group.IsNilpotent ↥S := IsPGroup.isNilpotent S.isPGroup'
    have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
    have hlt : P < Subgroup.normalizer P := hnc P hPtop
    obtain ⟨n, hnN, hnP⟩ := SetLike.not_le_iff_exists.mp hlt.not_ge
    have hnN' : (n : ↥K) ∈ Subgroup.normalizer T'' := by
      have h : n ∈ (Subgroup.normalizer T'').subgroupOf (S : Subgroup ↥K) := by
        rwa [Subgroup.subgroupOf_normalizer_eq hT''S]
      exact Subgroup.mem_subgroupOf.mp h
    have hnN'' : (n : ↥K).1 ∈ Subgroup.normalizer T' := by
      have h : (n : ↥K) ∈ (Subgroup.normalizer T').subgroupOf K := by
        rw [Subgroup.subgroupOf_normalizer_eq hT'K]
        exact hnN'
      exact Subgroup.mem_subgroupOf.mp h
    have hnT'' : (n : ↥K) ∉ T'' := fun h => hnP (Subgroup.mem_subgroupOf.mpr h)
    have hnL : (n : ↥K).1 ∈ L := hN _ (n : ↥K).2 (by simpa only [T'] using hnN'')
    let M : Subgroup ↥K := Subgroup.normalizer T'' ⊓ (S : Subgroup ↥K)
    have hMp : IsPGroup p M := S.isPGroup'.to_le inf_le_right
    have hnM : (n : ↥K) ∈ M := ⟨hnN', n.2⟩
    let A : Subgroup ↥L := (M.map K.subtype).comap L.subtype
    have hAp : IsPGroup p A :=
      (hMp.map K.subtype).comap_of_injective L.subtype L.subtype_injective
    have hTA : (T : Subgroup ↥L) ≤ A := by
      intro t ht
      rw [Subgroup.mem_comap]
      have ht' : (t : G) ∈ T' := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      have htK : (⟨(t : G), hLK t.2⟩ : ↥K) ∈ T'' := by
        rw [Subgroup.mem_subgroupOf]; exact ht'
      have htM : (⟨(t : G), hLK t.2⟩ : ↥K) ∈ M :=
        ⟨Subgroup.le_normalizer htK, hT''S htK⟩
      exact Subgroup.mem_map.mpr ⟨⟨(t : G), hLK t.2⟩, htM, rfl⟩
    have hAnT : (⟨(n : ↥K).1, hnL⟩ : ↥L) ∈ A := by
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_map.mpr ⟨(n : ↥K), hnM, rfl⟩
    have hAnTnot : (⟨(n : ↥K).1, hnL⟩ : ↥L) ∉ (T : Subgroup ↥L) := by
      intro h
      have h1 : (n : ↥K).1 ∈ T' := Subgroup.mem_map.mpr ⟨⟨(n : ↥K).1, hnL⟩, h, rfl⟩
      exact hnT'' (Subgroup.mem_subgroupOf.mpr h1)
    have hAT : A = (T : Subgroup ↥L) := T.is_maximal' hAp hTA
    exact hAnTnot (hAT ▸ hAnT)
  have hT''card : Nat.card ↥T'' = p ^ padicValNat p (Nat.card ↥K) := by
    rw [hT''eqS, Sylow.card_eq_multiplicity S,
      Nat.factorization_def _ (Fact.out : p.Prime)]
  have hcardT : Nat.card ↥(T : Subgroup ↥L) = Nat.card ↥T'' :=
    (Subgroup.card_map_of_injective L.subtype_injective).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'K).toEquiv).symm
  rw [hcardT, hT''card, padicValNat.prime_pow]

theorem exists_conj_mem_of_card_eq {p : ℕ} [Fact p.Prime] {K T₀ : Subgroup G} [Finite K]
    (hTK : T₀ ≤ K) (hcard : Nat.card ↥T₀ = p ^ padicValNat p (Nat.card ↥K)) {t : G} (htK : t ∈ K)
    (ht : orderOf t = p) : ∃ g ∈ K, g⁻¹ * t * g ∈ T₀ := by
  classical
  haveI : Finite ↥K := inferInstance
  let tK : ↥K := ⟨t, htK⟩
  have ht_order : orderOf tK = p := by
    have h1 : orderOf t = orderOf tK := orderOf_injective K.subtype K.subtype_injective tK
    rw [ht] at h1
    exact h1.symm
  have hzp : IsPGroup p ↥(Subgroup.zpowers tK) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ht_order, pow_one]
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  let T : Sylow p ↥K := Sylow.ofCard (T₀.subgroupOf K) (by
    rw [Nat.factorization_def _ (Fact.out : p.Prime)]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hcard])
  haveI : Finite (Sylow p ↥K) := T.finite_of_finiteIndex
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥K Q T
  have htQ : tK ∈ Q := hQ (Subgroup.mem_zpowers tK)
  have hmem : MulAut.conj h • tK ∈ MulAut.conj h • (Q : Subgroup ↥K) :=
    Subgroup.smul_mem_pointwise_smul tK (MulAut.conj h) (Q : Subgroup ↥K) htQ
  rw [← Sylow.coe_subgroup_smul] at hmem
  rw [hh] at hmem
  have hkey : h.1 * t * h.1⁻¹ ∈ T₀ := by
    have hthis : ((MulAut.conj h • tK : ↥K) : G) ∈ T₀ := by
      rw [show (T : Subgroup ↥K) = T₀.subgroupOf K from rfl] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    simpa [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hthis
  refine ⟨h.1⁻¹, K.inv_mem h.2, ?_⟩
  simpa using hkey

theorem exists_commute_of_card_not_dvd {p : ℕ} [Fact p.Prime] {C : Set G} [Finite ↥C] {ρ : G}
    (hρ : orderOf ρ = p) (hcl : ∀ x ∈ C, ρ * x * ρ⁻¹ ∈ C) (hcard : ¬ p ∣ Nat.card ↥C) :
    ∃ x ∈ C, ρ * x = x * ρ := by
  classical
  haveI : Fintype ↥C := Fintype.ofFinite _
  have hcard' : ¬ p ∣ Fintype.card ↥C := by
    rwa [Nat.card_eq_fintype_card] at hcard
  have hρp : ρ ^ p = 1 := by simpa [hρ] using pow_orderOf_eq_one ρ
  let f : ↥C → ↥C := fun x => ⟨ρ * x.1 * ρ⁻¹, hcl x.1 x.2⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h : ρ * (x : G) * ρ⁻¹ = ρ * (y : G) * ρ⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  let σ : Equiv.Perm ↥C := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hσ_apply : ∀ x : ↥C, (σ x : G) = ρ * x.1 * ρ⁻¹ := by
    intro x
    simp only [σ, Equiv.coe_ofBijective, f]
  have hσp : σ ^ p = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [Equiv.Perm.coe_pow]
    change ((f^[p]) x : G) = x.1
    have hiter : ∀ k : ℕ, ((f^[k]) x : G) = ρ ^ k * x.1 * (ρ ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        rw [show (f ((f^[k]) x) : G) = ρ * ((f^[k]) x : G) * ρ⁻¹ from rfl, ih,
          pow_succ, mul_inv_rev]
        group
    rw [hiter p, hρp]
    simp
  obtain ⟨x, hx⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime (p := p) (n := 1) hcard' (σ := σ) (by simpa using hσp)
  refine ⟨x.1, x.2, ?_⟩
  have hfix : (σ x : G) = x.1 := congrArg Subtype.val hx
  rw [hσ_apply x] at hfix
  exact mul_inv_eq_iff_eq_mul.mp hfix

theorem card_sup_zpowers_of_commute {L : Subgroup G} [Finite L] {g : G} (hpos : 0 < orderOf g)
    (hg : ∀ l ∈ L, l * g = g * l) (hdisj : ∀ k : ℕ, ¬ orderOf g ∣ k → g ^ k ∉ L) :
    Nat.card ↥(L ⊔ Subgroup.zpowers g) = Nat.card ↥L * orderOf g := by
  classical
  have hg_comm : ∀ l ∈ L, ∀ h ∈ Subgroup.zpowers g, l * h = h * l := by
    intro l hl h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact Commute.zpow_right (hg l hl) k
  have hcent : L ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hg_comm l hl h hh).symm
  have hnorm : L ≤ Subgroup.normalizer (Subgroup.zpowers g : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  let f : ↥L × ↥(Subgroup.zpowers g) → ↥(L ⊔ Subgroup.zpowers g) :=
    fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : G) ∈ (↑(L ⊔ Subgroup.zpowers g) : Set G) := y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L (Subgroup.zpowers g) hnorm] at hy
    obtain ⟨l, hl, h, hh, hlh⟩ := hy
    exact ⟨⟨⟨l, hl⟩, ⟨h, hh⟩⟩, Subtype.ext hlh⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨l1, hl1⟩, ⟨h1, hh1⟩⟩ ⟨⟨l2, hl2⟩, ⟨h2, hh2⟩⟩ heq
    have heq' : l1 * h1 = l2 * h2 := congrArg Subtype.val heq
    have hz : l2⁻¹ * l1 = h2 * h1⁻¹ := by
      have hcongr := congrArg (fun x => l2⁻¹ * x * h1⁻¹) heq'
      simpa [mul_assoc] using hcongr
    have hzL : l2⁻¹ * l1 ∈ L := L.mul_mem (L.inv_mem hl2) hl1
    have hzP : l2⁻¹ * l1 ∈ Subgroup.zpowers g := by
      rw [hz]
      exact (Subgroup.zpowers g).mul_mem hh2 ((Subgroup.zpowers g).inv_mem hh1)
    have hz1 : l2⁻¹ * l1 = 1 := by
      rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf (orderOf_pos_iff.mp hpos)] at hzP
      simp only [Finset.mem_coe, Finset.mem_image] at hzP
      obtain ⟨k, hkrange, hkg⟩ := hzP
      have hklt : k < orderOf g := Finset.mem_range.mp hkrange
      by_cases hk : orderOf g ∣ k
      · rw [← hkg, Nat.eq_zero_of_dvd_of_lt hk hklt, pow_zero]
      · exact absurd (hkg.symm ▸ hzL) (hdisj k hk)
    have hl12 : l1 = l2 := (eq_of_inv_mul_eq_one hz1).symm
    have hh12 : h1 = h2 := by
      rw [hl12] at heq'
      exact mul_left_cancel heq'
    exact Prod.ext (Subtype.ext hl12) (Subtype.ext hh12)
  have hcard : Nat.card ↥(L ⊔ Subgroup.zpowers g) =
      Nat.card (↥L × ↥(Subgroup.zpowers g)) :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
  rw [hcard, Nat.card_prod, Nat.card_zpowers]

end CFSG.EvenSporadicStandard.HNRecog.Section3
