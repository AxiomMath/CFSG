module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm

open Subgroup CFSG.LocalAnalysis.GLTheoremA.S8

instance oPrimeRes_normal (p : ℕ) (H : Type*) [Group H] : (oPrimeRes p H).Normal := by
  unfold oPrimeRes
  infer_instance

section Lift

variable {Y : Type} [Group Y]

theorem exists_lift_pPower {p : ℕ} (hp : p.Prime) {K : Subgroup Y} [K.Normal]
    (hK : Nat.Coprime p (Nat.card K)) {y : Y} {k : ℕ} (hyk : y ^ (p ^ k) ∈ K) :
    ∃ g : Y, (∃ j : ℕ, g ^ (p ^ j) = 1) ∧ y⁻¹ * g ∈ K := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, ⟨0, by simp⟩, ?_⟩
    simpa using K.inv_mem (by simpa using hyk)
  · have hm1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    have hcop : Nat.Coprime (Nat.card K) (p ^ k) := (hK.symm).pow_right k
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm1
    have hdiv : p ^ k * (Nat.card K * s / p ^ k) + Nat.card K * s % p ^ k = Nat.card K * s :=
      Nat.div_add_mod _ _
    rw [hs] at hdiv
    have hyN : (y ^ (p ^ k)) ^ Nat.card K = 1 := by
      have hz : (⟨y ^ (p ^ k), hyk⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
      have h2 : (((⟨y ^ (p ^ k), hyk⟩ : K) ^ Nat.card K : K) : Y) = 1 := by rw [hz]; rfl
      rw [Subgroup.coe_pow] at h2
      exact h2
    refine ⟨y ^ (Nat.card K * s), ⟨k, ?_⟩, ?_⟩
    · calc (y ^ (Nat.card K * s)) ^ (p ^ k) = ((y ^ (p ^ k)) ^ Nat.card K) ^ s := by
            rw [← pow_mul, ← pow_mul, ← pow_mul]
            ring_nf
        _ = 1 := by rw [hyN, one_pow]
    · rw [← hdiv, pow_succ', ← mul_assoc, inv_mul_cancel, one_mul, pow_mul]
      exact K.pow_mem hyk _

theorem oPrimeRes_map_quotient {p : ℕ} (hp : p.Prime) {K : Subgroup Y} [K.Normal]
    (hK : Nat.Coprime p (Nat.card K)) :
    (oPrimeRes p Y).map (QuotientGroup.mk' K) = oPrimeRes p (Y ⧸ K) := by
  unfold oPrimeRes
  rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective K)]
  congr 1
  apply Set.Subset.antisymm
  · rintro _ ⟨g, ⟨j, hj⟩, rfl⟩
    refine ⟨j, ?_⟩
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_pow, hj, QuotientGroup.mk_one]
  · rintro x ⟨j, hj⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
    have hyk : y ^ (p ^ j) ∈ K := by
      rw [← QuotientGroup.eq_one_iff]
      simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_pow] using hj
    obtain ⟨g, ⟨i, hi⟩, hgy⟩ := exists_lift_pPower hp hK hyk
    refine ⟨g, ⟨i, hi⟩, ?_⟩
    simp only [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq).2 (by simpa using K.inv_mem hgy)

theorem isSimpleGroup_oPrimeRes_quotient {K : Subgroup Y} [K.Normal]
    (hK : Nat.Coprime 5 (Nat.card K)) (hT : IsSimpleGroup ↥(oPrimeRes 5 Y)) :
    IsSimpleGroup ↥(oPrimeRes 5 (Y ⧸ K)) := by
  have hp : Nat.Prime 5 := by norm_num
  have hTK : K.subgroupOf (oPrimeRes 5 Y) = ⊥ := by
    rcases hT.eq_bot_or_eq_top_of_normal (K.subgroupOf (oPrimeRes 5 Y)) with h | h
    · exact h
    · exfalso
      have hne : ∃ g : Y, (∃ j : ℕ, g ^ (5 ^ j) = 1) ∧ g ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hle : oPrimeRes 5 Y ≤ ⊥ := by
          unfold oPrimeRes
          apply normalClosure_le_normal
          intro g hg
          exact (Subgroup.mem_bot).2 (hcon g hg)
        obtain ⟨t, ht⟩ := exists_ne (1 : ↥(oPrimeRes 5 Y))
        exact ht (Subtype.ext ((Subgroup.mem_bot).1 (hle t.2)))
      obtain ⟨g, ⟨j, hj⟩, hg1⟩ := hne
      have hgT : g ∈ oPrimeRes 5 Y := subset_normalClosure ⟨j, hj⟩
      have hgK : g ∈ K := by
        have hmem : (⟨g, hgT⟩ : ↥(oPrimeRes 5 Y)) ∈ K.subgroupOf (oPrimeRes 5 Y) := by
          rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf).1 hmem
      have hord : orderOf g ∣ 5 ^ j := orderOf_dvd_of_pow_eq_one hj
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hord
      have h5 : 5 ∣ orderOf g := by
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · exact absurd (orderOf_eq_one_iff.1 (by simpa using hi)) hg1
        · rw [hi]; exact dvd_pow_self 5 hipos.ne'
      have hdvdK : orderOf g ∣ Nat.card K := by
        have h := orderOf_dvd_natCard (⟨g, hgK⟩ : K)
        rwa [← Subgroup.orderOf_coe] at h
      have h5K : 5 ∣ Nat.card K := h5.trans hdvdK
      have := Nat.Coprime.eq_one_of_dvd hK h5K
      norm_num at this
  have hinj : Function.Injective ((QuotientGroup.mk' K).comp (oPrimeRes 5 Y).subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have htK : (t : Y) ∈ K := by
      rw [MonoidHom.comp_apply] at ht
      simpa using (QuotientGroup.eq_one_iff (N := K) (t : Y)).1 ht
    have hmem : t ∈ K.subgroupOf (oPrimeRes 5 Y) := (Subgroup.mem_subgroupOf).2 htK
    rw [hTK] at hmem
    exact (Subgroup.mem_bot).1 hmem
  let f : oPrimeRes 5 Y →* ↥((oPrimeRes 5 Y).map (QuotientGroup.mk' K)) :=
    ((QuotientGroup.mk' K).comp (oPrimeRes 5 Y).subtype).codRestrict _
      (fun t => ⟨t, t.2, rfl⟩)
  have hfbij : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hinj
      have := congrArg Subtype.val hab
      exact this
    · rintro ⟨y, hy⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨t, ht⟩, rfl⟩
  have hiso : IsSimpleGroup ↥((oPrimeRes 5 Y).map (QuotientGroup.mk' K)) :=
    MulEquiv.isSimpleGroup (MulEquiv.ofBijective f hfbij).symm
  rw [← oPrimeRes_map_quotient hp hK]
  exact hiso

end Lift

theorem isSimpleGroup_oPrimeRes_of_simple {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (h5 : 5 ∣ Nat.card Y) : IsSimpleGroup ↥(oPrimeRes 5 Y) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Y) 5 h5
  have hgT : g ∈ oPrimeRes 5 Y :=
    subset_normalClosure (show ∃ j : ℕ, g ^ (5 ^ j) = 1 from
      ⟨1, by rw [pow_one, ← hg, pow_orderOf_eq_one]⟩)
  have hTtop : oPrimeRes 5 Y = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oPrimeRes 5 Y) with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at hgT
      rw [hgT, orderOf_one] at hg
      norm_num at hg
    · exact h
  exact MulEquiv.isSimpleGroup ((MulEquiv.subgroupCongr hTtop).trans Subgroup.topEquiv)

theorem oPrimeRes_map_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') :
    (oPrimeRes 5 Y).map e.toMonoidHom = oPrimeRes 5 Y' := by
  unfold oPrimeRes
  rw [Subgroup.map_normalClosure _ _ e.surjective]
  congr 1
  apply Set.Subset.antisymm
  · rintro _ ⟨x, ⟨j, hj⟩, rfl⟩
    exact ⟨j, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hj, map_one]⟩
  · rintro y ⟨j, hj⟩
    refine ⟨e.symm y, ⟨j, ?_⟩, by simp⟩
    apply e.injective
    simp [map_pow, hj]

theorem oPrimeRes_perm_prod_eq {X : Type} [Group X] [Finite X] {Ω : Subgroup X} [Ω.Normal]
    (hΩ : IsSimpleGroup ↥Ω) (h5 : 5 ∣ Nat.card Ω)
    (hX : ∀ x : X, (∃ j : ℕ, x ^ (5 ^ j) = 1) → x ∈ Ω) :
    oPrimeRes 5 (Equiv.Perm (Fin 3) × X) = (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod Ω := by
  haveI : (((⊥ : Subgroup (Equiv.Perm (Fin 3)))).prod Ω).Normal := Subgroup.prod_normal _ _
  apply le_antisymm
  · unfold oPrimeRes
    apply normalClosure_le_normal
    rintro g ⟨j, hj⟩
    have hs : g.1 ^ (5 ^ j) = 1 := by simpa using congrArg Prod.fst hj
    have hx : g.2 ^ (5 ^ j) = 1 := by simpa using congrArg Prod.snd hj
    have hs1 : g.1 = 1 := by
      have h1 : orderOf g.1 ∣ 5 ^ j := orderOf_dvd_of_pow_eq_one hs
      have h2 : orderOf g.1 ∣ Nat.card (Equiv.Perm (Fin 3)) := orderOf_dvd_natCard _
      have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
      rw [hcard] at h2
      have hcop : Nat.Coprime (5 ^ j) 6 := Nat.Coprime.pow_left j (by norm_num)
      have h3 : orderOf g.1 ∣ Nat.gcd (5 ^ j) 6 := Nat.dvd_gcd h1 h2
      rw [hcop.gcd_eq_one] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    exact Subgroup.mem_prod.2 ⟨(Subgroup.mem_bot).2 hs1, hX _ ⟨j, hx⟩⟩
  ·
    set N := oPrimeRes 5 (Equiv.Perm (Fin 3) × X) with hN
    have hΩ1 : ∀ x ∈ Ω, ((1 : Equiv.Perm (Fin 3)), x) ∈ N := by
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      let N₀ : Subgroup X := N.comap (MonoidHom.inr (Equiv.Perm (Fin 3)) X)
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ω) 5 h5
      have hx0 : (t : X) ^ 5 = 1 := by
        have := pow_orderOf_eq_one t
        rw [ht] at this
        simpa using congrArg Subtype.val this
      have hx0N₀ : (t : X) ∈ N₀ := by
        apply subset_normalClosure
        refine ⟨1, ?_⟩
        refine Prod.ext ?_ ?_ <;> simp [pow_one, hx0]
      have hK1 := hΩ.eq_bot_or_eq_top_of_normal (N₀.subgroupOf Ω)
      have htop : N₀.subgroupOf Ω = ⊤ := by
        rcases hK1 with h | h
        · exfalso
          have hmem : t ∈ N₀.subgroupOf Ω := (Subgroup.mem_subgroupOf).2 hx0N₀
          rw [h, Subgroup.mem_bot] at hmem
          have : orderOf t = 1 := by rw [hmem, orderOf_one]
          rw [ht] at this
          norm_num at this
        · exact h
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥Ω) ∈ N₀.subgroupOf Ω := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf).1 hmem
    rintro g hg
    obtain ⟨s, x⟩ := g
    obtain ⟨hs, hx⟩ := Subgroup.mem_prod.1 hg
    have hs1 : s = 1 := (Subgroup.mem_bot).1 hs
    subst hs1
    exact hΩ1 x hx

theorem isSimpleGroup_oPrimeRes_perm_prod {X : Type} [Group X] [Finite X] {Ω : Subgroup X}
    [Ω.Normal] (hΩ : IsSimpleGroup ↥Ω) (h5 : 5 ∣ Nat.card Ω)
    (hX : ∀ x : X, (∃ j : ℕ, x ^ (5 ^ j) = 1) → x ∈ Ω) :
    IsSimpleGroup ↥(oPrimeRes 5 (Equiv.Perm (Fin 3) × X)) := by
  rw [oPrimeRes_perm_prod_eq hΩ h5 hX]
  let φ : ↥((⊥ : Subgroup (Equiv.Perm (Fin 3))).prod Ω) →* ↥Ω :=
    { toFun := fun p => ⟨p.1.2, (Subgroup.mem_prod.1 p.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨s, x⟩, hp⟩ ⟨⟨s', x'⟩, hq⟩ h
      have hx : x = x' := congrArg Subtype.val h
      have hs : s = 1 := (Subgroup.mem_bot).1 (Subgroup.mem_prod.1 hp).1
      have hs' : s' = 1 := (Subgroup.mem_bot).1 (Subgroup.mem_prod.1 hq).1
      subst hx; subst hs; subst hs'
      rfl
    · rintro ⟨y, hy⟩
      exact ⟨⟨(1, y), Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hy⟩⟩, rfl⟩
  exact MulEquiv.isSimpleGroup (MulEquiv.ofBijective φ hφ)

end CFSG.LocalAnalysis.GLTheoremA.Timm
