module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

@[expose] noncomputable def primeResidual (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sSup {P : Subgroup G | IsPGroup p P}

theorem pSubgroup_le_residual {G : Type*} [Group G] (p : ℕ)
    (P : Subgroup G) (hP : IsPGroup p P) : P ≤ primeResidual p G := le_sSup hP

theorem primeResidual_eq_closure {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    primeResidual p G = Subgroup.closure {x : G | ∃ k : ℕ, orderOf x = p ^ k} := by
  apply le_antisymm
  · apply sSup_le
    intro P hP x hx
    apply Subgroup.subset_closure
    obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨x, hx⟩ : P)
    exact ⟨k, (Subgroup.orderOf_coe (⟨x, hx⟩ : P)).trans hk⟩
  · apply (Subgroup.closure_le (primeResidual p G)).mpr
    rintro x ⟨k, hk⟩
    have hP : IsPGroup p (Subgroup.zpowers x) := by
      apply IsPGroup.iff_card.mpr
      exact ⟨k, (Nat.card_zpowers x).trans hk⟩
    exact pSubgroup_le_residual p _ hP (Subgroup.mem_zpowers x)

theorem primeResidual_map_le {G H : Type*} [Group G] [Group H]
    (p : ℕ) (f : G →* H) : (primeResidual p G).map f ≤ primeResidual p H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro P hP
  exact Subgroup.map_le_iff_le_comap.mp
    (pSubgroup_le_residual p (P.map f) (hP.map f))

theorem primeResidual_map_equiv {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) : (primeResidual p G).map e.toMonoidHom = primeResidual p H := by
  apply le_antisymm (primeResidual_map_le p e.toMonoidHom)
  intro x hx
  have hinverse := primeResidual_map_le p e.symm.toMonoidHom
    (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx)
  exact ⟨e.symm x, hinverse, e.apply_symm_apply x⟩

theorem primeResidual_characteristic (p : ℕ) (G : Type*) [Group G] :
    (primeResidual p G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro e
  exact primeResidual_map_equiv p e

theorem primeResidual_coprime_index (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] : p.Coprime (primeResidual p G).index := by
  let P : Sylow p G := Classical.choice inferInstance
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index |>.of_dvd_right
    (Subgroup.index_dvd_of_le (pSubgroup_le_residual p (P : Subgroup G) P.isPGroup'))

theorem primeResidual_le_normal_of_coprime_index {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) [N.Normal] (hindex : p.Coprime N.index) :
    primeResidual p G ≤ N := by
  apply sSup_le
  intro P hP
  let q := QuotientGroup.mk' N
  obtain ⟨k, hk⟩ := (hP.map q).exists_card_eq
  have hcard : Nat.card (P.map q) = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (hindex.pow_left k)
    · rw [hk]
    · exact Subgroup.card_subgroup_dvd_card _
  have hkernel := (P.map_eq_bot_iff).mp (Subgroup.card_eq_one.mp hcard)
  simpa only [q, QuotientGroup.ker_mk'] using hkernel

theorem primeResidual_le_subnormal_of_coprime_index {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) (hN : N.IsSubnormal)
    (hindex : p.Coprime N.index) : primeResidual p G ≤ N := by
  induction hN with
  | top => exact le_top
  | step lower upper hle hsubnormal hnormal hinduction =>
      have hupper := hinduction (hindex.of_dvd_right (Subgroup.index_dvd_of_le hle))
      have hlowerIndex : p.Coprime (lower.subgroupOf upper).index := by
        have hmul := Subgroup.index_map_subtype (lower.subgroupOf upper)
        rw [Subgroup.map_subgroupOf_eq_of_le hle] at hmul
        exact hindex.of_dvd_right ⟨upper.index, hmul⟩
      let : (lower.subgroupOf upper).Normal := hnormal
      have hlocal := primeResidual_le_normal_of_coprime_index p
        (lower.subgroupOf upper) hlowerIndex
      apply sSup_le
      intro P hP
      have hPU : P ≤ upper := (pSubgroup_le_residual p P hP).trans hupper
      have hlocalP : IsPGroup p (P.subgroupOf upper) :=
        hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPU).symm
      have hcontains := (pSubgroup_le_residual p _ hlocalP).trans hlocal
      intro x hx
      exact hcontains (show (⟨x, hPU hx⟩ : upper) ∈ P.subgroupOf upper from hx)

theorem primeResidual_map_surjective {G H : Type*} [Group G] [Finite G] [Group H]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f) :
    (primeResidual p G).map f = primeResidual p H := by
  apply le_antisymm (primeResidual_map_le p f)
  apply sSup_le
  intro P hP
  let V := P.comap f
  let restriction : V →* P := (f.domRestrict V).codRestrict P fun x => x.property
  have hrestriction : Function.Surjective restriction := by
    intro x
    obtain ⟨y, hy⟩ := hf x.val
    have hyV : y ∈ V := by
      change f y ∈ P
      rw [hy]
      exact x.property
    exact ⟨⟨y, hyV⟩, Subtype.ext hy⟩
  let S : Sylow p V := Classical.choice inferInstance
  have htopP : IsPGroup p (⊤ : Subgroup P) := hP.to_subgroup ⊤
  have himage : (S : Subgroup V).map restriction = ⊤ := by
    have hle := htopP.le_sylow_of_normal (S.mapSurjective hrestriction)
    rw [Sylow.coe_mapSurjective] at hle
    exact top_unique hle
  have hambient := pSubgroup_le_residual p ((S : Subgroup V).map V.subtype)
    (S.isPGroup'.map V.subtype)
  intro x hx
  have htarget : (⟨x, hx⟩ : P) ∈ (S : Subgroup V).map restriction := by
    rw [himage]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hvalue⟩ := Subgroup.mem_map.mp htarget
  exact ⟨y.val, hambient ⟨y, hy, rfl⟩, congrArg Subtype.val hvalue⟩

theorem primeResidual_idempotent (p : ℕ) (G : Type*) [Group G] :
    (primeResidual p (primeResidual p G)).map (primeResidual p G).subtype =
      primeResidual p G := by
  apply le_antisymm (Subgroup.map_subtype_le _)
  apply sSup_le
  intro P hP
  have hle := pSubgroup_le_residual p P hP
  have hlocal : IsPGroup p (P.subgroupOf (primeResidual p G)) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hlocalLe := pSubgroup_le_residual p _ hlocal
  intro x hx
  exact ⟨⟨x, hle hx⟩, hlocalLe hx, rfl⟩

theorem coprime_index_of_surjective_restriction {G H : Type*}
    [Group G] [Finite G] [Group H] (p : ℕ)
    (f : G →* H) (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    (J : Subgroup G) (hJ : Function.Surjective (f.domRestrict J)) : p.Coprime J.index := by
  let : Finite H := Finite.of_surjective f hf
  let restriction := f.domRestrict J
  have hambient : Nat.card G = Nat.card H * Nat.card f.ker := by
    have h := f.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.liftEquiv f.ker hf rfl).toEquiv] at h
    exact h
  have hsubgroup : Nat.card J = Nat.card H * Nat.card restriction.ker := by
    have h := restriction.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.liftEquiv restriction.ker hJ rfl).toEquiv] at h
    exact h
  have hmul : Nat.card H * (Nat.card restriction.ker * J.index) =
      Nat.card H * Nat.card f.ker := by
    rw [← mul_assoc, ← hsubgroup, J.card_mul_index, hambient]
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H)) hmul
  exact hker.of_dvd_right ⟨Nat.card restriction.ker, by
    simpa only [mul_comm] using hcancel.symm⟩

theorem primeResidual_eq_of_subnormal_covering {G H : Type*}
    [Group G] [Finite G] [Group H] (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    (J : Subgroup G) (hJ : J.IsSubnormal) (hgenerated : primeResidual p J = ⊤)
    (hcover : Function.Surjective (f.domRestrict J)) : J = primeResidual p G := by
  apply le_antisymm
  · have hmap := primeResidual_map_le p J.subtype
    rw [hgenerated] at hmap
    intro x hx
    exact hmap ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  · exact primeResidual_le_subnormal_of_coprime_index p J hJ
      (coprime_index_of_surjective_restriction p f hf hker J hcover)

theorem primeResidual_normalizer_le {G : Type*} [Group G] (p : ℕ) (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer ((primeResidual p V).map V.subtype : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hactor
  let e : V ≃* V := ((MulAut.conj actor).subgroupMap V).trans (MulEquiv.subgroupCongr hmap)
  have hresidual : e y ∈ primeResidual p V := by
    rw [← primeResidual_map_equiv p e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  exact Subgroup.mem_map.mpr ⟨e y, hresidual, rfl⟩

end CFSG.ComponentClassification.CatalogueBPrimeJoin
