module

public import CFSG.GH74.GLS.Balance.Bender.Ambient
public import CFSG.GH74.GLS.Balance.Bender.Aux1
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.GH74.GLS.Balance.BenderExt

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance
open scoped commutatorElement

section Basic

variable {p : ℕ}

theorem exists_pow_coprime {Y : Type*} [Group Y] [Finite Y] (hp : p.Prime) (x : Y) :
    ∃ e : ℕ, Nat.Coprime (orderOf (x ^ (p ^ e))) p := by
  have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨(orderOf x).factorization p, ?_⟩
  rw [orderOf_pow' x (pow_ne_zero _ hp.ne_zero)]
  have hd : p ^ (orderOf x).factorization p ∣ orderOf x := Nat.ordProj_dvd _ p
  rw [Nat.gcd_eq_right hd]
  exact (Nat.coprime_ordCompl hp hn0).symm

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_mem_oResOf (hp : p.Prime) {X : Subgroup G} {x : G} (hx : x ∈ X) :
    ∃ e : ℕ, x ^ (p ^ e) ∈ oResOf p X := by
  obtain ⟨e, he⟩ := exists_pow_coprime hp x
  exact ⟨e, mem_oResOf (X.pow_mem hx _) he⟩

omit [Finite G] in
theorem conj_mem_oResOf {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) {x : G}
    (hx : x ∈ oResOf p X) : g * x * g⁻¹ ∈ oResOf p X := by
  rw [oResOf_eq_closure] at hx ⊢
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure
    {x : G | x ∈ X ∧ Nat.Coprime (orderOf x) p}) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨hyX, hy⟩
    apply Subgroup.subset_closure
    refine ⟨(mem_normalizer_iff.mp hg y).mp hyX, ?_⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    have e : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := rfl
    rw [e] at this
    rw [this]; exact hy
  · simp
  · intro a b _ _ ha hb
    have := Subgroup.mul_mem _ ha hb
    simpa [mul_assoc] using this
  · intro a _ ha
    have h1 := Subgroup.inv_mem _ ha
    rwa [show (g * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ by group] at h1

omit [Finite G] in
theorem oResOf_oResOf (X : Subgroup G) : oResOf p (oResOf p X) = oResOf p X := by
  apply le_antisymm (oResOf_le p _)
  rw [oResOf_eq_closure p X]
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact mem_oResOf (Subgroup.subset_closure hx) hx.2

omit [Finite G] in
theorem oResidual_eq_top_iff (X : Subgroup G) : oResidual p ↥X = ⊤ ↔ oResOf p X = X := by
  constructor
  · intro h
    unfold oResOf
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · intro h
    apply Subgroup.map_injective X.subtype_injective
    have h1 : (oResidual p ↥X).map X.subtype = oResOf p X := rfl
    rw [h1, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]


omit [Finite G] in
theorem pow_mul_mem_of_normal {Y : Type*} [Group Y] {A : Subgroup Y} [A.Normal] {a : Y} (c : Y) (ha : a ∈ A)
    (n : ℕ) : ∃ a' ∈ A, (a * c) ^ n = a' * c ^ n := by
  induction n with
  | zero => exact ⟨1, A.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨a', ha', h⟩ := ih
    refine ⟨a' * (c ^ n * a * (c ^ n)⁻¹), A.mul_mem ha' (Normal.conj_mem ‹A.Normal› a ha (c ^ n)), ?_⟩
    rw [pow_succ, h]
    group

theorem map_oResOf {G' : Type} [Group G'] (hp : p.Prime) (f : G →* G') (X : Subgroup G) :
    (oResOf p X).map f = oResOf p (X.map f) := by
  have h1 := map_oResidual hp (f.subgroupMap X) (f.subgroupMap_surjective X)
  unfold oResOf
  rw [Subgroup.map_map]
  have hcomp : f.comp X.subtype = (X.map f).subtype.comp (f.subgroupMap X) := rfl
  rw [hcomp, ← Subgroup.map_map, h1]

theorem isSylowIn_map_surjective [Fact p.Prime] {G' : Type} [Group G'] (f : G →* G')
    (hf : Function.Surjective f) {P N : Subgroup G} (h : IsSylowIn p P N) :
    IsSylowIn p (P.map f) (N.map f) := by
  have : Finite G' := Finite.of_surjective f hf
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowIn p h
  have hg : Function.Surjective (f.subgroupMap N) := f.subgroupMap_surjective N
  have h1 := isSylowIn_of_sylow p (S.mapSurjective hg)
  have h2 : ((S.mapSurjective hg : Sylow p ↥(N.map f)) : Subgroup ↥(N.map f)).map (N.map f).subtype =
      ((S : Subgroup ↥N).map N.subtype).map f := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h2] at h1
  exact h1

theorem sup_oResOf_eq_top (hp : p.Prime) {Y : Type} [Group Y] [Finite Y] (hY : oResidual p Y = ⊤)
    {A C : Subgroup Y} [A.Normal] (h : A ⊔ C = ⊤) : A ⊔ oResOf p C = ⊤ := by
  rw [eq_top_iff, ← hY]
  apply oResidual_le_of_pow_mem
  intro y
  have hy : y ∈ A ⊔ C := by rw [h]; exact mem_top y
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  obtain ⟨e, he⟩ := exists_pow_mem_oResOf hp hc
  refine ⟨e, ?_⟩
  obtain ⟨a', ha', h'⟩ := pow_mul_mem_of_normal c ha (p ^ e)
  rw [h']
  exact Subgroup.mul_mem_sup ha' he

theorem oResOf_centralizer_map_le (hp : p.Prime) {Z : Type} [Group Z] (π : G →* Z)
    (hπ : Function.Surjective π) (hN : IsPGroup p ↥π.ker) (hNc : π.ker ≤ center G) (T : Subgroup G) :
    oResOf p (centralizer ((T.map π : Subgroup Z) : Set Z)) ≤ (centralizer (T : Set G)).map π := by
  refine oResOf_le_of fun z hz hzc => ?_
  obtain ⟨y₀, hy₀⟩ := hπ z
  obtain ⟨y, hy, hycop⟩ := exists_coprime_lift hp π hzc hy₀
  refine ⟨y, ?_, hy⟩
  show y ∈ centralizer (T : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hπy' : π (t * y * t⁻¹) = π y := by
    have := Subgroup.mem_centralizer_iff.mp hz (π t) (Subgroup.mem_map_of_mem π ht)
    rw [map_mul, map_mul, map_inv, hy, this, mul_inv_cancel_right]
  have hn : y⁻¹ * (t * y * t⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπy']; group
  set n := y⁻¹ * (t * y * t⁻¹) with hndef
  obtain ⟨k, hk⟩ := hN ⟨n, hn⟩
  have hnk : n ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hnord : orderOf n ∣ p ^ k := orderOf_dvd_of_pow_eq_one hnk
  have hcomm : Commute y n := (Subgroup.mem_center_iff.mp (hNc hn)) y
  have hcop : Nat.Coprime (orderOf y) (orderOf n) :=
    Nat.Coprime.coprime_dvd_right hnord (Nat.Coprime.pow_right k hycop)
  have hy'eq : t * y * t⁻¹ = y * n := by rw [hndef]; group
  have hord1 : orderOf (y * n) = orderOf y * orderOf n := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hord2 : orderOf (t * y * t⁻¹) = orderOf y := by
    have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective y
    exact this
  rw [hy'eq] at hord2
  have hpos : 0 < orderOf y := orderOf_pos y
  have hn1 : orderOf n = 1 := by
    rw [hord1] at hord2
    have : orderOf y * orderOf n = orderOf y * 1 := by rw [mul_one]; exact hord2
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hn1' : n = 1 := orderOf_eq_one_iff.mp hn1
  rw [hn1', mul_one] at hy'eq
  calc t * y = (t * y * t⁻¹) * t := by group
    _ = y * t := by rw [hy'eq]

end Basic


section SylowConj

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem sup_centralizer_eq_top_of_sylow {M Q : Subgroup G} [M.Normal] (hQ : IsSylowIn p Q M)
    (h : M ⊔ centralizer (Q : Set G) = ⊤) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup p ↥T) :
    M ⊔ centralizer (T : Set G) = ⊤ := by
  have hT' : IsPGroup p (T.subgroupOf M) := hT.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨S, hS⟩ := hT'.exists_le_sylow
  have hTP' : T ≤ (S : Subgroup ↥M).map M.subtype := fun t ht => ⟨⟨t, hTM ht⟩, hS ht, rfl⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_of_isSylowIn p hQ
  have hQo : CFSG.ABGLocalTools.IsSylowOf p Q M := ⟨S₀, hS₀⟩
  have hP'o : CFSG.ABGLocalTools.IsSylowOf p ((S : Subgroup ↥M).map M.subtype) M := ⟨S, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQo.exists_mem_conj hP'o
  rw [eq_top_iff]
  intro x _
  have hx : k⁻¹ * x * k ∈ M ⊔ centralizer (Q : Set G) := by rw [h]; exact mem_top _
  obtain ⟨u, hu, c, hc, huc⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have hxe : x = (k * u * k⁻¹) * (k * c * k⁻¹) := by
    have : k⁻¹ * x * k = u * c := huc.symm
    calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      _ = k * (u * c) * k⁻¹ := by rw [this]
      _ = (k * u * k⁻¹) * (k * c * k⁻¹) := by group
  rw [hxe]
  refine Subgroup.mul_mem_sup (Normal.conj_mem ‹M.Normal› u hu k) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htQ : k⁻¹ * t * k ∈ Q := (hconj t).mp (hTP' ht)
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ htQ
  calc t * (k * c * k⁻¹) = k * ((k⁻¹ * t * k) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * t * k)) * k⁻¹ := by rw [h1]
    _ = (k * c * k⁻¹) * t := by group


end SylowConj

section Burnside

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem coprime_card_oResOf_of_central_sylow {N P : Subgroup G} (hP : IsSylowIn p P N)
    (hc : N ≤ centralizer (P : Set G)) : Nat.Coprime p (Nat.card ↥(oResOf p N)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn p hP
  have hnorm : normalizer (S : Set ↥N) ≤ centralizer (S : Set ↥N) := by
    intro x _
    rw [mem_centralizer_iff]
    intro s hs
    have hsP : (s : G) ∈ P := by rw [← hS]; exact ⟨s, hs, rfl⟩
    exact Subtype.ext ((mem_centralizer_iff.mp (hc x.2)) (s : G) hsP)
  obtain ⟨K, hKn, hKp, hKindex, -⟩ := CFSG.GroupTheory.burnside_normal_complement S hnorm
  have hq : IsPGroup p (↥N ⧸ K) := by
    obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := m) ?_
    rw [← Subgroup.index_eq_card, hKindex]
    exact hm
  have hres : oResidual p ↥N ≤ K := by
    apply oResidual_le_of_pow_mem
    intro y
    obtain ⟨k, hk⟩ := hq (y : ↥N ⧸ K)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow] at hk
    exact (QuotientGroup.eq_one_iff _).mp hk
  have hdvd : Nat.card ↥(oResOf p N) ∣ Nat.card K := by
    have h1 : Nat.card ↥(oResOf p N) = Nat.card ↥(oResidual p ↥N) :=
      Subgroup.card_map_of_injective N.subtype_injective
    rw [h1]; exact Subgroup.card_dvd_of_le hres
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hKp (h.trans hdvd))


end Burnside

section MinNormal

variable {p : ℕ} [Fact p.Prime]

theorem minimal_normal_trichotomy {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN1 : N ≠ ⊥) (hmin : ∀ M : Subgroup Y, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    (IsPGroup p ↥N ∧ N ≤ centralizer (N : Set Y)) ∨ ¬ p ∣ Nat.card ↥N ∨
      (Subgroup.center ↥N = ⊥ ∧ p ∣ Nat.card ↥N ∧ ⁅N, N⁆ = N) := by
  have hp : p.Prime := Fact.out
  have hcn : (⁅N, N⁆).Normal := inferInstance
  have hcle : ⁅N, N⁆ ≤ N := Subgroup.commutator_le_left (H₁ := N) (H₂ := N)
  rcases hmin ⁅N, N⁆ hcn hcle with h | h
  ·
    have hcomm : N ≤ centralizer (N : Set Y) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := N) (H₂ := N)).mp h
    have : IsMulCommutative N := (Subgroup.le_centralizer_iff_isMulCommutative (K := N)).mp hcomm
    have : Group.IsSolvable ↥N := inferInstance
    have : CFSG.IsMinimalNormal N := ⟨fun M _ hMK => hmin M inferInstance hMK⟩
    obtain ⟨q, hq, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
    have hpow : ∀ y : N, y ^ q = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p
    have hNq : IsPGroup q ↥N := fun g => ⟨1, by rw [pow_one]; exact hpow g⟩
    by_cases hqp : q = p
    · subst hqp
      exact Or.inl ⟨hNq, hcomm⟩
    · right; left
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hNq
      intro hdvd
      rw [hn] at hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)
      exact hqp this.symm
  ·
    have hZ : Subgroup.center ↥N = ⊥ := by
      have hZc : (Subgroup.center ↥N).Characteristic := inferInstance
      have hZn : ((Subgroup.center ↥N).map N.subtype).Normal := inferInstance
      rcases hmin _ hZn (Subgroup.map_subtype_le _) with hz | hz
      · exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hz
      · exfalso
        have hcent : N ≤ centralizer (N : Set Y) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hxc : (⟨x, hx⟩ : ↥N) ∈ Subgroup.center ↥N := by
            have : x ∈ (Subgroup.center ↥N).map N.subtype := by rw [hz]; exact hx
            obtain ⟨z, hz', hzx⟩ := this
            have : z = ⟨x, hx⟩ := Subtype.ext hzx
            rwa [← this]
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩)
        have hbot : ⁅N, N⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := N) (H₂ := N)).mpr hcent
        exact hN1 (by rw [← h]; exact hbot)
    by_cases hpN : p ∣ Nat.card ↥N
    · exact Or.inr (Or.inr ⟨hZ, hpN, h⟩)
    · exact Or.inr (Or.inl hpN)


end MinNormal

end CFSG.GH74.GLS.Balance.BenderExt
