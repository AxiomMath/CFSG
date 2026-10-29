module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34Loc

open CFSG.Open

section Counting

variable {X : Type*} [Group X]

theorem exists_mul_of_card_eq [Finite X] {C A B : Subgroup X} (hA : A ≤ C) (hB : B ≤ C)
    (hAB : A ⊓ B = ⊥) (hcard : Nat.card A * Nat.card B = Nat.card C) :
    ∀ c ∈ C, ∃ a ∈ A, ∃ b ∈ B, a * b = c := by
  intro c hc
  let f : ↥A × ↥B → ↥C := fun p => ⟨(p.1 : X) * (p.2 : X), C.mul_mem (hA p.1.2) (hB p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : X) * (b : X) = (a' : X) * (b' : X) := congrArg Subtype.val h
    have hx : (a' : X)⁻¹ * (a : X) = (b' : X) * (b : X)⁻¹ := by
      calc (a' : X)⁻¹ * (a : X) = (a' : X)⁻¹ * ((a : X) * (b : X)) * (b : X)⁻¹ := by group
        _ = (a' : X)⁻¹ * ((a' : X) * (b' : X)) * (b : X)⁻¹ := by rw [h']
        _ = (b' : X) * (b : X)⁻¹ := by group
    have hmem : (a' : X)⁻¹ * (a : X) ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, by rw [hx]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    have hae : (a : X) = a' := (inv_mul_eq_one.mp hmem).symm
    have hbe : (b : X) = b' := by
      have h2 : (a : X) * (b : X) = (a : X) * (b' : X) := by rw [h', hae]
      exact mul_left_cancel h2
    exact Prod.ext (Subtype.ext hae) (Subtype.ext hbe)
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).2 ⟨hinj, by rw [Nat.card_prod, hcard]⟩
  obtain ⟨p, hp⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, congrArg Subtype.val hp⟩

theorem exists_complement_four [Finite X] {Q E : Subgroup X} (hQe : IsElemAbelian 2 Q)
    (hQc : Nat.card Q = 16) (hEQ : E ≤ Q) (hEc : Nat.card E = 4) :
    ∃ K : Subgroup X, K ≤ Q ∧ Nat.card K = 4 ∧ K ⊓ E = ⊥ := by
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have h := hQe.1.is_comm.comm (⟨a, ha⟩ : ↥Q) ⟨b, hb⟩
    exact congrArg Subtype.val h
  have hsq : ∀ a ∈ Q, a * a = 1 := fun a ha => by
    have := hQe.2 a ha
    rwa [pow_two] at this
  obtain ⟨s, hsQ, hsE⟩ : ∃ s ∈ Q, s ∉ E := by
    by_contra hcon
    push Not at hcon
    have heq : Q = E := Subgroup.eq_of_le_of_card_ge hcon (by rw [hQc, hEc]; norm_num)
    have := congrArg (fun H : Subgroup X => Nat.card H) heq
    rw [hQc, hEc] at this
    norm_num at this
  obtain ⟨t, htQ, htE, htS⟩ : ∃ t ∈ Q, t ∉ E ∧ ∀ e ∈ E, t ≠ s * e := by
    by_contra hcon
    push Not at hcon
    let f : ↥E ⊕ ↥E → ↥Q :=
      Sum.elim (fun e => ⟨(e : X), hEQ e.2⟩) (fun e => ⟨s * e, Q.mul_mem hsQ (hEQ e.2)⟩)
    have hf : Function.Surjective f := by
      rintro ⟨t, ht⟩
      by_cases htE : t ∈ E
      · exact ⟨Sum.inl ⟨t, htE⟩, rfl⟩
      · obtain ⟨e, he, hte⟩ := hcon t ht htE
        exact ⟨Sum.inr ⟨e, he⟩, Subtype.ext hte.symm⟩
    have hle := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_sum, hEc, hQc] at hle
    omega
  have e1 : s * s = 1 := hsq s hsQ
  have e2 : t * t = 1 := hsq t htQ
  have e5 : t * s = s * t := hcomm t htQ s hsQ
  have e4 : s * (s * t) = t := by rw [← mul_assoc, e1, one_mul]
  have e6 : t * (s * t) = s := by rw [← e5, ← mul_assoc, e2, one_mul]
  have e7 : s * t * s = t := by rw [mul_assoc, e5, e4]
  have e8 : s * t * t = s := by rw [mul_assoc, e2, mul_one]
  have e9 : s * t * (s * t) = 1 := by rw [mul_assoc, e6, e1]
  have hs1 : s ≠ 1 := fun h => hsE (h ▸ E.one_mem)
  have ht1 : t ≠ 1 := fun h => htE (h ▸ E.one_mem)
  have hst1 : s * t ≠ 1 := by
    intro h
    have hsEq : s = t := by
      rw [eq_inv_iff_mul_eq_one.mpr h, inv_eq_of_mul_eq_one_right e2]
    exact htS 1 E.one_mem (by rw [mul_one]; exact hsEq.symm)
  have hs_t : s ≠ t := fun h => htS 1 E.one_mem (by rw [mul_one, h])
  have hs_st : s ≠ s * t := fun h => ht1 (mul_left_cancel (a := s) (by rw [mul_one]; exact h)).symm
  have ht_st : t ≠ s * t := fun h => hs1 (mul_right_cancel (a := 1) (b := t) (by rw [one_mul]; exact h)).symm
  let K : Subgroup X :=
    { carrier := {1, s, t, s * t}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [e1, e2, e4, e5, e6, e7, e8, e9, mul_assoc]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · right; left; exact inv_eq_of_mul_eq_one_right e1
        · right; right; left; exact inv_eq_of_mul_eq_one_right e2
        · right; right; right
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right e2, inv_eq_of_mul_eq_one_right e1, e5] }
  have hKset : (K : Set X) = {1, s, t, s * t} := rfl
  have hKc : Nat.card K = 4 := by
    change Nat.card (K : Set X) = 4
    rw [Nat.card_coe_set_eq, hKset]
    have h1 : (1 : X) ∉ ({s, t, s * t} : Set X) := by simp [hs1.symm, ht1.symm, hst1.symm]
    have h2 : s ∉ ({t, s * t} : Set X) := by simp [hs_t, hs_st]
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair ht_st]
  have hKE : K ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxE⟩
    change x ∈ ({1, s, t, s * t} : Set X) at hxK
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxK
    rcases hxK with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exact absurd hxE hsE
    · exact absurd hxE htE
    · exact absurd e4.symm (htS (s * t) hxE)
  have hKQ : K ≤ Q := by
    intro x hx
    change x ∈ ({1, s, t, s * t} : Set X) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Q.one_mem
    · exact hsQ
    · exact htQ
    · exact Q.mul_mem hsQ htQ
  exact ⟨K, hKQ, hKc, hKE⟩

theorem mem_sup_of_le_normalizer {G : Type*} [Group G] {R K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R ⊔ K) :
    ∃ r ∈ R, ∃ k ∈ K, r * k = x := by
  let T : Subgroup G :=
    { carrier := {x | ∃ r ∈ R, ∃ k ∈ K, r * k = x}
      one_mem' := ⟨1, R.one_mem, 1, K.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨r1, hr1, k1, hk1, rfl⟩ ⟨r2, hr2, k2, hk2, rfl⟩
        have hc : k1 * r2 * k1⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hK hk1) r2).mp hr2
        exact ⟨r1 * (k1 * r2 * k1⁻¹), R.mul_mem hr1 hc, k1 * k2, K.mul_mem hk1 hk2, by group⟩
      inv_mem' := by
        rintro _ ⟨r, hr, k, hk, rfl⟩
        have hc : k⁻¹ * r⁻¹ * k⁻¹⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hK (K.inv_mem hk)) r⁻¹).mp (R.inv_mem hr)
        rw [inv_inv] at hc
        exact ⟨k⁻¹ * r⁻¹ * k, hc, k⁻¹, K.inv_mem hk, by group⟩ }
  have hle : R ⊔ K ≤ T :=
    sup_le (fun r hr => ⟨r, hr, 1, K.one_mem, mul_one r⟩) (fun k hk => ⟨1, R.one_mem, k, hk, one_mul k⟩)
  exact hle hx

theorem sup_uniq {H : Type*} [Group H] {V A : Subgroup H} (huniq : A ⊓ V = ⊥) (v v' : ↥V) (a a' : ↥A)
    (h : (v : H) * (a : H) = (v' : H) * (a' : H)) : v = v' ∧ a = a' := by
  have hx : (v' : H)⁻¹ * (v : H) = (a' : H) * (a : H)⁻¹ := by
    calc (v' : H)⁻¹ * (v : H) = (v' : H)⁻¹ * ((v : H) * (a : H)) * (a : H)⁻¹ := by group
      _ = (v' : H)⁻¹ * ((v' : H) * (a' : H)) * (a : H)⁻¹ := by rw [h]
      _ = (a' : H) * (a : H)⁻¹ := by group
  have hmem : (v' : H)⁻¹ * (v : H) ∈ A ⊓ V := by
    refine ⟨?_, V.mul_mem (V.inv_mem v'.2) v.2⟩
    rw [hx]
    exact A.mul_mem a'.2 (A.inv_mem a.2)
  rw [huniq, Subgroup.mem_bot] at hmem
  have hv : v = v' := Subtype.ext (inv_mul_eq_one.mp hmem).symm
  subst hv
  refine ⟨rfl, Subtype.ext ?_⟩
  exact mul_left_cancel h

theorem semidirect_mulEquiv {G Y : Type*} [Group G] [Group Y] {L : Subgroup G} {L' : Subgroup Y}
    {V A : Subgroup G} {V' A' : Subgroup Y}
    (hVL : V ≤ L) (hAL : A ≤ L) (hV'L : V' ≤ L') (hA'L : A' ≤ L')
    (hVn : ∀ h ∈ L, ∀ v ∈ V, h * v * h⁻¹ ∈ V) (hdec : ∀ x ∈ L, ∃ v ∈ V, ∃ a ∈ A, v * a = x)
    (huniq : A ⊓ V = ⊥) (hdec' : ∀ y ∈ L', ∃ v ∈ V', ∃ a ∈ A', v * a = y) (huniq' : A' ⊓ V' = ⊥)
    (β : ↥V ≃* ↥V') (α : ↥A ≃* ↥A')
    (hequiv : ∀ (a : ↥A) (v w : ↥V), (w : G) = (a : G) * (v : G) * (a : G)⁻¹ →
        (β w : Y) = (α a : Y) * (β v : Y) * (α a : Y)⁻¹) :
    ∃ ψ : ↥L ≃* ↥L', (∀ x : ↥L, ∀ hx : (x : G) ∈ V, (ψ x : Y) = (β ⟨x, hx⟩ : Y)) ∧
      (∀ x : ↥L, ∀ hx : (x : G) ∈ A, (ψ x : Y) = (α ⟨x, hx⟩ : Y)) := by
  have hdec2 : ∀ x : ↥L, ∃ v : ↥V, ∃ a : ↥A, (v : G) * (a : G) = (x : G) := by
    intro x
    obtain ⟨v, hv, a, ha, h⟩ := hdec x x.2
    exact ⟨⟨v, hv⟩, ⟨a, ha⟩, h⟩
  choose vS aS hprod using hdec2
  have hmul : ∀ x y : ↥L,
      ((β (vS (x * y)) : ↥V') : Y) * ((α (aS (x * y)) : ↥A') : Y) =
        ((β (vS x) : ↥V') : Y) * ((α (aS x) : ↥A') : Y) *
          (((β (vS y) : ↥V') : Y) * ((α (aS y) : ↥A') : Y)) := by
    intro x y
    have hu : (aS x : G) * (vS y : G) * (aS x : G)⁻¹ ∈ V := hVn _ (hAL (aS x).2) _ (vS y).2
    let u : ↥V := ⟨(aS x : G) * (vS y : G) * (aS x : G)⁻¹, hu⟩
    let w : ↥V := vS x * u
    let a' : ↥A := aS x * aS y
    have hwa : (w : G) * (a' : G) = ((x * y : ↥L) : G) := by
      show ((vS x : G) * ((aS x : G) * (vS y : G) * (aS x : G)⁻¹)) * ((aS x : G) * (aS y : G)) =
        ((x * y : ↥L) : G)
      rw [Subgroup.coe_mul]
      calc ((vS x : G) * ((aS x : G) * (vS y : G) * (aS x : G)⁻¹)) * ((aS x : G) * (aS y : G))
          = ((vS x : G) * (aS x : G)) * ((vS y : G) * (aS y : G)) := by group
        _ = (x : G) * (y : G) := by rw [hprod x, hprod y]
    obtain ⟨hvw, haa⟩ := sup_uniq huniq (vS (x * y)) w (aS (x * y)) a' ((hprod (x * y)).trans hwa.symm)
    have e1 : (β w : Y) = (β (vS x) : Y) * ((α (aS x) : Y) * (β (vS y) : Y) * (α (aS x) : Y)⁻¹) := by
      rw [show w = vS x * u from rfl, map_mul, Subgroup.coe_mul, hequiv (aS x) (vS y) u rfl]
    have e2 : (α a' : Y) = (α (aS x) : Y) * (α (aS y) : Y) := by
      rw [show a' = aS x * aS y from rfl, map_mul, Subgroup.coe_mul]
    rw [hvw, haa, e1, e2]
    group
  let ψf : ↥L → ↥L' := fun x => ⟨(β (vS x) : Y) * (α (aS x) : Y),
    L'.mul_mem (hV'L (β (vS x)).2) (hA'L (α (aS x)).2)⟩
  have hψmul : ∀ x y : ↥L, ψf (x * y) = ψf x * ψf y := by
    intro x y
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hmul x y
  let ψh : ↥L →* ↥L' :=
    { toFun := ψf
      map_one' := by
        obtain ⟨h1, h2⟩ := sup_uniq huniq (vS 1) 1 (aS 1) 1 (by rw [hprod 1]; simp)
        apply Subtype.ext
        simp [ψf, h1, h2]
      map_mul' := fun x y => hψmul x y }
  have hinj : Function.Injective ψh := by
    intro x y hxy
    have h : (β (vS x) : Y) * (α (aS x) : Y) = (β (vS y) : Y) * (α (aS y) : Y) :=
      congrArg Subtype.val hxy
    obtain ⟨h1, h2⟩ := sup_uniq huniq' (β (vS x)) (β (vS y)) (α (aS x)) (α (aS y)) h
    have hv : vS x = vS y := β.injective h1
    have ha : aS x = aS y := α.injective h2
    apply Subtype.ext
    rw [← hprod x, ← hprod y, hv, ha]
  have hsurj : Function.Surjective ψh := by
    intro y
    obtain ⟨v', hv', a', ha', hy⟩ := hdec' y.1 y.2
    obtain ⟨v, hv⟩ : ∃ v : ↥V, β v = ⟨v', hv'⟩ := ⟨β.symm ⟨v', hv'⟩, β.apply_symm_apply _⟩
    obtain ⟨a, ha⟩ : ∃ a : ↥A, α a = ⟨a', ha'⟩ := ⟨α.symm ⟨a', ha'⟩, α.apply_symm_apply _⟩
    let x : ↥L := ⟨(v : G) * (a : G), L.mul_mem (hVL v.2) (hAL a.2)⟩
    refine ⟨x, ?_⟩
    obtain ⟨hvS, haS⟩ := sup_uniq huniq (vS x) v (aS x) a (hprod x)
    apply Subtype.ext
    show (β (vS x) : Y) * (α (aS x) : Y) = (y : Y)
    rw [hvS, haS, hv, ha]
    exact hy
  refine ⟨MulEquiv.ofBijective ψh ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨hv1, ha1⟩ := sup_uniq huniq (vS x) ⟨x, hx⟩ (aS x) 1 (by rw [hprod x]; simp)
    show (β (vS x) : Y) * (α (aS x) : Y) = (β ⟨x, hx⟩ : Y)
    rw [hv1, ha1, map_one, Subgroup.coe_one, mul_one]
  · intro x hx
    obtain ⟨hv1, ha1⟩ := sup_uniq huniq 1 (vS x) ⟨x, hx⟩ (aS x) (by rw [hprod x]; simp)
    show (β (vS x) : Y) * (α (aS x) : Y) = (α ⟨x, hx⟩ : Y)
    rw [← hv1, ← ha1, map_one, Subgroup.coe_one, one_mul]

end Counting

section Order3

variable {X : Type*} [Group X]

theorem card_modEq_one_of_fixedPointFree [Finite X] {E : Subgroup X} (hE : IsElemAbelian 2 E)
    {x : X} (hx3 : x ^ 3 = 1) (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E)
    (hff : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1) : Nat.card E ≡ 1 [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥E → ↥E := fun e => ⟨x * e * x⁻¹, hxE e e.2⟩
  have hfinj : Function.Injective f := by
    intro e e' h
    have h' : x * (e : X) * x⁻¹ = x * (e' : X) * x⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  let σ : Equiv.Perm ↥E := Equiv.ofBijective f ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  have hσf : ∀ e : ↥E, σ e = f e := fun e => rfl
  have hσ3 : σ ^ 3 = 1 := by
    ext e
    have hcalc : x * (x * (x * (e : X) * x⁻¹) * x⁻¹) * x⁻¹ = (e : X) := by
      have k1 : x * (x * (x * (e : X) * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * (e : X) * (x ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_rev, inv_mul_cancel_left]
      rw [k1, hx3, inv_one, mul_one, one_mul]
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hσf]
    exact hcalc
  have hord : orderOf σ ∣ 3 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hσ3
  have hpG : IsPGroup 3 (Subgroup.zpowers σ) := by
    rw [IsPGroup.iff_card]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
    exact ⟨i, by rw [Nat.card_zpowers, hi]⟩
  have hfix : MulAction.fixedPoints (Subgroup.zpowers σ) ↥E = {1} := by
    ext e
    rw [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro h
      have hσe : σ e = e := by
        have := h ⟨σ, Subgroup.mem_zpowers σ⟩
        simpa using this
      have h2 : f e = e := by rw [← hσf]; exact hσe
      have hfe : x * (e : X) * x⁻¹ = e := congrArg Subtype.val h2
      exact Subtype.ext (hff e e.2 hfe)
    · rintro rfl m
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (Equiv.Perm ↥E) (1 : ↥E) := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, hσf]
        exact Subtype.ext (by simp [f])
      have hm := hst m.2
      rw [MulAction.mem_stabilizer_iff] at hm
      exact hm
  have hcard := hpG.card_modEq_card_fixedPoints ↥E
  rw [hfix] at hcard
  simpa using hcard

end Order3

end CFSG.GH74.QTGen4.DSGen4.L34Loc
