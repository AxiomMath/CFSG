module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.LieType.CentralExt

variable {E G : Type*} [Group E] [Group G]

open _root_.Classical in
noncomputable def pLift (p : ℕ) (π : E →* G) (u : G) : E :=
  if h : ∃ e : E, π e = u ∧ ∃ n : ℕ, orderOf e = p ^ n then h.choose else 1

@[expose] def liftSubgroup (p : ℕ) (π : E →* G) (U : Subgroup G) : Subgroup E :=
  Subgroup.closure {e : E | π e ∈ U ∧ ∃ n : ℕ, orderOf e = p ^ n}

variable {p : ℕ} [hp : Fact p.Prime] {π : E →* G}

theorem exists_orderOf_eq_pow_of_pow_eq_one {x : E} {n : ℕ} (h : x ^ p ^ n = 1) :
    ∃ m : ℕ, orderOf x = p ^ m := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨m, hm⟩

theorem exists_orderOf_eq_pow_of_mem {H : Type*} [Group H] {U : Subgroup H} (hU : IsPGroup p U)
    (u : U) : ∃ n : ℕ, orderOf (u : H) = p ^ n := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hU) u
  exact ⟨n, by rw [Subgroup.orderOf_coe, hn]⟩

theorem exists_orderOf_map_eq_pow {H K : Type*} [Group H] [Group K] (f : H →* K) {x : H}
    (hx : ∃ n : ℕ, orderOf x = p ^ n) : ∃ n : ℕ, orderOf (f x) = p ^ n := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).1 (hn ▸ orderOf_map_dvd f x)
  exact ⟨m, hm⟩

theorem coprime_of_not_dvd (hC : ¬p ∣ Nat.card π.ker) (n : ℕ) :
    Nat.Coprime (p ^ n) (Nat.card π.ker) :=
  Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hC)

theorem eq_one_of_mem_ker (hC : ¬p ∣ Nat.card π.ker) {c : E} (hc : c ∈ π.ker) {n : ℕ}
    (hn : c ^ p ^ n = 1) : c = 1 := by
  have hN : c ^ Nat.card π.ker = 1 := by
    have h := pow_card_eq_one' (G := π.ker) (x := ⟨c, hc⟩)
    exact congrArg Subtype.val h
  have h1 : c ^ (p ^ n).gcd (Nat.card π.ker) = 1 := pow_gcd_eq_one.2 ⟨hn, hN⟩
  rwa [coprime_of_not_dvd hC n, pow_one] at h1

theorem exists_pElement_lift (hC : ¬p ∣ Nat.card π.ker) (e : E) {n : ℕ}
    (hn : orderOf (π e) = p ^ n) : ∃ x : E, π x = π e ∧ ∃ m : ℕ, orderOf x = p ^ m := by
  have hcop : (Nat.card π.ker).Coprime (orderOf (π e)) := hn ▸ (coprime_of_not_dvd hC n).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hker : e ^ p ^ n ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hn, pow_orderOf_eq_one]
  have hN : (e ^ p ^ n) ^ Nat.card π.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := π.ker) (x := ⟨_, hker⟩))
  refine ⟨(e ^ Nat.card π.ker) ^ m, by rw [map_pow, map_pow, hm], ?_⟩
  apply exists_orderOf_eq_pow_of_pow_eq_one (n := n)
  have h : ((e ^ Nat.card π.ker) ^ m) ^ p ^ n = ((e ^ p ^ n) ^ Nat.card π.ker) ^ m := by
    simp only [← pow_mul]
    congr 1
    ring
  rw [h, hN, one_pow]

theorem eq_of_pElement (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {x y : E}
    (hxy : π x = π y) (hx : ∃ n : ℕ, orderOf x = p ^ n) (hy : ∃ n : ℕ, orderOf y = p ^ n) :
    x = y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hc : y⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hcomm : Commute y (y⁻¹ * x) :=
    (Subgroup.mem_center_iff.1 (hcen hc) y)
  have hxa : x ^ p ^ (a + b) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (ha ▸ pow_dvd_pow p (Nat.le_add_right a b))
  have hyb : y ^ p ^ (a + b) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hb ▸ pow_dvd_pow p (Nat.le_add_left b a))
  have hpow : (y⁻¹ * x) ^ p ^ (a + b) = 1 := by
    have h := hcomm.mul_pow (p ^ (a + b))
    rw [mul_inv_cancel_left, hxa, hyb, one_mul] at h
    exact h.symm
  have h1 := eq_one_of_mem_ker hC hc hpow
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem exists_pLift_aux (hπ : Function.Surjective π) (hC : ¬p ∣ Nat.card π.ker) {u : G}
    (hu : ∃ n : ℕ, orderOf u = p ^ n) : ∃ e : E, π e = u ∧ ∃ n : ℕ, orderOf e = p ^ n := by
  obtain ⟨n, hn⟩ := hu
  obtain ⟨e, rfl⟩ := hπ u
  obtain ⟨x, hx, hxp⟩ := exists_pElement_lift hC e hn
  exact ⟨x, hx, hxp⟩

omit hp in
theorem pLift_spec_of_exists {u : G} (h : ∃ e : E, π e = u ∧ ∃ n : ℕ, orderOf e = p ^ n) :
    π (pLift p π u) = u ∧ ∃ n : ℕ, orderOf (pLift p π u) = p ^ n := by
  classical
  rw [pLift, dite_eq_left h]
  exact h.choose_spec

theorem pLift_spec (hπ : Function.Surjective π) (hC : ¬p ∣ Nat.card π.ker) {u : G}
    (hu : ∃ n : ℕ, orderOf u = p ^ n) :
    π (pLift p π u) = u ∧ ∃ n : ℕ, orderOf (pLift p π u) = p ^ n :=
  pLift_spec_of_exists (exists_pLift_aux hπ hC hu)

theorem map_pLift (hπ : Function.Surjective π) (hC : ¬p ∣ Nat.card π.ker) {u : G}
    (hu : ∃ n : ℕ, orderOf u = p ^ n) : π (pLift p π u) = u :=
  (pLift_spec hπ hC hu).1

theorem orderOf_pLift (hπ : Function.Surjective π) (hC : ¬p ∣ Nat.card π.ker) {u : G}
    (hu : ∃ n : ℕ, orderOf u = p ^ n) : ∃ n : ℕ, orderOf (pLift p π u) = p ^ n :=
  (pLift_spec hπ hC hu).2

theorem pLift_unique (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {u : G}
    {e : E} (he : π e = u) (hpe : ∃ n : ℕ, orderOf e = p ^ n) : pLift p π u = e := by
  have h := pLift_spec_of_exists ⟨e, he, hpe⟩
  exact eq_of_pElement hcen hC (h.1.trans he.symm) h.2 hpe

theorem pLift_apply (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {e : E}
    (hpe : ∃ n : ℕ, orderOf e = p ^ n) : pLift p π (π e) = e :=
  pLift_unique hcen hC rfl hpe

theorem pLift_one (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) :
    pLift p π (1 : G) = 1 :=
  pLift_unique hcen hC (map_one π) ⟨0, by simp⟩

theorem conj_pLift (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) (e : E) {u : G} (hu : ∃ n : ℕ, orderOf u = p ^ n) :
    e * pLift p π u * e⁻¹ = pLift p π (π e * u * (π e)⁻¹) := by
  obtain ⟨h1, n, hn⟩ := pLift_spec hπ hC hu
  symm
  apply pLift_unique hcen hC
  · rw [map_mul, map_mul, map_inv, h1]
  · refine ⟨n, ?_⟩
    rw [← hn]
    exact (SemiconjBy.orderOf_eq e (by simp [SemiconjBy, mul_assoc])).symm

theorem pLift_inv (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {u : G} (hu : ∃ n : ℕ, orderOf u = p ^ n) :
    pLift p π u⁻¹ = (pLift p π u)⁻¹ := by
  obtain ⟨h1, n, hn⟩ := pLift_spec hπ hC hu
  exact pLift_unique hcen hC (by rw [map_inv, h1]) ⟨n, by rw [orderOf_inv, hn]⟩

theorem pLift_pow (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {u : G} (hu : ∃ n : ℕ, orderOf u = p ^ n) (k : ℕ) :
    pLift p π (u ^ k) = pLift p π u ^ k := by
  obtain ⟨h1, n, hn⟩ := pLift_spec hπ hC hu
  apply pLift_unique hcen hC (by rw [map_pow, h1])
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).1 (hn ▸ orderOf_pow_dvd (x := pLift p π u) k)
  exact ⟨m, hm⟩

section Subgroup

variable [Finite E]

omit [Finite E] in
theorem ker_subgroupComap_le_center (hcen : π.ker ≤ Subgroup.center E) (U : Subgroup G) :
    (π.subgroupComap U).ker ≤ Subgroup.center (U.comap π) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hx' : (x : E) ∈ π.ker := by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen hx') y)

theorem mem_sylow_of_pElement (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G}
    (hU : IsPGroup p U) (P : Sylow p (U.comap π)) (x : U.comap π)
    (hx : ∃ n : ℕ, orderOf (x : E) = p ^ n) : x ∈ P := by
  let f := (π.subgroupComap U).rangeRestrict
  have : Finite (π.subgroupComap U).range :=
    Finite.of_surjective f (π.subgroupComap U).rangeRestrict_surjective
  have : Group.IsNilpotent (π.subgroupComap U).range :=
    (hU.to_subgroup (π.subgroupComap U).range).isNilpotent
  have : Group.IsNilpotent (U.comap π) :=
    Subgroup.isNilpotent_of_ker_le_center f
      ((MonoidHom.ker_rangeRestrict _).le.trans (ker_subgroupComap_le_center hcen U))
  obtain ⟨n, hn⟩ := hx
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := n)
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hn
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  have hPQ : Q = P := by
    have := Sylow.unique_of_normal P inferInstance
    exact Subsingleton.elim _ _
  exact hPQ ▸ hQ (Subgroup.mem_zpowers x)

theorem mem_liftSubgroup_iff (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G}
    (hU : IsPGroup p U) {e : E} :
    e ∈ liftSubgroup p π U ↔ π e ∈ U ∧ ∃ n : ℕ, orderOf e = p ^ n := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p (U.comap π)))
  have hle : liftSubgroup p π U ≤ (P : Subgroup (U.comap π)).map (U.comap π).subtype := by
    rw [liftSubgroup, Subgroup.closure_le]
    exact fun e he => ⟨⟨e, he.1⟩, mem_sylow_of_pElement hcen hU P ⟨e, he.1⟩ he.2, rfl⟩
  refine ⟨fun he => ?_, fun he => Subgroup.subset_closure he⟩
  obtain ⟨x, hx, rfl⟩ := hle he
  obtain ⟨n, hn⟩ := exists_orderOf_eq_pow_of_mem P.isPGroup' ⟨x, hx⟩
  exact ⟨x.2, n, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hn⟩

theorem liftSubgroup_le_comap (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G}
    (hU : IsPGroup p U) : liftSubgroup p π U ≤ U.comap π :=
  fun _ he => ((mem_liftSubgroup_iff hcen hU).1 he).1

theorem liftSubgroup_isPGroup (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G}
    (hU : IsPGroup p U) : IsPGroup p (liftSubgroup p π U) := by
  rw [IsPGroup.iff_orderOf]
  intro x
  obtain ⟨n, hn⟩ := ((mem_liftSubgroup_iff hcen hU).1 x.2).2
  exact ⟨n, by rw [← Subgroup.orderOf_coe, hn]⟩

theorem sylow_map_eq_liftSubgroup (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G}
    (hU : IsPGroup p U) (P : Sylow p (U.comap π)) :
    (P : Subgroup (U.comap π)).map (U.comap π).subtype = liftSubgroup p π U := by
  ext e
  rw [mem_liftSubgroup_iff hcen hU]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := exists_orderOf_eq_pow_of_mem P.isPGroup' ⟨x, hx⟩
    exact ⟨x.2, n, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hn⟩
  · rintro ⟨he, hpe⟩
    exact ⟨⟨e, he⟩, mem_sylow_of_pElement hcen hU P ⟨e, he⟩ hpe, rfl⟩

theorem map_liftSubgroup (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G} (hU : IsPGroup p U) :
    (liftSubgroup p π U).map π = U := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p (U.comap π)))
  have hP := sylow_map_eq_liftSubgroup hcen hU P
  have hq : Function.Surjective (π.subgroupComap U) :=
    MonoidHom.subgroupComap_surjective π U hπ
  let P' : Sylow p U := P.mapSurjective hq
  have hP' : (P' : Subgroup U) = ⊤ :=
    (Sylow.is_maximal' P' (hU.to_subgroup ⊤) le_top).symm
  have hcomp : π.comp (U.comap π).subtype = U.subtype.comp (π.subgroupComap U) := by
    ext x
    rfl
  calc
    (liftSubgroup p π U).map π
        = ((P : Subgroup (U.comap π)).map (U.comap π).subtype).map π := by rw [← hP]
    _ = (P : Subgroup (U.comap π)).map (π.comp (U.comap π).subtype) := by
          rw [Subgroup.map_map]
    _ = (P : Subgroup (U.comap π)).map (U.subtype.comp (π.subgroupComap U)) := by rw [hcomp]
    _ = ((P : Subgroup (U.comap π)).map (π.subgroupComap U)).map U.subtype := by
          rw [Subgroup.map_map]
    _ = (P' : Subgroup U).map U.subtype := by
          rw [Sylow.coe_mapSurjective]
    _ = (⊤ : Subgroup U).map U.subtype := by rw [hP']
    _ = U := by
          rw [← Subgroup.subgroupOf_self U]
          exact Subgroup.map_subgroupOf_eq_of_le le_rfl

theorem liftSubgroup_ne_bot (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G} (hU : IsPGroup p U)
    (hUbot : U ≠ ⊥) : liftSubgroup p π U ≠ ⊥ := by
  intro hbot
  apply hUbot
  rw [← map_liftSubgroup hπ hcen hU, hbot, Subgroup.map_bot]

theorem map_liftSubgroup_mulAut (hcen : π.ker ≤ Subgroup.center E)
    (a : MulAut E) (b : MulAut G) (hcomm : ∀ x : E, π (a x) = b (π x))
    {U : Subgroup G} (hU : IsPGroup p U) (hbU : U.map b.toMonoidHom = U) :
    (liftSubgroup p π U).map a.toMonoidHom = liftSubgroup p π U := by
  have hcomm_inv : ∀ x : E, π (a.symm x) = b.symm (π x) := by
    intro x
    apply b.injective
    rw [b.apply_symm_apply, ← hcomm, a.apply_symm_apply]
  have hbU_inv : ∀ u : G, u ∈ U → b.symm u ∈ U := by
    intro u hu
    have hu' : u ∈ U.map b.toMonoidHom := by rwa [hbU]
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu'
    have hbvu : b.symm u = v := by
      rw [← hvu]
      simp
    rwa [hbvu]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxU, n, hn⟩ := (mem_liftSubgroup_iff hcen hU).1 hx
    refine (mem_liftSubgroup_iff hcen hU).2 ⟨?_, n, ?_⟩
    · have h := hcomm x
      change π (a.toMonoidHom x) = b.toMonoidHom (π x) at h
      rw [h]
      exact hbU ▸ ⟨π x, hxU, rfl⟩
    · change orderOf (a x) = p ^ n
      rw [MulEquiv.orderOf_eq a x, hn]
  · intro hy
    obtain ⟨hyU, n, hn⟩ := (mem_liftSubgroup_iff hcen hU).1 hy
    refine ⟨a.symm y, ?_, a.apply_symm_apply y⟩
    refine (mem_liftSubgroup_iff hcen hU).2 ⟨?_, n, ?_⟩
    · rw [hcomm_inv]
      exact hbU_inv (π y) hyU
    · rw [MulEquiv.orderOf_eq a.symm y, hn]

theorem pLift_mem_liftSubgroup (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G} (hU : IsPGroup p U) {u : G} (hu : u ∈ U) :
    pLift p π u ∈ liftSubgroup p π U := by
  obtain ⟨h1, h2⟩ := pLift_spec hπ hC (exists_orderOf_eq_pow_of_mem hU ⟨u, hu⟩)
  exact (mem_liftSubgroup_iff hcen hU).2 ⟨by rw [h1]; exact hu, h2⟩

theorem pLift_mul (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G} (hU : IsPGroup p U) {u v : G} (hu : u ∈ U)
    (hv : v ∈ U) : pLift p π (u * v) = pLift p π u * pLift p π v := by
  have hmem := (liftSubgroup p π U).mul_mem (pLift_mem_liftSubgroup hπ hcen hC hU hu)
    (pLift_mem_liftSubgroup hπ hcen hC hU hv)
  apply pLift_unique hcen hC _ ((mem_liftSubgroup_iff hcen hU).1 hmem).2
  rw [map_mul, map_pLift hπ hC (exists_orderOf_eq_pow_of_mem hU ⟨u, hu⟩),
    map_pLift hπ hC (exists_orderOf_eq_pow_of_mem hU ⟨v, hv⟩)]

@[expose] noncomputable def pLiftHom (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G} (hU : IsPGroup p U) : U →* E where
  toFun u := pLift p π u
  map_one' := pLift_one hcen hC
  map_mul' u v := pLift_mul hπ hcen hC hU u.2 v.2

theorem pLiftHom_apply (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G} (hU : IsPGroup p U) (u : U) :
    pLiftHom hπ hcen hC hU u = pLift p π u :=
  rfl

theorem map_pLiftHom (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G} (hU : IsPGroup p U) (u : U) :
    π (pLiftHom hπ hcen hC hU u) = u :=
  map_pLift hπ hC (exists_orderOf_eq_pow_of_mem hU u)

theorem range_pLiftHom (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G} (hU : IsPGroup p U) :
    (pLiftHom hπ hcen hC hU).range = liftSubgroup p π U := by
  ext e
  constructor
  · rintro ⟨u, rfl⟩
    exact pLift_mem_liftSubgroup hπ hcen hC hU u.2
  · intro he
    obtain ⟨he1, he2⟩ := (mem_liftSubgroup_iff hcen hU).1 he
    exact ⟨⟨π e, he1⟩, pLift_apply hcen hC he2⟩

@[expose] noncomputable def liftSubgroupEquiv (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G}
    (hU : IsPGroup p U) : liftSubgroup p π U ≃* U where
  toFun x := ⟨π x, liftSubgroup_le_comap hcen hU x.2⟩
  invFun u := ⟨pLift p π u, pLift_mem_liftSubgroup hπ hcen hC hU u.2⟩
  left_inv x := Subtype.ext (pLift_apply hcen hC ((mem_liftSubgroup_iff hcen hU).1 x.2).2)
  right_inv u := Subtype.ext (map_pLift hπ hC (exists_orderOf_eq_pow_of_mem hU u))
  map_mul' x y := Subtype.ext (map_mul π (x : E) (y : E))

theorem liftSubgroupEquiv_apply (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G}
    (hU : IsPGroup p U) (x : liftSubgroup p π U) :
    (liftSubgroupEquiv hπ hcen hC hU x : G) = π (x : E) :=
  rfl

theorem liftSubgroupEquiv_symm_apply (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G}
    (hU : IsPGroup p U) (u : U) :
    ((liftSubgroupEquiv hπ hcen hC hU).symm u : E) = pLift p π u :=
  rfl

@[expose] noncomputable def kerProdLiftSubgroupHom (hcen : π.ker ≤ Subgroup.center E)
    {U : Subgroup G} (hU : IsPGroup p U) : π.ker × liftSubgroup p π U →* U.comap π :=
  MonoidHom.noncommCoprod (Subgroup.inclusion (fun c hc => by
      rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hc]; exact U.one_mem))
    (Subgroup.inclusion (liftSubgroup_le_comap hcen hU))
    (fun c x => Subtype.ext (Subgroup.mem_center_iff.1 (hcen c.2) x).symm)

theorem kerProdLiftSubgroupHom_apply (hcen : π.ker ≤ Subgroup.center E) {U : Subgroup G}
    (hU : IsPGroup p U) (x : π.ker × liftSubgroup p π U) :
    (kerProdLiftSubgroupHom hcen hU x : E) = x.1 * x.2 :=
  rfl

theorem kerProdLiftSubgroupHom_bijective (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G}
    (hU : IsPGroup p U) : Function.Bijective (kerProdLiftSubgroupHom hcen hU) := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨c, x⟩ h
    have h' : (c : E) * x = 1 := congrArg Subtype.val h
    have hx : (x : E) ∈ π.ker := by
      rw [eq_inv_of_mul_eq_one_right h']
      exact π.ker.inv_mem c.2
    obtain ⟨n, hn⟩ := ((mem_liftSubgroup_iff hcen hU).1 x.2).2
    have hx1 : (x : E) = 1 :=
      eq_one_of_mem_ker hC hx (n := n) (by rw [← hn, pow_orderOf_eq_one])
    have hc1 : (c : E) = 1 := by rw [hx1, mul_one] at h'; exact h'
    exact Prod.ext (Subtype.ext hc1) (Subtype.ext hx1)
  · rintro ⟨f, hf⟩
    have hpf : ∃ n : ℕ, orderOf (π f) = p ^ n := exists_orderOf_eq_pow_of_mem hU ⟨π f, hf⟩
    have hx := pLift_mem_liftSubgroup hπ hcen hC hU (Subgroup.mem_comap.1 hf)
    have hc : f * (pLift p π (π f))⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pLift hπ hC hpf, mul_inv_cancel]
    exact ⟨⟨⟨_, hc⟩, ⟨_, hx⟩⟩, Subtype.ext (inv_mul_cancel_right f _)⟩

@[expose] noncomputable def kerProdLiftSubgroupEquiv (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G}
    (hU : IsPGroup p U) : π.ker × liftSubgroup p π U ≃* U.comap π :=
  MulEquiv.ofBijective (kerProdLiftSubgroupHom hcen hU)
    (kerProdLiftSubgroupHom_bijective hπ hcen hC hU)

theorem kerProdLiftSubgroupEquiv_apply (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) {U : Subgroup G}
    (hU : IsPGroup p U) (x : π.ker × liftSubgroup p π U) :
    (kerProdLiftSubgroupEquiv hπ hcen hC hU x : E) = x.1 * x.2 :=
  rfl

theorem central_coprime_canonical_pLifts (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker) :
    (∀ (U : Subgroup G) (hU : IsPGroup p U),
      (∀ P : Sylow p (U.comap π),
        (P : Subgroup (U.comap π)).map (U.comap π).subtype = liftSubgroup p π U) ∧
      Function.Bijective (kerProdLiftSubgroupHom hcen hU) ∧
      Function.Bijective
        (fun x : liftSubgroup p π U => (⟨π x, liftSubgroup_le_comap hcen hU x.2⟩ : U))) ∧
    (∀ u : G, (∃ n : ℕ, orderOf u = p ^ n) →
      (π (pLift p π u) = u ∧ ∃ n : ℕ, orderOf (pLift p π u) = p ^ n) ∧
      ∀ e : E, π e = u → (∃ n : ℕ, orderOf e = p ^ n) → e = pLift p π u) ∧
    (∀ U : Subgroup G, IsPGroup p U → ∀ u ∈ U, ∀ v ∈ U,
      pLift p π (u * v) = pLift p π u * pLift p π v) ∧
    (∀ (e : E) (u : G), (∃ n : ℕ, orderOf u = p ^ n) →
      e * pLift p π u * e⁻¹ = pLift p π (π e * u * (π e)⁻¹)) :=
  ⟨fun _ hU => ⟨sylow_map_eq_liftSubgroup hcen hU, kerProdLiftSubgroupHom_bijective hπ hcen hC hU,
      (liftSubgroupEquiv hπ hcen hC hU).bijective⟩,
    fun _ hu => ⟨pLift_spec hπ hC hu, fun _ he hpe => (pLift_unique hcen hC he hpe).symm⟩,
    fun _ hU _ hu _ hv => pLift_mul hπ hcen hC hU hu hv,
    fun e _ hu => conj_pLift hπ hcen hC e hu⟩

end Subgroup

end CFSG.LieType.CentralExt
