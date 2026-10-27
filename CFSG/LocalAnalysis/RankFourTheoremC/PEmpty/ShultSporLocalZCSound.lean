module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCCheck
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimpleSound
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

section Eval

variable {A : Type} [Group A]

theorem zcPow_eq (cn : A → A) (hcn : ∀ x, cn x = x) (x : A) (e : ℕ) : zcPow cn x e = x ^ e := by
  induction e with
  | zero => simp [zcPow]
  | succ e ih => rw [zcPow, hcn, ih, pow_succ]

theorem zcEval_eq (cn : A → A) (hcn : ∀ x, cn x = x) (a b : A) (w : PW) :
    zcEval cn a b w = evalPW a b w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨c, e⟩ := x
    simp only [zcEval, evalPW, hcn, ih, zcPow_eq cn hcn]

theorem zc_mem_iterate_conj (cn : A → A) (hcn : ∀ x, cn x = x) (z u : A) (p : ℕ) (x : A) :
    x ∈ List.iterate (fun y => cn (z * y * z⁻¹)) u p ↔ ∃ i < p, x = z ^ i * u * (z ^ i)⁻¹ := by
  have key : ∀ i : ℕ, (fun y => cn (z * y * z⁻¹))^[i] u = z ^ i * u * (z ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      show cn (z * (z ^ i * u * (z ^ i)⁻¹) * z⁻¹) = _
      rw [hcn]
      simp only [pow_succ', mul_inv_rev, mul_assoc]
  simp only [List.mem_iterate, key]

end Eval

section Bfs

variable {A : Type} [DecidableEq A]

theorem mem_zcNew {acc l : List A} {y : A} (h : y ∈ zcNew acc l) : y ∈ l := by
  simp only [zcNew, List.mem_dedup, List.mem_filter] at h
  exact h.1

theorem zcBfsAux_prop {P : A → Prop} (step : A → List A) (cap : ℕ)
    (hstep : ∀ x, P x → ∀ y ∈ step x, P y) :
    ∀ (fuel : ℕ) (acc fr : List A), (∀ x ∈ acc, P x) → (∀ x ∈ fr, P x) →
      ∀ x ∈ zcBfsAux step cap fuel acc fr, P x := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc fr hacc _ x hx
    exact hacc x (by simpa [zcBfsAux] using hx)
  | succ fuel ih =>
    intro acc fr hacc hfr
    cases fr with
    | nil =>
      intro x hx
      exact hacc x (by simpa [zcBfsAux] using hx)
    | cons f fs =>
      rw [zcBfsAux]
      split_ifs with hc
      · exact hacc
      · have hnew : ∀ y ∈ zcNew acc ((f :: fs).flatMap step), P y := by
          intro y hy
          obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.mp (mem_zcNew hy)
          exact hstep x (hfr x hx) y hyx
        refine ih _ _ ?_ hnew
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hacc x hx
        · exact hnew x hx

theorem zcBfs_prop {P : A → Prop} (step : A → List A) (hstep : ∀ x, P x → ∀ y ∈ step x, P y)
    (cap fuel : ℕ) (seeds : List A) (hseeds : ∀ x ∈ seeds, P x) :
    ∀ x ∈ zcBfs step cap fuel seeds, P x := by
  have hs : ∀ y ∈ seeds.dedup, P y := fun y hy => hseeds y (List.mem_dedup.mp hy)
  simpa only [zcBfs] using zcBfsAux_prop step cap hstep fuel _ _ hs hs

theorem mem_of_zcMemK {key : A → ℕ} {O : List A} {y : A}
    (h : zcMemK key (O.map (fun x => (key x, x))) y = true) : y ∈ O := by
  simp only [zcMemK, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨q, hq, -, hqy⟩ := h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  have hxy : x = y := hqy
  exact hxy ▸ hx

end Bfs

section Sylow

variable {A : Type} [Group A]

theorem zc_mul_inv_mem_of_finite [Finite A] {E : Set A} {g : A} (h : ∀ x ∈ E, x * g ∈ E) :
    ∀ x ∈ E, x * g⁻¹ ∈ E := by
  have hm : Set.MapsTo (fun x => x * g) E E := fun x hx => h x hx
  have hb := ((Set.toFinite E).injOn_iff_bijOn_of_mapsTo hm).mp
    (fun x _ y _ hxy => mul_right_cancel hxy)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hb.surjOn hx
  simpa using hy

theorem zc_mem_list_of_mem_closure [Finite A] (gens E : List A) (h1 : (1 : A) ∈ E)
    (hmul : ∀ x ∈ E, ∀ s ∈ gens, x * s ∈ E) {g : A} (hg : g ∈ closure {s | s ∈ gens}) :
    g ∈ E := by
  have key : ∀ g ∈ closure {s | s ∈ gens}, ∀ x ∈ E, x * g ∈ E := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact fun x hx => hmul x hx s hs
    | one => exact fun x hx => by simpa using hx
    | mul g h _ _ hg hh => exact fun x hx => by simpa [mul_assoc] using hh _ (hg x hx)
    | inv g _ hg => exact zc_mul_inv_mem_of_finite (E := {x | x ∈ E}) hg
  simpa using key g hg 1 h1

theorem zc_card_closure_of_list [Finite A] (gens E : List A) (hnd : E.Nodup) (h1 : (1 : A) ∈ E)
    (hmul : ∀ x ∈ E, ∀ s ∈ gens, x * s ∈ E) (hsub : ∀ x ∈ E, x ∈ closure {s | s ∈ gens}) :
    Nat.card (closure {s | s ∈ gens}) = E.length := by
  classical
  have hiff : ∀ x, x ∈ closure {s | s ∈ gens} ↔ x ∈ E := fun x =>
    ⟨zc_mem_list_of_mem_closure gens E h1 hmul, hsub x⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (List.mem_toFinset (a := x) (l := E)).symm)),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]

theorem zc_isPGroup_zpowers {G : Type*} [Group G] {t : G} {n : ℕ} (ht : t ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers t) := by
  rintro ⟨s, hs⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]

theorem zc_exists_conj_mem_of_card {M : Type*} [Group M] [Finite M] (S : Subgroup M) (k : ℕ)
    (hS : Nat.card S = 2 ^ k) (hk : ¬ 2 ^ (k + 1) ∣ Nat.card M) {u : M} (hu : u * u = 1) :
    ∃ g : M, g * u * g⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ k ∣ Nat.card M := by
    rw [← hS]
    exact Subgroup.card_subgroup_dvd_card S
  have hne : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card M).factorization 2 = k := by
    have h1 : k ≤ (Nat.card M).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
    have h2 : ¬ (k + 1 ≤ (Nat.card M).factorization 2) := fun h =>
      hk ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mpr h)
    omega
  let P : Sylow 2 M := Sylow.ofCard S (by rw [hS, hfac])
  have hP : (P : Subgroup M) = S := rfl
  have hut : u ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hu
  obtain ⟨R, hR⟩ := (zc_isPGroup_zpowers hut).exists_le_sylow
  haveI : Finite (Sylow 2 M) :=
    Finite.of_injective (fun Q : Sylow 2 M => (Q : Set M)) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M R P
  refine ⟨g, ?_⟩
  rw [← hP, ← hg]
  exact ⟨u, hR (Subgroup.mem_zpowers u), by simp [MulAut.conj_apply]⟩

theorem zc_conj_mem_of_closure {O : List A} {a b : A}
    (h : ∀ x ∈ O, ∀ g ∈ [a, b, a⁻¹, b⁻¹], g * x * g⁻¹ ∈ O) :
    ∀ g ∈ closure ({a, b} : Set A), ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
  have key : ∀ g ∈ closure ({a, b} : Set A),
      (∀ x ∈ O, g * x * g⁻¹ ∈ O) ∧ (∀ x ∈ O, g⁻¹ * x * g ∈ O) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      have hg' : g ∈ [a, b, a⁻¹, b⁻¹] ∧ g⁻¹ ∈ [a, b, a⁻¹, b⁻¹] := by
        rcases hg with hg | hg
        · rw [hg]
          simp
        · rw [Set.mem_singleton_iff.mp hg]
          simp
      exact ⟨fun x hx => h x hx g hg'.1, fun x hx => by simpa using h x hx g⁻¹ hg'.2⟩
    | one => exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    | mul g k _ _ hg hk =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simpa [mul_assoc] using hg.1 _ (hk.1 x hx)
      · simpa [mul_assoc] using hk.2 _ (hg.2 x hx)
    | inv g _ hg =>
      exact ⟨fun x hx => by simpa using hg.2 x hx, fun x hx => by simpa using hg.1 x hx⟩
  exact fun g hg => (key g hg).1

end Sylow

section Closure

variable {A : Type} [Group A]

theorem zc_mem_normalizer_of_conj_mem [Finite A] (K : Subgroup A) {h : A}
    (hK : ∀ v ∈ K, h * v * h⁻¹ ∈ K) : h ∈ normalizer (K : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hK x, fun hx => ?_⟩
  have hm : Set.MapsTo (fun v => h * v * h⁻¹) (K : Set A) (K : Set A) := fun v hv => hK v hv
  have hb := ((Set.toFinite (K : Set A)).injOn_iff_bijOn_of_mapsTo hm).mp (by
    intro v _ w _ hvw
    simpa using hvw)
  obtain ⟨y, hy, hyx⟩ := hb.surjOn hx
  have : y = x := by simpa using hyx
  rw [← this]
  exact hy

theorem zcRStep_mem_closure (cn : A → A) (hcn : ∀ x, cn x = x) {gens : List A} {x y : A}
    (hx : x ∈ closure {s | s ∈ gens}) (hy : y ∈ zcRStep cn gens x) :
    y ∈ closure {s | s ∈ gens} := by
  simp only [zcRStep, List.mem_map] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  rw [hcn]
  exact mul_mem hx (subset_closure hs)

theorem zc_mem_closure_iff_of_closed (cs L : List A) (h1 : (1 : A) ∈ L) (hc : ∀ c ∈ cs, c ∈ L)
    (hm : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) (hi : ∀ x ∈ L, x⁻¹ ∈ L)
    (hsub : ∀ x ∈ L, x ∈ closure {c | c ∈ cs}) (x : A) :
    x ∈ closure {c | c ∈ cs} ↔ x ∈ L := by
  refine ⟨fun hx => ?_, hsub x⟩
  let LS : Subgroup A :=
    { carrier := {x | x ∈ L}
      mul_mem' := fun ha hb => hm _ ha _ hb
      one_mem' := h1
      inv_mem' := fun ha => hi _ ha }
  exact (Subgroup.closure_le LS).mpr (fun c hc' => hc c hc') hx

theorem zc_exists_pow_lt_of_mem_zpowers {G : Type*} [Group G] [Finite G] {z g : G} {p : ℕ}
    (hz : orderOf z = p) (hg : g ∈ zpowers z) : ∃ i < p, g = z ^ i := by
  classical
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  have h := hfin.mem_zpowers_iff_mem_range_orderOf.mp hg
  simp only [Finset.mem_image, Finset.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hz ▸ hi, rfl⟩

theorem zc_orderOf_mk_eq_prime {M : Subgroup A} {z : A} (hzM : z ∈ M) {p : ℕ} (hp : p.Prime)
    (hz : z ^ p = 1) (hz1 : z ≠ 1) : orderOf (⟨z, hzM⟩ : M) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (Subtype.ext (by simpa using hz))
    (fun e => hz1 (by simpa using congrArg Subtype.val e))

theorem zc_mem_zConjClosure_iff [Finite A] {M : Subgroup A} {z₀ u : A} (hz : z₀ ∈ M) (hu : u ∈ M)
    {p : ℕ} (hord : orderOf (⟨z₀, hz⟩ : M) = p) (cs : List A)
    (hcs : ∀ x, x ∈ cs ↔ ∃ i < p, x = z₀ ^ i * u * (z₀ ^ i)⁻¹) (v : M) :
    v ∈ zConjClosure (⟨z₀, hz⟩ : M) ⟨u, hu⟩ ↔ (v : A) ∈ closure {c | c ∈ cs} := by
  have hmap : (zConjClosure (⟨z₀, hz⟩ : M) ⟨u, hu⟩).map M.subtype = closure {c | c ∈ cs} := by
    rw [zConjClosure, MonoidHom.map_closure]
    congr 1
    ext c
    simp only [Set.mem_image, Set.mem_setOf_eq, hcs]
    constructor
    · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨i, hi, rfl⟩ := zc_exists_pow_lt_of_mem_zpowers hord hg
      exact ⟨i, hi, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨(⟨z₀, hz⟩ : M) ^ i, pow_mem (mem_zpowers _) i, rfl⟩, by simp⟩
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm

end Closure

section PerU

variable {A : Type} [Group A] [DecidableEq A]

@[expose] def ZCCond {G : Type} [Group G] (z₀ u : G) : Prop :=
  (∃ g ∈ zpowers z₀, ∃ h ∈ zpowers z₀,
      g * u * g⁻¹ * (h * u * h⁻¹) ≠ h * u * h⁻¹ * (g * u * g⁻¹)) ∨
    ∃ H : Subgroup G, H ≤ normalizer (zConjClosure z₀ u : Set G) ∧ IsSimpleGroup H ∧
      ¬ IsMulCommutative H ∧ z₀ ∈ H ∧ 3 ∣ Nat.card H

theorem zcSubOK_sound [Finite A] (cn : A → A) (hcn : ∀ x, cn x = x) {hs : List (A × A × PSimple)}
    {cs L : List A} (hLsub : ∀ x ∈ L, x ∈ closure {c | c ∈ cs})
    (h : zcSubOK cn hs cs L = true) :
    ∃ t ∈ hs, t.1 ∈ normalizer (closure {c | c ∈ cs} : Set A) ∧
      t.2.1 ∈ normalizer (closure {c | c ∈ cs} : Set A) := by
  unfold zcSubOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    and_assoc] at h
  obtain ⟨h1, hc, hm, hi, t, ht, hn⟩ := h
  simp only [hcn] at hm hn
  have hiff := zc_mem_closure_iff_of_closed cs L h1 hc hm hi hLsub
  refine ⟨t, ht, zc_mem_normalizer_of_conj_mem _ fun v hv => ?_,
    zc_mem_normalizer_of_conj_mem _ fun v hv => ?_⟩
  · rw [hiff] at hv ⊢
    exact (hn v hv).1
  · rw [hiff] at hv ⊢
    exact (hn v hv).2

theorem zcPerUWith_sound [Finite A] (cn : A → A) (hcn : ∀ x, cn x = x) {M : Subgroup A}
    {z₀ u : A} {p : ℕ} (hp : p.Prime) (hz₀M : z₀ ∈ M) (huM : u ∈ M) (hz₀ : z₀ ^ p = 1)
    (hz₀1 : z₀ ≠ 1) {hs : List (A × A × PSimple)} (hsM : ∀ t ∈ hs, t.1 ∈ M ∧ t.2.1 ∈ M)
    (hps : ∀ t ∈ hs, t.2.2.check t.1 t.2.1 z₀ = true) (cap fuel : ℕ) {cs : List A}
    (hcs : ∀ x, x ∈ cs ↔ ∃ i < p, x = z₀ ^ i * u * (z₀ ^ i)⁻¹)
    (h : (!(cs.all (fun x => cs.all (fun y => decide (x * y = y * x)))) ||
      zcSubOK cn hs cs (zcBfs (zcRStep cn cs) cap fuel [1])) = true) :
    ZCCond (⟨z₀, hz₀M⟩ : M) ⟨u, huM⟩ := by
  have hord : orderOf (⟨z₀, hz₀M⟩ : M) = p := zc_orderOf_mk_eq_prime hz₀M hp hz₀ hz₀1
  unfold ZCCond
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · left
    have hne : ¬ ∀ x ∈ cs, ∀ y ∈ cs, x * y = y * x := by
      intro hall
      have h' : cs.all (fun x => cs.all (fun y => decide (x * y = y * x))) = true := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using hall
      simp [h'] at h
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ cs, ∃ y ∈ cs, x * y ≠ y * x := by
      by_contra hcon
      exact hne fun x hx y hy => by_contra fun hxy => hcon ⟨x, hx, y, hy, hxy⟩
    obtain ⟨i, -, rfl⟩ := (hcs x).1 hx
    obtain ⟨j, -, rfl⟩ := (hcs y).1 hy
    refine ⟨(⟨z₀, hz₀M⟩ : M) ^ i, pow_mem (mem_zpowers _) i, (⟨z₀, hz₀M⟩ : M) ^ j,
      pow_mem (mem_zpowers _) j, fun heq => hxy ?_⟩
    simpa using congrArg Subtype.val heq
  · right
    have hLsub : ∀ x ∈ zcBfs (zcRStep cn cs) cap fuel [1], x ∈ closure {c | c ∈ cs} := by
      refine zcBfs_prop (P := fun x => x ∈ closure {c | c ∈ cs}) (zcRStep cn cs) ?_ cap fuel [1]
        ?_
      · exact fun x hx y hy => zcRStep_mem_closure cn hcn hx hy
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact one_mem _
    obtain ⟨t, ht, hn1, hn2⟩ := zcSubOK_sound cn hcn hLsub h
    obtain ⟨hsimp, hnc, hzH, h3⟩ := PSimple.sound t.2.2 t.1 t.2.1 z₀ (hps t ht)
    have hHN : closure ({t.1, t.2.1} : Set A) ≤ normalizer (closure {c | c ∈ cs} : Set A) := by
      rw [closure_le]
      rintro x (rfl | hx)
      · exact hn1
      · rw [Set.mem_singleton_iff.mp hx]
        exact hn2
    have hHM : closure ({t.1, t.2.1} : Set A) ≤ M := by
      rw [closure_le]
      rintro x (rfl | hx)
      · exact (hsM t ht).1
      · rw [Set.mem_singleton_iff.mp hx]
        exact (hsM t ht).2
    have hV := zc_mem_zConjClosure_iff hz₀M huM hord cs hcs
    refine ⟨(closure ({t.1, t.2.1} : Set A)).subgroupOf M, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxN : (x : A) ∈ normalizer (closure {c | c ∈ cs} : Set A) :=
        hHN (Subgroup.mem_subgroupOf.mp hx)
      rw [Subgroup.mem_normalizer_iff]
      intro v
      rw [hV v, hV (x * v * x⁻¹)]
      simpa using Subgroup.mem_normalizer_iff.mp hxN (v : A)
    · exact (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hHM)).mpr hsimp
    · intro hcomm
      apply hnc
      rw [isMulCommutative_iff] at hcomm ⊢
      intro x y
      apply (Subgroup.subgroupOfEquivOfLe hHM).symm.injective
      rw [map_mul, map_mul]
      exact hcomm _ _
    · exact Subgroup.mem_subgroupOf.mpr hzH
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]
      exact h3

theorem zcPerU_sound [Finite A] (cn : A → A) (hcn : ∀ x, cn x = x) {M : Subgroup A}
    {z₀ u : A} {p : ℕ} (hp : p.Prime) (hz₀M : z₀ ∈ M) (huM : u ∈ M) (hz₀ : z₀ ^ p = 1)
    (hz₀1 : z₀ ≠ 1) {hs : List (A × A × PSimple)} (hsM : ∀ t ∈ hs, t.1 ∈ M ∧ t.2.1 ∈ M)
    (hps : ∀ t ∈ hs, t.2.2.check t.1 t.2.1 z₀ = true) (fuel : ℕ)
    (h : zcPerU cn fuel z₀ p hs u = true) : ZCCond (⟨z₀, hz₀M⟩ : M) ⟨u, huM⟩ :=
  zcPerUWith_sound cn hcn hp hz₀M huM hz₀ hz₀1 hsM hps fuel fuel
    (zc_mem_iterate_conj cn hcn z₀ u p) h

end PerU

section Main

variable {A : Type} [Group A] [DecidableEq A]

theorem zcw_of_checkWith [Finite A] (cn : A → A) (hcn : ∀ x, cn x = x) (key : A → ℕ) (a b : A)
    (n p k : ℕ) (hp : p.Prime) (hcard : Nat.card ↥(closure ({a, b} : Set A)) = n) {z₀ : A}
    (hz₀M : z₀ ∈ closure ({a, b} : Set A)) {gens E O : List A}
    (hgens : ∀ s ∈ gens, s ∈ closure ({a, b} : Set A))
    (hE : ∀ x ∈ E, x ∈ closure {s | s ∈ gens}) {hs : List (A × A × PSimple)}
    (hsM : ∀ t ∈ hs, t.1 ∈ closure ({a, b} : Set A) ∧ t.2.1 ∈ closure ({a, b} : Set A))
    (h : zcCheckWith cn key n p k z₀ gens E [a, b, a⁻¹, b⁻¹] O hs = true) :
    ZCW ↥(closure ({a, b} : Set A)) p := by
  unfold zcCheckWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, hlen, hnd, h1E, hEmul, hO, hinv, hU, hps⟩ := h
  rw [zcPow_eq cn hcn] at h1
  simp only [hcn] at hEmul
  have hO' : ∀ x ∈ O, ∀ g ∈ [a, b, a⁻¹, b⁻¹], g * x * g⁻¹ ∈ O := fun x hx g hg => by
    simpa only [hcn] using mem_of_zcMemK (hO x hx g hg)
  have hS : Nat.card (closure {s | s ∈ gens}) = 2 ^ k :=
    (zc_card_closure_of_list gens E hnd h1E hEmul hE).trans hlen
  have hiffS : ∀ x, x ∈ closure {s | s ∈ gens} ↔ x ∈ E := fun x =>
    ⟨zc_mem_list_of_mem_closure gens E h1E hEmul, hE x⟩
  have hSM : closure {s | s ∈ gens} ≤ closure ({a, b} : Set A) :=
    (closure_le _).mpr fun s hs => hgens s hs
  have hS' : Nat.card ((closure {s | s ∈ gens}).subgroupOf (closure ({a, b} : Set A))) =
      2 ^ k := by
    rw [← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  have hk' : ¬ 2 ^ (k + 1) ∣ Nat.card ↥(closure ({a, b} : Set A)) := by rwa [hcard]
  have hOconj := zc_conj_mem_of_closure hO'
  have hinvO : ∀ u : ↥(closure ({a, b} : Set A)), u * u = 1 → u ≠ 1 → (u : A) ∈ O := by
    intro u hu hu1
    obtain ⟨g, hg⟩ := zc_exists_conj_mem_of_card _ k hS' hk' hu
    have hgE : ((g : A) * u * (g : A)⁻¹) ∈ E :=
      (hiffS _).mp (by simpa using Subgroup.mem_subgroupOf.mp hg)
    have hss : ((g : A) * u * (g : A)⁻¹) * ((g : A) * u * (g : A)⁻¹) = 1 := by
      have : ((g : A) * u * (g : A)⁻¹) * ((g : A) * u * (g : A)⁻¹) =
          (g : A) * ((u : A) * u) * (g : A)⁻¹ := by group
      rw [this, show (u : A) * u = 1 from by simpa using congrArg Subtype.val hu]
      simp
    have hs1 : ((g : A) * u * (g : A)⁻¹) ≠ 1 := by
      intro e
      apply hu1
      apply Subtype.ext
      simpa using e
    have hgO := mem_of_zcMemK (hinv _ hgE hss hs1)
    have := hOconj ((g⁻¹ : ↥(closure ({a, b} : Set A))) : A) (g⁻¹).2 _ hgO
    have e : ((g⁻¹ : ↥(closure ({a, b} : Set A))) : A) * ((g : A) * u * (g : A)⁻¹) *
        ((g⁻¹ : ↥(closure ({a, b} : Set A))) : A)⁻¹ = u := by
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at this
  unfold ZCW
  refine ⟨⟨z₀, hz₀M⟩, zc_orderOf_mk_eq_prime hz₀M hp h1 h2, fun u hu hu1 => ?_⟩
  exact zcPerU_sound cn hcn hp hz₀M u.2 h1 h2 hsM hps n (hU _ (hinvO u hu hu1))

theorem ZCData.zcw_of_check [Finite A] [ZCKey A] (cn : A → A) (hcn : ∀ x, cn x = x) (a b : A)
    (d : ZCData) (n : ℕ) (hp : d.p.Prime) (hcard : Nat.card ↥(closure ({a, b} : Set A)) = n)
    (h : d.check cn a b n = true) : ZCW ↥(closure ({a, b} : Set A)) d.p := by
  have hM : ∀ w : PW, cn (zcEval cn a b w) ∈ closure ({a, b} : Set A) := fun w => by
    rw [hcn, zcEval_eq cn hcn]
    exact evalPW_mem a b w
  simp only [ZCData.check] at h
  refine zcw_of_checkWith cn hcn ZCKey.key a b n d.p d.k hp hcard (hM d.z) ?_ ?_ ?_ h
  · intro s hs
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hs
    exact hM w
  · refine zcBfs_prop
      (P := fun x => x ∈ closure {s | s ∈ d.syl.map (fun w => cn (zcEval cn a b w))}) _ ?_
      (2 ^ d.k) n [1] ?_
    · exact fun x hx y hy => zcRStep_mem_closure cn hcn hx hy
    · intro x hx
      rw [List.mem_singleton.mp hx]
      exact one_mem _
  · intro t ht
    obtain ⟨t', -, rfl⟩ := List.mem_map.mp ht
    exact ⟨hM _, hM _⟩

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
