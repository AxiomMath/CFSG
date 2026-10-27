module

public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.Module
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Quasithin
open scoped commutatorElement

section OddOrder

variable {V : Type*} [CommGroup V]

private theorem eq_one_of_sq_eq_one_of_pow_odd (hV : ∀ v : V, v ^ 2 = 1) {x : V} {m : ℕ}
    (hm : Odd m) (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, hV, one_pow, one_mul] at hx
  exact hx

private theorem pow_apply_mul_eq {z : MulAut V} {u t : V} (hzt : z t = t)
    (hu : z u = t * u) (k : ℕ) : (z ^ k) u = u * t ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hzt, hu, pow_succ', mul_left_comm,
      mul_assoc]

private theorem pow_apply_eq_of_fixed {z : MulAut V} {u v : V} (hu : z u = u)
    (huv : z v = u * v) (k : ℕ) : (z ^ k) v = u ^ k * v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hu, huv, pow_succ', mul_assoc, mul_left_comm]

theorem eq_one_of_trivial_on_commV (hV : ∀ v : V, v ^ 2 = 1)
    {K : Subgroup (MulAut V)} {z : MulAut V} (hzK : z ∈ K) {m : ℕ} (hm : Odd m) (hzm : z ^ m = 1)
    (h : ∀ u ∈ commV K, z u * u⁻¹ ∈ fixV K) : z = 1 := by
  refine MulEquiv.ext fun v => ?_
  set u₀ : V := z v * v⁻¹ with hu₀
  have hu₀K : u₀ ∈ commV K := Subgroup.subset_closure ⟨z, hzK, v, rfl⟩
  set t : V := z u₀ * u₀⁻¹ with ht
  have htK : t ∈ fixV K := h u₀ hu₀K
  have hzt : z t = t := htK z hzK
  have hzu : z u₀ = t * u₀ := by rw [ht, inv_mul_cancel_right]
  have h1 : t ^ m = 1 := by
    have := pow_apply_mul_eq hzt hzu m
    rw [hzm] at this
    simpa using this
  have ht1 : t = 1 := eq_one_of_sq_eq_one_of_pow_odd hV hm h1
  have hzu' : z u₀ = u₀ := by rw [hzu, ht1, one_mul]
  have hzv : z v = u₀ * v := by rw [hu₀, inv_mul_cancel_right]
  have h2 : u₀ ^ m = 1 := by
    have := pow_apply_eq_of_fixed hzu' hzv m
    rw [hzm] at this
    simpa using this.symm
  have hu1 : u₀ = 1 := eq_one_of_sq_eq_one_of_pow_odd hV hm h2
  rw [hzv, hu1, one_mul]
  rfl

end OddOrder

section Section

variable {V : Type*} [CommGroup V] (U C : Subgroup V)

private def secStab : Subgroup (MulAut V) where
  carrier := {g | (∀ v, g v ∈ U ↔ v ∈ U) ∧ (∀ v, g v ∈ C ↔ v ∈ C)}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨fun v => (ha.1 _).trans (hb.1 v), fun v => (ha.2 _).trans (hb.2 v)⟩
  inv_mem' := fun {g} hg =>
    ⟨fun v => by rw [← hg.1 (g⁻¹ v), MulAut.apply_inv_self],
      fun v => by rw [← hg.2 (g⁻¹ v), MulAut.apply_inv_self]⟩

private abbrev Sec : Type _ := ↥U ⧸ C.subgroupOf U

private def secMap (g : MulAut V) (hg : g ∈ secStab U C) : Sec U C →* Sec U C :=
  QuotientGroup.map (C.subgroupOf U) (C.subgroupOf U)
    { toFun := fun u => ⟨g (u : V), (hg.1 u).2 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
    (fun x hx => (hg.2 x).2 hx)

private theorem secMap_mk (g : MulAut V) (hg : g ∈ secStab U C) (u : U) (hu : g (u : V) ∈ U) :
    secMap U C g hg (QuotientGroup.mk u) = QuotientGroup.mk ⟨g (u : V), hu⟩ := rfl

private theorem secMap_mul (g h : MulAut V) (hg : g ∈ secStab U C) (hh : h ∈ secStab U C)
    (x : Sec U C) :
    secMap U C (g * h) ((secStab U C).mul_mem hg hh) x =
      secMap U C g hg (secMap U C h hh x) :=
  QuotientGroup.induction_on x fun _ => rfl

private theorem secMap_inv_apply (g : MulAut V) (hg : g ∈ secStab U C) (x : Sec U C) :
    secMap U C g⁻¹ ((secStab U C).inv_mem hg) (secMap U C g hg x) = x :=
  QuotientGroup.induction_on x fun u => by
    have hu : g (u : V) ∈ U := (hg.1 u).2 u.2
    rw [secMap_mk U C g hg u hu, secMap_mk U C g⁻¹ _ _ (((secStab U C).inv_mem hg).1 _ |>.2 hu)]
    exact congrArg QuotientGroup.mk (Subtype.ext (MulAut.inv_apply_self V g u))

private theorem secMap_apply_inv (g : MulAut V) (hg : g ∈ secStab U C) (x : Sec U C) :
    secMap U C g hg (secMap U C g⁻¹ ((secStab U C).inv_mem hg) x) = x := by
  have := secMap_inv_apply U C g⁻¹ ((secStab U C).inv_mem hg) x
  simpa using this

private def secAut (g : MulAut V) (hg : g ∈ secStab U C) : MulAut (Sec U C) where
  toFun := secMap U C g hg
  invFun := secMap U C g⁻¹ ((secStab U C).inv_mem hg)
  left_inv := secMap_inv_apply U C g hg
  right_inv := secMap_apply_inv U C g hg
  map_mul' := map_mul _

private def secRep : secStab U C →* MulAut (Sec U C) where
  toFun g := secAut U C g.1 g.2
  map_one' := MulEquiv.ext fun x => QuotientGroup.induction_on x fun _ => rfl
  map_mul' g h := MulEquiv.ext fun x => secMap_mul U C g.1 h.1 g.2 h.2 x

private theorem secRep_mk (g : secStab U C) (u : U) (hu : g.1 (u : V) ∈ U) :
    secRep U C g (QuotientGroup.mk u) = QuotientGroup.mk ⟨g.1 (u : V), hu⟩ := rfl

end Section

section Irr

variable {V : Type*} [CommGroup V] {K P : Subgroup (MulAut V)}

private theorem apply_comm_of_centralizer (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V)))
    {p x : MulAut V} (hp : p ∈ P) (hx : x ∈ K) (v : V) : x (p v) = p (x v) :=
  congrArg (fun φ : MulAut V => φ v) (Subgroup.mem_centralizer_iff.1 (hP hp) x hx)

private theorem apply_mem_commV (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V)))
    {p : MulAut V} (hp : p ∈ P) {u : V} (hu : u ∈ commV K) : p u ∈ commV K := by
  induction hu using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, v, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨x, hx, p v, ?_⟩
    rw [map_mul, map_inv, apply_comm_of_centralizer hP hp hx]
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

private theorem fixed_le_fixV : XMod.fixed ↥K (commV K) ≤ fixV K :=
  fun _ hc x hx => hc.2 ⟨x, hx⟩

private theorem apply_mem_commV_iff (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V)))
    {p : MulAut V} (hp : p ∈ P) (v : V) : p v ∈ commV K ↔ v ∈ commV K :=
  ⟨fun h => by simpa using apply_mem_commV hP (P.inv_mem hp) h, apply_mem_commV hP hp⟩

private theorem mem_secStab_of_mem (hinv : XMod.IsInv ↥K (commV K)) {k : MulAut V} (hk : k ∈ K) :
    k ∈ secStab (commV K) (XMod.fixed ↥K (commV K)) := by
  have hU : ∀ k ∈ K, ∀ v : V, v ∈ commV K → k v ∈ commV K := fun k hk v hv => hinv ⟨k, hk⟩ v hv
  refine ⟨fun v => ⟨fun h => ?_, hU k hk v⟩, fun v => ⟨fun h => ?_, fun hv => ?_⟩⟩
  · simpa using hU k⁻¹ (K.inv_mem hk) _ h
  · have h2 : k⁻¹ (k v) = k v := h.2 ⟨k⁻¹, K.inv_mem hk⟩
    rw [MulAut.inv_apply_self] at h2
    rw [← h2] at h
    exact h
  · have h2 : k v = v := hv.2 ⟨k, hk⟩
    rw [h2]
    exact hv

private theorem mem_secStab_of_centralizer (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V)))
    {p : MulAut V} (hp : p ∈ P) :
    p ∈ secStab (commV K) (XMod.fixed ↥K (commV K)) := by
  refine ⟨apply_mem_commV_iff hP hp, fun v => ?_⟩
  have hiff : ∀ a : K, (a : MulAut V) (p v) = p v ↔ (a : MulAut V) v = v := fun a => by
    rw [apply_comm_of_centralizer hP hp a.2 v]
    exact p.injective.eq_iff
  exact ⟨fun h => ⟨(apply_mem_commV_iff hP hp v).1 h.1, fun a => (hiff a).1 (h.2 a)⟩,
    fun h => ⟨(apply_mem_commV_iff hP hp v).2 h.1, fun a => (hiff a).2 (h.2 a)⟩⟩

theorem commutator_trivial_of_isIrrPlus {V : Type} [CommGroup V] [Finite V]
    {K P : Subgroup (MulAut V)} (hirr : commV K ∈ IrrPlus K ⊤)
    (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V))) :
    ∀ x ∈ ⁅P, P⁆, ∀ u ∈ commV K, x u * u⁻¹ ∈ fixV K := by
  obtain ⟨-, hinv, -, hsec⟩ := hirr
  have hKs : K ≤ secStab (commV K) (XMod.fixed ↥K (commV K)) := fun _ hk =>
    mem_secStab_of_mem hinv hk
  have hPs : P ≤ secStab (commV K) (XMod.fixed ↥K (commV K)) := fun _ hp =>
    mem_secStab_of_centralizer hP hp
  set U := commV K with hU
  set C := XMod.fixed ↥K U with hC
  set S : Subgroup (MulAut (Sec U C)) := (K.subgroupOf (secStab U C)).map (secRep U C) with hS
  set T : Subgroup (MulAut (Sec U C)) := (P.subgroupOf (secStab U C)).map (secRep U C) with hT
  have hirrS : XMod.IsIrrSec ↥S (⊥ : Subgroup (Sec U C)) ⊤ := by
    refine ⟨?_, fun J hJ _ _ => ?_⟩
    · obtain ⟨x, hxU, hxC⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hsec.1).2
      refine lt_of_le_of_ne bot_le fun h => hxC ?_
      have h1 : (QuotientGroup.mk ⟨x, hxU⟩ : Sec U C) ∈ (⊥ : Subgroup (Sec U C)) := by
        rw [h]; trivial
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    · let Jv : Subgroup V := (J.comap (QuotientGroup.mk' (C.subgroupOf U))).map U.subtype
      have hmemJv : ∀ x : U, (x : V) ∈ Jv ↔ (QuotientGroup.mk x : Sec U C) ∈ J := by
        intro x
        constructor
        · rintro ⟨y, hy, hyx⟩
          have : y = x := Subtype.ext hyx
          subst this
          exact hy
        · intro h
          exact ⟨x, h, rfl⟩
      have hJvinv : XMod.IsInv ↥K Jv := by
        intro a v hv
        obtain ⟨y, hy, rfl⟩ := hv
        have hy' : (QuotientGroup.mk y : Sec U C) ∈ J := hy
        have hay : (a : MulAut V) (y : V) ∈ U := hinv a y y.2
        refine (hmemJv ⟨_, hay⟩).2 ?_
        exact hJ ⟨secRep U C ⟨a, hKs a.2⟩,
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 a.2)⟩ _ hy'
      have hCJ : C ≤ Jv := fun c hc => by
        refine (hmemJv ⟨c, hc.1⟩).2 ?_
        have : (QuotientGroup.mk ⟨c, hc.1⟩ : Sec U C) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hc)
        rw [this]
        exact J.one_mem
      rcases hsec.2 Jv hJvinv hCJ (Subgroup.map_subtype_le _) with h | h
      · left
        rw [eq_bot_iff]
        intro n hn
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective n
        have h1 : (x : V) ∈ Jv := (hmemJv x).2 hn
        rw [h] at h1
        exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h1)
      · right
        rw [eq_top_iff]
        intro n _
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective n
        have h1 : (x : V) ∈ Jv := by rw [h]; exact x.2
        exact (hmemJv x).1 h1
  have hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hP hb) _ ha)
  have hcomm := A37.commute_of_irreducible S T hirrS hST
  have hker : ⁅P, P⁆ ≤ (secRep U C).ker.map (secStab U C).subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, hPs ha⟩ : secStab U C), ⟨b, hPs hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ha)) _
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb))
  intro x hx u hu
  obtain ⟨y, hy, rfl⟩ := hker hx
  have h1 : secRep U C y (QuotientGroup.mk ⟨u, hu⟩) = QuotientGroup.mk ⟨u, hu⟩ := by
    rw [MonoidHom.mem_ker.1 hy]
    rfl
  have hyu : y.1 (u : V) ∈ U := (y.2.1 u).2 hu
  rw [secRep_mk U C y ⟨u, hu⟩ hyu, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have h2 : (y.1 u)⁻¹ * u ∈ C := h1
  have e : y.1 u * u⁻¹ = ((y.1 u)⁻¹ * u)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact mul_comm _ _
  show y.1 u * u⁻¹ ∈ fixV K
  rw [e]
  exact fixed_le_fixV (C.inv_mem h2)

end Irr

end CFSG.HardMathSupport.Curtis.Coordinator
