module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard
public import CFSG.Quasithin.H13.U3S1347P
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

section Comm

variable {V : Type*} [CommGroup V]

@[expose] def commMap (g : MulAut V) : V →* V where
  toFun v := g v * v⁻¹
  map_one' := by simp
  map_mul' x y := by
    show g (x * y) * (x * y)⁻¹ = g x * x⁻¹ * (g y * y⁻¹)
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commMap_apply (g : MulAut V) (v : V) : commMap g v = g v * v⁻¹ := rfl

theorem commMap_eq_one_iff (g : MulAut V) (v : V) : commMap g v = 1 ↔ g v = v := by
  rw [commMap_apply, mul_inv_eq_one]

theorem card_ker_mul_card_range_commMap [Finite V] (g : MulAut V) :
    Nat.card V = Nat.card (commMap g).ker * Nat.card (commMap g).range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (commMap g).ker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (commMap g)).toEquiv]

theorem commMap_range_le_ker (h2 : ∀ v : V, v * v = 1) {g : MulAut V} (hg : g * g = 1) :
    (commMap g).range ≤ (commMap g).ker := by
  rintro _ ⟨v, rfl⟩
  rw [MonoidHom.mem_ker, commMap_eq_one_iff, commMap_apply, map_mul, map_inv]
  have hgg : g (g v) = v := by rw [← MulAut.mul_apply, hg, MulAut.one_apply]
  rw [hgg, inv_eq_of_mul_eq_one_right (h2 (g v)), inv_eq_of_mul_eq_one_right (h2 v), mul_comm]

theorem card_commRange_of_sq [Finite V] (h2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 16)
    {g : MulAut V} (hg : g * g = 1) (hg1 : g ≠ 1) :
    Nat.card (commMap g).range = 2 ∨ Nat.card (commMap g).range = 4 := by
  have hcard := card_ker_mul_card_range_commMap g
  have hle := Subgroup.card_le_of_le (commMap_range_le_ker h2 hg)
  have hdvd : Nat.card (commMap g).range ∣ 16 := hV ▸ Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card (commMap g).range ≠ 1 := by
    intro h1
    apply hg1
    ext v
    have hv : commMap g v = 1 := by
      have := Subgroup.eq_bot_of_card_eq _ h1
      have hmem : commMap g v ∈ (commMap g).range := ⟨v, rfl⟩
      rw [this] at hmem
      exact hmem
    rw [commMap_eq_one_iff] at hv
    rw [hv, MulAut.one_apply]
  have hpos : 0 < Nat.card (commMap g).ker := Nat.card_pos
  have hsq : Nat.card (commMap g).range * Nat.card (commMap g).range ≤ 16 := by
    rw [hV] at hcard
    calc Nat.card (commMap g).range * Nat.card (commMap g).range
        ≤ Nat.card (commMap g).ker * Nat.card (commMap g).range :=
          Nat.mul_le_mul_right _ hle
      _ = 16 := hcard.symm
  have h16 : Nat.card (commMap g).range ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card (commMap g).range <;> simp_all <;> omega

theorem commMap_conj (g h : MulAut V) (v : V) :
    commMap (h * g * h⁻¹) v = h (commMap g (h⁻¹ v)) := by
  simp only [commMap_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem commRange_conj (g h : MulAut V) :
    (commMap (h * g * h⁻¹)).range = (commMap g).range.map h.toMonoidHom := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨commMap g (h⁻¹ w), ⟨_, rfl⟩, (commMap_conj g h w).symm⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨h w, ?_⟩
    rw [commMap_conj, MulAut.inv_apply_self]
    rfl

theorem card_commRange_conj (g h : MulAut V) :
    Nat.card (commMap (h * g * h⁻¹)).range = Nat.card (commMap g).range := by
  rw [commRange_conj, Subgroup.card_map_of_injective h.injective]

theorem apply_eq_of_mem_commRange (h2 : ∀ v : V, v * v = 1) {g : MulAut V} (hg : g * g = 1)
    {u : V} (hu : u ∈ (commMap g).range) : g u = u :=
  (commMap_eq_one_iff g u).mp (commMap_range_le_ker h2 hg hu)

theorem apply_eq_mul_commMap (g : MulAut V) (v : V) : g v = v * commMap g v := by
  rw [commMap_apply, mul_inv_cancel_comm_assoc]

theorem commute_of_commRange_eq (h2 : ∀ v : V, v * v = 1) {g h : MulAut V} (hg : g * g = 1)
    (hh : h * h = 1) (heq : (commMap g).range = (commMap h).range) : g * h = h * g := by
  ext v
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have hgh : g (commMap h v) = commMap h v :=
    apply_eq_of_mem_commRange h2 hg (heq ▸ ⟨v, rfl⟩)
  have hhg : h (commMap g v) = commMap g v :=
    apply_eq_of_mem_commRange h2 hh (heq ▸ ⟨v, rfl⟩)
  conv_lhs => rw [apply_eq_mul_commMap h v, map_mul, hgh, apply_eq_mul_commMap g v]
  conv_rhs => rw [apply_eq_mul_commMap g v, map_mul, hhg, apply_eq_mul_commMap h v]
  rw [mul_assoc, mul_assoc, mul_comm (commMap g v)]

theorem eq_one_of_isTv_of_pow_five [Finite V] (h2 : ∀ v : V, v * v = 1) {g h : MulAut V}
    (hg : g * g = 1) (hh : h * h = 1) (htg : Nat.card (commMap g).range = 2)
    (hth : Nat.card (commMap h).range = 2) (h5 : (g * h) ^ 5 = 1) : g * h = 1 := by
  set U : Subgroup V := (commMap g).range ⊔ (commMap h).range with hU
  set r : MulAut V := g * h with hr
  have hUcard : Nat.card U ≤ 4 := by
    have hsurj : Function.Surjective
        (fun p : (commMap g).range × (commMap h).range =>
          (⟨(p.1 : V) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
            (Subgroup.mem_sup_right p.2.2)⟩ : U)) := by
      rintro ⟨u, hu⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
      exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, htg, hth] at this
  have hgU : ∀ u ∈ U, g u ∈ U := by
    intro u hu
    rw [apply_eq_mul_commMap]
    exact U.mul_mem hu (Subgroup.mem_sup_left ⟨u, rfl⟩)
  have hhU : ∀ u ∈ U, h u ∈ U := by
    intro u hu
    rw [apply_eq_mul_commMap]
    exact U.mul_mem hu (Subgroup.mem_sup_right ⟨u, rfl⟩)
  have hgg : ∀ x, g (g x) = x := fun x => by
    rw [← MulAut.mul_apply, hg, MulAut.one_apply]
  have hhh : ∀ x, h (h x) = x := fun x => by
    rw [← MulAut.mul_apply, hh, MulAut.one_apply]
  have hrU : ∀ u, u ∈ U ↔ MulAut.toPerm V r u ∈ U := by
    intro u
    constructor
    · intro hu
      exact hgU _ (hhU _ hu)
    · intro hu
      have hrr : h (g (r u)) = u := by
        rw [hr, MulAut.mul_apply, hgg, hhh]
      rw [← hrr]
      exact hhU _ (hgU _ hu)
  have hfix : ∀ u ∈ U, r u = u := by
    let p : Perm U := (MulAut.toPerm V r).subtypePerm fun u => (hrU u).symm
    have hr5 : (MulAut.toPerm V r) ^ 5 = 1 := by rw [← map_pow, h5, map_one]
    have hp5 : p ^ 5 = 1 := by
      ext x
      simp only [p, Equiv.Perm.subtypePerm_pow, hr5]
      rfl
    have hord5 : orderOf p ∣ 5 := orderOf_dvd_of_pow_eq_one hp5
    have hordU : orderOf p ∣ (Nat.card U).factorial := by
      rw [← Nat.card_perm]
      exact orderOf_dvd_natCard p
    have h24 : (Nat.card U).factorial ∣ 24 := by
      interval_cases h : Nat.card U <;> decide
    have hp1 : orderOf p = 1 := by
      have := Nat.dvd_gcd hord5 (hordU.trans h24)
      rw [show Nat.gcd 5 24 = 1 by decide] at this
      exact Nat.dvd_one.mp this
    rw [orderOf_eq_one_iff] at hp1
    intro u hu
    have := congrArg (fun q : Perm U => (q ⟨u, hu⟩ : V)) hp1
    simp only [p, Equiv.Perm.subtypePerm_apply, Equiv.Perm.coe_one, id_eq] at this
    exact this
  have hrr : r * r = 1 := by
    ext v
    have hw : commMap r v ∈ U := by
      have : commMap r v = commMap g (h v) * commMap h v := by
        simp only [commMap_apply, hr, MulAut.mul_apply]
        rw [mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact U.mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)
    have hrv : r v = v * commMap r v := apply_eq_mul_commMap r v
    calc (r * r) v = r (r v) := rfl
      _ = r (v * commMap r v) := by rw [← hrv]
      _ = r v * r (commMap r v) := map_mul _ _ _
      _ = v * commMap r v * commMap r v := by rw [← hrv, hfix _ hw]
      _ = v := by rw [mul_assoc, h2, mul_one]
      _ = (1 : MulAut V) v := rfl
  calc r = r ^ 5 * ((r * r) * (r * r))⁻¹ := by group
    _ = 1 := by rw [h5, hrr]; group

theorem commKer_conj (g h : MulAut V) :
    (commMap (h * g * h⁻¹)).ker = (commMap g).ker.map h.toMonoidHom := by
  ext v
  rw [MonoidHom.mem_ker, commMap_conj, map_eq_one_iff _ h.injective, Subgroup.mem_map_equiv,
    MonoidHom.mem_ker]
  rfl

theorem card_commKer_conj (g h : MulAut V) :
    Nat.card (commMap (h * g * h⁻¹)).ker = Nat.card (commMap g).ker := by
  rw [commKer_conj, Subgroup.card_map_of_injective h.injective]

end Comm

section Classes

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def e8Perm (s : Fin 3 → ZMod 2) : Perm (Fin 6) :=
  (if s 0 = 1 then swap 0 1 else 1) * (if s 1 = 1 then swap 2 3 else 1) *
    (if s 2 = 1 then swap 4 5 else 1)

theorem e8Perm_add : ∀ s t : Fin 3 → ZMod 2, e8Perm (s + t) = e8Perm s * e8Perm t := by
  decide

@[expose] def e8Hom : Multiplicative (Fin 3 → ZMod 2) →* Perm (Fin 6) where
  toFun s := e8Perm s.toAdd
  map_one' := by decide
  map_mul' s t := e8Perm_add s.toAdd t.toAdd

theorem e8Perm_injective : Function.Injective e8Perm := by
  intro s t h
  revert s t
  decide

theorem image_e8Perm : (Finset.univ : Finset (Fin 3 → ZMod 2)).image e8Perm =
    {1, swap 0 1, swap 2 3, swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5,
      swap 2 3 * swap 4 5, swap 0 1 * swap 2 3 * swap 4 5} := by
  decide

theorem eight_dvd_sum_card_commKer (ρ : Perm (Fin 6) →* MulAut V) :
    8 ∣ ∑ σ ∈ ({1, swap 0 1, swap 2 3, swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5,
      swap 2 3 * swap 4 5, swap 0 1 * swap 2 3 * swap 4 5} : Finset (Perm (Fin 6))),
        Nat.card (commMap (ρ σ)).ker := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  letI : MulAction (Multiplicative (Fin 3 → ZMod 2)) V := MulAction.compHom V (ρ.comp e8Hom)
  have hfix : ∀ s : Multiplicative (Fin 3 → ZMod 2),
      Fintype.card (MulAction.fixedBy V s) = Nat.card (commMap (ρ (e8Perm s.toAdd))).ker := by
    intro s
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [MulAction.mem_fixedBy, MonoidHom.mem_ker, commMap_eq_one_iff]
    rfl
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (Fin 3 → ZMod 2)) V
  have h8 : Fintype.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by decide
  rw [h8] at hB
  have hsum : ∑ s : Multiplicative (Fin 3 → ZMod 2), Fintype.card (MulAction.fixedBy V s) =
      ∑ σ ∈ (Finset.univ : Finset (Fin 3 → ZMod 2)).image e8Perm,
        Nat.card (commMap (ρ σ)).ker := by
    rw [Finset.sum_image fun s _ t _ h => e8Perm_injective h]
    exact Fintype.sum_equiv Multiplicative.toAdd _ _ fun s => hfix s
  rw [← image_e8Perm, ← hsum, hB]
  exact Dvd.intro_left _ rfl

theorem rho_sq_of_sq (ρ : Perm (Fin 6) →* MulAut V) {x : Perm (Fin 6)} (hx : x * x = 1) :
    ρ x * ρ x = 1 := by
  rw [← map_mul, hx, map_one]

theorem card_commKer_rho_conj (ρ : Perm (Fin 6) →* MulAut V) (σ x : Perm (Fin 6)) :
    Nat.card (commMap (ρ (σ * x * σ⁻¹))).ker = Nat.card (commMap (ρ x)).ker := by
  rw [map_mul, map_mul, map_inv, card_commKer_conj]

theorem card_commRange_rho_conj (ρ : Perm (Fin 6) →* MulAut V) (σ x : Perm (Fin 6)) :
    Nat.card (commMap (ρ (σ * x * σ⁻¹))).range = Nat.card (commMap (ρ x)).range := by
  rw [map_mul, map_mul, map_inv, card_commRange_conj]

theorem card_commRange_double_ne_two (h2 : ∀ v : V, v * v = 1) (ρ : Perm (Fin 6) →* MulAut V)
    (hρ : Function.Injective ρ) : Nat.card (commMap (ρ (swap 0 1 * swap 2 3))).range ≠ 2 := by
  intro htv
  have hy : (swap 1 2 * swap 3 4 : Perm (Fin 6)) =
      (swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1) * (swap 0 1 * swap 2 3) *
        (swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1)⁻¹ := by decide
  have htv' : Nat.card (commMap (ρ (swap 1 2 * swap 3 4))).range = 2 := by
    rw [hy, card_commRange_rho_conj, htv]
  have h5 : (ρ (swap 0 1 * swap 2 3) * ρ (swap 1 2 * swap 3 4)) ^ 5 = 1 := by
    rw [← map_mul, ← map_pow, show ((swap 0 1 * swap 2 3) * (swap 1 2 * swap 3 4) :
      Perm (Fin 6)) ^ 5 = 1 by decide, map_one]
  have h1 := eq_one_of_isTv_of_pow_five h2 (rho_sq_of_sq ρ (by decide)) (rho_sq_of_sq ρ
    (by decide)) htv htv' h5
  rw [← map_mul] at h1
  exact absurd (hρ (h1.trans (map_one ρ).symm)) (by decide)

theorem card_commKer_rho (h2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 16)
    (ρ : Perm (Fin 6) →* MulAut V) (hρ : Function.Injective ρ) {x : Perm (Fin 6)}
    (hx : x * x = 1) (hx1 : x ≠ 1) :
    (Nat.card (commMap (ρ x)).range = 2 ∧ Nat.card (commMap (ρ x)).ker = 8) ∨
      (Nat.card (commMap (ρ x)).range = 4 ∧ Nat.card (commMap (ρ x)).ker = 4) := by
  have hne : ρ x ≠ 1 := fun h => hx1 (hρ (h.trans (map_one ρ).symm))
  have hcard := card_ker_mul_card_range_commMap (ρ x)
  rw [hV] at hcard
  rcases card_commRange_of_sq h2 hV (rho_sq_of_sq ρ hx) hne with h | h
  · exact Or.inl ⟨h, by rw [h] at hcard; omega⟩
  · exact Or.inr ⟨h, by rw [h] at hcard; omega⟩

theorem card_commRange_swap_or_triple (h2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 16)
    (ρ : Perm (Fin 6) →* MulAut V) (hρ : Function.Injective ρ) :
    Nat.card (commMap (ρ (swap 0 1))).range = 2 ∨
      Nat.card (commMap (ρ (swap 0 1 * swap 2 3 * swap 4 5))).range = 2 := by
  have hdvd := eight_dvd_sum_card_commKer ρ
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hdvd
  have hk0 : Nat.card (commMap (ρ 1)).ker = 16 := by
    rw [map_one, ← hV]
    refine Nat.card_congr (Equiv.subtypeUnivEquiv fun v => ?_)
    rw [MonoidHom.mem_ker, commMap_eq_one_iff, MulAut.one_apply]
  have e23 : Nat.card (commMap (ρ (swap 2 3))).ker = Nat.card (commMap (ρ (swap 0 1))).ker := by
    rw [show (swap 2 3 : Perm (Fin 6)) = (swap 0 2 * swap 1 3) * swap 0 1 *
      (swap 0 2 * swap 1 3)⁻¹ by decide, card_commKer_rho_conj]
  have e45 : Nat.card (commMap (ρ (swap 4 5))).ker = Nat.card (commMap (ρ (swap 0 1))).ker := by
    rw [show (swap 4 5 : Perm (Fin 6)) = (swap 0 4 * swap 1 5) * swap 0 1 *
      (swap 0 4 * swap 1 5)⁻¹ by decide, card_commKer_rho_conj]
  have e0145 : Nat.card (commMap (ρ (swap 0 1 * swap 4 5))).ker =
      Nat.card (commMap (ρ (swap 0 1 * swap 2 3))).ker := by
    rw [show (swap 0 1 * swap 4 5 : Perm (Fin 6)) = (swap 2 4 * swap 3 5) *
      (swap 0 1 * swap 2 3) * (swap 2 4 * swap 3 5)⁻¹ by decide, card_commKer_rho_conj]
  have e2345 : Nat.card (commMap (ρ (swap 2 3 * swap 4 5))).ker =
      Nat.card (commMap (ρ (swap 0 1 * swap 2 3))).ker := by
    rw [show (swap 2 3 * swap 4 5 : Perm (Fin 6)) = (swap 0 4 * swap 1 5) *
      (swap 0 1 * swap 2 3) * (swap 0 4 * swap 1 5)⁻¹ by decide, card_commKer_rho_conj]
  rw [hk0, e23, e45, e0145, e2345] at hdvd
  have hd := card_commRange_double_ne_two h2 ρ hρ
  rcases card_commKer_rho h2 hV ρ hρ (x := swap 0 1 * swap 2 3) (by decide) (by decide) with
    ⟨h, -⟩ | ⟨-, hk2⟩
  · exact absurd h hd
  rcases card_commKer_rho h2 hV ρ hρ (x := swap 0 1) (by decide) (by decide) with
    ⟨h, -⟩ | ⟨-, hk1⟩
  · exact Or.inl h
  rcases card_commKer_rho h2 hV ρ hρ (x := swap 0 1 * swap 2 3 * swap 4 5) (by decide)
    (by decide) with ⟨h, -⟩ | ⟨-, hk3⟩
  · exact Or.inr h
  rw [hk1, hk2, hk3] at hdvd
  omega

end Classes

section Centre

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_of_card_eq_two {H : Subgroup V} (h : Nat.card H = 2) :
    ∃ e ∈ H, e ≠ 1 ∧ ∀ x ∈ H, x = 1 ∨ x = e := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h
  refine ⟨y, y.2, fun h1 => hy (Subtype.ext h1), fun x hx => ?_⟩
  by_cases hx1 : (⟨x, hx⟩ : H) = 1
  · exact Or.inl (congrArg Subtype.val hx1)
  · exact Or.inr (congrArg Subtype.val (huniq _ hx1))

@[expose] noncomputable def tvCentre (g : MulAut V) : V :=
  if h : Nat.card (commMap g).range = 2 then (exists_of_card_eq_two h).choose else 1

section

variable {g : MulAut V} (hg : Nat.card (commMap g).range = 2)
include hg

theorem tvCentre_mem : tvCentre g ∈ (commMap g).range := by
  rw [tvCentre, dif_pos hg]
  exact (exists_of_card_eq_two hg).choose_spec.1

theorem tvCentre_ne_one : tvCentre g ≠ 1 := by
  rw [tvCentre, dif_pos hg]
  exact (exists_of_card_eq_two hg).choose_spec.2.1

theorem mem_commRange_iff {x : V} : x ∈ (commMap g).range ↔ x = 1 ∨ x = tvCentre g := by
  constructor
  · intro hx
    rw [tvCentre, dif_pos hg]
    exact (exists_of_card_eq_two hg).choose_spec.2.2 x hx
  · rintro (rfl | rfl)
    · exact (commMap g).range.one_mem
    · exact tvCentre_mem hg

theorem tvCentre_conj (k : MulAut V) : tvCentre (k * g * k⁻¹) = k (tvCentre g) := by
  have hk : Nat.card (commMap (k * g * k⁻¹)).range = 2 := by rw [card_commRange_conj]; exact hg
  have hmem : k (tvCentre g) ∈ (commMap (k * g * k⁻¹)).range := by
    rw [commRange_conj]
    exact ⟨_, tvCentre_mem hg, rfl⟩
  rcases (mem_commRange_iff hk).mp hmem with h1 | h1
  · exact absurd ((map_eq_one_iff k k.injective).mp h1) (tvCentre_ne_one hg)
  · exact h1.symm

end

theorem commRange_eq_of_tvCentre_eq {g h : MulAut V} (hg : Nat.card (commMap g).range = 2)
    (hh : Nat.card (commMap h).range = 2) (heq : tvCentre g = tvCentre h) :
    (commMap g).range = (commMap h).range := by
  ext x
  rw [mem_commRange_iff hg, mem_commRange_iff hh, heq]

end Centre

section Natural

variable {V : Type*} [CommGroup V] [Finite V] (ρ : Perm (Fin 6) →* MulAut V)

@[expose] noncomputable def swapCentre (i j : Fin 6) : V :=
  tvCentre (ρ (swap i j))

@[expose] noncomputable def baseCentre (j : Fin 6) : V :=
  if j = 0 then 1 else swapCentre ρ 0 j

@[expose] def pairVec (i j : Fin 6) : Fin 6 → ZMod 2 :=
  Pi.single i 1 + Pi.single j 1

theorem evenWeight_six_cases : ∀ x : Fin 6 → ZMod 2, ∑ k, x k = 0 →
    x = 0 ∨ x = allOnes 6 ∨
      ∃ i j : Fin 6, i ≠ j ∧ (x = pairVec i j ∨ x = allOnes 6 + pairVec i j) := by
  decide

theorem eq_sum_pairVec : ∀ x : Fin 6 → ZMod 2, ∑ k, x k = 0 →
    x = ∑ j, (x j).val • pairVec 0 j := by
  decide

theorem sum_allOnes_add_pairVec : ∀ i j : Fin 6, ∑ l, (allOnes 6 + pairVec i j) l = 0 := by
  decide

theorem exists_ne_ne_fin_six : ∀ i j : Fin 6, ∃ k, k ≠ i ∧ k ≠ j := by
  decide

theorem pow_val_add_of_sq {v : V} (hv : v * v = 1) (a b : ZMod 2) :
    v ^ (a + b).val = v ^ a.val * v ^ b.val := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 + 1 : ZMod 2) = 0 from rfl, ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, hv]

variable (h2 : ∀ v : V, v * v = 1)

@[expose] noncomputable def natMap : (Fin 6 → ZMod 2) →+ Additive V where
  toFun x := Additive.ofMul (∏ j, baseCentre ρ j ^ (x j).val)
  map_zero' := by simp
  map_add' x y := by
    rw [← ofMul_mul, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun j _ => pow_val_add_of_sq (h2 _) (x j) (y j)

variable {ρ}

theorem natMap_single (k : Fin 6) :
    natMap ρ h2 (Pi.single k 1) = Additive.ofMul (baseCentre ρ k) := by
  show Additive.ofMul (∏ j, baseCentre ρ j ^ ((Pi.single k (1 : ZMod 2) : Fin 6 → ZMod 2) j).val)
    = _
  rw [Finset.prod_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, ZMod.val_zero,
    pow_zero]) (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, ZMod.val_one,
    pow_one]

theorem natMap_pairVec (i j : Fin 6) :
    natMap ρ h2 (pairVec i j) = Additive.ofMul (baseCentre ρ i * baseCentre ρ j) := by
  rw [pairVec, map_add, natMap_single, natMap_single, ofMul_mul]

@[expose] def permVec (σ : Perm (Fin 6)) : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2) where
  toFun x k := x (σ⁻¹ k)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem permVec_single (σ : Perm (Fin 6)) (a : Fin 6) :
    permVec σ (Pi.single a 1) = Pi.single (σ a) 1 := by
  funext k
  show (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) (σ⁻¹ k) = (Pi.single (σ a) 1 : Fin 6 → ZMod 2) k
  by_cases hk : k = σ a
  · rw [hk, show σ⁻¹ (σ a) = a by simp, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne]
    intro h
    exact hk (by rw [← h]; simp)

theorem permVec_pairVec (σ : Perm (Fin 6)) (a b : Fin 6) :
    permVec σ (pairVec a b) = pairVec (σ a) (σ b) := by
  rw [pairVec, map_add, permVec_single, permVec_single, pairVec]

theorem permVec_allOnes (σ : Perm (Fin 6)) : permVec σ (allOnes 6) = allOnes 6 := rfl

theorem pairVec_self (a : Fin 6) : pairVec a a = 0 := by
  funext k
  simp only [pairVec, Pi.add_apply, Pi.zero_apply]
  by_cases hk : k = a
  · rw [hk, Pi.single_eq_same]; rfl
  · rw [Pi.single_eq_of_ne hk, add_zero]

section Swap

variable (hρ : Function.Injective ρ) (htv : Nat.card (commMap (ρ (swap 0 1))).range = 2)
include htv

theorem card_commRange_swap {i j : Fin 6} (hij : i ≠ j) :
    Nat.card (commMap (ρ (swap i j))).range = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (by decide : (0 : Fin 6) ≠ 1) hij)
  rw [← hc, card_commRange_rho_conj, htv]

theorem rho_swapCentre (σ : Perm (Fin 6)) {i j : Fin 6} (hij : i ≠ j) :
    ρ σ (swapCentre ρ i j) = swapCentre ρ (σ i) (σ j) := by
  rw [swapCentre, swapCentre, swap_apply_apply, map_mul, map_mul, map_inv,
    tvCentre_conj (card_commRange_swap htv hij)]

theorem swapCentre_ne_one {i j : Fin 6} (hij : i ≠ j) : swapCentre ρ i j ≠ 1 :=
  tvCentre_ne_one (card_commRange_swap htv hij)

omit htv in
theorem swapCentre_comm (i j : Fin 6) : swapCentre ρ i j = swapCentre ρ j i := by
  rw [swapCentre, swapCentre, swap_comm]

include h2 hρ in
theorem swapCentre_ne {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    swapCentre ρ i j ≠ swapCentre ρ j k := by
  intro heq
  have hc := commute_of_commRange_eq h2 (rho_sq_of_sq ρ (swap_mul_self i j))
    (rho_sq_of_sq ρ (swap_mul_self j k))
    (commRange_eq_of_tvCentre_eq (card_commRange_swap htv hij) (card_commRange_swap htv hjk) heq)
  rw [← map_mul, ← map_mul] at hc
  have := congrArg (fun σ : Perm (Fin 6) => σ i) (hρ hc)
  simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hij hik, swap_apply_left] at this
  exact hjk this

include h2 hρ in
theorem swapCentre_mul {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    swapCentre ρ i k = swapCentre ρ i j * swapCentre ρ j k := by
  have h1 : swapCentre ρ i k = ρ (swap j k) (swapCentre ρ i j) := by
    rw [rho_swapCentre htv _ hij, swap_apply_of_ne_of_ne hij hik, swap_apply_left]
  have hmem : commMap (ρ (swap j k)) (swapCentre ρ i j) ∈ (commMap (ρ (swap j k))).range :=
    ⟨_, rfl⟩
  rw [mem_commRange_iff (card_commRange_swap htv hjk)] at hmem
  rcases hmem with h | h
  · exfalso
    have : swapCentre ρ i k = swapCentre ρ i j := by
      rw [h1, apply_eq_mul_commMap, h, mul_one]
    exact swapCentre_ne h2 hρ htv hij.symm hik hjk (by rw [swapCentre_comm, this])
  · rw [h1, apply_eq_mul_commMap, h]
    rfl

include h2 hρ in
theorem baseCentre_mul {i j : Fin 6} (hij : i ≠ j) :
    baseCentre ρ i * baseCentre ρ j = swapCentre ρ i j := by
  by_cases hi : i = 0
  · subst hi
    rw [baseCentre, if_pos rfl, one_mul, baseCentre, if_neg (Ne.symm hij)]
  by_cases hj : j = 0
  · subst hj
    rw [baseCentre, if_neg hi, baseCentre, if_pos rfl, mul_one, swapCentre_comm]
  rw [baseCentre, if_neg hi, baseCentre, if_neg hj, swapCentre_comm 0 i]
  exact (swapCentre_mul h2 hρ htv hi (Ne.symm hj) hij).symm

include hρ in
theorem natMap_pairVec_of_ne {i j : Fin 6} (hij : i ≠ j) :
    natMap ρ h2 (pairVec i j) = Additive.ofMul (swapCentre ρ i j) := by
  rw [natMap_pairVec, baseCentre_mul h2 hρ htv hij]

include hρ in
theorem natMap_permVec (σ : Perm (Fin 6)) {x : Fin 6 → ZMod 2} (hx : ∑ k, x k = 0) :
    natMap ρ h2 (permVec σ x) = (ρ σ).toMonoidHom.toAdditive (natMap ρ h2 x) := by
  have hgen : ∀ j, natMap ρ h2 (permVec σ (pairVec 0 j)) =
      (ρ σ).toMonoidHom.toAdditive (natMap ρ h2 (pairVec 0 j)) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [pairVec_self, map_zero, map_zero, map_zero]
    rw [permVec_pairVec, natMap_pairVec_of_ne h2 hρ htv (Ne.symm hj),
      natMap_pairVec_of_ne h2 hρ htv (σ.injective.ne (Ne.symm hj))]
    show Additive.ofMul _ = Additive.ofMul (ρ σ (swapCentre ρ 0 j))
    rw [rho_swapCentre htv σ (Ne.symm hj)]
  rw [eq_sum_pairVec x hx, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_nsmul, map_nsmul, map_nsmul, map_nsmul, hgen]

include hρ in
theorem natMap_allOnes (hV : Nat.card V = 16) : natMap ρ h2 (allOnes 6) = 0 := by
  have hsum1 : ∑ k : Fin 6, allOnes 6 k = 0 := by decide
  have h4 : ∀ i j : Fin 6, i ≠ j → natMap ρ h2 (allOnes 6 + pairVec i j) ≠ 0 := by
    intro i j hij h0
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_fin_six i j
    have hsum := sum_allOnes_add_pairVec i j
    have h0' : natMap ρ h2 (allOnes 6 + pairVec i k) = 0 := by
      have := natMap_permVec h2 hρ htv (swap j k) hsum
      rw [h0, map_zero, map_add, permVec_allOnes, permVec_pairVec,
        swap_apply_of_ne_of_ne hij (Ne.symm hki), swap_apply_left] at this
      exact this
    rw [map_add] at h0 h0'
    have heq : natMap ρ h2 (pairVec i j) = natMap ρ h2 (pairVec i k) := by
      rw [← add_left_cancel_iff (a := natMap ρ h2 (allOnes 6)), h0, h0']
    rw [natMap_pairVec_of_ne h2 hρ htv hij, natMap_pairVec_of_ne h2 hρ htv (Ne.symm hki)] at heq
    have heq' := Additive.ofMul.injective heq
    exact swapCentre_ne h2 hρ htv hij.symm (Ne.symm hki) (Ne.symm hkj)
      (by rw [swapCentre_comm, heq'])
  let f : evenWeight 6 → Additive V := fun x => natMap ρ h2 x
  have hni : ¬ Function.Injective f := by
    intro hinj
    have := Nat.card_le_card_of_injective f hinj
    rw [CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight 6 (by norm_num),
      show Nat.card (Additive V) = 16 from hV] at this
    norm_num at this
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨x, y, hxy, hne⟩ := hni
  set z : Fin 6 → ZMod 2 := (x : Fin 6 → ZMod 2) - y with hz
  have hz0 : natMap ρ h2 z = 0 := by
    rw [hz, map_sub]
    exact sub_eq_zero.mpr hxy
  have hzs : ∑ k, z k = 0 := (evenWeight 6).sub_mem x.2 y.2
  rcases evenWeight_six_cases z hzs with h | h | ⟨i, j, hij, h | h⟩
  · exact absurd (Subtype.ext (sub_eq_zero.mp (hz ▸ h))) hne
  · rwa [h] at hz0
  · rw [h, natMap_pairVec_of_ne h2 hρ htv hij] at hz0
    exact absurd (ofMul_eq_zero.mp hz0) (swapCentre_ne_one htv hij)
  · rw [h] at hz0
    exact absurd hz0 (h4 i j hij)

include hρ in
theorem eq_zero_or_allOnes_of_natMap (hV : Nat.card V = 16) {x : Fin 6 → ZMod 2}
    (hx : ∑ k, x k = 0) (h : natMap ρ h2 x = 0) : x = 0 ∨ x = allOnes 6 := by
  rcases evenWeight_six_cases x hx with rfl | rfl | ⟨i, j, hij, rfl | rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rw [natMap_pairVec_of_ne h2 hρ htv hij] at h
    exact absurd (ofMul_eq_zero.mp h) (swapCentre_ne_one htv hij)
  · rw [map_add, natMap_allOnes h2 hρ htv hV, zero_add,
      natMap_pairVec_of_ne h2 hρ htv hij] at h
    exact absurd (ofMul_eq_zero.mp h) (swapCentre_ne_one htv hij)

end Swap

end Natural

section Classify

theorem card_evenWeightOnes_six : Nat.card (evenWeightOnes 6) = 2 := by
  have hmem : allOnes 6 ∈ evenWeight 6 := by
    show ∑ _i : Fin 6, (1 : ZMod 2) = 0
    decide
  have hone : (⟨allOnes 6, hmem⟩ : evenWeight 6) ∈ evenWeightOnes 6 :=
    mem_evenWeightOnes_of_forall_eq (c := 1) fun _ => rfl
  rw [Nat.card_eq_two_iff' (0 : evenWeightOnes 6)]
  refine ⟨⟨⟨allOnes 6, hmem⟩, hone⟩, fun h => ?_, ?_⟩
  · have := congrArg (fun x : evenWeightOnes 6 => ((x : evenWeight 6) : Fin 6 → ZMod 2) 0) h
    simp [allOnes] at this
  · rintro ⟨⟨y, hy⟩, hy'⟩ hne
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hy'
    rcases zmod_two_cases c with rfl | rfl
    · exact absurd (Subtype.ext (Subtype.ext (funext hc))) hne
    · exact Subtype.ext (Subtype.ext (funext hc))

theorem card_altHeart_six : Nat.card (altHeart 6) = 16 := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (evenWeightOnes 6)
  rw [CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight 6 (by norm_num),
    card_evenWeightOnes_six] at h
  show Nat.card (evenWeight 6 ⧸ evenWeightOnes 6) = 16
  norm_num at h
  omega

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_mulEquiv_altHeart_of_isTv (h2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 16)
    {ρ : Perm (Fin 6) →* MulAut V} (hρ : Function.Injective ρ)
    (htv : Nat.card (commMap (ρ (swap 0 1))).range = 2) :
    ∃ ψ : Multiplicative (altHeart 6) ≃* V, ∀ σ (v : Multiplicative (altHeart 6)),
      ψ (Multiplicative.ofAdd (altAct σ v.toAdd)) = ρ σ (ψ v) := by
  let φ₀ : evenWeight 6 →+ Additive V := (natMap ρ h2).comp (evenWeight 6).subtype
  have hle : evenWeightOnes 6 ≤ φ₀.ker := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
    rw [AddMonoidHom.mem_ker]
    show natMap ρ h2 (x : Fin 6 → ZMod 2) = 0
    rcases zmod_two_cases c with rfl | rfl
    · rw [show (x : Fin 6 → ZMod 2) = 0 from funext hc, map_zero]
    · rw [show (x : Fin 6 → ZMod 2) = allOnes 6 from funext hc, natMap_allOnes h2 hρ htv hV]
  let φ : altHeart 6 →+ Additive V := QuotientAddGroup.lift (evenWeightOnes 6) φ₀ hle
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
    have hx0 : natMap ρ h2 (x : Fin 6 → ZMod 2) = 0 := hv
    rw [QuotientAddGroup.eq_zero_iff]
    rcases eq_zero_or_allOnes_of_natMap h2 hρ htv hV x.2 hx0 with h | h
    · exact mem_evenWeightOnes_of_forall_eq (c := 0) fun i => by rw [h]; rfl
    · exact mem_evenWeightOnes_of_forall_eq (c := 1) fun i => by rw [h]; rfl
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [card_altHeart_six]; exact hV.le)
  refine ⟨AddEquiv.toMultiplicativeLeft (AddEquiv.ofBijective φ hbij), fun σ v => ?_⟩
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd v)
  obtain rfl : v = Multiplicative.ofAdd (x : altHeart 6) := by rw [hx]; rfl
  show Additive.toMul (φ (altAct σ (x : altHeart 6))) = ρ σ (Additive.toMul (φ (x : altHeart 6)))
  rw [altAct_mk]
  show Additive.toMul (natMap ρ h2 (permVec σ (x : Fin 6 → ZMod 2))) =
    ρ σ (Additive.toMul (natMap ρ h2 (x : Fin 6 → ZMod 2)))
  rw [natMap_permVec h2 hρ htv σ x.2]
  rfl

theorem exists_mulEquiv_altHeart_of_injective (h2 : ∀ v : V, v * v = 1)
    (hV : Nat.card V = 16) (ρ : Perm (Fin 6) →* MulAut V) (hρ : Function.Injective ρ) :
    ∃ (β : Perm (Fin 6) ≃* Perm (Fin 6)) (ψ : Multiplicative (altHeart 6) ≃* V),
      ∀ σ (v : Multiplicative (altHeart 6)),
        ψ (Multiplicative.ofAdd (altAct σ v.toAdd)) = ρ (β σ) (ψ v) := by
  rcases card_commRange_swap_or_triple h2 hV ρ hρ with htv | htv
  · obtain ⟨ψ, hψ⟩ := exists_mulEquiv_altHeart_of_isTv h2 hV hρ htv
    exact ⟨MulEquiv.refl _, ψ, hψ⟩
  · let β : Perm (Fin 6) ≃* Perm (Fin 6) := CFSG.Quasithin.H13.U3.S6Out.phiEquiv
    have hinj : Function.Injective (ρ.comp β.toMonoidHom) := hρ.comp β.injective
    have htv' : Nat.card (commMap ((ρ.comp β.toMonoidHom) (swap 0 1))).range = 2 := by
      have e : β (swap 0 1) =
          swap 1 2 * (swap 0 1 * swap 2 3 * swap 4 5) * (swap 1 2)⁻¹ := by
        show CFSG.Quasithin.H13.U3.S6Out.phi (swap 0 1) = _
        decide
      show Nat.card (commMap (ρ (β (swap 0 1)))).range = 2
      rw [e, card_commRange_rho_conj, htv]
    obtain ⟨ψ, hψ⟩ := exists_mulEquiv_altHeart_of_isTv h2 hV hinj htv'
    exact ⟨β, ψ, hψ⟩

end Classify

end CFSG.CGT.Stroth77
