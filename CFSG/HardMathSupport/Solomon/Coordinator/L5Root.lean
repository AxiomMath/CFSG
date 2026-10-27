module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Lift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.Proving

variable {L S : Type*} [Group L] [Group S] [Finite L] {Γ : L →* S}

omit [Finite L] in
theorem pow_odd_eq_one_of_mem_ker {m : ℕ} (hm : Nat.card Γ.ker = 2 * m + 1) {w : L}
    (hw : w ∈ Γ.ker) : w ^ (2 * m + 1) = 1 := by
  have := pow_card_eq_one' (G := Γ.ker) (x := ⟨w, hw⟩)
  rw [hm] at this
  exact congrArg Subtype.val this

omit [Finite L] in
theorem eq_of_two_lift (hZ : Γ.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card Γ.ker)) {u v : L}
    {e : ℕ} (hu : u ^ 2 ^ e = 1) (hv : v ^ 2 ^ e = 1) (huv : Γ u = Γ v) : u = v := by
  obtain ⟨m, hm⟩ := hodd
  have hz : u⁻¹ * v ∈ Γ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
  set z := u⁻¹ * v with hzdef
  have hzc : ∀ y : L, z * y = y * z := fun y => (Subgroup.mem_center_iff.1 (hZ hz) y).symm
  have hv' : v = u * z := by rw [hzdef, mul_inv_cancel_left]
  have hz2 : z ^ 2 ^ e = 1 := by
    have h1 : (u * z) ^ 2 ^ e = u ^ 2 ^ e * z ^ 2 ^ e :=
      (show Commute u z from (hzc u).symm).mul_pow _
    rw [← hv', hv, hu, one_mul] at h1
    exact h1.symm
  have hd1 : orderOf z ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hz2
  have hd2 : orderOf z ∣ 2 * m + 1 := orderOf_dvd_of_pow_eq_one (pow_odd_eq_one_of_mem_ker hm hz)
  have hcop : Nat.Coprime (2 ^ e) (2 * m + 1) :=
    Nat.Coprime.pow_left e (Odd.coprime_two_left ⟨m, rfl⟩)
  have hz1 : z = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  rw [hv', hz1, mul_one]

omit [Finite L] in
theorem exists_two_lift (hΓ : Function.Surjective Γ) (hodd : Odd (Nat.card Γ.ker)) {g : S} {e : ℕ}
    (hg : g ^ 2 ^ e = 1) : ∃ u : L, Γ u = g ∧ u ^ 2 ^ e = 1 := by
  obtain ⟨m, hm⟩ := hodd
  have hcop : Nat.Coprime (2 * m + 1) (orderOf g) :=
    (Nat.Coprime.pow_right e (Odd.coprime_two_right ⟨m, rfl⟩)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  obtain ⟨x, rfl⟩ := hΓ g
  refine ⟨x ^ ((2 * m + 1) * c), by rw [map_pow, pow_mul, hc], ?_⟩
  have h1 : x ^ 2 ^ e ∈ Γ.ker := by rw [MonoidHom.mem_ker, map_pow, hg]
  calc (x ^ ((2 * m + 1) * c)) ^ 2 ^ e = ((x ^ 2 ^ e) ^ (2 * m + 1)) ^ c := by
        rw [← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = 1 := by rw [pow_odd_eq_one_of_mem_ker hm h1, one_pow]

@[expose] def twoLiftSet (Ubar : Subgroup S) : Set L :=
  {x | Γ x ∈ Ubar ∧ ∃ e : ℕ, x ^ 2 ^ e = 1}

omit [Finite L] in
theorem commute_of_two_lift (hZ : Γ.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card Γ.ker))
    {Ubar : Subgroup S} (hUc : IsMulCommutative Ubar) {u v : L} (hu : u ∈ twoLiftSet (Γ := Γ) Ubar)
    (hv : v ∈ twoLiftSet (Γ := Γ) Ubar) : Commute u v := by
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨huU, e, he⟩ := hu
  have hc : u * v * u⁻¹ * v⁻¹ ∈ Γ.ker := by
    have := congrArg Subtype.val (hUc.is_comm.comm (⟨Γ u, huU⟩ : Ubar) ⟨Γ v, hv.1⟩)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    change Γ u * Γ v = Γ v * Γ u at this
    rw [this]
    group
  set z := u * v * u⁻¹ * v⁻¹ with hzdef
  have hzc : ∀ y : L, z * y = y * z := fun y => (Subgroup.mem_center_iff.1 (hZ hc) y).symm
  have hconj : u * v * u⁻¹ = z * v := by rw [hzdef]; group
  have hk : ∀ k : ℕ, u ^ k * v * (u ^ k)⁻¹ = z ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc u ^ (k + 1) * v * (u ^ (k + 1))⁻¹ = u * (u ^ k * v * (u ^ k)⁻¹) * u⁻¹ := by group
        _ = u * (z ^ k * v) * u⁻¹ := by rw [ih]
        _ = z ^ k * (u * v * u⁻¹) := by
            have hzu : u * z ^ k = z ^ k * u := (((show Commute z u from hzc u).pow_left k)).symm.eq
            rw [← mul_assoc, hzu]
            group
        _ = z ^ (k + 1) * v := by rw [hconj, ← mul_assoc, ← pow_succ]
  have h2 := hk (2 ^ e)
  rw [he, one_mul, inv_one, mul_one] at h2
  have hz2 : z ^ 2 ^ e = 1 := by
    have := congrArg (· * v⁻¹) h2
    simpa using this.symm
  have hd1 : orderOf z ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hz2
  have hd2 : orderOf z ∣ 2 * m + 1 := orderOf_dvd_of_pow_eq_one (pow_odd_eq_one_of_mem_ker hm hc)
  have hcop : Nat.Coprime (2 ^ e) (2 * m + 1) :=
    Nat.Coprime.pow_left e (Odd.coprime_two_left ⟨m, rfl⟩)
  have hz1 : z = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  rw [hzdef, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hz1
  exact hz1

@[expose] def twoLift (hZ : Γ.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card Γ.ker))
    (Ubar : Subgroup S) (hUc : IsMulCommutative Ubar) : Subgroup L where
  carrier := twoLiftSet (Γ := Γ) Ubar
  mul_mem' {a b} ha hb := by
    refine ⟨by rw [map_mul]; exact Ubar.mul_mem ha.1 hb.1, ?_⟩
    obtain ⟨e₁, he₁⟩ := ha.2
    obtain ⟨e₂, he₂⟩ := hb.2
    refine ⟨e₁ + e₂, ?_⟩
    rw [(commute_of_two_lift hZ hodd hUc ha hb).mul_pow, pow_add, pow_mul, he₁, one_pow,
      one_mul, mul_comm, pow_mul, he₂, one_pow]
  one_mem' := ⟨by rw [map_one]; exact Ubar.one_mem, 0, by simp⟩
  inv_mem' {a} ha := by
    refine ⟨by rw [map_inv]; exact Ubar.inv_mem ha.1, ?_⟩
    obtain ⟨e, he⟩ := ha.2
    exact ⟨e, by rw [inv_pow, he, inv_one]⟩

section TwoLift

variable (hΓ : Function.Surjective Γ) (hZ : Γ.ker ≤ Subgroup.center L)
  (hodd : Odd (Nat.card Γ.ker)) {Ubar : Subgroup S} (hUc : IsMulCommutative Ubar)

theorem isPGroup_twoLift : IsPGroup 2 (twoLift hZ hodd Ubar hUc) := by
  intro x
  obtain ⟨-, e, he⟩ := x.2
  exact ⟨e, Subtype.ext he⟩

include hΓ in
theorem map_twoLift (hU2 : IsPGroup 2 Ubar) : (twoLift hZ hodd Ubar hUc).map Γ = Ubar := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  · intro g hg
    obtain ⟨e, he⟩ := hU2 ⟨g, hg⟩
    have he' : g ^ 2 ^ e = 1 := congrArg Subtype.val he
    obtain ⟨u, hu, hu2⟩ := exists_two_lift hΓ hodd he'
    exact ⟨u, ⟨by rw [hu]; exact hg, e, hu2⟩, hu⟩

theorem mem_normalizer_twoLift {g : L} (hg : Γ g ∈ Subgroup.normalizer (Ubar : Set S)) :
    g ∈ Subgroup.normalizer ((twoLift hZ hodd Ubar hUc : Subgroup L) : Set L) := by
  have key : ∀ g' : L, Γ g' ∈ Subgroup.normalizer (Ubar : Set S) → ∀ y : L,
      y ∈ twoLift hZ hodd Ubar hUc → g' * y * g'⁻¹ ∈ twoLift hZ hodd Ubar hUc := by
    intro g' hg' y hy
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hg' _).1 hy.1
    · obtain ⟨e, he⟩ := hy.2
      exact ⟨e, by rw [conj_pow, he, mul_one, mul_inv_cancel]⟩
  have hg' : Γ g⁻¹ ∈ Subgroup.normalizer (Ubar : Set S) := by
    rw [map_inv]; exact Subgroup.inv_mem _ hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ hg' _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem twoLift_fixed {β : MulAut L} {b : MulAut S} (hβ : ∀ x, Γ (β x) = b (Γ x))
    (hUfix : ∀ u ∈ Ubar, b u = u) {u : L} (hu : u ∈ twoLift hZ hodd Ubar hUc) : β u = u := by
  obtain ⟨huU, e, he⟩ := hu
  refine eq_of_two_lift hZ hodd (e := e) (by rw [← map_pow, he, map_one]) he ?_
  rw [hβ, hUfix _ huU]

include hΓ in
theorem twoLift_ne_bot (hU2 : IsPGroup 2 Ubar) (hU1 : Ubar ≠ ⊥) :
    twoLift hZ hodd Ubar hUc ≠ ⊥ := by
  intro h
  apply hU1
  rw [← map_twoLift hΓ hZ hodd hUc hU2, h, Subgroup.map_bot]

end TwoLift

section Torus

variable {p r : ℕ} [NeZero r]

theorem hasTorusFixed_one_of_root (hp : p.Prime) (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (D : TorusData (Fin r) p S) (hcard : Nat.card (Subgroup.closure (Set.range D.X)) = p ^ r)
    (Ubar : Subgroup S) (hUc : IsMulCommutative Ubar) (hU2 : IsPGroup 2 Ubar) (hU1 : Ubar ≠ ⊥)
    (hXU : ∀ k, D.X k ∈ Subgroup.normalizer (Ubar : Set S)) : HasTorusFixed p r L 1 := by
  have hodd' : Odd (Nat.card Γ.ker) := by rw [hker]; exact hodd
  obtain ⟨E, hE, hEker, hEmap⟩ := exists_cover_torus hp D Γ hΓ hker.le hodd'
  refine ⟨E, twoLift hker.le hodd' Ubar hUc, hE, ?_, by rw [← hker]; exact hEker,
    twoLift_ne_bot hΓ hker.le hodd' hUc hU2 hU1, isPGroup_twoLift hker.le hodd' hUc, ?_,
    fun x _ => rfl, fun u hu => hu⟩
  · have hinj : Function.Injective (Γ.domRestrict E) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : L) ∈ E ⊓ Γ.ker := ⟨x.2, hx⟩
      rw [hEker, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    rw [← hcard, ← hEmap, ← MonoidHom.domRestrict_range]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  · intro x hx
    refine mem_normalizer_twoLift hker.le hodd' hUc ?_
    have hle : Subgroup.closure (Set.range D.X) ≤ Subgroup.normalizer (Ubar : Set S) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact hXU k
    exact hle (hEmap ▸ Subgroup.mem_map_of_mem Γ hx)

theorem hasTorusFixed_of_fixData_root (hp : p.Prime) (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center L) (hodd : Odd (Nat.card (Subgroup.center L)))
    {β : MulAut L} {b : MulAut S} (hβ : ∀ x, Γ (β x) = b (Γ x))
    (D : TorusData (Fin r) p ↥((autFix β).map Γ))
    (hcard : Nat.card (Subgroup.closure (Set.range D.X)) = p ^ r)
    (Ubar : Subgroup S) (hUc : IsMulCommutative Ubar) (hU2 : IsPGroup 2 Ubar) (hU1 : Ubar ≠ ⊥)
    (hUfix : ∀ u ∈ Ubar, b u = u)
    (hXU : ∀ k, ((D.X k : ↥((autFix β).map Γ)) : S) ∈ Subgroup.normalizer (Ubar : Set S)) :
    HasTorusFixed p r L β := by
  classical
  have hodd' : Odd (Nat.card Γ.ker) := by rw [hker]; exact hodd
  let Γ' : ↥(autFix β) →* ↥((autFix β).map Γ) :=
    (Γ.comp (autFix β).subtype).codRestrict ((autFix β).map Γ) (fun x => ⟨x, x.2, rfl⟩)
  have hΓ'apply : ∀ x : ↥(autFix β), ((Γ' x : ↥((autFix β).map Γ)) : S) = Γ x := fun x => rfl
  have hΓ's : Function.Surjective Γ' := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker' : ∀ x : ↥(autFix β), x ∈ Γ'.ker ↔ (x : L) ∈ Γ.ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hΓ'apply]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hZ' : Γ'.ker ≤ Subgroup.center ↥(autFix β) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxZ : (x : L) ∈ Subgroup.center L := hker ▸ (hker' x).1 hx
    exact Subgroup.mem_center_iff.1 hxZ y
  have hodd'' : Odd (Nat.card Γ'.ker) := by
    have hle : (Γ'.ker.map (autFix β).subtype) ≤ Subgroup.center L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker ▸ (hker' x).1 hx
    have hdvd : Nat.card Γ'.ker ∣ Nat.card (Subgroup.center L) := by
      rw [← Subgroup.card_map_of_injective (autFix β).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨E, hE, hEker, hEmap⟩ := exists_cover_torus hp D Γ' hΓ's hZ' hodd''
  set U := twoLift hker.le hodd' Ubar hUc with hU
  refine ⟨E.map (autFix β).subtype, U, ?_, ?_, ?_, twoLift_ne_bot hΓ hker.le hodd' hUc hU2 hU1,
    isPGroup_twoLift hker.le hodd' hUc, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      show (x : L) * y = y * x
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      exact congrArg Subtype.val this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  · have hinj : Function.Injective (Γ'.domRestrict E) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : ↥(autFix β)) ∈ E ⊓ Γ'.ker := ⟨x.2, hx⟩
      rw [hEker, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have h1 : Nat.card (E.map Γ') = Nat.card E := by
      have h2 : (Γ'.domRestrict E).range = E.map Γ' := MonoidHom.domRestrict_range (K := E) Γ'
      have h3 := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rwa [h2] at h3
    rw [hEmap, hcard] at h1
    rw [Subgroup.card_map_of_injective (autFix β).subtype_injective, ← h1]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxZ⟩
    have hxk : x ∈ Γ'.ker := (hker' x).2 (by rw [hker]; exact hxZ)
    have : x ∈ E ⊓ Γ'.ker := ⟨hx, hxk⟩
    rw [hEker, Subgroup.mem_bot] at this
    rw [this]
    rfl
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_normalizer_twoLift hker.le hodd' hUc ?_
    have hle : Subgroup.closure (Set.range D.X) ≤
        (Subgroup.normalizer (Ubar : Set S)).comap ((autFix β).map Γ).subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact hXU k
    have hxmem : Γ' x ∈ Subgroup.closure (Set.range D.X) := hEmap ▸ Subgroup.mem_map_of_mem Γ' hx
    exact hle hxmem
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · intro u hu
    rw [twoLift_fixed hker.le hodd' hUc hβ hUfix hu]
    exact hu

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator
