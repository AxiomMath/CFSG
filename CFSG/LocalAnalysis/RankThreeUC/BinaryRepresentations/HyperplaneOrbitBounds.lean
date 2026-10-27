module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialDimensionDivisibility
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

open Subgroup

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def minHyperplaneOrbit (p : ℕ) (X : Subgroup G) : ℕ :=
  sInf {c | ∃ D ∈ hyperplanes p X,
    c = Set.ncard {E : Subgroup G | ∃ g ∈ normalizer (X : Set G),
      E = CFSG.CGT.Timmesfeld75.conjSubgroup g D}}

@[expose] noncomputable def eOfPrime (p : ℕ) : ℕ :=
  if Even (WeakClosure.dOfPrime p) then WeakClosure.dOfPrime p else 2 * WeakClosure.dOfPrime p

namespace HyperplaneOrbitBounds

theorem two_v (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem key_pair (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X] (t : G)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) (hX2 : ∀ x ∈ X, x ^ 2 = 1 → x = 1)
    {u : V} (htu : ρ t u = u) (hN : normOp ρ X u = 0) :
    ∃ y ∈ Submodule.span (ZMod 2) {w | ∃ x ∈ X, w = ρ x u}, ρ t y - y = u := by
  classical
  obtain ⟨r⟩ : Nonempty (X ≃ Fin (Fintype.card X)) := ⟨Fintype.equivFin X⟩
  let c : X → Prop := fun a => (r a : ℕ) < r a⁻¹
  refine ⟨∑ a : X, if c a then ρ a u else 0, ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun a _ => ?_)
    split_ifs
    · exact Submodule.subset_span ⟨a, a.2, rfl⟩
    · exact Submodule.zero_mem _
  · have h1 : ∀ a : X, ρ t (ρ a u) = ρ (a⁻¹ : X) u := by
      intro a
      rw [← rho_mul_apply]
      have : t * (a : G) = ((a⁻¹ : X) : G) * t := by
        have := hinv a a.2
        simp only [Subgroup.coe_inv]
        calc t * (a:G) = (t * a * t⁻¹) * t := by group
          _ = _ := by rw [this]
      rw [this, rho_mul_apply, htu]
    rw [map_sum, ← Finset.sum_sub_distrib]
    have h3 : ∀ a : X, ρ t (if c a then ρ a u else 0) - (if c a then ρ a u else 0)
        = (if c a then ρ (a⁻¹ : X) u else 0) + (if c a then ρ a u else 0) := by
      intro a
      by_cases h : c a
      · simp only [h, if_true, h1]
        have := two_v (ρ a u)
        rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right this]
      · simp [h]
    rw [Finset.sum_congr rfl (fun a _ => h3 a), Finset.sum_add_distrib]
    have h4 : ∑ a : X, (if c a then ρ (a⁻¹ : X) u else 0) = ∑ a : X, (if c a⁻¹ then ρ a u else 0) :=
      Fintype.sum_equiv (Equiv.inv X) _ _ (fun a => by simp)
    rw [h4, ← Finset.sum_add_distrib]
    have h5 : ∀ a : X, ((if c a⁻¹ then ρ a u else 0) + (if c a then ρ a u else 0))
        = if a = 1 then 0 else ρ a u := by
      intro a
      by_cases ha : a = 1
      · subst ha; simp [c]
      · have hne : a⁻¹ ≠ a := by
          intro h
          apply ha
          have h2 : (a : G) ^ 2 = 1 := by
            have : (a⁻¹ : X) * a = 1 := by simp
            rw [h] at this
            have := congrArg Subtype.val this
            simpa [pow_two] using this
          exact Subtype.ext (hX2 a a.2 h2)
        have hr : (r a : ℕ) ≠ r a⁻¹ := fun h => hne (r.injective (Fin.ext h)).symm
        simp only [c, inv_inv, ha, if_false]
        rcases lt_or_gt_of_ne hr with h | h
        · simp [h, not_lt.2 h.le]
        · simp [h, not_lt.2 h.le]
    rw [Finset.sum_congr rfl (fun a _ => h5 a)]
    have h6 : ∑ a : X, (if a = 1 then (0 : V) else ρ a u) = normOp ρ X u - u := by
      rw [normOp_apply]
      have : ∑ a : X, ρ a u = ∑ a : X, (if a = 1 then u else 0) + ∑ a : X, (if a = 1 then (0 : V) else ρ a u) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        by_cases ha : a = 1 <;> simp [ha]
      rw [this, Finset.sum_ite_eq' Finset.univ (1 : X)]
      simp
    rw [h6, hN]; simp [neg_eq_of_add_eq_zero_right (two_v u)]

theorem finrank_eq_two_mul [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (X : Subgroup G) [Fintype X] (t : G) (ht : t * t = 1)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) (hX2 : ∀ x ∈ X, x ^ 2 = 1 → x = 1)
    (U : Submodule (ZMod 2) V) (hUt : ∀ u ∈ U, ρ t u ∈ U) (hUX : ∀ x ∈ X, ∀ u ∈ U, ρ x u ∈ U)
    (hN : ∀ u ∈ U, normOp ρ X u = 0) :
    Module.finrank (ZMod 2) U = 2 * Module.finrank (ZMod 2) (U.map ((ρ t : V →ₗ[ZMod 2] V) - 1)) := by
  classical
  set f : V →ₗ[ZMod 2] V := (ρ t : V →ₗ[ZMod 2] V) - 1 with hf
  have hfa : ∀ v, f v = ρ t v - v := fun v => by simp [hf]
  have hff : ∀ v, f (f v) = 0 := by
    intro v
    have h0 : ρ t (ρ t v) = v := by rw [← rho_mul_apply, ht]; simp
    rw [hfa, hfa, map_sub, h0]
    rw [show v - ρ t v - (ρ t v - v) = (v + v) - (ρ t v + ρ t v) by abel, two_v, two_v, sub_zero]
  have hRK : U.map f = U ⊓ LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hfa]; exact U.sub_mem (hUt u hu) hu
      · exact hff u
    · rintro v ⟨hvU, hv⟩
      have hv' : ρ t v = v := by have := (LinearMap.mem_ker.1 hv); rw [hfa] at this; exact sub_eq_zero.1 this
      obtain ⟨y, hy, hyv⟩ := key_pair ρ X t hinv hX2 hv' (hN v hvU)
      refine ⟨y, ?_, by rw [hfa]; exact hyv⟩
      refine Submodule.span_le.2 ?_ hy
      rintro _ ⟨x, hx, rfl⟩
      exact hUX x hx v hvU
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict] at h1
  have h2 : Module.finrank (ZMod 2) (LinearMap.ker (f.domRestrict U)) =
      Module.finrank (ZMod 2) (U.map f) := by
    rw [hRK, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
    congr 1
  omega

theorem comm_stable (ρ : Representation (ZMod 2) G V) {X : Subgroup G} {g : G}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {w : V} (hw : w ∈ commSpace ρ X) :
    ρ g w ∈ commSpace ρ X := by
  unfold commSpace at hw ⊢
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨g * x * g⁻¹, hg x hx, ρ g v, ?_⟩
    rw [map_sub, ← rho_mul_apply, ← rho_mul_apply]
    simp [mul_assoc]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem sq_eq_one {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) (x : G) (hxp : x ^ p = 1)
    (hx2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have : x ^ p = x := by
    rw [hk, pow_succ, pow_mul, hx2, one_pow, one_mul]
  rw [← this, hxp]

theorem fixed_inf_comm (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X]
    (hodd : Odd (Fintype.card X)) :
    fixedSpace ρ X ⊓ commSpace ρ X = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  have a := normOp_of_mem_fixedSpace ρ X h1
  rw [normOp_commSpace ρ X h2] at a
  have hc : ((Fintype.card X : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.2 hodd
  rw [hc, one_smul] at a
  simpa using a.symm

theorem sup_zpowers_eq {p : ℕ} (hp : p.Prime) {X D : Subgroup G} {x : G} (hx : x ∈ X)
    (hDX : D ≤ X) (hD : D.relIndex X = p) (hxD : x ∉ D) : D ⊔ zpowers x = X := by
  have hK : D ⊔ zpowers x ≤ X := sup_le hDX ((zpowers_le).2 hx)
  have h1 := Subgroup.relIndex_mul_relIndex D (D ⊔ zpowers x) X le_sup_left hK
  rw [hD] at h1
  have hdvd : (D ⊔ zpowers x).relIndex X ∣ p := ⟨(D.relIndex (D ⊔ zpowers x)), by rw [← h1]; ring⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact le_antisymm hK (Subgroup.relIndex_eq_one.1 h)
  · exfalso
    rw [h] at h1
    have h2 : D.relIndex (D ⊔ zpowers x) = 1 := by
      have := hp.pos
      nlinarith
    have := Subgroup.relIndex_eq_one.1 h2
    exact hxD (this ((le_sup_right : zpowers x ≤ D ⊔ zpowers x) (mem_zpowers x)))

theorem e_bound [Finite G] [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (X : Subgroup G) [Fintype X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXp : ∀ x ∈ X, x ^ p = 1)
    (hodd : Odd (Fintype.card X)) (t : G) (ht : t * t = 1)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹)
    (D : Subgroup G) (hDX : D ≤ X) (hD : D.relIndex X = p)
    (hne : commSpace ρ X ⊓ fixedSpace ρ D ≠ ⊥) :
    eOfPrime p ≤ Module.finrank (ZMod 2) ↥(commSpace ρ X ⊓ fixedSpace ρ D) := by
  have hp := (Fact.out : p.Prime)
  set W := commSpace ρ X with hW
  set U := W ⊓ fixedSpace ρ D with hU
  have hX2 : ∀ x ∈ X, x ^ 2 = 1 → x = 1 := fun x hx h => sq_eq_one hp2 hp x (hXp x hx) h
  have hWX : ∀ x ∈ X, ∀ w ∈ W, ρ x w ∈ W := fun x hx w hw =>
    comm_stable ρ (fun y hy => by
      have : x * y * x⁻¹ = y := by rw [hcomm x hx y hy]; group
      rw [this]; exact hy) hw
  have hWt : ∀ w ∈ W, ρ t w ∈ W := fun w hw =>
    comm_stable ρ (fun y hy => by
      have := hinv y hy
      have e : t * y * t⁻¹ = y⁻¹ := this
      rw [e]; exact X.inv_mem hy) hw
  have hUX : ∀ x ∈ X, ∀ u ∈ U, ρ x u ∈ U := by
    intro x hx u hu
    refine ⟨hWX x hx u hu.1, (mem_fixedSpace_iff ρ D _).2 (fun d hd => ?_)⟩
    rw [← rho_mul_apply, hcomm d (hDX hd) x hx, rho_mul_apply, (mem_fixedSpace_iff ρ D u).1 hu.2 d hd]
  have hUt : ∀ u ∈ U, ρ t u ∈ U := by
    intro u hu
    refine ⟨hWt u hu.1, (mem_fixedSpace_iff ρ D _).2 (fun d hd => ?_)⟩
    have e : d * t = t * d⁻¹ := by
      have := hinv d (hDX hd)
      calc d * t = t * (t⁻¹ * d * t) := by group
        _ = t * d⁻¹ := by
          have ti : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one]; exact ht
          rw [ti]
          have := hinv d (hDX hd)
          rw [ti] at this
          rw [this]
    rw [← rho_mul_apply, e, rho_mul_apply, (mem_fixedSpace_iff ρ D u).1 hu.2 d⁻¹ (D.inv_mem hd)]
  have hN : ∀ u ∈ U, normOp ρ X u = 0 := fun u hu => normOp_commSpace ρ X hu.1
  have heven := finrank_eq_two_mul ρ X t ht hinv hX2 U hUt hUX hN
  have hpos : 0 < Module.finrank (ZMod 2) U := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]; exact hne
  obtain ⟨x, hx, hxD⟩ : ∃ x ∈ X, x ∉ D := by
    by_contra hcon
    push Not at hcon
    have h1 : D.relIndex X = 1 := Subgroup.relIndex_eq_one.2 (fun x hx => hcon x hx)
    rw [hD] at h1; exact hp.one_lt.ne' h1
  have hsup := sup_zpowers_eq hp hx hDX hD hxD
  let ρU := ExtraspecialDimensionDivisibility.restrictRep ρ X U hUX
  let u := (MonoidHom.toHomUnits ρU) ⟨x, hx⟩
  let σ : U ≃ₗ[ZMod 2] U := LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ u
  have hσp : σ ^ p = 1 := by
    have : u ^ p = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : X) ^ p = 1 := Subtype.ext (hXp x hx)
      rw [this, map_one]
    rw [← map_pow, this, map_one]
  have hσ : ∀ w : U, σ w = ρU ⟨x, hx⟩ w := fun w => rfl
  have key := CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension.orderOf_two_dvd_finrank p hp2 σ hσp ?_
  · rw [← WeakClosure.dOfPrime_eq_orderOf hp hp2] at key
    have hdvd2 : 2 ∣ Module.finrank (ZMod 2) U := ⟨_, heven⟩
    unfold eOfPrime
    split_ifs with he
    · exact Nat.le_of_dvd hpos key
    · have hcop : Nat.Coprime (WeakClosure.dOfPrime p) 2 := by
        rw [Nat.coprime_two_right]; exact Nat.not_even_iff_odd.1 he
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop key hdvd2
      rw [mul_comm] at this
      exact Nat.le_of_dvd hpos this
  · rw [eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hfx : ρ x (w : V) = w := by
      have : σ w - w = 0 := by simpa using hw
      have := sub_eq_zero.1 this
      rw [hσ] at this
      exact congrArg Subtype.val this
    have hwx : (w : V) ∈ fixedSpace ρ (zpowers x) := by
      rw [mem_fixedSpace_iff]
      intro g hg
      obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 hg
      have hk' : x ^ k = g := hk
      rw [← hk']
      clear hk hk'
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ, rho_mul_apply, hfx, ihk]
    have hwX := mem_fixedSpace_sup ρ D (zpowers x) w.2.2 hwx
    rw [hsup] at hwX
    have : (w : V) ∈ fixedSpace ρ X ⊓ commSpace ρ X := ⟨hwX, w.2.1⟩
    rw [fixed_inf_comm ρ X hodd] at this
    simpa using this

theorem fixed_map (ρ : Representation (ZMod 2) G V) (X : Subgroup G) (W : Submodule (ZMod 2) V)
    (hWX : ∀ x ∈ X, ∀ w ∈ W, ρ x w ∈ W) (D' : Subgroup X) :
    (fixedSpace (ExtraspecialDimensionDivisibility.restrictRep ρ X W hWX) D').map W.subtype =
      W ⊓ fixedSpace ρ (D'.map X.subtype) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, (mem_fixedSpace_iff ρ _ _).2 ?_⟩
    rintro g ⟨d, hd, rfl⟩
    have := (mem_fixedSpace_iff _ D' w).1 hw d hd
    exact congrArg Subtype.val this
  · rintro ⟨hvW, hv⟩
    refine ⟨⟨v, hvW⟩, (mem_fixedSpace_iff _ D' _).2 (fun d hd => ?_), rfl⟩
    apply Subtype.ext
    exact (mem_fixedSpace_iff ρ _ v).1 hv d ⟨d, hd, rfl⟩

theorem relIndex_map_sub {X : Subgroup G} (D' : Subgroup X) :
    (D'.map X.subtype).relIndex X = D'.index := by
  have := Subgroup.relIndex_map_map_of_injective D' ⊤ (f := X.subtype) X.subtype_injective
  rw [Subgroup.relIndex_top_right] at this
  rw [← this]
  congr 1
  ext x; simp

theorem finrank_commSpace_eq_two_mul_iterated_commutator [Finite G] [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (X : Subgroup G) [Fintype X] (t : G) (ht : orderOf t = 2)
    (hodd : Odd (Fintype.card X)) (hX2 : ∀ x ∈ X, x ^ 2 = 1 → x = 1)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Module.finrank (ZMod 2) ↥(commSpace ρ X) =
        2 * Module.finrank (ZMod 2) ↥(commOn ρ (zpowers t) (commSpace ρ X)) := by
  have htt : t * t = 1 := by rw [← pow_two]; exact pow_eq_one_iff_modEq.mpr (by simp [ht])
  set W := commSpace ρ X with hW
  have hWX : ∀ x ∈ X, ∀ w ∈ W, ρ x w ∈ W := fun x hx w hw =>
    comm_stable ρ (fun y hy => by
      have : x * y * x⁻¹ = y := by rw [hcomm x hx y hy]; group
      rw [this]; exact hy) hw
  have hWt : ∀ w ∈ W, ρ t w ∈ W := fun w hw =>
    comm_stable ρ (fun y hy => by
      have e : t * y * t⁻¹ = y⁻¹ := hinv y hy
      rw [e]; exact X.inv_mem hy) hw
  have h := finrank_eq_two_mul ρ X t htt hinv hX2 W hWt hWX (fun u hu => normOp_commSpace ρ X hu)
  suffices hmap : Submodule.map ((ρ t : V →ₗ[ZMod 2] V) - 1) W = commOn ρ (zpowers t) W by
    rw [h, hmap]
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨t, mem_zpowers t, u, hu, by simp⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rw [← zpow_mod_orderOf, ht]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · simp only [Nat.cast_ofNat, h0]; exact ⟨0, W.zero_mem, by simp⟩
    · simp only [Nat.cast_ofNat, h1]
      exact ⟨u, hu, by simp⟩

theorem minHyperplaneOrbit_degree_le_finrank_commSpace [Finite G] [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (t : G) (ht : t * t = 1) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 0 < n) (X : Subgroup G) [Fintype X] (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hXp : ∀ x ∈ X, x ^ p = 1) (hXcard : Nat.card X = p ^ n)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) :
    max n (minHyperplaneOrbit p X) * eOfPrime p ≤ Module.finrank (ZMod 2) ↥(commSpace ρ X) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hpodd := hp.odd_of_ne_two hp2
  have hodd : Odd (Fintype.card X) := by
    rw [Fintype.card_eq_nat_card, hXcard]; exact hpodd.pow
  have hX2 : ∀ x ∈ X, x ^ 2 = 1 → x = 1 := fun x hx h => sq_eq_one hp2 hp x (hXp x hx) h
  set W := commSpace ρ X with hW
  have hWX : ∀ x ∈ X, ∀ w ∈ W, ρ x w ∈ W := fun x hx w hw =>
    comm_stable ρ (fun y hy => by
      have : x * y * x⁻¹ = y := by rw [hcomm x hx y hy]; group
      rw [this]; exact hy) hw
  have hWt : ∀ w ∈ W, ρ t w ∈ W := fun w hw =>
    comm_stable ρ (fun y hy => by
      have e : t * y * t⁻¹ = y⁻¹ := hinv y hy
      rw [e]; exact X.inv_mem hy) hw
  let ρ' := ExtraspecialDimensionDivisibility.restrictRep ρ X W hWX
  have hfix : fixedSpace ρ' ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : (w : V) ∈ fixedSpace ρ X := by
      rw [mem_fixedSpace_iff]
      intro x hx
      exact congrArg Subtype.val ((mem_fixedSpace_iff ρ' ⊤ w).1 hw ⟨x, hx⟩ trivial)
    have : (w : V) ∈ fixedSpace ρ X ⊓ commSpace ρ X := ⟨h1, w.2⟩
    rw [fixed_inf_comm ρ X hodd] at this
    simpa using this
  have htop : commSpace ρ' ⊤ = ⊤ :=
    ExtraspecialDimensionDivisibility.commSpace_eq_top ρ' ⊤
      (by rw [Subgroup.card_top, Nat.card_eq_fintype_card]; exact hodd) hfix
  have hA : CFSG.Open.IsElemAbelian p (⊤ : Subgroup X) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm a.1.1 a.1.2 b.1.1 b.1.2))⟩⟩,
      fun x _ => Subtype.ext (hXp x.1 x.2)⟩
  have hint := coprime_hyperplane_decomposition (q := 2) hp2 ρ' ⊤ hA htop
  haveI : Finite (Subgroup X) := inferInstance
  haveI : Fintype (hyperplanes p (⊤ : Subgroup X)) := Fintype.ofFinite _
  have hsum : Module.finrank (ZMod 2) W =
      ∑ D : hyperplanes p (⊤ : Subgroup X), Module.finrank (ZMod 2) (fixedSpace ρ' D.1) := by
    have e := LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (fun D : hyperplanes p (⊤ : Subgroup X) => fixedSpace ρ' D.1)) hint
    rw [← e.finrank_eq, Module.finrank_directSum]
  set S' := Finset.univ.filter (fun D : hyperplanes p (⊤ : Subgroup X) => fixedSpace ρ' D.1 ≠ ⊥)
    with hS'
  have hDe : ∀ D ∈ S', eOfPrime p ≤ Module.finrank (ZMod 2) (fixedSpace ρ' D.1) := by
    intro D hD
    have hDne : fixedSpace ρ' D.1 ≠ ⊥ := (Finset.mem_filter.1 hD).2
    have hmap := fixed_map ρ X W hWX D.1
    have hne : W ⊓ fixedSpace ρ (D.1.map X.subtype) ≠ ⊥ := by
      rw [← hmap]
      obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hDne
      exact (Submodule.ne_bot_iff _).2 ⟨W.subtype w, ⟨w, hw, rfl⟩, by simpa using hw0⟩
    have := e_bound ρ X hp2 hcomm hXp hodd t ht hinv (D.1.map X.subtype)
      (Subgroup.map_subtype_le _) (by rw [relIndex_map_sub, ← Subgroup.relIndex_top_right]; exact D.2.2) hne
    rw [← hmap, Submodule.finrank_map_subtype_eq] at this
    exact this
  have hS'e : S'.card * eOfPrime p ≤ Module.finrank (ZMod 2) W := by
    rw [hsum]
    calc S'.card * eOfPrime p = ∑ _D ∈ S', eOfPrime p := by simp
      _ ≤ ∑ D ∈ S', Module.finrank (ZMod 2) (fixedSpace ρ' D.1) := Finset.sum_le_sum hDe
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hS'ne : ∀ D ∈ S', W ⊓ fixedSpace ρ (D.1.map X.subtype) ≠ ⊥ := by
    intro D hD
    have hDne : fixedSpace ρ' D.1 ≠ ⊥ := (Finset.mem_filter.1 hD).2
    rw [← fixed_map ρ X W hWX D.1]
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hDne
    exact (Submodule.ne_bot_iff _).2 ⟨W.subtype w, ⟨w, hw, rfl⟩, by simpa using hw0⟩
  have hn_le : n ≤ S'.card := by
    have hx1 : ∀ x : X, (∀ D ∈ S', x ∈ D.1) → x = 1 := by
      intro x hx
      have hK : (⨆ D : hyperplanes p (⊤ : Subgroup X), fixedSpace ρ' D.1) ≤
          LinearMap.ker ((ρ' x : W →ₗ[ZMod 2] W) - 1) := by
        refine iSup_le (fun D => ?_)
        by_cases hD : D ∈ S'
        · intro w hw
          rw [LinearMap.mem_ker]
          have := (mem_fixedSpace_iff ρ' D.1 w).1 hw x (hx D hD)
          simp [this]
        · have : fixedSpace ρ' D.1 = ⊥ := by
            by_contra h
            exact hD (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
          rw [this]; exact bot_le
      rw [hint.submodule_iSup_eq_top] at hK
      have hW1 : ∀ w ∈ W, ρ x w = w := by
        intro w hw
        have := hK (Submodule.mem_top : (⟨w, hw⟩ : W) ∈ ⊤)
        rw [LinearMap.mem_ker] at this
        have h2 : ρ' x ⟨w, hw⟩ = ⟨w, hw⟩ := sub_eq_zero.1 (by simpa using this)
        exact congrArg Subtype.val h2
      have hsq : ρ (x.1 * x.1) = ρ 1 := by
        ext v
        have hg : ρ x v - v ∈ W := Submodule.subset_span ⟨x.1, x.2, v, rfl⟩
        have h := hW1 _ hg
        rw [map_sub] at h
        rw [rho_mul_apply]
        simp only [map_one, Module.End.one_apply]
        have : ρ x (ρ x v) = (ρ x v - v) + ρ x v := by
          rw [← sub_eq_zero] at h ⊢
          rw [← h]; abel
        rw [this, show ρ (x:G) v - v + ρ (x:G) v = (ρ x v + ρ x v) - v by abel, two_v, zero_sub]
        exact neg_eq_of_add_eq_zero_right (two_v v)
      have := hρ hsq
      exact Subtype.ext (hX2 x.1 x.2 (by rw [pow_two]; exact this))
    by_contra hlt
    push Not at hlt
    have hbot : (⨅ D : S', (D.1.1 : Subgroup X)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_iInf] at hx
      exact (Subgroup.mem_bot).2 (hx1 x (fun D hD => hx ⟨D, hD⟩))
    have h1 := Subgroup.index_iInf_le (fun D : S' => (D.1.1 : Subgroup X))
    rw [hbot, Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_eq_nat_card, hXcard] at h1
    have h2 : ∀ D : S', (D.1.1 : Subgroup X).index = p := fun D => by
      have := D.1.2.2
      rw [Subgroup.relIndex_top_right] at this; exact this
    simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_coe] at h1
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    omega
  set SG : Set (Subgroup G) := {D | D ∈ hyperplanes p X ∧ W ⊓ fixedSpace ρ D ≠ ⊥} with hSG
  have hSGfin : SG.Finite := Set.toFinite _
  have hSGle : SG.ncard ≤ S'.card := by
    have hsub : SG ⊆ (fun D : hyperplanes p (⊤ : Subgroup X) => D.1.map X.subtype) '' (S' : Set _) := by
      rintro D ⟨⟨hDX, hDi⟩, hDne⟩
      have hmapcomap : (D.comap X.subtype).map X.subtype = D := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩; exact hz
        · intro hy; exact ⟨⟨y, hDX hy⟩, hy, rfl⟩
      have hidx : (D.comap X.subtype).relIndex ⊤ = p := by
        rw [Subgroup.relIndex_top_right, ← relIndex_map_sub, hmapcomap]; exact hDi
      refine ⟨⟨D.comap X.subtype, le_top, hidx⟩, ?_, hmapcomap⟩
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      intro hbot
      apply hDne
      have := fixed_map ρ X W hWX (D.comap X.subtype)
      rw [hbot, hmapcomap, Submodule.map_bot] at this
      exact this.symm
    calc SG.ncard ≤ ((fun D : hyperplanes p (⊤ : Subgroup X) => D.1.map X.subtype) '' (S' : Set _)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (S' : Set (hyperplanes p (⊤ : Subgroup X))).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = S'.card := Set.ncard_coe_finset S'
  have hr_le : minHyperplaneOrbit p X ≤ S'.card := by
    have hne : S'.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨D1, hD1⟩ := hne
    set D0 := D1.1.map X.subtype with hD0
    have hD0SG : D0 ∈ SG := ⟨⟨Subgroup.map_subtype_le _, by
      rw [hD0, relIndex_map_sub, ← Subgroup.relIndex_top_right]; exact D1.2.2⟩, hS'ne D1 hD1⟩
    set O : Set (Subgroup G) := {E | ∃ g ∈ normalizer (X : Set G),
      E = CFSG.CGT.Timmesfeld75.conjSubgroup g D0} with hO
    have hOsub : O ⊆ SG := by
      rintro E ⟨g, hg, rfl⟩
      rw [Subgroup.mem_normalizer_iff] at hg
      have hgX : ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun x hx => (hg x).1 hx
      have hgX' : ∀ x, g * x * g⁻¹ ∈ X → x ∈ X := fun x hx => (hg x).2 hx
      have hEX : CFSG.CGT.Timmesfeld75.conjSubgroup g D0 ≤ X := by
        rintro _ ⟨d, hd, rfl⟩
        exact hgX d (hD0SG.1.1 hd)
      have hXmap : X.map (MulAut.conj g).toMonoidHom = X := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩; exact hgX z hz
        · intro hy
          refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
          apply hgX'
          simpa [mul_assoc] using hy
      refine ⟨⟨hEX, ?_⟩, ?_⟩
      · have := Subgroup.relIndex_map_map_of_injective D0 X (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective
        rw [hXmap] at this
        unfold CFSG.CGT.Timmesfeld75.conjSubgroup
        rw [this]; exact hD0SG.1.2
      · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hD0SG.2
        refine (Submodule.ne_bot_iff _).2 ⟨ρ g w, ⟨comm_stable ρ hgX hw.1, ?_⟩, ?_⟩
        · show ρ g w ∈ fixedSpace ρ _
          rw [mem_fixedSpace_iff]
          rintro _ ⟨d, hd, rfl⟩
          have : (MulAut.conj g).toMonoidHom d = g * d * g⁻¹ := rfl
          rw [this, ← rho_mul_apply, show g * d * g⁻¹ * g = g * d by group, rho_mul_apply,
            (mem_fixedSpace_iff ρ D0 w).1 hw.2 d hd]
        · intro h
          apply hw0
          have := congrArg (ρ g⁻¹) h
          rw [← rho_mul_apply] at this
          simpa using this
    have h1 : minHyperplaneOrbit p X ≤ O.ncard := by
      unfold minHyperplaneOrbit
      exact Nat.sInf_le ⟨D0, hD0SG.1, rfl⟩
    exact h1.trans ((Set.ncard_le_ncard hOsub hSGfin).trans hSGle)
  exact (Nat.mul_le_mul_right _ (max_le hn_le hr_le)).trans hS'e

end HyperplaneOrbitBounds

open scoped Classical in
theorem finrank_commutator_eq_two_mul_and_involution_rank_bound [Finite G] [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (t : G) (ht : orderOf t = 2)
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (X : Subgroup G) (hXab : CFSG.Assembly.IsElemAbelian p X) (hXcard : Nat.card X = p ^ n)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) :
    Module.finrank (ZMod 2) ↥(commSpace ρ X) =
        2 * Module.finrank (ZMod 2) ↥(commOn ρ (zpowers t) (commSpace ρ X)) ∧
      max n (minHyperplaneOrbit p X) * eOfPrime p ≤
        2 * Module.finrank (ZMod 2) ↥(commSpace ρ (zpowers t)) := by
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => by
    have := hXab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hXp : ∀ x ∈ X, x ^ p = 1 := hXab.2
  have hodd : Odd (Fintype.card X) := by
    rw [Fintype.card_eq_nat_card, hXcard]; exact (hp.odd_of_ne_two hp2).pow
  have hX2 : ∀ x ∈ X, x ^ 2 = 1 → x = 1 := fun x hx h => HyperplaneOrbitBounds.sq_eq_one hp2 hp x (hXp x hx) h
  have htt : t * t = 1 := by rw [← pow_two]; exact pow_eq_one_iff_modEq.mpr (by simp [ht])
  have h1 := HyperplaneOrbitBounds.finrank_commSpace_eq_two_mul_iterated_commutator ρ X t ht hodd hX2 hinv hcomm
  refine ⟨h1, ?_⟩
  have h2 := HyperplaneOrbitBounds.minHyperplaneOrbit_degree_le_finrank_commSpace ρ hρ t htt hp2 hn X hcomm hXp hXcard hinv
  have hle : commOn ρ (zpowers t) (commSpace ρ X) ≤ commSpace ρ (zpowers t) :=
    Submodule.span_mono (fun w ⟨x, hx, u, _, e⟩ => ⟨x, hx, u, e⟩)
  have h3 := Submodule.finrank_mono hle
  omega

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
