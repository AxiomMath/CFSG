module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.Simproc.Factors

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup

namespace GL32Aux

variable {V : Type} [Group V]

theorem inv_eq_self_of_mul_self (h2 : ∀ v : V, v * v = 1) (v : V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (h2 v)

theorem mul_comm_of_mul_self (h2 : ∀ v : V, v * v = 1) (a b : V) : a * b = b * a := by
  calc a * b = (a * b)⁻¹ := (inv_eq_self_of_mul_self h2 _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_self_of_mul_self h2, inv_eq_self_of_mul_self h2]

abbrev commGroupOfMulSelf (h2 : ∀ v : V, v * v = 1) : CommGroup V :=
  { ‹Group V› with mul_comm := mul_comm_of_mul_self h2 }

theorem two_nsmul_eq_zero (h2 : ∀ v : V, v * v = 1) (x : Additive V) : 2 • x = 0 := by
  rw [two_nsmul]
  exact h2 (Additive.toMul x)

def addEquivEquivLinearEquiv {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod n) M] :
    (M ≃+ M) ≃ (M ≃ₗ[ZMod n] M) where
  toFun f := { f with map_smul' := fun c x => ZMod.map_smul f c x }
  invFun g := g.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_mulAut_aux (hcard : Nat.card V = 8) (h2 : ∀ v : V, v * v = 1) :
    Nat.card (MulAut V) = 168 := by
  classical
  let _ : CommGroup V := commGroupOfMulSelf h2
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (two_nsmul_eq_zero h2)
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive V) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = 8 from hcard] at h
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    exact (Nat.pow_right_injective (le_refl 2) (h8.trans h)).symm
  let b : Module.Basis (Fin 3) (ZMod 2) (Additive V) := Module.finBasisOfFinrankEq _ _ hfin
  let e1 : MulAut V ≃ (Additive V ≃+ Additive V) := MulEquiv.toAdditive
  let e3 : (Additive V ≃ₗ[ZMod 2] Additive V) ≃ GL (Fin 3) (ZMod 2) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm).toEquiv
  rw [Nat.card_congr (e1.trans (addEquivEquivLinearEquiv.trans e3)), Matrix.card_GL_field]
  simp [Fin.prod_univ_three]

theorem exists_cover_of_orderOf_seven (hcard : Nat.card V = 8) {c : MulAut V}
    (hc : orderOf c = 7) :
    ∃ v₀ : V, ∀ v : V, v ≠ 1 → ∃ j : ℕ, (c ^ j) v₀ = v := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, c v₀ ≠ v₀ := by
    by_contra hcon
    have h1 : c = 1 := MulEquiv.ext fun v => by_contra fun h => hcon ⟨v, h⟩
    rw [h1, orderOf_one] at hc
    omega
  have hmove : ∀ k : ℕ, 0 < k → k < 7 → (c ^ k) v₀ ≠ v₀ := by
    intro k hk0 hk7 hfix
    have hcop : k.Coprime (orderOf c) := by
      rw [hc]
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr ?_)
      intro h
      have := Nat.le_of_dvd hk0 h
      omega
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hall : ∀ n : ℕ, ((c ^ k) ^ n) v₀ = v₀ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
    exact hv₀ (by rw [← hm]; exact hall m)
  have hne : ∀ i j : ℕ, i < j → j < 7 → (c ^ i) v₀ ≠ (c ^ j) v₀ := by
    intro i j hij hj heq
    refine hmove (j - i) (by omega) (by omega) ?_
    apply (c ^ i).injective
    rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
    exact heq.symm
  have hinj : Function.Injective (fun j : Fin 7 => (c ^ (j : ℕ)) v₀) := by
    intro i j hij
    by_contra hij'
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hij' (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hne _ _ h j.2 hij
    · exact hne _ _ h i.2 hij.symm
  let T : Finset V := Finset.univ.image (fun j : Fin 7 => (c ^ (j : ℕ)) v₀)
  have hTcard : T.card = 7 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hv₀1 : v₀ ≠ 1 := by
    intro h
    exact hv₀ (by rw [h, map_one])
  have hsub : T ⊆ Finset.univ.erase 1 := by
    intro v hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    apply hv₀1
    apply (c ^ (j : ℕ)).injective
    rw [h, map_one]
  have hcard' : (Finset.univ.erase (1 : V)).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard]
  have hTeq : T = Finset.univ.erase 1 := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨v₀, fun v hv => ?_⟩
  have hvT : v ∈ T := by
    rw [hTeq]
    exact Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hvT
  exact ⟨j, hj⟩

theorem exists_eq_one_of_commute_of_fix (hcard : Nat.card V = 8) {c : MulAut V}
    (hc : orderOf c = 7) :
    ∃ v₀ : V, ∀ m : MulAut V, m * c = c * m → m v₀ = v₀ → m = 1 := by
  obtain ⟨v₀, hv₀⟩ := exists_cover_of_orderOf_seven hcard hc
  refine ⟨v₀, fun m hmc hmv => MulEquiv.ext fun v => ?_⟩
  by_cases hv : v = 1
  · rw [hv, map_one, map_one]
  · obtain ⟨j, rfl⟩ := hv₀ v hv
    have hcomm : m * c ^ j = c ^ j * m := Commute.pow_right (show Commute m c from hmc) j
    calc m ((c ^ j) v₀) = (m * c ^ j) v₀ := (MulAut.mul_apply V m (c ^ j) v₀).symm
      _ = (c ^ j * m) v₀ := by rw [hcomm]
      _ = (c ^ j) (m v₀) := MulAut.mul_apply V _ _ _
      _ = (c ^ j) v₀ := by rw [hmv]

theorem card_le_of_mem_zpowers_conj (hcard : Nat.card V = 8) {c : MulAut V}
    (hc : orderOf c = 7) (H : Subgroup (MulAut V))
    (hH : ∀ h ∈ H, h * c * h⁻¹ ∈ zpowers c) : Nat.card H ≤ 56 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨v₀, hv₀⟩ := exists_eq_one_of_commute_of_fix hcard hc
  choose k hk using fun h : H => Subgroup.mem_zpowers_iff.mp (hH h.1 h.2)
  let F : H → V × ZMod 7 := fun h => ((h : MulAut V) v₀, (k h : ZMod 7))
  have hF : Function.Injective F := by
    intro h h' hhh
    obtain ⟨h1, h2⟩ := Prod.mk.inj hhh
    have hk' : c ^ k h = c ^ k h' := by
      rw [zpow_eq_zpow_iff_modEq, hc]
      exact (ZMod.intCast_eq_intCast_iff _ _ 7).mp h2
    have hconj : (h : MulAut V) * c * (h : MulAut V)⁻¹ =
        (h' : MulAut V) * c * (h' : MulAut V)⁻¹ := by
      rw [← hk h, ← hk h', hk']
    have hm : ((h' : MulAut V)⁻¹ * h) * c = c * ((h' : MulAut V)⁻¹ * h) := by
      calc ((h' : MulAut V)⁻¹ * h) * c
          = (h' : MulAut V)⁻¹ * ((h : MulAut V) * c * (h : MulAut V)⁻¹) * h := by group
        _ = (h' : MulAut V)⁻¹ * ((h' : MulAut V) * c * (h' : MulAut V)⁻¹) * h := by rw [hconj]
        _ = c * ((h' : MulAut V)⁻¹ * h) := by group
    have h3 := hv₀ _ hm (by
      rw [MulAut.mul_apply, h1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply])
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  calc Nat.card H ≤ Nat.card (V × ZMod 7) := Nat.card_le_card_of_injective F hF
    _ = 56 := by rw [Nat.card_prod, hcard, Nat.card_zmod]

theorem exists_orderOf_seven_normalizing {G : Type*} [Group G] (hG : Nat.card G = 84) :
    ∃ c : G, orderOf c = 7 ∧ ∀ g : G, g * c * g⁻¹ ∈ zpowers c := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 7) (G := G)
  have hQcard : Nat.card (Q : Subgroup G) = 7 := by
    rw [Sylow.card_eq_multiplicity, hG]
    simp [Nat.factorization]
  have hindex : (Q : Subgroup G).index = 12 := by
    have h := Subgroup.card_mul_index (Q : Subgroup G)
    rw [hQcard, hG] at h
    omega
  have hdvd : Nat.card (Sylow 7 G) ∣ 12 := hindex ▸ Q.card_dvd_index
  have hmod : Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
  have hone : Nat.card (Sylow 7 G) = 1 := by
    have hpos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
    have hle : Nat.card (Sylow 7 G) ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 7 G) = n at hdvd hmod hpos hle ⊢
    unfold Nat.ModEq at hmod
    interval_cases n <;> omega
  have : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hone).1
  have hQn : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := (Q : Subgroup G)) 7 (by rw [hQcard])
  have hc : orderOf (g : G) = 7 := by rw [Subgroup.orderOf_coe, hg]
  have hzp : zpowers (g : G) = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr g.2) (by rw [Nat.card_zpowers, hc, hQcard])
  refine ⟨g, hc, fun x => ?_⟩
  rw [hzp]
  exact hQn.conj_mem _ g.2 x

end GL32Aux

theorem card_mulAut_elemAb8 {V : Type} [Group V] (hcard : Nat.card V = 8)
    (h2 : ∀ v : V, v * v = 1) : Nat.card (MulAut V) = 168 :=
  GL32Aux.card_mulAut_aux hcard h2

theorem eq_top_of_dvd_84 {V : Type} [Group V] (hcard : Nat.card V = 8)
    (h2 : ∀ v : V, v * v = 1) (H : Subgroup (MulAut V)) (h84 : 84 ∣ Nat.card H) : H = ⊤ := by
  have hA : Nat.card (MulAut V) = 168 := card_mulAut_elemAb8 hcard h2
  have : Finite (MulAut V) := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : Nat.card H ∣ 168 := hA ▸ Subgroup.card_subgroup_dvd_card H
  have hle : Nat.card H ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card H := Nat.card_pos
  obtain ⟨k, hk⟩ := h84
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl
  · exfalso
    obtain ⟨c, hc7, hnorm⟩ := GL32Aux.exists_orderOf_seven_normalizing (G := H) (by omega)
    have hc : orderOf (c : MulAut V) = 7 := by rw [Subgroup.orderOf_coe, hc7]
    have hnorm' : ∀ h ∈ H, h * (c : MulAut V) * h⁻¹ ∈ zpowers (c : MulAut V) := by
      intro h hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hnorm ⟨h, hh⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simpa using congrArg (fun x : H => (x : MulAut V)) hk
    have := GL32Aux.card_le_of_mem_zpowers_conj hcard hc H hnorm'
    omega
  · exact H.eq_top_of_card_eq (by omega)

theorem card_map_sylow_eq_eight {V : Type} [Group V] (hcard : Nat.card V = 8)
    (h2 : ∀ v : V, v * v = 1) {N : Type} [Group N] [Finite N] (ρ : N →* MulAut V)
    (h12 : 12 ∣ Nat.card ρ.range) (h7 : 7 ∣ Nat.card ρ.range) (P : Sylow 2 N) :
    Nat.card ((P : Subgroup N).map ρ) = 8 := by
  have h84 : 84 ∣ Nat.card ρ.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h12 h7
  have hsurj : Function.Surjective ρ :=
    MonoidHom.range_eq_top.mp (eq_top_of_dvd_84 hcard h2 ρ.range h84)
  have hA : Nat.card (MulAut V) = 168 := card_mulAut_elemAb8 hcard h2
  have : Finite (MulAut V) := Nat.finite_of_card_ne_zero (by omega)
  have h := (P.mapSurjective hsurj).card_eq_multiplicity
  rw [hA, show (168 : ℕ).factorization 2 = 3 by simp [Nat.factorization]] at h
  exact h

namespace GL32Aux

variable {V : Type} [Group V]

theorem ncard_ne_one_ne (hcard : Nat.card V = 8) (q : V) (hq : q ≠ 1) :
    {v : V | v ≠ 1 ∧ v ≠ q}.ncard = 6 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have h1 : {v : V | v ≠ 1 ∧ v ≠ q} = ({1, q} : Set V)ᶜ := by
    ext v; simp [not_or]
  rw [h1, Set.ncard_compl, Set.ncard_pair hq.symm, hcard]

theorem ncard_ne_one (hcard : Nat.card V = 8) : {v : V | v ≠ 1}.ncard = 7 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have h1 : {v : V | v ≠ 1} = ({1} : Set V)ᶜ := by
    ext v; simp
  rw [h1, Set.ncard_compl, Set.ncard_singleton, hcard]

end GL32Aux

theorem dvd_card_of_orbits {V : Type} [Group V] (hcard : Nat.card V = 8)
    (H : Subgroup (MulAut V)) (q π : V) (hq1 : q ≠ 1) (hp1 : π ≠ 1) (hpq : π ≠ q)
    (hπ : ∃ φ ∈ H, φ q = π) (horb : ∀ v : V, v ≠ 1 → v ≠ q → ∃ φ ∈ H, φ q = q ∧ φ π = v) :
    7 ∣ Nat.card H ∧ 6 ∣ Nat.card H := by
  set Hq : Subgroup (MulAut V) := H ⊓ MulAction.stabilizer (MulAut V) q with hHq
  have horbq : MulAction.orbit H q = {v : V | v ≠ 1} := by
    ext v
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩ h1
      have : (g : MulAut V) q = (g : MulAut V) 1 := by
        simpa [MulAut.smul_def] using h1
      exact hq1 (g.injective this)
    · intro hv
      by_cases hvq : v = q
      · subst hvq; exact MulAction.mem_orbit_self _
      · obtain ⟨φ, hφ, hφq, hφπ⟩ := horb v hv hvq
        obtain ⟨ψ, hψ, hψq⟩ := hπ
        refine ⟨⟨φ * ψ, H.mul_mem hφ hψ⟩, ?_⟩
        show (φ * ψ) q = v
        rw [MulAut.mul_apply, hψq, hφπ]
  have horbp : MulAction.orbit Hq π = {v : V | v ≠ 1 ∧ v ≠ q} := by
    ext v
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      have hgq : g q = q := by simpa [MulAut.smul_def] using hg.2
      refine ⟨fun h1 => hp1 ?_, fun h1 => hpq ?_⟩
      · have : g π = g 1 := by simpa [MulAut.smul_def] using h1
        exact g.injective this
      · have : g π = g q := by
          have h1' : g π = q := by simpa [MulAut.smul_def] using h1
          rw [h1', hgq]
        exact g.injective this
    · rintro ⟨hv1, hvq⟩
      obtain ⟨φ, hφ, hφq, hφπ⟩ := horb v hv1 hvq
      exact ⟨⟨φ, hφ, by simpa [MulAut.smul_def] using hφq⟩, hφπ⟩
  refine ⟨?_, ?_⟩
  · have h := MulAction.index_stabilizer H q
    rw [horbq, GL32Aux.ncard_ne_one hcard] at h
    rw [← h]
    exact Subgroup.index_dvd_card _
  · have h := MulAction.index_stabilizer Hq π
    rw [horbp, GL32Aux.ncard_ne_one_ne hcard q hq1] at h
    have h6 : 6 ∣ Nat.card Hq := h ▸ Subgroup.index_dvd_card _
    exact h6.trans (Subgroup.card_dvd_of_le inf_le_left)

end CFSG.OddStandard.ChengHeld
