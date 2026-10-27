module

public import CFSG.Quasithin.Background.HA5Weyl
public import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.GroupTheory.AlternatingFive

open Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H.A5W CFSG.QuasithinUnique.A5.Delta5
open scoped commutatorElement

private theorem mem_kleinSet_of_centralizes (σ : Perm (Fin 5))
    (h : ∀ x ∈ kleinSet, σ * x = x * σ) :
    σ ∈ kleinSet := by
  decide +kernel +revert

set_option synthInstance.maxSize 10000 in
private theorem eq_one_of_normalizes_kleinSet (σ : Perm (Fin 5)) (k : Alt5)
    (hσW : ∀ x ∈ kleinSet, σ * x * σ⁻¹ ∈ kleinSet)
    (hσ8 : σ ^ 8 = 1)
    (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hkW : ∀ x ∈ kleinSet, (k : Perm (Fin 5)) * x * (k : Perm (Fin 5))⁻¹ ∈ kleinSet)
    (hcomm : σ * (k : Perm (Fin 5)) * σ⁻¹ = (k : Perm (Fin 5))) :
    σ = 1 := by
  decide +kernel +revert

private theorem eq_one_of_commutes_generators (τ : Perm (Fin 5))
    (ha : τ * ((a0' : Alt5) : Perm (Fin 5)) * τ⁻¹ = ((a0' : Alt5) : Perm (Fin 5)))
    (hb : τ * ((b0' : Alt5) : Perm (Fin 5)) * τ⁻¹ = ((b0' : Alt5) : Perm (Fin 5))) :
    τ = 1 := by
  decide +kernel +revert

private theorem pow_eight_eq_one_of_twoPow (σ : Perm (Fin 5)) (m : ℕ)
    (hm : σ ^ (2 ^ m) = 1) : σ ^ 8 = 1 := by
  have hdvd1 : orderOf σ ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr hm
  have hdvd2 : orderOf σ ∣ 120 := by
    have h := orderOf_dvd_natCard σ
    rwa [Nat.card_perm, Nat.card_fin] at h
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
  have hk_dvd : 2 ^ k ∣ 120 := hk ▸ hdvd2
  have hcop : Nat.Coprime (2 ^ k) 15 := (by norm_num : Nat.Coprime 2 15).pow_left k
  have hk8 : 2 ^ k ∣ 8 := by
    have h : 2 ^ k ∣ 8 * 15 := by norm_num at hk_dvd ⊢; exact hk_dvd
    exact hcop.dvd_mul_right.mp h
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))).mp
    (by simpa using hk8)
  rw [← orderOf_dvd_iff_pow_eq_one]
  calc orderOf σ = 2 ^ k := hk
    _ ∣ 2 ^ 3 := pow_dvd_pow 2 hk3
    _ = 8 := by norm_num

theorem eq_one_of_preserves_sylow_of_twoPow
    (φ : MulAut Alt5) (V : Sylow 2 Alt5) (k : Alt5)
    (hV : ∀ v : Alt5, v ∈ V ↔ φ v ∈ V)
    (h2 : ∃ m, φ ^ (2 ^ m) = 1)
    (hk3 : orderOf k = 3)
    (hkN : k ∈ Subgroup.normalizer (V : Set Alt5))
    (hfix : φ k = k) : φ = 1 := by
  classical
  obtain ⟨σ, hσ⟩ := aut_inner φ
  have hφσ : φ = MulAut.conjNormal (H := Alt5) σ := by
    refine MulEquiv.ext fun a => ?_
    apply Subtype.ext
    simpa [MulAut.conjNormal_apply] using hσ a
  have hσVmap : (V : Subgroup Alt5).map (MulAut.conjNormal (H := Alt5) σ) =
      (V : Subgroup Alt5) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hφσ]
      exact (hV y).mp hy
    · intro hx
      have hx' : φ ((MulAut.conjNormal (H := Alt5) σ)⁻¹ x) ∈ V := by
        rw [hφσ]
        have hfixx : (MulAut.conjNormal (H := Alt5) σ)
            ((MulAut.conjNormal (H := Alt5) σ)⁻¹ x) = x := by
          apply Subtype.ext
          rw [MulAut.conjNormal_apply, MulAut.conjNormal_inv_apply]
          push_cast
          group
        rwa [hfixx]
      exact ⟨(MulAut.conjNormal (H := Alt5) σ)⁻¹ x, (hV _).mpr hx', by simp⟩
  obtain ⟨m, hm⟩ := h2
  have hσm : MulAut.conjNormal (H := Alt5) (σ ^ (2 ^ m)) = 1 := by
    have h : (MulAut.conjNormal (H := Alt5) σ) ^ (2 ^ m) = 1 := by
      rw [← hφσ]
      exact hm
    simpa [map_pow] using h
  have hσm_a : σ ^ (2 ^ m) * ((a0' : Alt5) : Perm (Fin 5)) * (σ ^ (2 ^ m))⁻¹ =
      ((a0' : Alt5) : Perm (Fin 5)) := by
    have h := congrArg (fun f : MulAut Alt5 => ((f a0' : Alt5) : Perm (Fin 5))) hσm
    change σ ^ (2 ^ m) * ((a0' : Alt5) : Perm (Fin 5)) * (σ ^ (2 ^ m))⁻¹ =
      ((a0' : Alt5) : Perm (Fin 5)) at h
    exact h
  have hσm_b : σ ^ (2 ^ m) * ((b0' : Alt5) : Perm (Fin 5)) * (σ ^ (2 ^ m))⁻¹ =
      ((b0' : Alt5) : Perm (Fin 5)) := by
    have h := congrArg (fun f : MulAut Alt5 => ((f b0' : Alt5) : Perm (Fin 5))) hσm
    change σ ^ (2 ^ m) * ((b0' : Alt5) : Perm (Fin 5)) * (σ ^ (2 ^ m))⁻¹ =
      ((b0' : Alt5) : Perm (Fin 5)) at h
    exact h
  have hσpow : σ ^ (2 ^ m) = 1 := eq_one_of_commutes_generators _ hσm_a hσm_b
  have hσ8 : σ ^ 8 = 1 := pow_eight_eq_one_of_twoPow σ m hσpow
  obtain ⟨g, hVW⟩ := exists_conj_kleinStd (V : Subgroup Alt5) (card_sylow_two_eq V)
  have hVWmap : (V : Subgroup Alt5) =
      (kleinStd : Subgroup Alt5).map (MulAut.conjNormal (H := Alt5) g) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, (hVW x).mp hx, ?_⟩
      apply Subtype.ext
      change (g * (g⁻¹ * x * g) * g⁻¹ : Perm (Fin 5)) = (x : Perm (Fin 5))
      push_cast
      group
    · rintro ⟨w, hw, rfl⟩
      refine (hVW (g * w * g⁻¹)).mpr ?_
      have h : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rwa [h]
  have hkVmap : (V : Subgroup Alt5).map (MulAut.conjNormal (H := Alt5) k) =
      (V : Subgroup Alt5) := by
    rw [MulAut.conjNormal_val]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hkN
  let τ : Perm (Fin 5) := g⁻¹ * σ * g
  let k' : Alt5 := g⁻¹ * k * g
  have hτW : ∀ x ∈ kleinSet, τ * x * τ⁻¹ ∈ kleinSet := by
    intro x hx
    let w : Alt5 := ⟨x, by rw [Equiv.Perm.mem_alternatingGroup]; exact kleinSet_alt x hx⟩
    have hw : w ∈ (kleinStd : Subgroup Alt5) := mem_kleinStd.mpr hx
    have hwcoe : (w : Perm (Fin 5)) = x := rfl
    let v : Alt5 := MulAut.conjNormal (H := Alt5) g w
    have hv : v ∈ V := by
      show v ∈ (V : Subgroup Alt5)
      rw [hVWmap]
      exact Subgroup.mem_map_of_mem _ hw
    let v' : Alt5 := MulAut.conjNormal (H := Alt5) σ v
    have hv' : v' ∈ V := by
      show v' ∈ (V : Subgroup Alt5)
      rw [← hσVmap]
      exact Subgroup.mem_map_of_mem _ hv
    let w' : Alt5 := MulAut.conjNormal (H := Alt5) g⁻¹ v'
    have hw' : w' ∈ (kleinStd : Subgroup Alt5) := by
      have hv'' : v' ∈ (V : Subgroup Alt5) := hv'
      rw [hVWmap] at hv''
      obtain ⟨u, hu, huv⟩ := hv''
      have hwu : w' = u := by
        show MulAut.conjNormal (H := Alt5) g⁻¹ v' = u
        rw [← huv]
        simp
      rwa [hwu]
    have hxeq : τ * x * τ⁻¹ = (w' : Perm (Fin 5)) := by
      show (g⁻¹ * σ * g) * x * (g⁻¹ * σ * g)⁻¹ =
        ((MulAut.conjNormal (H := Alt5) g⁻¹ v' : Alt5) : Perm (Fin 5))
      simp only [v', v, w, MulAut.conjNormal_apply, Subtype.coe_mk, hwcoe]
      push_cast
      group
    rw [hxeq]
    exact mem_kleinStd.mp hw'
  have hk'W : ∀ x ∈ kleinSet, (k' : Perm (Fin 5)) * x * (k' : Perm (Fin 5))⁻¹ ∈ kleinSet := by
    intro x hx
    let w : Alt5 := ⟨x, by rw [Equiv.Perm.mem_alternatingGroup]; exact kleinSet_alt x hx⟩
    have hw : w ∈ (kleinStd : Subgroup Alt5) := mem_kleinStd.mpr hx
    have hwcoe : (w : Perm (Fin 5)) = x := rfl
    let v : Alt5 := MulAut.conjNormal (H := Alt5) g w
    have hv : v ∈ V := by
      show v ∈ (V : Subgroup Alt5)
      rw [hVWmap]
      exact Subgroup.mem_map_of_mem _ hw
    let v' : Alt5 := MulAut.conjNormal (H := Alt5) k v
    have hv' : v' ∈ V := by
      show v' ∈ (V : Subgroup Alt5)
      rw [← hkVmap]
      exact Subgroup.mem_map_of_mem _ hv
    let w' : Alt5 := MulAut.conjNormal (H := Alt5) g⁻¹ v'
    have hw' : w' ∈ (kleinStd : Subgroup Alt5) := by
      have hv'' : v' ∈ (V : Subgroup Alt5) := hv'
      rw [hVWmap] at hv''
      obtain ⟨u, hu, huv⟩ := hv''
      have hwu : w' = u := by
        show MulAut.conjNormal (H := Alt5) g⁻¹ v' = u
        rw [← huv]
        simp
      rwa [hwu]
    have hxeq : (k' : Perm (Fin 5)) * x * (k' : Perm (Fin 5))⁻¹ = (w' : Perm (Fin 5)) := by
      show ((g⁻¹ * k * g : Alt5) : Perm (Fin 5)) * x *
        (((g⁻¹ * k * g : Alt5) : Perm (Fin 5)))⁻¹ =
        ((MulAut.conjNormal (H := Alt5) g⁻¹ v' : Alt5) : Perm (Fin 5))
      simp only [v', v, w, MulAut.conjNormal_apply, Subtype.coe_mk, hwcoe]
      push_cast
      group
    rw [hxeq]
    exact mem_kleinStd.mp hw'
  have hk3' : orderOf k' = 3 := by
    rw [show k' = MulAut.conjNormal (H := Alt5) g⁻¹ k from rfl]
    rw [MulEquiv.orderOf_eq]
    exact hk3
  have hk'3 : k' ^ 3 = 1 := by
    have h := pow_orderOf_eq_one k'
    rwa [hk3'] at h
  have hk'1 : k' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk3'
    omega
  have hσk : σ * (k : Perm (Fin 5)) * σ⁻¹ = (k : Perm (Fin 5)) := by
    rw [← hσ k, hfix]
  have hcomm : τ * (k' : Perm (Fin 5)) * τ⁻¹ = (k' : Perm (Fin 5)) := by
    show (g⁻¹ * σ * g) * ((g⁻¹ * k * g : Alt5) : Perm (Fin 5)) * (g⁻¹ * σ * g)⁻¹ =
      ((g⁻¹ * k * g : Alt5) : Perm (Fin 5))
    push_cast
    calc (g⁻¹ * σ * g) * (g⁻¹ * k * g) * (g⁻¹ * σ * g)⁻¹
        = g⁻¹ * (σ * k * σ⁻¹) * g := by push_cast; group
      _ = g⁻¹ * k * g := by rw [hσk]
  have hτ8 : τ ^ 8 = 1 := by
    show (g⁻¹ * σ * g) ^ 8 = 1
    have hconj : (g⁻¹ * σ * g : Perm (Fin 5)) ^ 8 = g⁻¹ * σ ^ 8 * g := by
      simpa using (conj_pow (a := (g⁻¹ : Perm (Fin 5))) (b := σ) (i := 8))
    rw [hconj, hσ8]
    push_cast
    group
  have hτ1 : τ = 1 :=
    eq_one_of_normalizes_kleinSet τ k' hτW hτ8 hk'3 hk'1 hk'W hcomm
  have hσ1 : σ = 1 := by
    calc σ = g * τ * g⁻¹ := by
          show σ = g * (g⁻¹ * σ * g) * g⁻¹
          push_cast
          group
      _ = 1 := by rw [hτ1]; push_cast; group
  rw [hφσ, hσ1, map_one]

theorem exists_mem_sylow_of_fixes (φ : MulAut Alt5) (V : Sylow 2 Alt5)
    (hfix : ∀ v : Alt5, v ∈ V → φ v = v) :
    ∃ v : Alt5, v ∈ V ∧ φ = MulAut.conj v := by
  classical
  obtain ⟨σ, hσ⟩ := aut_inner φ
  have hφσ : φ = MulAut.conjNormal (H := Alt5) σ := by
    refine MulEquiv.ext fun a => ?_
    apply Subtype.ext
    simpa [MulAut.conjNormal_apply] using hσ a
  have hσV : ∀ v : Alt5, v ∈ V → σ * (v : Perm (Fin 5)) * σ⁻¹ = (v : Perm (Fin 5)) := by
    intro v hv
    calc σ * (v : Perm (Fin 5)) * σ⁻¹ = (φ v : Perm (Fin 5)) := (hσ v).symm
      _ = (v : Perm (Fin 5)) := congrArg (fun x : Alt5 => (x : Perm (Fin 5))) (hfix v hv)
  obtain ⟨g, hVW⟩ := exists_conj_kleinStd (V : Subgroup Alt5) (card_sylow_two_eq V)
  have hVWmap : (V : Subgroup Alt5) =
      (kleinStd : Subgroup Alt5).map (MulAut.conjNormal (H := Alt5) g) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, (hVW x).mp hx, ?_⟩
      apply Subtype.ext
      change (g * (g⁻¹ * x * g) * g⁻¹ : Perm (Fin 5)) = (x : Perm (Fin 5))
      push_cast
      group
    · rintro ⟨w, hw, rfl⟩
      refine (hVW (g * w * g⁻¹)).mpr ?_
      have h : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rwa [h]
  let τ : Perm (Fin 5) := g⁻¹ * σ * g
  have hτW : ∀ x ∈ kleinSet, τ * x = x * τ := by
    intro x hx
    let w : Alt5 := ⟨x, by rw [Equiv.Perm.mem_alternatingGroup]; exact kleinSet_alt x hx⟩
    have hw : w ∈ (kleinStd : Subgroup Alt5) := mem_kleinStd.mpr hx
    have hwcoe : (w : Perm (Fin 5)) = x := rfl
    let v : Alt5 := MulAut.conjNormal (H := Alt5) g w
    have hv : v ∈ V := by
      show v ∈ (V : Subgroup Alt5)
      rw [hVWmap]
      exact Subgroup.mem_map_of_mem _ hw
    have hσv : σ * (v : Perm (Fin 5)) * σ⁻¹ = (v : Perm (Fin 5)) := hσV v hv
    have hσv' : σ * (g * x * g⁻¹) * σ⁻¹ = g * x * g⁻¹ := by
      simpa [v, w, hwcoe, MulAut.conjNormal_apply] using hσv
    have hconj : τ * x * τ⁻¹ = x := by
      show (g⁻¹ * σ * g) * x * (g⁻¹ * σ * g)⁻¹ = x
      calc (g⁻¹ * σ * g) * x * (g⁻¹ * σ * g)⁻¹
          = g⁻¹ * (σ * (g * x * g⁻¹) * σ⁻¹) * g := by push_cast; group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hσv']
        _ = x := by push_cast; group
    calc τ * x = (τ * x * τ⁻¹) * τ := by push_cast; group
      _ = x * τ := by rw [hconj]
  have hτmem : τ ∈ kleinSet := mem_kleinSet_of_centralizes τ hτW
  let t : Alt5 := ⟨τ, by rw [Equiv.Perm.mem_alternatingGroup]; exact kleinSet_alt τ hτmem⟩
  have ht : t ∈ (kleinStd : Subgroup Alt5) := mem_kleinStd.mpr (by simpa [t] using hτmem)
  let v : Alt5 := g * t * g⁻¹
  have hvcoe' : (v : Perm (Fin 5)) = g * τ * g⁻¹ := by
    change (g * t * g⁻¹ : Perm (Fin 5)) = g * τ * g⁻¹
    simp only [t, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  have hσeq : σ = g * τ * g⁻¹ := by
    simp [τ, mul_assoc]
  have hvcoe : (v : Perm (Fin 5)) = σ := hvcoe'.trans hσeq.symm
  have hvV : v ∈ V := (hVW v).mpr (by simpa [v, t, mul_assoc] using ht)
  refine ⟨v, hvV, ?_⟩
  rw [hφσ, ← hvcoe]
  exact MulAut.conjNormal_val

theorem eq_one_of_preserves_sylow_of_twoPow_of_mulEquiv
    {A : Type*} [Group A] (e : A ≃* Alt5) (φ : MulAut A) (V : Sylow 2 A) (k : A)
    (hV : ∀ v : A, v ∈ V ↔ φ v ∈ V)
    (h2 : ∃ m, φ ^ (2 ^ m) = 1)
    (hk3 : orderOf k = 3)
    (hkN : k ∈ Subgroup.normalizer (V : Set A))
    (hfix : φ k = k) : φ = 1 := by
  classical
  haveI : Finite A := Finite.of_equiv Alt5 e.symm
  have hsurj : Function.Surjective (e.toMonoidHom : A →* Alt5) := fun x => e.surjective x
  let V' : Sylow 2 Alt5 := V.mapSurjective (f := e.toMonoidHom) hsurj
  have hV'coe : (V' : Subgroup Alt5) = (V : Subgroup A).map e.toMonoidHom := rfl
  let φ' : MulAut Alt5 := (e.symm.trans φ).trans e
  have hφ' : ∀ a : A, φ' (e a) = e (φ a) := by
    intro a
    simp [φ']
  let k' : Alt5 := e k
  have hV' : ∀ v' : Alt5, v' ∈ V' ↔ φ' v' ∈ V' := by
    intro v'
    change v' ∈ (V' : Subgroup Alt5) ↔ φ' v' ∈ (V' : Subgroup Alt5)
    rw [hV'coe]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨φ v, (hV v).mp hv, ?_⟩
      simp [φ']
    · rintro ⟨w, hw, hw'⟩
      refine ⟨e.symm v', ?_, by simp⟩
      apply (hV _).mpr
      have hφ'v : φ' v' = e (φ (e.symm v')) := by simp [φ']
      rw [← hw'] at hφ'v
      have : φ (e.symm v') = w := e.injective hφ'v.symm
      rwa [this]
  have h2' : ∃ m, φ' ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := h2
    have hpow : ∀ n : ℕ, ∀ a : Alt5, (φ' ^ n) a = e ((φ ^ n) (e.symm a)) := by
      intro n
      induction n with
      | zero => intro a; simp [φ']
      | succ n ih =>
          intro a
          rw [pow_succ']
          simp only [MulAut.mul_apply, ih]
          rw [hφ']
          congr 1
          rw [pow_succ']
          rfl
    refine ⟨m, MulEquiv.ext fun a => ?_⟩
    rw [hpow (2 ^ m) a, hm]
    simp
  have hk3' : orderOf k' = 3 := by
    rw [show k' = e k from rfl]
    rw [MulEquiv.orderOf_eq]
    exact hk3
  have hkN' : k' ∈ Subgroup.normalizer (V' : Set Alt5) := by
    rw [show k' = e k from rfl]
    change e k ∈ Subgroup.normalizer ((V' : Subgroup Alt5) : Set Alt5)
    rw [hV'coe]
    rw [← Subgroup.map_normalizer_eq_of_bijective (H := (V : Subgroup A))
      (f := e.toMonoidHom) e.bijective]
    exact Subgroup.mem_map_of_mem _ hkN
  have hfix' : φ' k' = k' := by
    simp only [k', hφ']
    rw [hfix]
  have hφ'1 : φ' = 1 :=
    eq_one_of_preserves_sylow_of_twoPow φ' V' k' hV' h2' hk3' hkN' hfix'
  ext a
  have ha := congrArg (fun f : MulAut Alt5 => f (e a)) hφ'1
  rw [hφ'] at ha
  exact e.injective ha

theorem exists_mem_sylow_of_fixes_of_mulEquiv
    {A : Type*} [Group A] (e : A ≃* Alt5) (φ : MulAut A) (V : Sylow 2 A)
    (hfix : ∀ v : A, v ∈ V → φ v = v) :
    ∃ v : A, v ∈ V ∧ φ = MulAut.conj v := by
  classical
  haveI : Finite A := Finite.of_equiv Alt5 e.symm
  have hsurj : Function.Surjective (e.toMonoidHom : A →* Alt5) := fun x => e.surjective x
  let V' : Sylow 2 Alt5 := V.mapSurjective (f := e.toMonoidHom) hsurj
  have hV'coe : (V' : Subgroup Alt5) = (V : Subgroup A).map e.toMonoidHom := rfl
  let φ' : MulAut Alt5 := (e.symm.trans φ).trans e
  have hφ' : ∀ a : A, φ' (e a) = e (φ a) := by
    intro a
    simp [φ']
  have hV'fix : ∀ v' : Alt5, v' ∈ V' → φ' v' = v' := by
    intro v' hv'
    change v' ∈ (V' : Subgroup Alt5) at hv'
    rw [hV'coe] at hv'
    obtain ⟨v, hv, rfl⟩ := hv'
    change φ' (e v) = e v
    rw [hφ']
    exact congrArg e (hfix v hv)
  obtain ⟨w, hwV', hwφ'⟩ := exists_mem_sylow_of_fixes φ' V' hV'fix
  refine ⟨e.symm w, ?_, ?_⟩
  · change e.symm w ∈ (V : Subgroup A)
    have hwV'' : w ∈ (V : Subgroup A).map e.toMonoidHom := by
      change w ∈ (V' : Subgroup Alt5)
      rwa [hV'coe]
    obtain ⟨v, hv, hvw⟩ := hwV''
    have hvv : e.symm w = v := by
      rw [← hvw]
      exact e.symm_apply_apply v
    rwa [hvv]
  · ext a
    have ha := congrArg (fun f : MulAut Alt5 => f (e a)) hwφ'
    rw [hφ'] at ha
    apply e.injective
    rw [MulAut.conj_apply]
    calc e (φ a) = (MulAut.conj w) (e a) := ha
      _ = e (e.symm w) * e a * (e (e.symm w))⁻¹ := by
            rw [MulAut.conj_apply, e.apply_symm_apply]
      _ = e (e.symm w * a * (e.symm w)⁻¹) := by rw [map_mul, map_mul, map_inv]

theorem conjModPCore_eq_one_of_twoPow_of_normalizes_sylow
    {G : Type} [Group G] {L : Subgroup G} [Finite ↥L] {c : G}
    (e : oTwoQuot ↥L ≃* Alt5) (hc : c ∈ Subgroup.normalizer (L : Set G))
    (hc2 : ∃ m, c ^ (2 ^ m) = 1)
    {P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hcP : c ∈ Subgroup.normalizer (P : Set G))
    {k : G} (hkL : k ∈ L) (hck : c * k = k * c)
    (hkP : k ∈ Subgroup.normalizer (P : Set G))
    (hk3 : orderOf (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥L) ⟨k, hkL⟩) = 3) :
    ∀ l ∈ L, ⁅c, l⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  classical
  let M : Subgroup G := Subgroup.normalizer (L : Set G)
  have hM : M ≤ Subgroup.normalizer (L : Set G) := le_rfl
  let cN : ↥M := ⟨c, hc⟩
  let φq : MulAut (oTwoQuot ↥L) := conjModPCore 2 L M hM cN
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨S, hS⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow hP
  let Vq : Sylow 2 (oTwoQuot ↥L) := S.mapSurjective (f := π) hπsurj
  have hVqcoe : (Vq : Subgroup (oTwoQuot ↥L)) = (P.subgroupOf L).map π := by
    change (S.mapSurjective (f := π) hπsurj : Subgroup (oTwoQuot ↥L)) =
      (P.subgroupOf L).map π
    rw [Sylow.coe_mapSurjective, hS]
  let kq : oTwoQuot ↥L := π ⟨k, hkL⟩
  have hkq3 : orderOf kq = 3 := by
    simpa [kq, π] using hk3
  have h2q : ∃ m, φq ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hc2
    have hcNpow : cN ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      simpa [cN] using hm
    have hpow : φq ^ (2 ^ m) = (conjModPCore 2 L M hM) (cN ^ (2 ^ m)) := by
      rw [show φq = (conjModPCore 2 L M hM) cN from rfl, ← map_pow]
    refine ⟨m, ?_⟩
    rw [hpow, hcNpow, map_one]
  have hVq_pres : ∀ y : oTwoQuot ↥L, y ∈ Vq ↔ φq y ∈ Vq := by
    intro y
    constructor
    · intro hy
      have hy' : y ∈ (Vq : Subgroup (oTwoQuot ↥L)) := hy
      rw [hVqcoe] at hy'
      obtain ⟨p, hp, hpy⟩ := hy'
      rw [← hpy]
      let p' : ↥L := ⟨c * (p : G) * c⁻¹,
        (Subgroup.mem_normalizer_iff.mp hc (p : G)).mp p.2⟩
      have hp' : p' ∈ P.subgroupOf L :=
        (Subgroup.mem_normalizer_iff.mp hcP (p : G)).mp hp
      have hφp : φq (π p) = π p' := by
        rw [show φq = (conjModPCore 2 L M hM) cN from rfl]
        simp only [π, QuotientGroup.mk'_apply]
        rw [conjModPCore_mk]
      rw [hφp]
      change π p' ∈ (Vq : Subgroup (oTwoQuot ↥L))
      rw [hVqcoe]
      exact Subgroup.mem_map_of_mem _ hp'
    · intro hy
      have hy' : φq y ∈ (Vq : Subgroup (oTwoQuot ↥L)) := hy
      rw [hVqcoe] at hy'
      obtain ⟨p, hp, hpy⟩ := hy'
      have hφqinv : φq⁻¹ = (conjModPCore 2 L M hM) (cN⁻¹) := by
        rw [show φq = (conjModPCore 2 L M hM) cN from rfl, ← map_inv]
      have hcMinv : c⁻¹ ∈ M := M.inv_mem (show c ∈ M from hc)
      have hcPinv : c⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).inv_mem hcP
      let p' : ↥L := ⟨c⁻¹ * (p : G) * c, by
        simpa using (Subgroup.mem_normalizer_iff.mp hcMinv (p : G)).mp p.2⟩
      have hp' : p' ∈ P.subgroupOf L := by
        simpa [p', Subgroup.mem_subgroupOf] using
          (Subgroup.mem_normalizer_iff.mp hcPinv (p : G)).mp hp
      have hφinv : φq⁻¹ (π p) = π p' := by
        rw [hφqinv]
        simp only [π, QuotientGroup.mk'_apply]
        rw [conjModPCore_mk]
        apply congrArg QuotientGroup.mk
        apply Subtype.ext
        simp [p', cN]
      have hyeq : y = φq⁻¹ (φq y) := (MulEquiv.symm_apply_apply φq y).symm
      rw [hyeq, ← hpy, hφinv]
      change π p' ∈ (Vq : Subgroup (oTwoQuot ↥L))
      rw [hVqcoe]
      exact Subgroup.mem_map_of_mem _ hp'
  have hkqN : kq ∈ Subgroup.normalizer (Vq : Set (oTwoQuot ↥L)) := by
    change kq ∈ Subgroup.normalizer ((Vq : Subgroup (oTwoQuot ↥L)) : Set (oTwoQuot ↥L))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hy' : y ∈ (Vq : Subgroup (oTwoQuot ↥L)) := hy
      change y ∈ (Vq : Subgroup (oTwoQuot ↥L)) at hy'
      rw [hVqcoe] at hy'
      obtain ⟨p, hp, hpy⟩ := hy'
      rw [← hpy]
      let p' : ↥L := ⟨k * (p : G) * k⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hkL) (p : G)).mp p.2⟩
      have hp' : p' ∈ P.subgroupOf L :=
        (Subgroup.mem_normalizer_iff.mp hkP (p : G)).mp hp
      have hkqmul : kq * π p * kq⁻¹ = π p' := by
        show π ⟨k, hkL⟩ * π p * (π ⟨k, hkL⟩)⁻¹ = π p'
        rw [← map_mul, ← map_inv, ← map_mul]
        apply congrArg π
        apply Subtype.ext
        simp [p', mul_assoc]
      rw [hkqmul]
      change π p' ∈ (Vq : Subgroup (oTwoQuot ↥L))
      rw [hVqcoe]
      exact Subgroup.mem_map_of_mem _ hp'
    · intro hy
      have hy' : kq * y * kq⁻¹ ∈ (Vq : Subgroup (oTwoQuot ↥L)) := hy
      change kq * y * kq⁻¹ ∈ (Vq : Subgroup (oTwoQuot ↥L)) at hy'
      rw [hVqcoe] at hy'
      obtain ⟨p, hp, hpy⟩ := hy'
      have hkLinv : k⁻¹ ∈ L := L.inv_mem hkL
      have hkPinv : k⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).inv_mem hkP
      let p' : ↥L := ⟨k⁻¹ * (p : G) * k, by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hkLinv)
          (p : G)).mp p.2⟩
      have hp' : p' ∈ P.subgroupOf L := by
        simpa [p', Subgroup.mem_subgroupOf] using
          (Subgroup.mem_normalizer_iff.mp hkPinv (p : G)).mp hp
      have hkqinv : kq⁻¹ * π p * kq = π p' := by
        show (π ⟨k, hkL⟩)⁻¹ * π p * π ⟨k, hkL⟩ = π p'
        rw [← map_inv, ← map_mul, ← map_mul]
        apply congrArg π
        apply Subtype.ext
        simp [p', mul_assoc]
      have hyeq : y = kq⁻¹ * (kq * y * kq⁻¹) * kq := by group
      rw [hyeq, ← hpy, hkqinv]
      change π p' ∈ (Vq : Subgroup (oTwoQuot ↥L))
      rw [hVqcoe]
      exact Subgroup.mem_map_of_mem _ hp'
  have hfixq : φq kq = kq := by
    rw [show φq = (conjModPCore 2 L M hM) cN from rfl]
    simp only [kq, π, QuotientGroup.mk'_apply]
    rw [conjModPCore_mk]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    show c * k * c⁻¹ = k
    rw [hck]
    group
  have hφq1 : φq = 1 :=
    eq_one_of_preserves_sylow_of_twoPow_of_mulEquiv e φq Vq kq hVq_pres h2q hkq3 hkqN hfixq
  have hcNker : cN ∈ (conjModPCore 2 L M hM).ker := by
    rw [MonoidHom.mem_ker]
    exact hφq1
  have hcK : c ∈ ((conjModPCore 2 L M hM).ker.map M.subtype) :=
    Subgroup.mem_map.mpr ⟨cN, hcNker, rfl⟩
  have hcomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L M hM).mp hcK
  intro l hl
  simpa [commutatorElement_def] using hcomm.2 l hl

theorem exists_conjModPCore_eq_one_of_fixes_sylow
    {G : Type} [Group G] {L : Subgroup G} [Finite ↥L] {c : G}
    (e : oTwoQuot ↥L ≃* Alt5) (hc : c ∈ Subgroup.normalizer (L : Set G))
    {P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hfixP : ∀ p ∈ P, ⁅c, p⁆ ∈ CFSG.Open.pCoreOf 2 L) :
    ∃ q ∈ P, ∀ l ∈ L, ⁅c * q⁻¹, l⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  classical
  let M : Subgroup G := Subgroup.normalizer (L : Set G)
  have hM : M ≤ Subgroup.normalizer (L : Set G) := le_rfl
  let cN : ↥M := ⟨c, hc⟩
  let φq : MulAut (oTwoQuot ↥L) := conjModPCore 2 L M hM cN
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨S, hS⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow hP
  let Vq : Sylow 2 (oTwoQuot ↥L) := S.mapSurjective (f := π) hπsurj
  have hVqcoe : (Vq : Subgroup (oTwoQuot ↥L)) = (P.subgroupOf L).map π := by
    change (S.mapSurjective (f := π) hπsurj : Subgroup (oTwoQuot ↥L)) =
      (P.subgroupOf L).map π
    rw [Sylow.coe_mapSurjective, hS]
  have hfixVq : ∀ y : oTwoQuot ↥L, y ∈ Vq → φq y = y := by
    intro y hy
    have hy' : y ∈ (Vq : Subgroup (oTwoQuot ↥L)) := hy
    change y ∈ (Vq : Subgroup (oTwoQuot ↥L)) at hy'
    rw [hVqcoe] at hy'
    obtain ⟨p, hp, hpy⟩ := hy'
    rw [← hpy]
    have hpL : (p : G) ∈ L := p.2
    have hcL : c * (p : G) * c⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hc (p : G)).mp hpL
    let p'' : ↥L := ⟨c * (p : G) * c⁻¹, hcL⟩
    have hφp : φq (π p) = π p'' := by
      rw [show φq = (conjModPCore 2 L M hM) cN from rfl]
      simp only [π, QuotientGroup.mk'_apply]
      rw [conjModPCore_mk]
    have hcomm : c * (p : G) * c⁻¹ * (p : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      simpa [commutatorElement_def] using hfixP (p : G) hp
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hcomm
    have hdiv : p'' / p ∈ CFSG.Open.pCore 2 ↥L := by
      have hz' : p'' / p = z := by
        apply Subtype.ext
        rw [div_eq_mul_inv]
        simpa [p''] using hzeq.symm
      rwa [hz']
    have hclass : π p'' = π p := QuotientGroup.eq_iff_div_mem.mpr hdiv
    rw [hφp, hclass]
  obtain ⟨v, hvVq, hvφ⟩ := exists_mem_sylow_of_fixes_of_mulEquiv e φq Vq hfixVq
  have hv' : v ∈ (Vq : Subgroup (oTwoQuot ↥L)) := hvVq
  change v ∈ (Vq : Subgroup (oTwoQuot ↥L)) at hv'
  rw [hVqcoe] at hv'
  obtain ⟨qL, hqP, hqv⟩ := hv'
  let q : G := qL
  have hq : q ∈ P := hqP
  have hqL : q ∈ L := qL.2
  have hqM : q ∈ M := Subgroup.le_normalizer hqL
  have hcqM : c * q⁻¹ ∈ M := M.mul_mem hc (M.inv_mem hqM)
  let cqN : ↥M := ⟨c * q⁻¹, hcqM⟩
  have hcqN_eq : cqN = cN * (⟨q, hqM⟩ : ↥M)⁻¹ := by
    apply Subtype.ext
    rfl
  have hqAut : (conjModPCore 2 L M hM) (⟨q, hqM⟩ : ↥M) = MulAut.conj v := by
    have h := conjModPCore_apply_eq_conj_mk 2 L M hM hqM hqL
    rw [show QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥L) ⟨q, hqL⟩ = v from by
      simpa [π, QuotientGroup.mk'_apply] using hqv] at h
    exact h
  have hcqKer : cqN ∈ (conjModPCore 2 L M hM).ker := by
    rw [MonoidHom.mem_ker]
    calc (conjModPCore 2 L M hM) cqN
        = (conjModPCore 2 L M hM) cN *
            ((conjModPCore 2 L M hM) (⟨q, hqM⟩ : ↥M))⁻¹ := by
            rw [hcqN_eq, map_mul, map_inv]
      _ = φq * (MulAut.conj v)⁻¹ := by rw [hqAut]
      _ = 1 := by rw [show φq = MulAut.conj v from hvφ, mul_inv_cancel]
  have hcK : c * q⁻¹ ∈ ((conjModPCore 2 L M hM).ker.map M.subtype) :=
    Subgroup.mem_map.mpr ⟨cqN, hcqKer, rfl⟩
  have hcomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L M hM).mp hcK
  refine ⟨q, hq, fun l hl => ?_⟩
  simpa [commutatorElement_def] using hcomm.2 l hl

end CFSG.GroupTheory.AlternatingFive
