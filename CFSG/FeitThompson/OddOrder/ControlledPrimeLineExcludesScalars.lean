module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Complement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem zmod_smul_eq_val_nsmul [NeZero p] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (a : ZMod p) (w : W) : a • w = a.val • w := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) a.val w, ZMod.natCast_val, ZMod.cast_id]

theorem nsmul_eq_zero_of_module_zmod [NeZero p] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (w : W) : p • w = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p w, ZMod.natCast_self, zero_smul]

theorem ofMul_pow_val_eq_smul [NeZero p] {A : Type*} [CommGroup A]
    [Module (ZMod p) (Additive A)] (a : ZMod p) (v : A) :
    Additive.ofMul (v ^ a.val) = a • Additive.ofMul v := by
  rw [ofMul_pow, zmod_smul_eq_val_nsmul]

theorem mem_normalizer_zpowers_of_conj_eq_pow (hp : p.Prime) {x g : G} (hx : x ≠ 1)
    (hxp : x ^ p = 1) {k : ℕ} (hconj : g⁻¹ * x * g = x ^ k) :
    g ∈ normalizer (zpowers x : Set G) := by
  have hfp := Fact.mk hp
  have hord : orderOf x = p := orderOf_eq_prime hxp hx
  have hxk : x ^ k ≠ 1 := by
    rw [← hconj]
    intro h
    exact hx (by simpa [mul_assoc] using congrArg (fun y : G => g * y * g⁻¹) h)
  have hk : ¬ p ∣ k := fun hdvd => hxk (by obtain ⟨m, rfl⟩ := hdvd; rw [pow_mul, hxp, one_pow])
  have hcop : k.Coprime (orderOf x) := by
    rw [hord]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hmap : (zpowers x).map ((MulAut.conj g⁻¹ : MulAut G) : G →* G) = zpowers x := by
    rw [MonoidHom.map_zpowers]
    have hc : ((MulAut.conj g⁻¹ : MulAut G) : G →* G) x = x ^ k := by
      simpa [mul_assoc] using hconj
    rw [hc]
    refine le_antisymm (zpowers_le.mpr (pow_mem (mem_zpowers x) k)) (zpowers_le.mpr ?_)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by rw [zpow_natCast]; exact hm⟩
  simpa using inv_mem (mem_normalizer_iff_map_conj_eq.mpr hmap)

theorem disjoint_of_isComplement'_subgroupOf {H E L : Subgroup G} (hEL : E ≤ L)
    (hcompl : (H.subgroupOf L).IsComplement' (E.subgroupOf L)) : Disjoint H E := by
  rw [Subgroup.disjoint_def]
  intro y hyH hyE
  have hyL : y ∈ L := hEL hyE
  have h1 : (⟨y, hyL⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hyH
  have h2 : (⟨y, hyL⟩ : L) ∈ E.subgroupOf L := Subgroup.mem_subgroupOf.mpr hyE
  exact congrArg Subtype.val (Subgroup.disjoint_def.mp hcompl.disjoint h1 h2)

theorem eq_one_of_forall_conj_eq_pow (hp : p.Prime) {H E L M V : Subgroup G}
    (hEL : E ≤ L) (hHE : Disjoint H E) (hML : M ⊓ L ≤ H)
    (hVexp : ∀ v ∈ V, v ^ p = 1) {x : G} (hxV : x ∈ V) (hx : x ≠ 1)
    (hNx : normalizer (zpowers x : Set G) ≤ M) {e : G} (heE : e ∈ E) {k : ℕ}
    (hconj : ∀ v ∈ V, e⁻¹ * v * e = v ^ k) : e = 1 := by
  have hmem : e ∈ normalizer (zpowers x : Set G) :=
    mem_normalizer_zpowers_of_conj_eq_pow hp hx (hVexp x hxV) (hconj x hxV)
  exact Subgroup.disjoint_def.mp hHE (hML (mem_inf.mpr ⟨hNx hmem, hEL heE⟩)) heE

theorem not_forall_conj_eq_pow (hp : p.Prime) {H E L M V : Subgroup G} (hEL : E ≤ L)
    (hcompl : (H.subgroupOf L).IsComplement' (E.subgroupOf L)) (hML : M ⊓ L ≤ H)
    (hVexp : ∀ v ∈ V, v ^ p = 1) {x : G} (hxV : x ∈ V) (hx : x ≠ 1)
    (hNx : normalizer (zpowers x : Set G) ≤ M) {e : G} (heE : e ∈ E) (he : e ≠ 1) (k : ℕ) :
    ¬ ∀ v ∈ V, e⁻¹ * v * e = v ^ k := fun hconj =>
  he (eq_one_of_forall_conj_eq_pow hp hEL (disjoint_of_isComplement'_subgroupOf hEL hcompl)
    hML hVexp hxV hx hNx heE hconj)

theorem not_exists_zmod_forall_conj_eq_pow_val (hp : p.Prime) {H E L M V : Subgroup G}
    (hEL : E ≤ L) (hcompl : (H.subgroupOf L).IsComplement' (E.subgroupOf L)) (hML : M ⊓ L ≤ H)
    (hVexp : ∀ v ∈ V, v ^ p = 1) {x : G} (hxV : x ∈ V) (hx : x ≠ 1)
    (hNx : normalizer (zpowers x : Set G) ≤ M) {e : G} (heE : e ∈ E) (he : e ≠ 1) :
    ¬ ∃ a : ZMod p, ∀ v ∈ V, e⁻¹ * v * e = v ^ (a.val) := by
  rintro ⟨a, ha⟩
  exact not_forall_conj_eq_pow hp hEL hcompl hML hVexp hxV hx hNx heE he a.val ha

theorem not_exists_smul_eq_conj (hp : p.Prime) {H E L M : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W] (f : Multiplicative W →* G)
    (hEL : E ≤ L) (hcompl : (H.subgroupOf L).IsComplement' (E.subgroupOf L)) (hML : M ⊓ L ≤ H)
    {y : W} (hy : f (Multiplicative.ofAdd y) ≠ 1)
    (hNy : normalizer (zpowers (f (Multiplicative.ofAdd y)) : Set G) ≤ M)
    {e : G} (heE : e ∈ E) (he : e ≠ 1) :
    ¬ ∃ a : ZMod p, ∀ w : W,
      e⁻¹ * f (Multiplicative.ofAdd w) * e = f (Multiplicative.ofAdd (a • w)) := by
  have hnz : NeZero p := ⟨hp.ne_zero⟩
  rintro ⟨a, ha⟩
  refine not_forall_conj_eq_pow hp hEL hcompl hML (V := f.range) ?_ ⟨_, rfl⟩ hy hNy heE he a.val ?_
  · rintro v ⟨w, rfl⟩
    have hw : w ^ p = 1 := by
      have h1 := congrArg Multiplicative.ofAdd (nsmul_eq_zero_of_module_zmod (p := p)
        (Multiplicative.toAdd w))
      rwa [ofAdd_nsmul, ofAdd_zero] at h1
    rw [← map_pow, hw, map_one]
  · rintro v ⟨w, rfl⟩
    have h := ha (Multiplicative.toAdd w)
    rwa [zmod_smul_eq_val_nsmul, ofAdd_nsmul, map_pow] at h

end

end CFSG.FeitThompson
