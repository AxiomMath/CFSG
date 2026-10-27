module

public import CFSG.FeitThompson.Foundations.NormOneGroupOrder
public import CFSG.FeitThompson.OddOrder.ComparisonWordFixedVector
public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.OddOrder.NormUnitsIrreducible
import CFSG.FeitThompson.OddOrder.AffineFieldCentralizers
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
import CFSG.FeitThompson.Local.PrimeOrderFixedFreeKernelCoprime
import CFSG.FeitThompson.Local.PSubgroupCentralizersLiftQuotient

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset Multiplicative Pointwise Subgroup

variable {p q : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

@[simp] theorem mem_map_conj_inv {A : Subgroup G} {g x : G} :
    x ∈ A.map (MulAut.conj g⁻¹ : G →* G) ↔ g * x * g⁻¹ ∈ A := by
  refine ⟨?_, fun h => ⟨g * x * g⁻¹, h, by simp [MulAut.conj, mul_assoc]⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [MulAut.conj, mul_assoc] using hk

theorem natCard_map_conj_inv (A : Subgroup G) (g : G) :
    Nat.card (A.map (MulAut.conj g⁻¹ : G →* G)) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem mem_normalizer_of_map_conj_inv_le [Finite G] {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g⁻¹ : G →* G) ≤ A) : g ∈ normalizer (A : Set G) := by
  have heq : A.map (MulAut.conj g⁻¹ : G →* G) = A :=
    Subgroup.eq_of_le_of_card_ge h (by rw [natCard_map_conj_inv])
  have : g⁻¹ ∈ normalizer (A : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
  simpa using inv_mem this

theorem mem_normalizer_of_le_map_conj_inv [Finite G] {A : Subgroup G} {g : G}
    (h : A ≤ A.map (MulAut.conj g⁻¹ : G →* G)) : g ∈ normalizer (A : Set G) :=
  mem_normalizer_of_map_conj_inv_le
    (Subgroup.eq_of_le_of_card_ge h (by rw [natCard_map_conj_inv])).ge

theorem le_map_conj_inv_of_mem_normalizer {A B : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) (hAB : A ≤ B) : A ≤ B.map (MulAut.conj g⁻¹ : G →* G) :=
  fun _ hx => mem_map_conj_inv.mpr (hAB ((mem_normalizer_iff.mp hg _).mp hx))

theorem map_conj_inv_le_of_mem {A L : Subgroup G} {g : G} (hg : g ∈ L) (hAL : A ≤ L) :
    A.map (MulAut.conj g⁻¹ : G →* G) ≤ L := by
  intro x hx
  have hxe : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [hxe]
  exact mul_mem (mul_mem (inv_mem hg) (hAL (mem_map_conj_inv.mp hx))) hg

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (ha : g ∈ normalizer (A : Set G))
    (hb : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_normalizer_iff.mp ha h,
    mem_normalizer_iff.mp hb h]

theorem le_of_isPGroup_of_le_normalizer_of_natCard_eq' [Finite G] (hp : p.Prime)
    {L A T : Subgroup G} (hAL : A ≤ L) (hTL : T ≤ L)
    (hA : Nat.card A = p ^ (Nat.card L).factorization p) (hT : IsPGroup p T)
    (hTA : T ≤ normalizer (A : Set G)) : T ≤ A := by
  have hA' : Nat.card (A.subgroupOf L) = p ^ (Nat.card L).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv, hA]
  have hT' : IsPGroup p (T.subgroupOf L) := hT.of_equiv (subgroupOfEquivOfLe hTL).symm
  have hTA' : T.subgroupOf L ≤ normalizer ((A.subgroupOf L : Subgroup L) : Set L) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => (Subgroup.mem_normalizer_iff.mp (hTA hx) h).mp hh,
      fun hh => (Subgroup.mem_normalizer_iff.mp (hTA hx) h).mpr hh⟩
  have key := le_of_isPGroup_of_le_normalizer_of_natCard_eq hp hA' hT' hTA'
  intro x hx
  exact key (show (⟨x, hTL hx⟩ : L) ∈ T.subgroupOf L from hx)

theorem normalizer_le_normalizer_of_natCard_eq [Finite G] (hp : p.Prime) {H A : Subgroup G}
    (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))
    (hA : Nat.card A = p ^ (Nat.card H).factorization p) :
    normalizer (H : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  have hTH : A.map (MulAut.conj g⁻¹ : G →* G) ≤ H :=
    fun x hx => (mem_normalizer_iff.mp hg x).mpr (hAH (mem_map_conj_inv.mp hx))
  have hTcard : Nat.card (A.map (MulAut.conj g⁻¹ : G →* G))
      = p ^ (Nat.card H).factorization p := by rw [natCard_map_conj_inv, hA]
  exact mem_normalizer_of_map_conj_inv_le
    (le_of_isPGroup_of_le_normalizer_of_natCard_eq' hp hAH hTH hA (IsPGroup.of_card hTcard)
      (hTH.trans hHA))

theorem natCard_sup_eq_mul_of_coprime_of_le_normalizer [Finite G] (hp : p.Prime) {Q A : Subgroup G}
    (hQ : (Nat.card Q).Coprime p) (hA : IsPGroup p A) (hAQ : A ≤ normalizer (Q : Set G)) :
    Nat.card (Q ⊔ A : Subgroup G) = Nat.card Q * Nat.card A := by
  have : Fact p.Prime := ⟨hp⟩
  have hbot : A ⊓ Q = ⊥ := inf_eq_bot_of_coprime_natCard hQ hA
  have h := natCard_sup_mul_natCard_inf_of_le_normalizer hAQ
  rw [show Q ⊓ A = ⊥ by rw [inf_comm]; exact hbot] at h
  simpa using h

theorem natCard_eq_pow_factorization_natCard_sup_of_coprime [Finite G] (hp : p.Prime)
    {Q A : Subgroup G} (hQ : (Nat.card Q).Coprime p) (hA : Nat.card A = p)
    (hAQ : A ≤ normalizer (Q : Set G)) :
    Nat.card A = p ^ ((Nat.card (Q ⊔ A : Subgroup G)).factorization p) := by
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hnd : ¬ p ∣ Nat.card Q := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hQ.symm h)
  rw [natCard_sup_eq_mul_of_coprime_of_le_normalizer hp hQ hAp hAQ, hA,
    Nat.factorization_mul Nat.card_pos.ne' hp.pos.ne']
  simp [Nat.factorization_eq_zero_of_not_dvd hnd, hp.factorization_self]

theorem inf_sup_eq_of_coprime [Finite G] (hp : p.Prime) {Q A A' : Subgroup G}
    (hQ : (Nat.card Q).Coprime p) (hA'p : IsPGroup p A') (hAA' : A ≤ A')
    (hAQ : A ≤ normalizer (Q : Set G)) : A' ⊓ (Q ⊔ A) = A := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ (le_inf hAA' le_sup_right)
  intro x hx
  obtain ⟨hxA', hxL⟩ := Subgroup.mem_inf.mp hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Q A hAQ] at hxL
  obtain ⟨a, ha, r, hr, hxeq⟩ := hxL
  have hxeq' : a * r = x := hxeq
  have haA' : a ∈ A' := by
    have he : a = x * r⁻¹ := by rw [← hxeq']; group
    rw [he]; exact mul_mem hxA' (inv_mem (hAA' hr))
  have ha1 : a = 1 := by
    have hmem : a ∈ A' ⊓ Q := Subgroup.mem_inf.2 ⟨haA', ha⟩
    rwa [inf_eq_bot_of_coprime_natCard hQ hA'p, Subgroup.mem_bot] at hmem
  rw [← hxeq', ha1, one_mul]
  exact hr

theorem normExponent_eq_geomSum (hp : p.Prime) (q : ℕ) :
    normExponent p q = ∑ i ∈ range q, p ^ i := by
  rw [normExponent_def, Nat.geomSum_eq hp.two_le]

theorem one_lt_normExponent (hp : p.Prime) (hq : 2 ≤ q) : 1 < normExponent p q := by
  rw [normExponent_eq_geomSum hp]
  calc 1 < 1 + p := by have := hp.pos; omega
    _ = ∑ i ∈ range 2, p ^ i := by simp [Finset.sum_range_succ]
    _ ≤ ∑ i ∈ range q, p ^ i := Finset.sum_le_sum_of_subset (by simpa using hq)

theorem rootsOfUnity_normExponent_eq_normOneUnits [Finite F] (hp : p.Prime)
    (hcard : Nat.card F = p ^ q) : rootsOfUnity (normExponent p q) F = normOneUnits F := by
  rw [normOneUnits_eq_rootsOfUnity hp hcard, normExponent_eq_geomSum hp]

def AppendixCSetup.subspaceOf [Finite F] (S : AppendixCSetup p q F G) (X : Subgroup G) :
    Submodule (⊥ : Subfield F) F where
  carrier := {z : F | S.pt (ofAdd z) ∈ X}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul] at *
    exact mul_mem ha hb
  smul_mem' c a ha := by
    have : Fact p.Prime := ⟨S.p_prime⟩
    have := S.charP_field
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).1 c.2
    have hc : (c : F) * a = n • a := by rw [← hn, zsmul_eq_mul]
    change S.pt (ofAdd ((c : F) * a)) ∈ X
    rw [hc, ofAdd_zsmul, map_zpow]
    exact zpow_mem ha n

namespace AppendixCSetup

variable [Finite F] (S : AppendixCSetup p q F G)

theorem apply_mem_P (w : Multiplicative F) : S.pt w ∈ S.P := S.P_def ▸ ⟨w, rfl⟩

theorem natCard_P : Nat.card S.P = p ^ q := by
  rw [S.P_def, ← S.card_field]
  exact Nat.card_congr (MonoidHom.ofInjective S.pt_injective).symm.toEquiv

theorem isPGroup_P : IsPGroup p S.P := IsPGroup.of_card S.natCard_P

theorem natCard_U : Nat.card S.U = normExponent p q := by
  rw [S.U_def, Nat.card_congr (MonoidHom.ofInjective S.ut_injective).symm.toEquiv,
    rootsOfUnity_normExponent_eq_normOneUnits S.p_prime S.card_field,
    natCard_normOneUnits_eq_div S.p_prime S.card_field, normExponent_def]

theorem not_dvd_natCard_U : ¬ p ∣ Nat.card S.U := by
  rw [S.natCard_U, normExponent_def]
  exact not_dvd_of_eq_div S.p_prime S.q_prime.ne_zero rfl

theorem one_lt_natCard_U : 1 < Nat.card S.U :=
  S.natCard_U ▸ one_lt_normExponent S.p_prime S.q_prime.two_le

theorem U_ne_bot : S.U ≠ ⊥ := fun h => by
  have h2 := S.one_lt_natCard_U; rw [h] at h2; simp at h2

theorem natCard_P₀ : Nat.card S.P₀ = p := by
  rw [S.P₀_def, Subgroup.card_map_of_injective S.pt_injective]
  exact (natCard_bot_subfield S.p_prime S.card_field).symm ▸ Nat.card_congr (Equiv.refl _)

theorem isPGroup_P₀ : IsPGroup p S.P₀ := IsPGroup.of_card (n := 1) (by rw [S.natCard_P₀, pow_one])

theorem P₀_ne_bot : S.P₀ ≠ ⊥ := fun h => by
  have h2 := S.natCard_P₀
  rw [h, Subgroup.card_bot] at h2
  exact S.p_prime.one_lt.ne h2

theorem P_inf_U : S.P ⊓ S.U = ⊥ := by
  rw [S.P_def, S.U_def, ← disjoint_iff]; exact S.disjoint_ranges

theorem U_le_normalizer_P : S.U ≤ normalizer (S.P : Set G) := by
  have hA : ∀ (u : rootsOfUnity (normExponent p q) F) (w : Multiplicative F),
      (S.ut u)⁻¹ * S.pt w * S.ut u ∈ S.P := fun u w =>
    S.P_def ▸ ⟨ofAdd (toAdd w * ((u : Fˣ) : F)), by rw [← S.conj_pt (toAdd w) u]; simp⟩
  rw [S.U_def]
  rintro g ⟨u, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · rw [S.P_def] at hw
    obtain ⟨x, rfl⟩ := hw
    have h := hA u⁻¹ x
    rwa [map_inv, inv_inv] at h
  · rw [S.P_def] at hw
    obtain ⟨x, hx⟩ := hw
    have h := hA u x
    rw [hx] at h
    have e : (S.ut u)⁻¹ * (S.ut u * w * (S.ut u)⁻¹) * S.ut u = w := by group
    rwa [e] at h

theorem P_le_H : S.P ≤ S.H := S.H_def ▸ le_sup_left

theorem U_le_H : S.U ≤ S.H := S.H_def ▸ le_sup_right

theorem P₀_le_H : S.P₀ ≤ S.H := S.P₀_le_P.trans S.P_le_H

theorem H_le_of_P_le_of_U_le {X : Subgroup G} (hP : S.P ≤ X) (hU : S.U ≤ X) : S.H ≤ X :=
  (le_of_eq S.H_def).trans (sup_le hP hU)

theorem H_le_normalizer_P : S.H ≤ normalizer (S.P : Set G) :=
  S.H_def ▸ sup_le le_normalizer S.U_le_normalizer_P

theorem coe_H : (S.H : Set G) = (S.P : Set G) * (S.U : Set G) := by
  rw [S.H_def]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ S.U_le_normalizer_P

theorem natCard_H : Nat.card S.H = p ^ q * normExponent p q := by
  have h := natCard_sup_mul_natCard_inf_of_le_normalizer S.U_le_normalizer_P
  rw [S.P_inf_U, ← S.H_def, S.natCard_P, S.natCard_U] at h
  simpa using h

theorem natCard_P_eq_pow_factorization_natCard_H :
    Nat.card S.P = p ^ ((Nat.card S.H).factorization p) := by
  have hm : normExponent p q ≠ 0 := (one_lt_normExponent S.p_prime S.q_prime.two_le).ne_bot
  have hnd : ¬ p ∣ normExponent p q := by rw [← S.natCard_U]; exact S.not_dvd_natCard_U
  rw [S.natCard_H, Nat.factorization_mul (pow_ne_zero _ S.p_prime.pos.ne') hm]
  simp [S.p_prime.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd, S.natCard_P]

theorem normalizer_H_le_normalizer_P [Finite G] :
    normalizer (S.H : Set G) ≤ normalizer (S.P : Set G) :=
  normalizer_le_normalizer_of_natCard_eq S.p_prime S.P_le_H S.H_le_normalizer_P
    S.natCard_P_eq_pow_factorization_natCard_H

variable {S}

theorem mem_subspaceOf {X : Subgroup G} {z : F} :
    z ∈ S.subspaceOf X ↔ S.pt (ofAdd z) ∈ X := Iff.rfl

theorem subspaceOf_eq_top_iff {X : Subgroup G} : S.subspaceOf X = ⊤ ↔ S.P ≤ X := by
  rw [Submodule.eq_top_iff']
  refine ⟨fun h g hg => ?_, fun h z => mem_subspaceOf.2 (h (S.apply_mem_P _))⟩
  rw [S.P_def] at hg
  obtain ⟨w, rfl⟩ := hg
  have hw := h (toAdd w)
  rwa [mem_subspaceOf, ofAdd_toAdd] at hw

theorem subspaceOf_eq_bot_iff {X : Subgroup G} : S.subspaceOf X = ⊥ ↔ S.P ⊓ X = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    rw [S.P_def] at hg1
    obtain ⟨w, rfl⟩ := hg1
    have hz : toAdd w ∈ S.subspaceOf X := mem_subspaceOf.2 (by rwa [ofAdd_toAdd])
    rw [h, Submodule.mem_bot] at hz
    rw [Subgroup.mem_bot, show w = 1 from by rw [← ofAdd_toAdd w, hz, ofAdd_zero], map_one]
  · intro h
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hmem : S.pt (ofAdd z) ∈ S.P ⊓ X :=
      Subgroup.mem_inf.2 ⟨S.apply_mem_P _, mem_subspaceOf.1 hz⟩
    rw [h, Subgroup.mem_bot] at hmem
    simpa using S.pt_injective (hmem.trans (map_one S.pt).symm)

theorem inf_eq_bot_or_le_of_U_le {X : Subgroup G} (hU : S.U ≤ X) : S.P ⊓ X = ⊥ ∨ S.P ≤ X := by
  rw [← subspaceOf_eq_bot_iff, ← subspaceOf_eq_top_iff]
  refine (eq_or_ne (S.subspaceOf X) ⊥).imp id fun hne => ?_
  refine eq_top_of_mul_mem_of_pow_eq_one S.p_prime S.card_field
    (normExponent_def p q ▸ S.coprime_normExponent) hne ?_
  intro u hu0 hu x hx
  have hv : Units.mk0 u hu0 ∈ rootsOfUnity (normExponent p q) F := by
    rw [mem_rootsOfUnity, normExponent_def]
    exact Units.ext (by simpa using hu)
  have hmem : S.ut ⟨Units.mk0 u hu0, hv⟩ ∈ X := hU (S.U_def ▸ ⟨_, rfl⟩)
  have hc := S.conj_pt x ⟨Units.mk0 u hu0, hv⟩
  rw [mem_subspaceOf] at hx ⊢
  rw [mul_comm]
  have hxu : S.pt (ofAdd (x * ((Units.mk0 u hu0 : Fˣ) : F))) ∈ X := by
    rw [← hc]; exact mul_mem (mul_mem (inv_mem hmem) hx) hmem
  simpa using hxu

theorem eq_one_of_mem_P_of_commute {r u : G} (hr : r ∈ S.P) (hu : u ∈ S.U) (hu1 : u ≠ 1)
    (h : r * u = u * r) : r = 1 := by
  rw [S.P_def] at hr
  rw [S.U_def] at hu
  obtain ⟨w, rfl⟩ := hr
  obtain ⟨v, rfl⟩ := hu
  have hv : ((v : Fˣ) : F) ≠ 1 := fun he =>
    hu1 (by rw [show v = 1 from Subtype.ext (Units.ext he), map_one])
  have hconj := S.conj_pt (toAdd w) v
  rw [ofAdd_toAdd] at hconj
  have hfix : S.pt w = S.pt (ofAdd (toAdd w * ((v : Fˣ) : F))) := by
    rw [← hconj, mul_assoc, h]; group
  have h2 : toAdd w = toAdd w * ((v : Fˣ) : F) := by
    simpa using congrArg toAdd (S.pt_injective hfix)
  have hz : toAdd w * (((v : Fˣ) : F) - 1) = 0 := by rw [mul_sub, mul_one, ← h2, sub_self]
  have hw0 : toAdd w = 0 := (mul_eq_zero.1 hz).resolve_right fun h1 => hv (sub_eq_zero.1 h1)
  rw [show w = 1 from by rw [← ofAdd_toAdd w, hw0, ofAdd_zero], map_one]

theorem eq_bot_of_le_P_of_le_normalizer_U {A : Subgroup G} (hAP : A ≤ S.P)
    (hAU : A ≤ normalizer (S.U : Set G)) : A = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 S.U_ne_bot
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hcU : a⁻¹ * u⁻¹ * a * u ∈ S.U := by
    have h1 : a⁻¹ * u⁻¹ * a ∈ S.U := by
      have h := (Subgroup.mem_set_normalizer_iff''.mp (hAU ha) u⁻¹).mp (inv_mem hu)
      simpa [mul_assoc] using h
    simpa [mul_assoc] using mul_mem h1 hu
  have hcP : a⁻¹ * u⁻¹ * a * u ∈ S.P := by
    have h : u⁻¹ * a * u ∈ S.P :=
      (Subgroup.mem_set_normalizer_iff''.mp (S.U_le_normalizer_P hu) a).mp (hAP ha)
    have h2 : a⁻¹ * (u⁻¹ * a * u) ∈ S.P := mul_mem (inv_mem (hAP ha)) h
    simpa [mul_assoc] using h2
  have hc1 : a⁻¹ * u⁻¹ * a * u = 1 := by
    have hmem := Subgroup.mem_inf.2 ⟨hcP, hcU⟩
    rwa [S.P_inf_U, Subgroup.mem_bot] at hmem
  have hcomm : a * u = u * a := by
    have e : a⁻¹ * (u⁻¹ * a * u) = 1 := by rw [← hc1]; group
    have h3 := congrArg (fun x => u * x) (inv_mul_eq_one.mp e).symm
    simpa [mul_assoc] using h3
  exact Subgroup.mem_bot.2 (eq_one_of_mem_P_of_commute (hAP ha) hu hu1' hcomm)

theorem eq_U_of_le_H_of_U_le_of_inf_eq_bot {X : Subgroup G} (hXH : X ≤ S.H) (hUX : S.U ≤ X)
    (hPX : S.P ⊓ X = ⊥) : X = S.U := by
  refine le_antisymm (fun x hx => ?_) hUX
  have hxH : (x : G) ∈ (S.H : Set G) := hXH hx
  rw [S.coe_H] at hxH
  obtain ⟨a, ha, u, hu, hxeq⟩ := hxH
  have hxeq' : a * u = x := hxeq
  have haX : a ∈ X := by
    have he : a = x * u⁻¹ := by rw [← hxeq']; group
    rw [he]; exact mul_mem hx (inv_mem (hUX hu))
  have ha1 : a = 1 := by
    have hmem : a ∈ S.P ⊓ X := Subgroup.mem_inf.2 ⟨ha, haX⟩
    rwa [hPX, Subgroup.mem_bot] at hmem
  rw [← hxeq', ha1, one_mul]
  exact hu

theorem H_inf_map_conj_inv_eq_U [Finite G] {Q : Subgroup G} (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : S.P₀ ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ Q)
    (hP₁U : S.P₀.map (MulAut.conj y⁻¹ : G →* G) ≤ normalizer (S.U : Set G))
    {z : G} (hz : z ∈ S.P₀.map (MulAut.conj y⁻¹ : G →* G)) (hz1 : z ≠ 1) :
    S.H ⊓ S.H.map (MulAut.conj z⁻¹ : G →* G) = S.U := by
  have hp := S.p_prime
  set P₁ : Subgroup G := S.P₀.map (MulAut.conj y⁻¹ : G →* G) with hP₁
  have hUX : S.U ≤ S.H ⊓ S.H.map (MulAut.conj z⁻¹ : G →* G) :=
    le_inf S.U_le_H (le_map_conj_inv_of_mem_normalizer (hP₁U hz) S.U_le_H)
  rcases inf_eq_bot_or_le_of_U_le hUX with hbot | hPX
  · exact eq_U_of_le_H_of_U_le_of_inf_eq_bot inf_le_left hUX hbot
  exfalso
  have hHle : S.H ≤ S.H.map (MulAut.conj z⁻¹ : G →* G) :=
    S.H_le_of_P_le_of_U_le (hPX.trans inf_le_right) (hUX.trans inf_le_right)
  have hznP : z ∈ normalizer (S.P : Set G) :=
    S.normalizer_H_le_normalizer_P (mem_normalizer_of_le_map_conj_inv hHle)
  have hP₁card : Nat.card P₁ = p := by rw [hP₁, natCard_map_conj_inv, S.natCard_P₀]
  have hP₁P : P₁ ≤ normalizer (S.P : Set G) := by
    rw [← zpowers_eq_of_natCard_eq_prime hp hP₁card hz hz1]
    exact zpowers_le.mpr hznP
  have hP₀L : S.P₀ ≤ Q ⊔ S.P₀ := le_sup_right
  have hP₁L : P₁ ≤ Q ⊔ S.P₀ := map_conj_inv_le_of_mem (le_sup_left (a := Q) hy) hP₀L
  have hPL : S.P ⊓ (Q ⊔ S.P₀) = S.P₀ :=
    inf_sup_eq_of_coprime hp hQp S.isPGroup_P S.P₀_le_P hQnorm
  have hP₁P₀ : P₁ ≤ normalizer (S.P₀ : Set G) := by
    rw [← hPL]
    exact fun x hx => mem_normalizer_inf (hP₁P hx) (le_normalizer (hP₁L hx))
  have hfull : Nat.card S.P₀ = p ^ ((Nat.card (Q ⊔ S.P₀ : Subgroup G)).factorization p) :=
    natCard_eq_pow_factorization_natCard_sup_of_coprime hp hQp S.natCard_P₀ hQnorm
  have hP₁eq : P₁ = S.P₀ :=
    Subgroup.eq_of_le_of_card_ge
      (le_of_isPGroup_of_le_normalizer_of_natCard_eq' hp hP₀L hP₁L hfull
        (IsPGroup.of_card (n := 1) (by rw [hP₁card, pow_one])) hP₁P₀)
      (by rw [hP₁card, S.natCard_P₀])
  exact S.P₀_ne_bot (eq_bot_of_le_P_of_le_normalizer_U S.P₀_le_P (hP₁eq ▸ hP₁U))

theorem H_inf_map_conj_inv_eq_U_of_appendixC [Finite G] {Q : Subgroup G}
    (_hQab : ∀ x ∈ Q, ∀ w ∈ Q, x * w = w * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : S.P₀ ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ Q)
    {P₁ : Subgroup G} (hP₁ : P₁ = S.P₀.map (MulAut.conj y⁻¹ : G →* G))
    (hP₁U : P₁ ≤ normalizer (S.U : Set G)) {t : G} (_ht : t = y⁻¹ * S.s * y)
    {z : G} (hz : z ∈ P₁) (hz1 : z ≠ 1) :
    S.H ⊓ S.H.map (MulAut.conj z⁻¹ : G →* G) = S.U :=
  H_inf_map_conj_inv_eq_U hQp hQnorm hy (hP₁ ▸ hP₁U) (hP₁ ▸ hz) hz1

end AppendixCSetup

end

end CFSG.FeitThompson
