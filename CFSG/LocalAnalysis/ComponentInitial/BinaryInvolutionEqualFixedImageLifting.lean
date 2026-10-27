module

public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.ComponentInitial.EqualFixedImage

open Subgroup

variable {X : Type*} [Group X]

theorem inv_eq_self_of_sq {e : X} (h : e ^ 2 = 1) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, h])

theorem commute_of_sq_eq_one {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1) {e f : X} (he : e ∈ E)
    (hf : f ∈ E) : e * f = f * e := by
  have h := inv_eq_self_of_sq (hE _ (E.mul_mem he hf))
  rw [mul_inv_rev, inv_eq_self_of_sq (hE e he), inv_eq_self_of_sq (hE f hf)] at h
  exact h.symm

theorem le_centralizer_of_sq {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1) :
    E ≤ centralizer (E : Set X) := fun _ he =>
  mem_centralizer_iff.mpr fun _ hf => commute_of_sq_eq_one hE hf he

theorem exists_mul_inv_commute {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1) {z : X}
    (hz : z ^ 2 = 1) (hA : ∀ a ∈ E, z * a = a * z → ∃ e ∈ E, e⁻¹ * z⁻¹ * e * z = a) {x : X}
    (hx : x⁻¹ * z⁻¹ * x * z ∈ E) : ∃ e ∈ E, x * e⁻¹ * z = z * (x * e⁻¹) := by
  have hzi : z⁻¹ = z := inv_eq_self_of_sq hz
  have hdi := inv_eq_self_of_sq (hE _ hx)
  have hzd : z * (x⁻¹ * z⁻¹ * x * z) = x⁻¹ * z⁻¹ * x * z * z := by
    rw [hzi] at hdi ⊢
    have h1 : z * x⁻¹ * z * x = x⁻¹ * z * x * z := by
      rw [← hdi]
      simp only [mul_inv_rev, inv_inv, hzi]
      group
    calc z * (x⁻¹ * z * x * z) = z * x⁻¹ * z * x * z := by group
      _ = x⁻¹ * z * x * z * z := by rw [h1]
  obtain ⟨e, he, hed⟩ := hA _ hx hzd
  refine ⟨e, he, ?_⟩
  have h2 : e⁻¹ * z = z * ((x⁻¹ * z⁻¹ * x * z)⁻¹ * e⁻¹) := by
    rw [← hed]
    group
  calc x * e⁻¹ * z = x * (e⁻¹ * z) := by group
    _ = x * (z * ((x⁻¹ * z⁻¹ * x * z)⁻¹ * e⁻¹)) := by rw [h2]
    _ = z * (x * e⁻¹) := by group

theorem centralizer_mk_eq_map_centralizer {E : Subgroup X} [E.Normal] (hE : ∀ e ∈ E, e ^ 2 = 1)
    {z : X} (hz : z ^ 2 = 1) (hA : ∀ a ∈ E, z * a = a * z → ∃ e ∈ E, e⁻¹ * z⁻¹ * e * z = a) :
    centralizer {(z : X ⧸ E)} = (centralizer {z}).map (QuotientGroup.mk' E) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [mem_centralizer_singleton_iff] at hq
    have hx : x⁻¹ * z⁻¹ * x * z ∈ E := by
      rw [← QuotientGroup.eq_one_iff, show (x⁻¹ * z⁻¹ * x * z : X) = (z * x)⁻¹ * (x * z) by group,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hq,
        inv_mul_cancel]
    obtain ⟨e, he, hcomm⟩ := exists_mul_inv_commute hE hz hA hx
    refine ⟨x * e⁻¹, mem_centralizer_singleton_iff.mpr hcomm, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff e).mpr he, inv_one, mul_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hx,
      QuotientGroup.mk_mul]

theorem mem_of_commutator_mem {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1) {z : X}
    (hz : z ^ 2 = 1) (hA : ∀ a ∈ E, z * a = a * z → ∃ e ∈ E, e⁻¹ * z⁻¹ * e * z = a)
    (hCA : centralizer (E : Set X) ⊓ centralizer {z} = E ⊓ centralizer {z}) {c : X}
    (hc : c ∈ centralizer (E : Set X)) (hcz : c⁻¹ * z⁻¹ * c * z ∈ E) : c ∈ E := by
  obtain ⟨e, he, hcomm⟩ := exists_mul_inv_commute hE hz hA hcz
  have h1 : c * e⁻¹ ∈ centralizer (E : Set X) ⊓ centralizer {z} :=
    mem_inf.mpr ⟨mul_mem hc (inv_mem (le_centralizer_of_sq hE he)),
      mem_centralizer_singleton_iff.mpr hcomm⟩
  rw [hCA] at h1
  simpa using mul_mem (mem_inf.mp h1).1 he

section quotient

variable {E : Subgroup X} [E.Normal] (z : X)

@[expose] noncomputable def conjCent : centralizer (E : Set X) →* centralizer (E : Set X) :=
  (MulAut.conjNormal (H := centralizer (E : Set X)) z).toMonoidHom

theorem conjCent_apply (c : centralizer (E : Set X)) :
    (conjCent (E := E) z c : X) = z * c * z⁻¹ :=
  MulAut.conjNormal_apply z c

theorem subgroupOf_le_comap_conjCent :
    E.subgroupOf (centralizer (E : Set X)) ≤
      (E.subgroupOf (centralizer (E : Set X))).comap (conjCent (E := E) z) := fun c hc => by
  rw [mem_comap, mem_subgroupOf, conjCent_apply]
  exact (inferInstance : E.Normal).conj_mem _ (mem_subgroupOf.mp hc) z

@[expose] noncomputable def quotAct :
    centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X)) →*
      centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X)) :=
  QuotientGroup.map _ _ (conjCent (E := E) z) (subgroupOf_le_comap_conjCent z)

theorem quotAct_mk (c : centralizer (E : Set X)) :
    quotAct (E := E) z (c : centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X))) =
      ((conjCent (E := E) z c : centralizer (E : Set X)) :
        centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X))) :=
  rfl

theorem quotAct_involutive {z : X} (hz : z ^ 2 = 1) :
    Function.Involutive (quotAct (E := E) z) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H c =>
    rw [quotAct_mk, quotAct_mk]
    congr 1
    ext
    rw [conjCent_apply, conjCent_apply, inv_eq_self_of_sq hz]
    calc z * (z * (c : X) * z) * z = (z * z) * c * (z * z) := by group
      _ = c := by rw [← sq, hz, one_mul, mul_one]

theorem quotAct_fixedPointFree (hE : ∀ e ∈ E, e ^ 2 = 1) {z : X} (hz : z ^ 2 = 1)
    (hA : ∀ a ∈ E, z * a = a * z → ∃ e ∈ E, e⁻¹ * z⁻¹ * e * z = a)
    (hCA : centralizer (E : Set X) ⊓ centralizer {z} = E ⊓ centralizer {z}) :
    MonoidHom.FixedPointFree (quotAct (E := E) z) := by
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H c =>
    rw [quotAct_mk, QuotientGroup.eq, mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    refine mem_of_commutator_mem hE hz hA hCA c.2 ?_
    have h := (inferInstance : E.Normal).conj_mem _ hq z⁻¹
    rw [coe_mul, coe_inv, conjCent_apply, inv_inv] at h
    convert h using 1
    group

end quotient

variable {E : Subgroup X} [E.Normal]

theorem exists_odd_pow_mem [Finite X] {z : X} (hfpf : MonoidHom.FixedPointFree (quotAct (E := E) z))
    (hinv : Function.Involutive (quotAct (E := E) z)) {x : X} (hx : x ∈ centralizer (E : Set X)) :
    ∃ m, Odd m ∧ x ^ m ∈ E := by
  refine ⟨Nat.card (centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X))),
    hfpf.odd_card_of_involutive hinv, ?_⟩
  have h1 : (((⟨x, hx⟩ : centralizer (E : Set X)) ^ Nat.card (centralizer (E : Set X) ⧸
      E.subgroupOf (centralizer (E : Set X))) : centralizer (E : Set X)) :
        centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X))) = 1 := by
    rw [QuotientGroup.mk_pow, pow_card_eq_one']
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  simpa using h1

theorem commute_of_mem_centralizer [Finite X] (hE : ∀ e ∈ E, e ^ 2 = 1) {z : X}
    (hfpf : MonoidHom.FixedPointFree (quotAct (E := E) z))
    (hinv : Function.Involutive (quotAct (E := E) z)) {x y : X}
    (hx : x ∈ centralizer (E : Set X)) (hy : y ∈ centralizer (E : Set X)) : x * y = y * x := by
  have hcomm := hfpf.commute_all_of_involutive hinv
  obtain ⟨m, hodd, hxm⟩ := exists_odd_pow_mem hfpf hinv hx
  set x' : centralizer (E : Set X) := ⟨x, hx⟩
  set y' : centralizer (E : Set X) := ⟨y, hy⟩
  have ht : x⁻¹ * y⁻¹ * x * y ∈ E := by
    have h2 : ((x'⁻¹ * y'⁻¹ * x' * y' : centralizer (E : Set X)) :
        centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X))) = 1 := by
      rw [show x'⁻¹ * y'⁻¹ * x' * y' = (y' * x')⁻¹ * (x' * y') by group, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        (hcomm (x' : centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X)))
          (y' : centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X)))).eq,
        inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
    simpa using h2
  set t := x⁻¹ * y⁻¹ * x * y with htdef
  have hpow : ∀ n : ℕ, (x ^ n)⁻¹ * y⁻¹ * x ^ n * y = t ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have htx : x⁻¹ * t ^ n = t ^ n * x⁻¹ :=
        ((mem_centralizer_iff.mp (inv_mem hx)) _ (pow_mem ht n)).symm
      calc (x ^ (n + 1))⁻¹ * y⁻¹ * x ^ (n + 1) * y
          = x⁻¹ * ((x ^ n)⁻¹ * y⁻¹ * x ^ n * y) * (y⁻¹ * x * y) := by group
        _ = x⁻¹ * t ^ n * (y⁻¹ * x * y) := by rw [ih]
        _ = t ^ n * (x⁻¹ * y⁻¹ * x * y) := by rw [htx]; group
        _ = t ^ (n + 1) := by rw [pow_succ]
  have htm : t ^ m = 1 := by
    rw [← hpow m]
    have h3 : x ^ m * y = y * x ^ m := (mem_centralizer_iff.mp hy) _ hxm
    calc (x ^ m)⁻¹ * y⁻¹ * x ^ m * y = (x ^ m)⁻¹ * y⁻¹ * (x ^ m * y) := by group
      _ = 1 := by rw [h3]; group
  have ht1 : t = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hE t ht, one_pow, one_mul] at htm
    exact htm
  calc x * y = y * x * t := by rw [htdef]; group
    _ = y * x := by rw [ht1, mul_one]

theorem ker_conjNormal : (MulAut.conjNormal (H := E)).ker = centralizer (E : Set X) := by
  ext x
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h e he
    have h1 := congrArg (fun φ : MulAut E => ((φ ⟨e, he⟩ : E) : X)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc e * x = x * e * x⁻¹ * x := by rw [h1]
      _ = x * e := by group
  · intro h
    ext ⟨e, he⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h e he]
    group

@[expose] def centralizerOddCore (E : Subgroup X) : Subgroup X :=
  (CFSG.piCore {q : Nat.Primes | q.val ≠ 2} (centralizer (E : Set X))).map
    (centralizer (E : Set X)).subtype

omit [E.Normal] in
theorem mem_centralizerOddCore_iff [Finite X] (hC : IsMulCommutative (centralizer (E : Set X)))
    {x : X} : x ∈ centralizerOddCore E ↔ x ∈ centralizer (E : Set X) ∧ Odd (orderOf x) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    have hπ := CFSG.LocalCores.piCore_isPiSubgroup (G := centralizer (E : Set X))
      {q : Nat.Primes | q.val ≠ 2}
    have hodd : Odd (Nat.card (CFSG.piCore {q : Nat.Primes | q.val ≠ 2}
        (centralizer (E : Set X)))) := by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      intro h2
      exact hπ ⟨2, Nat.prime_two⟩ h2 rfl
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hc)
  · rintro ⟨hx, hodd⟩
    have hn : (zpowers (⟨x, hx⟩ : centralizer (E : Set X))).Normal :=
      Subgroup.normal_of_isMulCommutative _
    have hπ : CFSG.IsPiSubgroup {q : Nat.Primes | q.val ≠ 2}
        (zpowers (⟨x, hx⟩ : centralizer (E : Set X))) := by
      intro q hq
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe] at hq
      intro hq2
      rw [hq2] at hq
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hq)
    exact ⟨⟨x, hx⟩, CFSG.LocalCores.le_piCore_of_normal hn hπ (mem_zpowers _), rfl⟩

theorem binary_involution_equal_fixed_image_centralizer_lifting [Finite X]
    (hE : ∀ e ∈ E, e ^ 2 = 1) {z : X} (hz : z ^ 2 = 1)
    (hfix : (fun e => e⁻¹ * z⁻¹ * e * z) '' (E : Set X) =
      ((E ⊓ centralizer {z} : Subgroup X) : Set X)) :
    centralizer {(z : X ⧸ E)} = (centralizer {z}).map (QuotientGroup.mk' E) ∧
      (centralizer (E : Set X) ⊓ centralizer {z} = E ⊓ centralizer {z} →
        IsMulCommutative (centralizer (E : Set X)) ∧
          E ⊔ centralizerOddCore E = centralizer (E : Set X) ∧ E ⊓ centralizerOddCore E = ⊥ ∧
          (∀ x, x ∈ centralizerOddCore E ↔ x ∈ centralizer (E : Set X) ∧ Odd (orderOf x)) ∧
          IsMulCommutative (centralizerOddCore E) ∧ (centralizerOddCore E).Normal ∧
          (∀ k ∈ centralizerOddCore E, z⁻¹ * k * z = k⁻¹) ∧
          (MulAut.conjNormal (H := E)).ker = E ⊔ centralizerOddCore E) := by
  have hA : ∀ a ∈ E, z * a = a * z → ∃ e ∈ E, e⁻¹ * z⁻¹ * e * z = a := fun a ha hza => by
    have : a ∈ ((E ⊓ centralizer {z} : Subgroup X) : Set X) :=
      mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hza.symm⟩
    rw [← hfix] at this
    obtain ⟨e, he, rfl⟩ := this
    exact ⟨e, he, rfl⟩
  refine ⟨centralizer_mk_eq_map_centralizer hE hz hA, fun hCA => ?_⟩
  have hfpf := quotAct_fixedPointFree hE hz hA hCA
  have hinv := quotAct_involutive (E := E) hz
  have hCcomm : IsMulCommutative (centralizer (E : Set X)) :=
    ⟨⟨fun a b => Subtype.ext (commute_of_mem_centralizer hE hfpf hinv a.2 b.2)⟩⟩
  have hK := fun x => mem_centralizerOddCore_iff (E := E) (x := x) hCcomm
  have hKC : centralizerOddCore E ≤ centralizer (E : Set X) := fun x hx => ((hK x).mp hx).1
  have hEK : E ⊓ centralizerOddCore E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_inf] at hx
    have hodd := ((hK x).mp hx.2).2
    rw [mem_bot, ← orderOf_eq_one_iff]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (hE x hx.1)) with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hEKC : E ⊔ centralizerOddCore E = centralizer (E : Set X) := by
    refine le_antisymm (sup_le (le_centralizer_of_sq hE) hKC) fun x hx => ?_
    obtain ⟨m, hm, hxm⟩ := exists_odd_pow_mem hfpf hinv hx
    have hsq : x ^ 2 ∈ centralizerOddCore E := by
      refine (hK _).mpr ⟨pow_mem hx 2, Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)⟩
      rw [← pow_mul, mul_comm, pow_mul, hE _ hxm]
    obtain ⟨k, rfl⟩ := hm
    have hx' : x = (x ^ (2 * k + 1))⁻¹ * (x ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      group
    rw [hx']
    exact mul_mem_sup (inv_mem hxm) (pow_mem hsq _)
  have hKn : (centralizerOddCore E).Normal := by
    refine ⟨fun k hk g => (hK _).mpr ⟨(inferInstance : (centralizer (E : Set X)).Normal).conj_mem
      k (hKC hk) g, ?_⟩⟩
    rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g k (g * k * g⁻¹) by
      rw [SemiconjBy]; group)]
    exact ((hK k).mp hk).2
  refine ⟨hCcomm, hEKC, hEK, hK, ?_, hKn, ?_, by rw [ker_conjNormal, hEKC]⟩
  · exact ⟨⟨fun a b => Subtype.ext (commute_of_mem_centralizer hE hfpf hinv (hKC a.2) (hKC b.2))⟩⟩
  ·
    intro k hk
    have hα := hfpf.coe_eq_inv_of_involutive hinv
    have h1 := congrFun hα ((⟨k, hKC hk⟩ : centralizer (E : Set X)) :
      centralizer (E : Set X) ⧸ E.subgroupOf (centralizer (E : Set X)))
    rw [quotAct_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq, mem_subgroupOf] at h1
    have hwE : k * (z * k * z⁻¹) ∈ E := by
      have h2 := inv_mem h1
      rw [coe_mul, coe_inv, coe_inv, conjCent_apply] at h2
      convert h2 using 1
      group
    have hwK : k * (z * k * z⁻¹) ∈ centralizerOddCore E := mul_mem hk (hKn.conj_mem k hk z)
    have hw1 : k * (z * k * z⁻¹) = 1 := by
      have : k * (z * k * z⁻¹) ∈ E ⊓ centralizerOddCore E := mem_inf.mpr ⟨hwE, hwK⟩
      rwa [hEK, mem_bot] at this
    have hzi : z⁻¹ = z := inv_eq_self_of_sq hz
    calc z⁻¹ * k * z = k⁻¹ * (k * (z * k * z⁻¹)) := by rw [hzi]; group
      _ = k⁻¹ := by rw [hw1, mul_one]

end CFSG.LocalAnalysis.ComponentInitial.EqualFixedImage
