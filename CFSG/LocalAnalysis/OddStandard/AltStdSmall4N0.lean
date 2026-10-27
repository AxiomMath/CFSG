module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G1Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Perm
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarOrder

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup Equiv AltStdCycTwo AltStdBal
open scoped Pointwise

section Group

variable {G : Type} [Group G]

private theorem mem_conjSub_iff' {g x : G} {X : Subgroup G} :
    x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem mem_normalizer_of_conj {X : Subgroup G} {g : G}
    (h1 : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (h2 : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

private theorem le_normalizer_of_conj {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ normalizer (X : Set G) := fun g hg =>
  mem_normalizer_of_conj (h g hg) fun x hx => by
    have := h g⁻¹ (inv_mem hg) x hx
    rwa [inv_inv] at this

private theorem conj_mem_sup {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) {x : G} (hx : x ∈ A ⊔ B) : g * x * g⁻¹ ∈ A ⊔ B := by
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hA a ha
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hB b hb
  have := h hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

private theorem card_sup_of_inf_eq_bot {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G))
    (hAB : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  let f : A × B → (A ⊔ B : Subgroup G) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a ∈ A ⊓ B := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2, ?_⟩
        have : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
          calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
            _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
            _ = b' * (b : G)⁻¹ := by group
        rw [this]
        exact mul_mem b'.2 (inv_mem b.2)
      rw [hAB, mem_bot] at h2
      have ha : (a : G) = a' := by
        calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
          _ = a' := by rw [h2, mul_one]
      have hb : (b : G) = b' := by
        rw [ha] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by
        rw [← hm]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod]

private theorem conj_mem_oddCoreOf {H : Subgroup G} {g : G} (hg : g ∈ H) {x : G}
    (hx : x ∈ AltStdSec.oddCoreOf H) : g * x * g⁻¹ ∈ AltStdSec.oddCoreOf H := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
    (inferInstance : (CFSG.oddCore ↥H).Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩

private theorem exists_fixed_sylow [Finite G] {K P : Subgroup G} (hP : IsPGroup 2 P)
    (hPK : P ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, ∀ p ∈ P, ∀ s : K, s ∈ S →
      p * (s : G) * p⁻¹ ∈ (S : Subgroup K).map K.subtype := by
  let φ : P →* MulAut K := (normAct K).comp (Subgroup.inclusion hPK)
  letI : MulDistribMulAction P K := MulDistribMulAction.compHom K φ
  obtain ⟨S, hS⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 K)
    (not_dvd_card_sylow 2 K)
  refine ⟨S, fun p hp s hs => ?_⟩
  have h1 : (⟨p, hp⟩ : P) • S = S := hS ⟨p, hp⟩
  have h2 : (⟨p, hp⟩ : P) • s ∈ (⟨p, hp⟩ : P) • (S : Subgroup K) :=
    Subgroup.smul_mem_pointwise_smul s _ _ hs
  rw [← Sylow.pointwise_smul_def, h1] at h2
  exact ⟨_, h2, rfl⟩

private theorem exists_conj_eq_of_sylow [Finite G] {T O : Subgroup G}
    (hTN : T ≤ normalizer (O : Set G)) (hT : IsPGroup 2 T) (hO : Nat.Coprime 2 (Nat.card O))
    (S : Sylow 2 ↥(T ⊔ O)) :
    ∃ o ∈ O, (S : Subgroup ↥(T ⊔ O)).map (T ⊔ O).subtype = conjSub o T := by
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have hOT : O ⊓ T = ⊥ :=
    inf_eq_bot_of_coprime (by rw [ha]; exact (Nat.Coprime.pow_left a hO).symm)
  have hcard : Nat.card ↥(T ⊔ O) = Nat.card T * Nat.card O := by
    rw [sup_comm, card_sup_of_inf_eq_bot hTN hOT, mul_comm]
  have hTK : T ≤ T ⊔ O := le_sup_left
  have hT' : IsPGroup 2 (T.subgroupOf (T ⊔ O)) := hT.of_equiv (subgroupOfEquivOfLe hTK).symm
  have hidx : ¬ 2 ∣ (T.subgroupOf (T ⊔ O)).index := by
    have h1 := Subgroup.card_mul_index (T.subgroupOf (T ⊔ O))
    rw [Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv, hcard] at h1
    have h2 : (T.subgroupOf (T ⊔ O)).index = Nat.card O :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h2]
    obtain ⟨m, hm⟩ := Nat.coprime_two_left.1 hO
    omega
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥(T ⊔ O) (hT'.toSylow hidx) S
  have hmemS : ∀ x : ↥(T ⊔ O), x ∈ (S : Subgroup ↥(T ⊔ O)) ↔ (k : G)⁻¹ * x * k ∈ T := by
    intro x
    rw [← hk, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, mem_pointwise_smul_iff_inv_smul_mem,
      mem_subgroupOf, MulAut.smul_def, MulAut.conj_inv_apply]
    rfl
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left O T hTN
  have hk' : (k : G) ∈ (O : Set G) * (T : Set G) := by
    rw [← hm, sup_comm]
    exact k.2
  obtain ⟨o, ho, t, ht, hot⟩ := Set.mem_mul.1 hk'
  refine ⟨o, ho, ?_⟩
  ext y
  rw [mem_conjSub_iff']
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := (hmemS x).1 hx
    rw [← hot] at hx'
    have : o⁻¹ * (T ⊔ O).subtype x * o = t * ((o * t)⁻¹ * x * (o * t)) * t⁻¹ := by
      rw [Subgroup.coe_subtype]
      group
    rw [this]
    exact mul_mem (mul_mem ht hx') (inv_mem ht)
  · intro hy
    have hyK : y ∈ T ⊔ O := by
      have : y = o * (o⁻¹ * y * o) * o⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem (mem_sup_right ho) (mem_sup_left hy)) (inv_mem (mem_sup_right ho))
    refine ⟨⟨y, hyK⟩, (hmemS _).2 ?_, rfl⟩
    rw [← hot]
    show (o * t)⁻¹ * y * (o * t) ∈ T
    have : (o * t)⁻¹ * y * (o * t) = t⁻¹ * (o⁻¹ * y * o) * t := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem ht) hy) ht

private theorem exists_cent_conj {O T : Subgroup G} {z o : G} (hz : z * z = 1)
    (hzO : ∀ x ∈ O, z * x * z⁻¹ ∈ O) (hO : ∀ x ∈ O, Odd (orderOf x))
    (hzT : z ∈ normalizer (T : Set G)) (ho : o ∈ O)
    (hzT' : z ∈ normalizer (conjSub o T : Set G)) :
    ∃ c ∈ O, c * z = z * c ∧ conjSub c T = conjSub o T := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hz'T : o⁻¹ * z * o ∈ normalizer (T : Set G) := by
    rw [mem_normalizer_iff]
    intro t
    have h1 := (mem_normalizer_iff.1 hzT') (o * t * o⁻¹)
    rw [mem_conjSub_iff', mem_conjSub_iff'] at h1
    have e1 : o⁻¹ * (o * t * o⁻¹) * o = t := by group
    have e2 : o⁻¹ * (z * (o * t * o⁻¹) * z⁻¹) * o = o⁻¹ * z * o * t * (o⁻¹ * z * o)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  obtain ⟨u, hu⟩ : ∃ u, u = o⁻¹ * z * o * z := ⟨_, rfl⟩
  have huO : u ∈ O := by
    have : u = o⁻¹ * (z * o * z⁻¹) := by
      rw [hu, hzi]
      group
    rw [this]
    exact mul_mem (inv_mem ho) (hzO o ho)
  have huT : u ∈ normalizer (T : Set G) := by
    rw [hu]
    exact mul_mem hz'T hzT
  have hinv : z * u * z⁻¹ = u⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    calc u * (z * u * z⁻¹) = o⁻¹ * z * o * (z * z) * o⁻¹ * z * o := by
          rw [hu]
          group
      _ = o⁻¹ * z * o * 1 * o⁻¹ * z * o := by rw [hz]
      _ = o⁻¹ * (z * z) * o := by group
      _ = 1 := by
          rw [hz]
          group
  obtain ⟨k, hk⟩ := hO u huO
  have hu1 : u ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one u
  obtain ⟨r, hr⟩ : ∃ r, r = u ^ (k + 1) := ⟨_, rfl⟩
  have hrO : r ∈ O := by
    rw [hr]
    exact pow_mem huO _
  have hrT : r ∈ normalizer (T : Set G) := by
    rw [hr]
    exact pow_mem huT _
  have hzr : z * r * z⁻¹ = r⁻¹ := by
    rw [hr, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  have hzr' : z * r⁻¹ = r * z := by
    have h2 : z * r⁻¹ * z⁻¹ = r := by
      calc z * r⁻¹ * z⁻¹ = (z * r * z⁻¹)⁻¹ := by group
        _ = r := by rw [hzr, inv_inv]
    calc z * r⁻¹ = z * r⁻¹ * z⁻¹ * z := by group
      _ = r * z := by rw [h2]
  have hrr : r * r = u := by
    rw [hr, ← pow_add, show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ u (2 * k + 1),
      hu1, one_mul]
  have hrz : r * z * r⁻¹ = o⁻¹ * z * o := by
    calc r * z * r⁻¹ = r * (z * r⁻¹) := by group
      _ = r * (r * z) := by rw [hzr']
      _ = r * r * z := by group
      _ = u * z := by rw [hrr]
      _ = o⁻¹ * z * o * (z * z) := by
          rw [hu]
          group
      _ = o⁻¹ * z * o := by rw [hz, mul_one]
  refine ⟨o * r, mul_mem ho hrO, ?_, ?_⟩
  · have h3 : o * r * z * (o * r)⁻¹ = z := by
      calc o * r * z * (o * r)⁻¹ = o * (r * z * r⁻¹) * o⁻¹ := by group
        _ = z := by
            rw [hrz]
            group
    calc o * r * z = o * r * z * (o * r)⁻¹ * (o * r) := by group
      _ = z * (o * r) := by rw [h3]
  · ext y
    rw [mem_conjSub_iff', mem_conjSub_iff']
    have e : (o * r)⁻¹ * y * (o * r) = r⁻¹ * (o⁻¹ * y * o) * r := by group
    rw [e]
    exact ((mem_normalizer_iff''.1 hrT) (o⁻¹ * y * o)).symm

end Group

section Unitriangular

variable {n : ℕ}

private def uFun (i : Fin 8) : Fin 8 → Fin 8 :=
  lin8 1 ⟨2 + i.val % 2, by omega⟩ ⟨4 + i.val / 2, by omega⟩

private theorem uFun_injective : ∀ i : Fin 8, Function.Injective (uFun i) := by
  decide +kernel

private theorem uFun_lin : ∀ i v w : Fin 8, uFun i (xr v w) = xr (uFun i v) (uFun i w) := by
  decide +kernel

private theorem uFun_zero : ∀ i : Fin 8, uFun i 0 = 0 := by
  decide +kernel

private theorem uFun_mul : ∀ i j : Fin 8, ∃ k : Fin 8, ∀ x, uFun k x = uFun i (uFun j x) := by
  decide +kernel

private theorem uFun_id : ∀ x : Fin 8, uFun 0 x = x := by
  decide +kernel

private theorem uFun_inv : ∀ i : Fin 8, ∃ k : Fin 8, ∀ x, uFun k (uFun i x) = x := by
  decide +kernel

private theorem uFun_inj : ∀ i j : Fin 8, (∀ x, uFun i x = uFun j x) → i = j := by
  decide +kernel

private noncomputable def uPerm8 (i : Fin 8) : Perm (Fin 8) :=
  Equiv.ofBijective (uFun i) (Finite.injective_iff_bijective.1 (uFun_injective i))

private def e8 (hn : 8 ≤ n) : Fin 8 ≃ {x : Fin n // x.val < 8} where
  toFun k := ⟨⟨k.val, by omega⟩, k.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def uPerm (hn : 8 ≤ n) (i : Fin 8) : Perm (Fin n) :=
  (uPerm8 i).extendDomain (e8 hn)

private theorem uPerm_apply_lt (hn : 8 ≤ n) (i : Fin 8) {x : Fin n} (hx : x.val < 8) :
    (uPerm hn i x).val = (uFun i ⟨x.val, hx⟩).val :=
  congrArg Fin.val (Perm.extendDomain_apply_image (uPerm8 i) (e8 hn) ⟨x.val, hx⟩)

private theorem uPerm_apply_ge (hn : 8 ≤ n) (i : Fin 8) {x : Fin n} (hx : 8 ≤ x.val) :
    uPerm hn i x = x :=
  Perm.extendDomain_apply_not_subtype _ _ (not_lt.2 hx)

private theorem uPerm_mul (hn : 8 ≤ n) {i j k : Fin 8} (h : ∀ x, uFun k x = uFun i (uFun j x)) :
    uPerm hn i * uPerm hn j = uPerm hn k := by
  unfold uPerm
  rw [Perm.extendDomain_mul]
  congr 1
  exact Equiv.ext fun x => (h x).symm

private theorem uPerm_zero (hn : 8 ≤ n) : uPerm hn 0 = 1 := by
  have : uPerm8 0 = 1 := Equiv.ext fun x => uFun_id x
  unfold uPerm
  rw [this, Perm.extendDomain_one]

private theorem uPerm_injective (hn : 8 ≤ n) : Function.Injective (uPerm hn) := by
  intro i j h
  apply uFun_inj
  intro x
  have hx : x.val < n := lt_of_lt_of_le x.2 hn
  have h1 := congrArg (fun σ : Perm (Fin n) => (σ ⟨x.val, hx⟩).val) h
  rw [uPerm_apply_lt hn i (x := ⟨x.val, hx⟩) x.2,
    uPerm_apply_lt hn j (x := ⟨x.val, hx⟩) x.2] at h1
  exact Fin.ext h1

private theorem uPerm_mem_alternatingGroup (hn : 8 ≤ n) (i : Fin 8) :
    uPerm hn i ∈ alternatingGroup (Fin n) := by
  unfold uPerm
  rw [Perm.mem_alternatingGroup, Perm.sign_extendDomain]
  exact sign_lin8 1 _ _ (uFun_injective i)

private theorem uPerm_pt_zero (hn : 8 ≤ n) (i : Fin 8) : (uPerm hn i (pt hn 0)).val = 0 := by
  rw [uPerm_apply_lt hn i (x := pt hn 0) (show (0 : ℕ) < 8 by norm_num)]
  exact congrArg Fin.val (uFun_zero i)

private theorem uPerm_mul_tr (hn : 8 ≤ n) (i v : Fin 8) :
    uPerm hn i * tr hn v = tr hn (uFun i v) * uPerm hn i := by
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : x.val < 8
  · have h8 : (uPerm hn i x).val < 8 := by
      rw [uPerm_apply_lt hn i hx]
      exact (uFun i _).2
    apply Fin.ext
    rw [uPerm_apply_lt hn i (val_tr_lt hn v hx), val_tr_of_lt hn _ h8, uPerm_apply_lt hn i hx]
    have e1 : (⟨(tr hn v x).val, val_tr_lt hn v hx⟩ : Fin 8) = xr ⟨x.val, hx⟩ v :=
      Fin.ext (val_tr_of_lt hn v hx)
    rw [e1, uFun_lin]
    rfl
  · push Not at hx
    rw [tr_of_ge hn v hx, uPerm_apply_ge hn i hx, tr_of_ge hn _ hx]

private def dBar (hn : 8 ≤ n) : Subgroup (alternatingGroup (Fin n)) where
  carrier := {σ | ∃ i : Fin 8, (σ : Perm (Fin n)) = uPerm hn i}
  mul_mem' := by
    rintro σ τ ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hk⟩ := uFun_mul i j
    exact ⟨k, by rw [Subgroup.coe_mul, hi, hj, uPerm_mul hn hk]⟩
  one_mem' := ⟨0, by rw [Subgroup.coe_one, uPerm_zero]⟩
  inv_mem' := by
    rintro σ ⟨i, hi⟩
    obtain ⟨k, hk⟩ := uFun_inv i
    refine ⟨k, ?_⟩
    rw [Subgroup.coe_inv, hi]
    have h1 : uPerm hn k * uPerm hn i = 1 := by
      rw [uPerm_mul hn (k := 0) (fun x => by rw [uFun_id, hk]), uPerm_zero]
    exact (eq_inv_of_mul_eq_one_left h1).symm

private theorem card_dBar (hn : 8 ≤ n) : Nat.card (dBar hn) = 8 := by
  let F : Fin 8 → dBar hn := fun i => ⟨⟨uPerm hn i, uPerm_mem_alternatingGroup hn i⟩, ⟨i, rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨fun i j hij => uPerm_injective hn ?_, fun σ => ?_⟩
    · exact congrArg (fun σ : dBar hn => ((σ : alternatingGroup (Fin n)) : Perm (Fin n))) hij
    · obtain ⟨i, hi⟩ := σ.2
      exact ⟨i, Subtype.ext (Subtype.ext hi.symm)⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem eq_one_of_mem_dBar_of_mem_eBar (hn : 8 ≤ n) {σ : alternatingGroup (Fin n)}
    (hσD : σ ∈ dBar hn) (hσE : σ ∈ eBar hn) : σ = 1 := by
  obtain ⟨i, hi⟩ := hσD
  obtain ⟨v, hv⟩ := (mem_eBar_iff hn).1 hσE
  have h0 : v = 0 := by
    have h1 : (uPerm hn i (pt hn 0)).val = (tr hn v (pt hn 0)).val := by rw [← hi, ← hv]
    rw [uPerm_pt_zero, val_tr_pt_zero] at h1
    exact Fin.ext h1.symm
  apply Subtype.ext
  rw [Subgroup.coe_one, hv, h0, tr_zero]

private theorem conj_mem_eBar_of_mem_dBar (hn : 8 ≤ n) {σ τ : alternatingGroup (Fin n)}
    (hσ : σ ∈ dBar hn) (hτ : τ ∈ eBar hn) : σ * τ * σ⁻¹ ∈ eBar hn := by
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨v, hv⟩ := (mem_eBar_iff hn).1 hτ
  refine (mem_eBar_iff hn).2 ⟨uFun i v, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hi, hv, uPerm_mul_tr,
    mul_inv_cancel_right]

end Unitriangular

section Config

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

private theorem z_mem_cent (c : Config G L Q n θ z) : z ∈ centralizer (L : Set G) :=
  c.ot.cyc.le c.ot.cyc.mem

private theorem z_mul_self (c : Config G L Q n θ z) : z * z = 1 := by
  rw [← sq, ← c.ot.cyc.order, pow_orderOf_eq_one]

private theorem z_not_mem_L (c : Config G L Q n θ z) : z ∉ L := by
  intro hz
  have h1 := eq_one_of_mem_of_mem_centralizer θ (by have := c.hn8; omega) hz (z_mem_cent c)
  have h2 := c.ot.cyc.order
  rw [h1, orderOf_one] at h2
  omega

private theorem eq_one_or_eq_of_mem_zpowers (c : Config G L Q n θ z) {y : G}
    (hy : y ∈ zpowers z) : y = 1 ∨ y = z := by
  have hQz : zpowers z = Q := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 c.ot.cyc.mem)
    (by rw [c.ot.card, Nat.card_zpowers, c.ot.cyc.order])
  rw [hQz] at hy
  exact eq_one_or_eq_of_card_eq_two c.ot.cyc c.ot.card hy

omit [Finite G] in
private theorem mem_normalizer_of_mem_centralizer {X : Subgroup G} (hX : X ≤ L) {g : G}
    (hg : g ∈ centralizer (L : Set G)) : g ∈ normalizer (X : Set G) := by
  refine mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
  · rw [← mem_centralizer_iff.1 hg x (hX hx), mul_inv_cancel_right]
    exact hx
  · rw [← mem_centralizer_iff.1 (inv_mem hg) x (hX hx), inv_mul_cancel_right]
    exact hx

omit [Finite G] in
private theorem mem_E_iff' (hn : 8 ≤ n) {x : G} :
    x ∈ E θ hn ↔ ∃ e ∈ eBar hn, ((θ.symm e : L) : G) = x := by
  constructor
  · rintro ⟨l, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨θ.symm e, ⟨e, he, rfl⟩, rfl⟩

omit [Finite G] in
private theorem E_le_L (hn : 8 ≤ n) : E θ hn ≤ L := by
  rintro x ⟨l, -, rfl⟩
  exact l.2

omit [Finite G] in
private theorem card_E' (hn : 8 ≤ n) : Nat.card (E θ hn) = 8 := by
  unfold E
  rw [card_map_of_injective L.subtype_injective,
    card_map_of_injective (f := θ.symm.toMonoidHom) θ.symm.injective, card_eBar]

private theorem mem_E_of_mem_sup (c : Config G L Q n θ z) {x : G}
    (hx : x ∈ E θ c.hn8 ⊔ zpowers z) (hxL : x ∈ L) : x ∈ E θ c.hn8 := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left (E θ c.hn8) (zpowers z)
    (zpowers_le.2 (mem_normalizer_of_mem_centralizer (E_le_L c.hn8) (z_mem_cent c)))
  have hx' : x ∈ (E θ c.hn8 : Set G) * (zpowers z : Set G) := by
    rw [← hm]
    exact hx
  obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.1 hx'
  rcases eq_one_or_eq_of_mem_zpowers c hy with h | h
  · rw [h, mul_one]
    exact he
  · exfalso
    rw [h] at hxL
    apply z_not_mem_L c
    have : z = e⁻¹ * (e * z) := by group
    rw [this]
    exact mul_mem (inv_mem (E_le_L c.hn8 he)) hxL

private theorem conj_mem_E (c : Config G L Q n θ z) {g : G} (hg : g ∈ N0 θ c.hn8 z)
    (hgL : g ∈ normalizer (L : Set G)) {e : G} (he : e ∈ E θ c.hn8) :
    g * e * g⁻¹ ∈ E θ c.hn8 :=
  mem_E_of_mem_sup c ((mem_normalizer_iff.1 hg e).1 (mem_sup_left he))
    ((mem_normalizer_iff.1 hgL e).1 (E_le_L c.hn8 he))

private theorem rho_normalizes_eBar (c : Config G L Q n θ z) {x : G} (hx : x ∈ N0 θ c.hn8 z)
    (hxN : x ∈ normalizer (L : Set G)) :
    ∀ e ∈ eBar c.hn8, ∃ e' ∈ eBar c.hn8,
      rho θ c.hn8 ⟨x, hxN⟩ * (e : Perm (Fin n)) * (rho θ c.hn8 ⟨x, hxN⟩)⁻¹ = e' := by
  intro e he
  rw [rho_conj]
  refine ⟨_, ?_, rfl⟩
  have h1 : x * ((θ.symm e : L) : G) * x⁻¹ ∈ E θ c.hn8 :=
    conj_mem_E c hx hxN ((mem_E_iff' c.hn8).2 ⟨e, he, rfl⟩)
  obtain ⟨e', he', hee'⟩ := (mem_E_iff' c.hn8).1 h1
  convert he' using 1
  exact θ.eq_symm_apply.1 (Subtype.ext hee'.symm)

theorem N0_inf_centralizer_le_sup (c : Config G L Q n θ z) :
    N0 θ c.hn8 z ⊓ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) := by
  rintro x ⟨hx0, hxC⟩
  rcases c.shape with hin | ⟨h9, -⟩
  · exact hin hxC
  · have hxN := cent_le_normalizer c.ot.std c.ot.cyc hxC
    exact mem_sup_of_rho_mem θ c.hn8 hxN
      (mem_alternatingGroup_of_normalizes_eBar c.hn8 (by omega) (rho_normalizes_eBar c hx0 hxN))

theorem sec4TwoElemN0_holds : Sec4TwoElemN0 := by
  intro G _ _ L Q n θ z c x hx k hxk
  obtain ⟨l, hl, h | h⟩ := exists_eq_of_two_pow c.ot.std θ c.hn8 c.ot.cyc c.ot.card hx.2
    (N0_inf_centralizer_le_sup c hx) hxk
  · exact ⟨l, hl, Or.inl h⟩
  · exact ⟨l, hl, Or.inr (h.trans (mem_centralizer_iff.1 (z_mem_cent c) l hl))⟩

private def Dstd (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) : Subgroup G :=
  ((dBar hn).map θ.symm.toMonoidHom).map L.subtype

omit [Finite G] in
private theorem mem_Dstd_iff (hn : 8 ≤ n) {x : G} :
    x ∈ Dstd θ hn ↔ ∃ σ ∈ dBar hn, ((θ.symm σ : L) : G) = x := by
  constructor
  · rintro ⟨l, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨σ, hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨θ.symm σ, ⟨σ, hσ, rfl⟩, rfl⟩

omit [Finite G] in
private theorem Dstd_le_L (hn : 8 ≤ n) : Dstd θ hn ≤ L := by
  rintro x ⟨l, -, rfl⟩
  exact l.2

omit [Finite G] in
private theorem card_Dstd (hn : 8 ≤ n) : Nat.card (Dstd θ hn) = 8 := by
  unfold Dstd
  rw [card_map_of_injective L.subtype_injective,
    card_map_of_injective (f := θ.symm.toMonoidHom) θ.symm.injective, card_dBar]

omit [Finite G] in
private theorem Dstd_inf_E (hn : 8 ≤ n) : Dstd θ hn ⊓ E θ hn = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxD, hxE⟩
  obtain ⟨σ, hσ, rfl⟩ := (mem_Dstd_iff hn).1 hxD
  obtain ⟨τ, hτ, hστ⟩ := (mem_E_iff' hn).1 hxE
  have h1 : τ = σ := θ.symm.injective (Subtype.ext hστ)
  rw [h1] at hτ
  rw [eq_one_of_mem_dBar_of_mem_eBar hn hσ hτ, map_one, OneMemClass.coe_one]
  exact one_mem _

omit [Finite G] in
private theorem conj_mem_E_of_mem_Dstd (hn : 8 ≤ n) {d e : G} (hd : d ∈ Dstd θ hn)
    (he : e ∈ E θ hn) : d * e * d⁻¹ ∈ E θ hn := by
  obtain ⟨σ, hσ, rfl⟩ := (mem_Dstd_iff hn).1 hd
  obtain ⟨τ, hτ, rfl⟩ := (mem_E_iff' hn).1 he
  refine (mem_E_iff' hn).2 ⟨σ * τ * σ⁻¹, conj_mem_eBar_of_mem_dBar hn hσ hτ, ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

private def P0 (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) : Subgroup G :=
  (E θ hn ⊔ Dstd θ hn) ⊔ zpowers z

omit [Finite G] in
private theorem Dstd_le_P0 (hn : 8 ≤ n) : Dstd θ hn ≤ P0 θ hn z :=
  (le_sup_right : Dstd θ hn ≤ E θ hn ⊔ Dstd θ hn).trans le_sup_left

private theorem card_P0 (c : Config G L Q n θ z) : Nat.card (P0 θ c.hn8 z) = 2 ^ 7 := by
  have hX : E θ c.hn8 ⊔ Dstd θ c.hn8 ≤ L := sup_le (E_le_L c.hn8) (Dstd_le_L c.hn8)
  have hDE : Dstd θ c.hn8 ≤ normalizer (E θ c.hn8 : Set G) :=
    le_normalizer_of_conj fun _ hd _ he => conj_mem_E_of_mem_Dstd c.hn8 hd he
  have hED : E θ c.hn8 ⊓ Dstd θ c.hn8 = ⊥ := by
    rw [inf_comm]
    exact Dstd_inf_E c.hn8
  have h1 : Nat.card (E θ c.hn8 ⊔ Dstd θ c.hn8 : Subgroup G) = 64 := by
    rw [card_sup_of_inf_eq_bot hDE hED, card_E' c.hn8, card_Dstd c.hn8]
  have h2 : (E θ c.hn8 ⊔ Dstd θ c.hn8) ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyX, hyz⟩
    rcases eq_one_or_eq_of_mem_zpowers c hyz with h | h
    · rw [h]
      exact one_mem _
    · rw [h] at hyX
      exact absurd (hX hyX) (z_not_mem_L c)
  have h3 : zpowers z ≤ normalizer ((E θ c.hn8 ⊔ Dstd θ c.hn8 : Subgroup G) : Set G) :=
    zpowers_le.2 (mem_normalizer_of_mem_centralizer hX (z_mem_cent c))
  unfold P0
  rw [card_sup_of_inf_eq_bot h3 h2, h1, Nat.card_zpowers, c.ot.cyc.order]
  norm_num

private theorem P0_le (c : Config G L Q n θ z) :
    P0 θ c.hn8 z ≤ N0 θ c.hn8 z ⊓ centralizer ({z} : Set G) := by
  have hLC := le_cent_single c.ot.std c.ot.cyc
  have hEN : E θ c.hn8 ≤ N0 θ c.hn8 z :=
    le_sup_left.trans (Subgroup.le_normalizer (H := E θ c.hn8 ⊔ zpowers z))
  have hzN : z ∈ N0 θ c.hn8 z :=
    Subgroup.le_normalizer (H := E θ c.hn8 ⊔ zpowers z) (mem_sup_right (mem_zpowers z))
  have hDN : Dstd θ c.hn8 ≤ N0 θ c.hn8 z := by
    show Dstd θ c.hn8 ≤ normalizer ((E θ c.hn8 ⊔ zpowers z : Subgroup G) : Set G)
    refine le_normalizer_of_conj fun d hd x hx => conj_mem_sup (fun e he => ?_) (fun y hy => ?_) hx
    · exact mem_sup_left (conj_mem_E_of_mem_Dstd c.hn8 hd he)
    · have hyK : y ∈ centralizer (L : Set G) := (zpowers_le.2 (z_mem_cent c)) hy
      rw [mem_centralizer_iff.1 hyK d (Dstd_le_L c.hn8 hd), mul_inv_cancel_right]
      exact mem_sup_right hy
  refine sup_le (sup_le (le_inf hEN ((E_le_L c.hn8).trans hLC))
    (le_inf hDN ((Dstd_le_L c.hn8).trans hLC))) ?_
  rw [zpowers_le]
  exact ⟨hzN, mem_centralizer_singleton_iff.2 rfl⟩

private theorem exists_g1Data (c : Config G L Q n θ z) {T : Subgroup G}
    (hH : HData θ c.hn8 z T) : ∃ S₀ D : Subgroup G, G1Data c T S₀ D := by
  have h0 := hH.n0
  set N := N0 θ c.hn8 z with hN
  set O := AltStdSec.oddCoreOf N with hO
  have hON : O ≤ N := Subgroup.map_subtype_le _
  have hOconj : ∀ g ∈ N, ∀ x ∈ O, g * x * g⁻¹ ∈ O := fun g hg x hx => conj_mem_oddCoreOf hg hx
  have hOodd : Nat.Coprime 2 (Nat.card O) := coprime_card_oddCoreOf N
  have hOord : ∀ x ∈ O, Odd (orderOf x) := by
    intro x hx
    have h1 : orderOf x ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (Nat.coprime_two_left.1 hOodd) h1
  have hTN : T ≤ N := h0.le
  have hTO : T ≤ normalizer (O : Set G) :=
    le_normalizer_of_conj fun t ht x hx => hOconj t (hTN ht) x hx
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 6) (by rw [h0.card_eq]; norm_num)
  have hKconj : ∀ g ∈ N, ∀ x ∈ T ⊔ O, g * x * g⁻¹ ∈ T ⊔ O := fun g hg x hx =>
    conj_mem_sup (fun a ha => h0.normal g hg a ha) (fun b hb => mem_sup_right (hOconj g hg b hb))
      hx
  have hPC := P0_le c
  have hPcard := card_P0 c
  have hPp : IsPGroup 2 (P0 θ c.hn8 z) := IsPGroup.of_card hPcard
  have hPK : P0 θ c.hn8 z ≤ normalizer ((T ⊔ O : Subgroup G) : Set G) :=
    le_normalizer_of_conj fun p hp x hx => hKconj p (hPC hp).1 x hx
  obtain ⟨S, hS⟩ := exists_fixed_sylow hPp hPK
  obtain ⟨o, ho, hSo⟩ := exists_conj_eq_of_sylow hTO hTp hOodd S
  have hPn : ∀ p ∈ P0 θ c.hn8 z, ∀ x ∈ conjSub o T, p * x * p⁻¹ ∈ conjSub o T := by
    intro p hp x hx
    rw [← hSo] at hx ⊢
    obtain ⟨s, hs, rfl⟩ := hx
    exact hS p hp s hs
  have hzP : z ∈ P0 θ c.hn8 z := mem_sup_right (mem_zpowers z)
  have hzN : z ∈ N := (hPC hzP).1
  have hzn : z ∈ normalizer (conjSub o T : Set G) :=
    le_normalizer_of_conj hPn hzP
  obtain ⟨c₀, hc₀O, hc₀z, hc₀T⟩ :=
    exists_cent_conj (z_mul_self c) (hOconj z hzN) hOord h0.norm ho hzn
  have hc₀N : c₀ ∈ N := hON hc₀O
  have hc₀C : c₀ ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hc₀z
  have hc₀L : c₀ ∈ normalizer (L : Set G) := cent_le_normalizer c.ot.std c.ot.cyc hc₀C
  have hPn' : ∀ p ∈ P0 θ c.hn8 z, p ∈ normalizer (conjSub c₀ T : Set G) := by
    intro p hp
    rw [hc₀T]
    exact le_normalizer_of_conj hPn hp
  have hmem : ∀ {X : Subgroup G} {x : G}, x ∈ conjSub c₀⁻¹ X ↔ c₀ * x * c₀⁻¹ ∈ X := by
    intro X x
    rw [mem_conjSub_iff', inv_inv]
  have hback : ∀ x : G, x = c₀⁻¹ * (c₀ * x * c₀⁻¹) * c₀ := fun x => by group
  have hS₀le : conjSub c₀⁻¹ (P0 θ c.hn8 z) ≤ N ⊓ centralizer ({z} : Set G) := by
    intro x hx
    rw [hmem] at hx
    rw [hback x]
    have hc : c₀ ∈ N ⊓ centralizer ({z} : Set G) := ⟨hc₀N, hc₀C⟩
    exact mul_mem (mul_mem (inv_mem hc) (hPC hx)) hc
  refine ⟨conjSub c₀⁻¹ (P0 θ c.hn8 z), conjSub c₀⁻¹ (Dstd θ c.hn8), {
    hH := hH
    S₀_le := hS₀le
    S₀_p := hPp.map _
    S₀_card := by
      rw [conjSub, card_map_of_injective (f := (MulAut.conj c₀⁻¹).toMonoidHom)
        (MulAut.conj c₀⁻¹).injective, hPcard]
    S₀_norm := ?_
    D_le_S₀ := map_mono (Dstd_le_P0 c.hn8)
    D_le_L := ?_
    D_card := by
      rw [conjSub, card_map_of_injective (f := (MulAut.conj c₀⁻¹).toMonoidHom)
        (MulAut.conj c₀⁻¹).injective, card_Dstd]
    D_inf := ?_ }⟩
  ·
    intro x hx
    rw [hmem] at hx
    have hp := hPn' _ hx
    rw [mem_normalizer_iff]
    intro t
    have h1 := (mem_normalizer_iff.1 hp) (c₀ * t * c₀⁻¹)
    rw [mem_conjSub_iff', mem_conjSub_iff'] at h1
    have e1 : c₀⁻¹ * (c₀ * t * c₀⁻¹) * c₀ = t := by group
    have e2 : c₀⁻¹ * (c₀ * x * c₀⁻¹ * (c₀ * t * c₀⁻¹) * (c₀ * x * c₀⁻¹)⁻¹) * c₀ =
        x * t * x⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  ·
    intro x hx
    rw [hmem] at hx
    rw [hback x]
    exact (mem_normalizer_iff''.1 hc₀L _).1 (Dstd_le_L c.hn8 hx)
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxT⟩ := Subgroup.mem_inf.1 hx
    have hxC : x ∈ centralizer ({z} : Set G) :=
      (hS₀le (map_mono (Dstd_le_P0 c.hn8) hxD)).2
    have hxE : x ∈ E θ c.hn8 := by
      rw [← h0.cent]
      exact Subgroup.mem_inf.2 ⟨hxT, hxC⟩
    rw [hmem] at hxD
    have hdE : c₀ * x * c₀⁻¹ ∈ E θ c.hn8 := conj_mem_E c hc₀N hc₀L hxE
    have hd1 : c₀ * x * c₀⁻¹ = 1 := by
      have : c₀ * x * c₀⁻¹ ∈ Dstd θ c.hn8 ⊓ E θ c.hn8 := Subgroup.mem_inf.2 ⟨hxD, hdE⟩
      rw [Dstd_inf_E] at this
      exact this
    rw [mem_bot, hback x, hd1]
    group

theorem sec4ExistsG1Data_holds : Sec4ExistsG1Data :=
  fun _ _ _ _ _ _ _ _ c _ hH => exists_g1Data c hH

end Config

end CFSG.OddStandard.AltStdSmall4
