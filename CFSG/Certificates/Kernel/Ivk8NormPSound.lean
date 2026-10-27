module

public import Certificates.Data.Kernel.Ivk8NormP
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.PK CFSG.KC.Enum

variable {n : ℕ}

@[expose] def RepF (n x : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i (hi : i < n), pg (wd n) (mask (wd n)) x i = (σ ⟨i, hi⟩ : ℕ)

theorem repF_cmp (hn : n < 2 ^ 32) {a b : ℕ} {σ τ : Equiv.Perm (Fin n)} (ha : RepF n a σ)
    (hb : RepF n b τ) : RepF n (cmpF n (wd n) a b) (σ * τ) := by
  intro i hi
  rw [cmpF, CFSG.KS.PF.pg_pcomp hn hi, hb i hi, ha _ (τ ⟨i, hi⟩).isLt]
  rfl

theorem shr_cmp (hn : n < 2 ^ 32) (a b : ℕ) : cmpF n (wd n) a b >>> (n * wd n) = 0 :=
  CFSG.KS.PF.pcomp_shr a b hn (Nat.succ_pos _)

theorem repF_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ wd n) : RepF n (pidn n (wd n)) 1 := by
  intro i hi
  rw [CFSG.KS.PF.pg_pidn hn hw hi]
  rfl

theorem eq_of_repF {x y : ℕ} {σ : Equiv.Perm (Fin n)} (hx : x >>> (n * wd n) = 0)
    (hy : y >>> (n * wd n) = 0) (hxr : RepF n x σ) (hyr : RepF n y σ) : x = y :=
  CFSG.KS.PF.eq_of_fields (Nat.succ_pos _) hx hy fun i hi => (hxr i hi).trans (hyr i hi).symm

theorem repF_fst (y : VP n) : RepF n y.1.1 (pkp y) := fun i hi => by
  rw [CFSG.KS.PK.pg_eq]
  exact (pkp_apply y ⟨i, hi⟩).symm

theorem repF_snd (y : VP n) : RepF n y.1.2 (pkp y)⁻¹ := fun _ _ => by
  rw [CFSG.KS.PK.pg_eq]
  rfl

theorem repF_powN (hn : n < 2 ^ 32) {y : ℕ} {σ : Equiv.Perm (Fin n)} (hy : RepF n y σ) :
    ∀ (k : ℕ) {z : ℕ} {τ : Equiv.Perm (Fin n)}, RepF n z τ →
      RepF n (powN n (wd n) y k z) (σ ^ k * τ)
  | 0, _, _, hz => by simpa [powN] using hz
  | k + 1, _, _, hz => by
    have := repF_powN hn hy k (repF_cmp hn hy hz)
    rw [powN]
    rwa [pow_succ, mul_assoc]

theorem shr_powN (hn : n < 2 ^ 32) (y : ℕ) :
    ∀ (k : ℕ) {z : ℕ}, z >>> (n * wd n) = 0 → powN n (wd n) y k z >>> (n * wd n) = 0
  | 0, _, hz => hz
  | k + 1, _, _ => by
    rw [powN]
    exact shr_powN hn y k (shr_cmp hn _ _)

theorem powN_mem_powsN (y : ℕ) :
    ∀ (k : ℕ) (z : ℕ), ∀ i < k, powN n (wd n) y i z ∈ powsN n (wd n) y k z
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, z, 0, _ => by
    rw [powsN]
    exact List.mem_cons_self ..
  | k + 1, z, i + 1, hi => by
    rw [powsN, powN]
    exact List.mem_cons_of_mem _ (powN_mem_powsN y k _ i (by omega))

theorem exists_pow_of_mem_zpowers {G : Type*} [Group G] {σ τ : G} {p : ℕ} (hp : orderOf σ = p)
    (hp0 : 0 < p) (hτ : τ ∈ Subgroup.zpowers σ) (h1 : τ ≠ 1) :
    ∃ j, 1 ≤ j ∧ j < p ∧ σ ^ j = τ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
  have hm0 : 0 ≤ m % (p : ℤ) := Int.emod_nonneg _ (by omega)
  have hmp : m % (p : ℤ) < p := Int.emod_lt_of_pos _ (by omega)
  refine ⟨(m % (p : ℤ)).toNat, ?_, by omega, ?_⟩
  · by_contra h0
    have e : m % (p : ℤ) = 0 := by omega
    apply h1
    rw [← zpow_mod_orderOf, hp, e, zpow_zero]
  · rw [← zpow_natCast, Int.toNat_of_nonneg hm0, ← hp, zpow_mod_orderOf]

theorem chkP_spec {p : ℕ} (hn : n < 2 ^ 32) (hn24 : n < 16777216) (hw : n + 1 < 2 ^ wd n)
    (hp : p.Prime) {hs L : List (VP n)}
    (h : chkP n (wd n) p (hs.map Subtype.val) (L.map fun y => y.1.1) = true) :
    ∀ y ∈ L, orderOf (pkp y) = p →
      ∃ g ∈ hs, pkp g ∉ Subgroup.normalizer
        (Subgroup.zpowers (pkp y) : Set (Equiv.Perm (Fin n))) := by
  intro y hy hyo
  have hok := List.all_eq_true.1 h _ (List.mem_map_of_mem hy)
  unfold okP at hok
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
  have hI := repF_pidn hn24 hw
  have hIs := CFSG.KS.PF.pidn_shr hn24 hw
  have hY := repF_fst y
  have hpow : powN n (wd n) y.1.1 p (pidn n (wd n)) = pidn n (wd n) := by
    refine eq_of_repF (shr_powN hn _ p hIs) hIs (repF_powN hn hY p hI) ?_
    rw [← hyo, pow_orderOf_eq_one, mul_one]
    exact hI
  have hy1 : pkp y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  rcases hok with (h1 | h2) | h3
  · rw [hpow, Nat.beq_refl] at h1
    exact absurd h1 (by decide)
  · exfalso
    apply hy1
    have e := Nat.eq_of_beq_eq_true h2
    ext i
    rw [← hY i i.2, e, hI i i.2]
  · unfold movesN at h3
    obtain ⟨hh, hmem, hnot⟩ := List.any_eq_true.1 h3
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
    refine ⟨g, hg, fun hN => ?_⟩
    have hc : pkp g * pkp y * (pkp g)⁻¹ ∈ Subgroup.zpowers (pkp y) :=
      (Subgroup.mem_normalizer_iff.1 hN _).1 (Subgroup.mem_zpowers _)
    have hc1 : pkp g * pkp y * (pkp g)⁻¹ ≠ 1 := by
      intro h1
      apply hy1
      calc pkp y = (pkp g)⁻¹ * (pkp g * pkp y * (pkp g)⁻¹) * pkp g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨j, hj1, hjp, hj⟩ := exists_pow_of_mem_zpowers hyo hp.pos hc hc1
    have hq := powN_mem_powsN (n := n) y.1.1 (p - 1) (cmpF n (wd n) y.1.1 (pidn n (wd n)))
      (j - 1) (by omega)
    have hz := List.all_eq_true.1 hnot _ hq
    have hrep : RepF n (powN n (wd n) y.1.1 (j - 1) (cmpF n (wd n) y.1.1 (pidn n (wd n))))
        (pkp g * pkp y * (pkp g)⁻¹) := by
      have := repF_powN hn hY (j - 1) (repF_cmp hn hY hI)
      rwa [mul_one, ← pow_succ, Nat.sub_add_cancel hj1, hj] at this
    have hcrep : RepF n (conjF n (wd n) g.1 y.1.1) (pkp g * pkp y * (pkp g)⁻¹) := by
      have := repF_cmp hn (repF_fst g) (repF_cmp hn hY (repF_snd g))
      rwa [← mul_assoc] at this
    have e : conjF n (wd n) g.1 y.1.1 = _ := eq_of_repF (shr_cmp hn _ _) (shr_powN hn _ _ (shr_cmp hn _ _)) hcrep hrep
    rw [e, Nat.beq_refl] at hz
    exact absurd hz (by decide)

end CFSG.KS.Ivk8NormP

end
