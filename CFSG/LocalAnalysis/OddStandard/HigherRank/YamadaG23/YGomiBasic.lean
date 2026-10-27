module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiData

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private def mulSubgroup (H K : Subgroup G)
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) : Subgroup G where
  carrier := {g | ∃ x ∈ H, ∃ y ∈ K, g = x * y}
  one_mem' := ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
    refine ⟨x * x', H.mul_mem hx hx', y * y', K.mul_mem hy hy', ?_⟩
    calc x * y * (x' * y') = x * (y * x') * y' := by group
      _ = x * (x' * y) * y' := by rw [hc x' hx' y hy]
      _ = x * x' * (y * y') := by group
  inv_mem' := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    refine ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, ?_⟩
    rw [hc x hx y hy, mul_inv_rev]

private theorem sup_eq_mulSubgroup (H K : Subgroup G)
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) : H ⊔ K = mulSubgroup H K hc := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro x hx
    exact ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
  · intro y hy
    exact ⟨1, H.one_mem, y, hy, (one_mul y).symm⟩
  · rintro g ⟨x, hx, y, hy, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

private theorem natCard_inf_mul_natCard_sup (H K : Subgroup G)
    (hcomm : ∀ c ∈ H, ∀ a ∈ K, c * a = a * c) :
    Nat.card ↥(H ⊓ K) * Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  let ψ : ↥H × ↥K →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := fun p q => by
        have h : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          hcomm (q.1 : G) q.1.2 (p.2 : G) p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : G) * q.1 * (p.2 * q.2) = (p.1 : G) * ((q.1 : G) * p.2) * q.2 := by
              group
          _ = (p.1 : G) * (p.2 * q.1) * q.2 := by rw [h]
          _ = (p.1 : G) * p.2 * (q.1 * q.2) := by group }
  have hψ : ∀ p : ↥H × ↥K, ψ p = (p.1 : G) * (p.2 : G) := fun _ => rfl
  have hrange : ψ.range = H ⊔ K := by
    rw [sup_eq_mulSubgroup H K hcomm]
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.1.2, p.2, p.2.2, hψ p⟩
    · rintro ⟨c, hc, a, ha, rfl⟩
      exact ⟨(⟨c, hc⟩, ⟨a, ha⟩), hψ _⟩
  have hker : Nat.card ψ.ker = Nat.card ↥(H ⊓ K) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1, ?_⟩
        invFun := fun w => ⟨(⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩,
          ⟨w.1⁻¹, K.inv_mem (Subgroup.mem_inf.mp w.2).2⟩), ?_⟩
        left_inv := fun p => ?_
        right_inv := fun w => ?_ }
    · have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      have hinv : (p.1.1 : G) = ((p.1.2 : G))⁻¹ := eq_inv_of_mul_eq_one_left hp
      exact Subgroup.mem_inf.mpr ⟨p.1.1.2, by rw [hinv]; exact K.inv_mem p.1.2.2⟩
    · show (w.1 : G) * (w.1 : G)⁻¹ = 1
      group
    · obtain ⟨⟨c, a⟩, hp⟩ := p
      have hp' : (c : G) * (a : G) = 1 := hp
      have hca : (c : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_left hp'
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext rfl
      · exact Subtype.ext (by simp [hca])
    · apply Subtype.ext
      rfl
  have key := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange, Nat.card_prod] at key
  exact key

theorem mem_sup_of_commute {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {g : G}
    (hg : g ∈ H ⊔ K) : ∃ x ∈ H, ∃ y ∈ K, g = x * y := by
  rw [sup_eq_mulSubgroup H K hc] at hg
  exact hg

namespace Gomi6Data

variable {A V C₀ C₁ : Subgroup G} {t u : G} (h : Gomi6Data A V C₀ C₁ t u)

include h

private theorem t_sq : t * t = 1 := by
  have hh := pow_orderOf_eq_one t
  rw [h.t_order, pow_two] at hh
  exact hh

private theorem t_inv_eq : t⁻¹ = t :=
  (eq_inv_of_mul_eq_one_right (t_sq h)).symm

private theorem t_conj_triple (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have ht2 : t * t = 1 := t_sq h
  have htinv : t⁻¹ = t := t_inv_eq h
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = x := by rw [ht2, htinv, ht2]; group

private theorem mem_cent_of_conj_u (x : G) (hx : x * u * x⁻¹ = u) :
    x ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [h.V_eq] at hv
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hconj : x * (u ^ j) * x⁻¹ = u ^ j := by
    rw [← conj_zpow (a := x) (b := u) (i := j)]
    rw [hx]
  have hcomm : x * u ^ j = u ^ j * x := by
    calc x * u ^ j = (x * u ^ j * x⁻¹) * x := by group
      _ = u ^ j * x := by rw [hconj]
  exact hcomm.symm

private theorem mem_sup_zpowers_t_cases {P : Subgroup G} (htN : t ∈ normalizer (P : Set G))
    {c : G} (hc : c ∈ P ⊔ zpowers t) : c ∈ P ∨ c * t ∈ P := by
  have ht2 : t * t = 1 := t_sq h
  have htinv : t⁻¹ = t := t_inv_eq h
  have hconj : ∀ y ∈ P, t * y * t ∈ P := by
    intro y hy
    have h1 : t * y * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp htN y).mp hy
    rwa [htinv] at h1
  let S : Subgroup G :=
    { carrier := {x | x ∈ P ∨ x * t ∈ P}
      one_mem' := Or.inl P.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (P.mul_mem hx hy)
        · exact Or.inr (by rw [show x * y * t = x * (y * t) by group]; exact P.mul_mem hx hy)
        · refine Or.inr ?_
          have h1 : t * y * t ∈ P := hconj y hy
          have heq : (x * t) * (t * y * t) = (x * y) * t := by
            calc (x * t) * (t * y * t) = x * (t * t) * y * t := by group
              _ = x * y * t := by rw [ht2]; group
              _ = (x * y) * t := by group
          rw [← heq]
          exact P.mul_mem hx h1
        · refine Or.inl ?_
          have h1 : t * (y * t) * t ∈ P := hconj (y * t) hy
          have heq : (x * t) * (t * (y * t) * t) = x * y := by
            calc (x * t) * (t * (y * t) * t) = x * (t * t) * y * (t * t) := by group
              _ = x * y := by rw [ht2]; group
          rw [← heq]
          exact P.mul_mem hx h1
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (P.inv_mem hx)
        · refine Or.inr ?_
          have h1 : t * (x * t)⁻¹ * t ∈ P := hconj (x * t)⁻¹ (P.inv_mem hx)
          have heq : x⁻¹ * t = t * (x * t)⁻¹ * t := by group
          rw [heq]
          exact h1 }
  have hPS : P ≤ S := fun x hx => Or.inl hx
  have htS : t ∈ S := Or.inr (by rw [ht2]; exact P.one_mem)
  have hle : P ⊔ zpowers t ≤ S := sup_le hPS (Subgroup.zpowers_le.mpr htS)
  exact hle hc

theorem V_comm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
  intro v hv w hw
  rw [h.V_eq] at hv hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact zpow_mul_comm u i j

theorem t_inv_mem : ∀ v ∈ V, t * v * t⁻¹ = v⁻¹ := by
  intro v hv
  rw [h.V_eq] at hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← conj_zpow (a := t) (b := u) (i := k), h.t_inv, inv_zpow]

theorem t_notMem_cent : t ∉ centralizer (V : Set G) := by
  intro ht
  have huV : u ∈ V := by rw [h.V_eq]; exact Subgroup.mem_zpowers u
  have hcomm : u * t = t * u := (Subgroup.mem_centralizer_iff.mp ht) u huV
  have hconj : t * u * t⁻¹ = u := by
    calc t * u * t⁻¹ = u * t * t⁻¹ := by rw [← hcomm]
      _ = u := by group
  have hu_inv : u⁻¹ = u := h.t_inv.symm.trans hconj
  have hu2 : u ^ 2 = 1 := by
    simpa [pow_two, hu_inv] using mul_inv_cancel u
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  rw [h.u_order] at hdvd
  norm_num at hdvd

theorem t_notMem_V : t ∉ V := by
  intro ht
  apply h.t_notMem_cent
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact h.V_comm v hv t ht

theorem V_le_cent : V ≤ centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact h.V_comm w hw v hv

theorem AV_le_cent : A ⊔ V ≤ centralizer (V : Set G) := by
  refine sup_le ?_ h.V_le_cent
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (h.V_cent_A a ha v hv).symm

theorem t_mem_normalizer_V : t ∈ normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h.t_inv_mem x hx]
    exact V.inv_mem hx
  · intro hx
    have h2 := h.t_inv_mem (t * x * t⁻¹) hx
    rw [t_conj_triple h x] at h2
    rw [h2]
    exact V.inv_mem hx

theorem t_mem_normalizer_AV : t ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) := by
  have hfw : ∀ y, y ∈ A ⊔ V → t * y * t⁻¹ ∈ A ⊔ V := by
    intro y hy
    obtain ⟨a, ha, v, hv, rfl⟩ := mem_sup_of_commute (H := A) (K := V) h.V_cent_A hy
    have hta : t * a * t⁻¹ = a := by rw [← h.t_cent_A a ha]; group
    have htv : t * v * t⁻¹ = v⁻¹ := h.t_inv_mem v hv
    have heq : t * (a * v) * t⁻¹ = a * v⁻¹ := by
      calc t * (a * v) * t⁻¹ = (t * a * t⁻¹) * (t * v * t⁻¹) := by group
        _ = a * v⁻¹ := by rw [hta, htv]
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (V.inv_mem hv))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hfw y, fun hy => ?_⟩
  rw [← t_conj_triple h y]
  exact hfw (t * y * t⁻¹) hy

theorem t_notMem_AV : t ∉ A ⊔ V := by
  intro ht
  apply h.t_notMem_cent
  exact h.AV_le_cent ht

theorem t_mem_K : t ∈ centralizerSection (A ⊔ V) V := by
  refine ⟨h.t_mem_normalizer_AV, h.t_mem_normalizer_V, fun k hk => ?_⟩
  obtain ⟨a, ha, v, hv, rfl⟩ := mem_sup_of_commute (H := A) (K := V) h.V_cent_A hk
  have hvt : ⁅v, t⁆ = v ^ 2 := by
    rw [commutatorElement_def]
    have h1 : t * v⁻¹ * t⁻¹ = v := by
      have htv := h.t_inv_mem v hv
      calc t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹ := by group
        _ = (v⁻¹)⁻¹ := by rw [htv]
        _ = v := inv_inv v
    calc v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) := by group
      _ = v * v := by rw [h1]
      _ = v ^ 2 := by rw [pow_two]
  have hat : ⁅a, t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (h.t_cent_A a ha)
  have hva : a * v ^ 2 * a⁻¹ = v ^ 2 := by
    rw [h.V_cent_A a ha (v ^ 2) (V.pow_mem hv 2)]
    group
  rw [commutatorElement_mul_left_eq_conj_mul, hvt, hat, mul_one, hva]
  exact V.pow_mem hv 2

theorem t_mem_C1 : t ∈ C₁ := by
  rw [h.C1_eq, h.C0_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem t_mem_C0 : t ∈ C₀ := by
  rw [h.C0_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem V_le_C0 : V ≤ C₀ := by
  rw [h.C0_eq]
  exact le_sup_left

theorem A_le_C1 : A ≤ C₁ := by
  rw [h.C1_eq]
  exact le_sup_left

theorem t_mem_normalizer_C0 : t ∈ normalizer (C₀ : Set G) :=
  Subgroup.le_normalizer h.t_mem_C0

theorem t_mem_normalizer_C1 : t ∈ normalizer (C₁ : Set G) :=
  Subgroup.le_normalizer h.t_mem_C1

theorem K_le_normalizer_V : centralizerSection (A ⊔ V) V ≤ normalizer (V : Set G) := by
  intro k hk
  exact hk.2.1

theorem K_conj_mem {y k : G} (hy : y ∈ normalizer ((A ⊔ V : Subgroup G) : Set G))
    (hk : k ∈ centralizerSection (A ⊔ V) V) : y * k * y⁻¹ ∈ centralizerSection (A ⊔ V) V := by
  refine ⟨?_, ?_, ?_⟩
  · exact mul_mem (mul_mem hy hk.1) (inv_mem hy)
  · exact mul_mem (mul_mem (h.N_AV_le hy) hk.2.1) (inv_mem (h.N_AV_le hy))
  · intro x hx
    have hxy : y⁻¹ * x * y ∈ A ⊔ V := by
      have hyinv : y⁻¹ ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) := inv_mem hy
      have h1 := (Subgroup.mem_normalizer_iff.mp hyinv x).mp hx
      rwa [inv_inv] at h1
    have hcomm : ⁅y⁻¹ * x * y, k⁆ ∈ V := hk.2.2 _ hxy
    have hconj : y * ⁅y⁻¹ * x * y, k⁆ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.N_AV_le hy) _).mp hcomm
    have heq : ⁅x, y * k * y⁻¹⁆ = y * ⁅y⁻¹ * x * y, k⁆ * y⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact hconj

theorem mem_sup_K {X : Subgroup G} (hX : X ≤ normalizer ((A ⊔ V : Subgroup G) : Set G)) {n : G}
    (hn : n ∈ X ⊔ centralizerSection (A ⊔ V) V) :
    ∃ y ∈ X, ∃ k ∈ centralizerSection (A ⊔ V) V, n = y * k := by
  let K := centralizerSection (A ⊔ V) V
  let S : Subgroup G :=
    { carrier := {g | ∃ y ∈ X, ∃ k ∈ K, g = y * k}
      one_mem' := ⟨1, X.one_mem, 1, K.one_mem, by rw [mul_one]⟩
      mul_mem' := by
        rintro _ _ ⟨y1, hy1, k1, hk1, rfl⟩ ⟨y2, hy2, k2, hk2, rfl⟩
        refine ⟨y1 * y2, X.mul_mem hy1 hy2, (y2⁻¹ * k1 * y2) * k2, K.mul_mem ?_ hk2, by group⟩
        simpa [inv_inv] using h.K_conj_mem (inv_mem (hX hy2)) hk1
      inv_mem' := by
        rintro _ ⟨y, hy, k, hk, rfl⟩
        refine ⟨y⁻¹, X.inv_mem hy, y * k⁻¹ * y⁻¹, h.K_conj_mem (hX hy) (K.inv_mem hk), by group⟩ }
  have hle : X ⊔ K ≤ S := sup_le
    (fun x hx => ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩)
    (fun k hk => ⟨1, X.one_mem, k, hk, (one_mul k).symm⟩)
  exact hle hn

theorem mem_cent_or_mul_t {n : G} (hn : n ∈ normalizer (V : Set G)) :
    n ∈ centralizer (V : Set G) ∨ n * t ∈ centralizer (V : Set G) := by
  have huV : u ∈ V := by rw [h.V_eq]; exact Subgroup.mem_zpowers u
  have hwV : n * u * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hn u).mp huV
  have hwzp : n * u * n⁻¹ ∈ zpowers u := by rwa [← h.V_eq]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwzp
  have h1 : u ^ (k % (4 : ℤ)) = u ^ k := by
    have hh := zpow_mod_orderOf u k
    rwa [h.u_order] at hh
  have hkmod : u ^ (k % (4 : ℤ)) = n * u * n⁻¹ := by rw [h1, hk]
  have hord : orderOf (u ^ (k % (4 : ℤ))) = 4 := by
    rw [hkmod, ← MulAut.conj_apply n u, MulEquiv.orderOf_eq, h.u_order]
  have hr0 : 0 ≤ k % (4 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hr4 : k % (4 : ℤ) < 4 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases hkm : k % (4 : ℤ)
  · exfalso
    rw [zpow_zero, orderOf_one] at hord
    norm_num at hord
  · left
    apply mem_cent_of_conj_u h
    rw [zpow_one] at hkmod
    exact hkmod.symm
  · exfalso
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at hord
    have h2 : orderOf (u ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (x := u) (n := 2) (by norm_num)
        (by rw [h.u_order]; norm_num), h.u_order]
    rw [h2] at hord
    norm_num at hord
  · right
    apply mem_cent_of_conj_u h (x := n * t)
    have hu4 : u ^ (4 : ℕ) = 1 := by
      have hh := pow_orderOf_eq_one u
      rwa [h.u_order] at hh
    have hu3 : u ^ (3 : ℤ) = u⁻¹ := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact eq_inv_of_mul_eq_one_left
        (by rw [← pow_succ, show (3 + 1 : ℕ) = 4 by norm_num, hu4])
    have hw3 : n * u * n⁻¹ = u⁻¹ := by rw [← hkmod, hu3]
    calc (n * t) * u * (n * t)⁻¹ = n * (t * u * t⁻¹) * n⁻¹ := by group
      _ = n * u⁻¹ * n⁻¹ := by rw [h.t_inv]
      _ = (n * u * n⁻¹)⁻¹ := by group
      _ = (u⁻¹)⁻¹ := by rw [hw3]
      _ = u := inv_inv u

theorem relIndex_cent {X : Subgroup G} (hX : X ≤ normalizer (V : Set G)) (ht : t ∈ X) :
    (centralizer (V : Set G) ⊓ X).relIndex X = 2 := by
  let C := centralizer (V : Set G)
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, ht, fun b hb => ?_⟩
  have hbX : b ∈ X := hb
  have hbtX : b * t ∈ X := X.mul_mem hb ht
  rcases h.mem_cent_or_mul_t (hX hb) with hbc | hbtc
  · refine Or.inr ⟨⟨hbc, hbX⟩, fun hbt => ?_⟩
    apply h.t_notMem_cent
    have h1 : b⁻¹ * (b * t) ∈ C := C.mul_mem (C.inv_mem hbc) hbt.1
    rwa [show b⁻¹ * (b * t) = t by group] at h1
  · refine Or.inl ⟨⟨hbtc, hbtX⟩, fun hb' => ?_⟩
    apply h.t_notMem_cent
    have h1 : b⁻¹ * (b * t) ∈ C := C.mul_mem (C.inv_mem hb'.1) hbtc
    rwa [show b⁻¹ * (b * t) = t by group] at h1

theorem card_V : Nat.card ↥V = 4 := by
  rw [h.V_eq, Nat.card_zpowers, h.u_order]

theorem inf_AV : A ⊓ V = zpowers (u ^ 2) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact h.A_inf_C0 ⟨hx.1, h.V_le_C0 hx.2⟩
  · intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨A.zpow_mem h.sq_mem k, ?_⟩
    have hu2V : u ^ 2 ∈ V := by
      rw [h.V_eq]
      simpa using Subgroup.zpow_mem_zpowers u (2 : ℤ)
    exact V.zpow_mem hu2V k

theorem card_AV : Nat.card ↥(A ⊔ V) = 64 := by
  have hform := natCard_inf_mul_natCard_sup A V h.V_cent_A
  have h2 : orderOf (u ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (x := u) (n := 2) (by norm_num)
      (by rw [h.u_order]; norm_num), h.u_order]
  have hcard2 : Nat.card ↥(zpowers (u ^ 2)) = 2 := by
    rw [Nat.card_zpowers, h2]
  rw [h.inf_AV, h.A_card, h.card_V, hcard2] at hform
  omega

theorem C1_eq' : C₁ = (A ⊔ V) ⊔ zpowers t := by
  rw [h.C1_eq, h.C0_eq, sup_assoc]

private theorem mem_C1_cases {c : G} (hc : c ∈ C₁) : c ∈ A ⊔ V ∨ c * t ∈ A ⊔ V := by
  rw [h.C1_eq'] at hc
  exact mem_sup_zpowers_t_cases h h.t_mem_normalizer_AV hc

private theorem mem_C0_cases {c : G} (hc : c ∈ C₀) : c ∈ V ∨ c * t ∈ V := by
  rw [h.C0_eq] at hc
  exact mem_sup_zpowers_t_cases h h.t_mem_normalizer_V hc

theorem AV_relIndex_C1 : (A ⊔ V).relIndex C₁ = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, h.t_mem_C1, fun b hb => ?_⟩
  rcases mem_C1_cases h hb with hbP | hbtP
  · refine Or.inr ⟨hbP, fun hbt => ?_⟩
    apply h.t_notMem_AV
    have h1 : b⁻¹ * (b * t) ∈ A ⊔ V := (A ⊔ V).mul_mem ((A ⊔ V).inv_mem hbP) hbt
    rwa [show b⁻¹ * (b * t) = t by group] at h1
  · refine Or.inl ⟨hbtP, fun hbP' => ?_⟩
    apply h.t_notMem_AV
    have h1 : b⁻¹ * (b * t) ∈ A ⊔ V := (A ⊔ V).mul_mem ((A ⊔ V).inv_mem hbP') hbtP
    rwa [show b⁻¹ * (b * t) = t by group] at h1

theorem comm_t_mem {m : G} (hm : m ∈ normalizer (C₁ : Set G)) : ⁅m, t⁆ ∈ A ⊔ V := by
  have hconj : m * t * m⁻¹ ∈ C₁ := (Subgroup.mem_normalizer_iff.mp hm t).mp h.t_mem_C1
  have hmP : m ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) := h.N_C1_le hm
  rcases mem_C1_cases h hconj with hP | hPt
  · exfalso
    apply h.t_notMem_AV
    have hmPinv : m⁻¹ ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) := inv_mem hmP
    have h1 : m⁻¹ * (m * t * m⁻¹) * m ∈ A ⊔ V := by
      have h2 := (Subgroup.mem_normalizer_iff.mp hmPinv (m * t * m⁻¹)).mp hP
      rwa [inv_inv] at h2
    rwa [show m⁻¹ * (m * t * m⁻¹) * m = t by group] at h1
  · have heq : ⁅m, t⁆ = (m * t * m⁻¹) * t := by
      simp [commutatorElement_def, t_inv_eq h]
    rw [heq]
    exact hPt

theorem cent_inf_cs_eq :
    centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V =
      centralizer (V : Set G) ⊓ normalizer (C₀ : Set G) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxC, hxCS⟩
    refine ⟨hxC, ?_⟩
    have h1 : x ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G) := hxCS.1
    rwa [← h.C0_eq] at h1
  · rintro x ⟨hxC, hxN⟩
    refine ⟨hxC, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← h.C0_eq]
      exact hxN
    · exact Subgroup.centralizer_le_normalizer (V : Set G) hxC
    · intro k hk
      rw [← h.C0_eq] at hk
      rcases mem_C0_cases h hk with hkV | hktV
      · have hcomm : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hxC) k hkV
        have h1 : ⁅k, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
        rw [h1]
        exact V.one_mem
      · have htv : ⁅t, x⁆ ∈ V := by
          have hxtC0 : x * t * x⁻¹ ∈ C₀ :=
            (Subgroup.mem_normalizer_iff.mp hxN t).mp h.t_mem_C0
          have hxt_notV : x * t * x⁻¹ ∉ V := by
            intro hmem
            apply h.t_notMem_V
            have hxV : x ∈ normalizer (V : Set G) :=
              Subgroup.centralizer_le_normalizer (V : Set G) hxC
            have h1 : x⁻¹ * (x * t * x⁻¹) * x ∈ V := by
              have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hxV) (x * t * x⁻¹)).mp hmem
              rwa [inv_inv] at h2
            rwa [show x⁻¹ * (x * t * x⁻¹) * x = t by group] at h1
          rcases mem_C0_cases h hxtC0 with hmem | hmem
          · exact absurd hmem hxt_notV
          · have heq : ⁅t, x⁆ = ((x * t * x⁻¹) * t)⁻¹ := by
              rw [commutatorElement_def]
              simp only [t_inv_eq h, mul_inv_rev, inv_inv]
              group
            rw [heq]
            exact V.inv_mem hmem
        have hvx : ⁅k * t, x⁆ = 1 := by
          have hcomm : (k * t) * x = x * (k * t) :=
            (Subgroup.mem_centralizer_iff.mp hxC) (k * t) hktV
          exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
        have hconj : (k * t) * ⁅t, x⁆ * (k * t)⁻¹ = ⁅t, x⁆ := by
          have hcomm2 : (k * t) * ⁅t, x⁆ = ⁅t, x⁆ * (k * t) :=
            h.V_comm (k * t) hktV ⁅t, x⁆ htv
          rw [hcomm2]
          group
        have hk_eq : k = (k * t) * t := by rw [mul_assoc, t_sq h, mul_one]
        have heq2 : ⁅k, x⁆ = ⁅t, x⁆ := by
          rw [hk_eq, commutatorElement_mul_left_eq_conj_mul, hvx, mul_one, hconj]
        rw [heq2]
        exact htv

end Gomi6Data

end CFSG.OddStandard.HigherRank.YamadaG23
