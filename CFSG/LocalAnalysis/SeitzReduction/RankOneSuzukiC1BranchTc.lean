module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchNu

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}
  {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}

theorem cent_le_sup (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) {v₀ : G} (hv₀ : v₀ ∈ U₁) :
    U₁ ⊓ centralizer ({v₀ * t} : Set G) ≤ szT₁ L T ⊔ V := by
  have hK' := h.card_K hK hc
  have hk := h.one_le_k hK hc
  intro w hw
  obtain ⟨hwU₁, hwx⟩ := mem_inf.mp hw
  rw [mem_centralizer_singleton_iff] at hwx
  have e0 : (v₀ * t) * w * (v₀ * t)⁻¹ = w := by rw [← hwx]; group
  have e : w * t * w⁻¹ * t⁻¹ = w * v₀⁻¹ * w⁻¹ * v₀⁻¹⁻¹ := by
    calc w * t * w⁻¹ * t⁻¹ = w * (v₀⁻¹ * ((v₀ * t) * w * (v₀ * t)⁻¹) * v₀)⁻¹ := by group
      _ = w * v₀⁻¹ * w⁻¹ * v₀⁻¹⁻¹ := by rw [e0]; group
  have hσA : w * t * w⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
    rw [e]
    exact h.comm_mem_szA₁ w hwU₁ v₀⁻¹ (inv_mem hv₀)
  have hσk : (w * t * w⁻¹ * t⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, pow_succ', pow_mul, hc.sq_eq_one_of_mem_szA₁ h.ha hK' hσA, one_pow]
  exact h.mem_sup_of_S_eq_zero hK hc hwU₁ (by rw [hσk, hc.v_one])

theorem card_cent_le (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hμ : U₁ ≤ centralizer (V : Set G)) {v₀ : G}
    (hv₀ : v₀ ∈ U₁) :
    Nat.card (U₁ ⊓ centralizer ({v₀ * t} : Set G) : Subgroup G) ≤ 2 ^ f * 2 ^ f := by
  set C := U₁ ⊓ centralizer ({v₀ * t} : Set G) with hC
  have hCsup := h.cent_le_sup hK hc hv₀
  have hCV : ∀ r ∈ V, r ∈ C → r ∈ szA₁ (szT₁ L T) := by
    intro r hr hrC
    refine h.omega r hr ?_
    have e1 : (v₀ * t) * r * (v₀ * t)⁻¹ = r⁻¹ := by
      calc (v₀ * t) * r * (v₀ * t)⁻¹ = v₀ * (t * r * t⁻¹) * v₀⁻¹ := by group
        _ = r⁻¹ := by rw [h.inv r hr, ← mem_centralizer_iff.mp (hμ hv₀) _ (inv_mem hr),
            mul_inv_cancel_right]
    rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp hrC).2, mul_inv_cancel_right] at e1
    rw [sq]
    nth_rewrite 2 [e1]
    exact mul_inv_cancel r
  have h1 := relIndex_mul_card (H := V) (K := C)
  have h2 : V.relIndex C ≤ 2 ^ f :=
    (relIndex_le_of_le_right hCsup (by rw [h.relIndex_V_sup hK hc]; positivity)).trans_eq
      (h.relIndex_V_sup hK hc)
  have h3 : Nat.card (V ⊓ C : Subgroup G) ≤ 2 ^ f :=
    (Subgroup.card_le_of_le fun r hr => hCV r (mem_inf.mp hr).1 (mem_inf.mp hr).2).trans_eq
      (h.card_szA₁ hK hc)
  rw [← h1]
  exact Nat.mul_le_mul h2 h3

theorem mem_cent_iff (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    {y₀ w y r : G} (hy₀ : y₀ ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hy : y ∈ szT₁ L T) (hr : r ∈ V) :
    y * r ∈ centralizer ({y₀ * w * t} : Set G) ↔ r ^ 2 = y⁻¹ * y₀ * y * y₀⁻¹ := by
  obtain ⟨hwU₁, hwC⟩ := mem_inf.mp hw
  have hwy : y * w = w * y := mem_centralizer_iff.mp hwC y hy
  have hwr : r⁻¹ * w = w * r⁻¹ := mem_centralizer_iff.mp (hμ hwU₁) _ (inv_mem hr)
  have hry₀ : y₀ * r⁻¹ = r⁻¹ * y₀ := h.V_comm (inv_mem hr) hy₀
  have hty : t * y * t⁻¹ = y := by rw [← h.t_comm hy, mul_inv_cancel_right]
  have e1 : w * y * r⁻¹ * w⁻¹ = y * r⁻¹ := by
    calc w * y * r⁻¹ * w⁻¹ = (y * w) * r⁻¹ * w⁻¹ := by rw [← hwy]
      _ = y * (w * r⁻¹) * w⁻¹ := by group
      _ = y * (r⁻¹ * w) * w⁻¹ := by rw [← hwr]
      _ = y * r⁻¹ := by group
  have e2 : r⁻¹ * y₀⁻¹ = y₀⁻¹ * r⁻¹ := by
    calc r⁻¹ * y₀⁻¹ = y₀⁻¹ * (y₀ * r⁻¹) * y₀⁻¹ := by group
      _ = y₀⁻¹ * (r⁻¹ * y₀) * y₀⁻¹ := by rw [hry₀]
      _ = y₀⁻¹ * r⁻¹ := by group
  have hx : (y₀ * w * t) * (y * r) * (y₀ * w * t)⁻¹ = y₀ * y * y₀⁻¹ * r⁻¹ := by
    calc (y₀ * w * t) * (y * r) * (y₀ * w * t)⁻¹ =
          y₀ * w * (t * y * t⁻¹) * (t * r * t⁻¹) * w⁻¹ * y₀⁻¹ := by group
      _ = y₀ * (w * y * r⁻¹ * w⁻¹) * y₀⁻¹ := by rw [hty, h.inv r hr]; group
      _ = y₀ * y * (r⁻¹ * y₀⁻¹) := by rw [e1]; group
      _ = y₀ * y * y₀⁻¹ * r⁻¹ := by rw [e2]; group
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hz
    have e : (y₀ * w * t) * (y * r) * (y₀ * w * t)⁻¹ = y * r := by rw [← hz]; group
    rw [hx] at e
    calc r ^ 2 = y⁻¹ * (y * r) * r := by rw [sq]; group
      _ = y⁻¹ * (y₀ * y * y₀⁻¹ * r⁻¹) * r := by rw [e]
      _ = y⁻¹ * y₀ * y * y₀⁻¹ := by group
  · intro hr2
    have e : (y₀ * w * t) * (y * r) * (y₀ * w * t)⁻¹ = y * r := by
      rw [hx]
      calc y₀ * y * y₀⁻¹ * r⁻¹ = y * (y⁻¹ * y₀ * y * y₀⁻¹) * r⁻¹ := by group
        _ = y * r ^ 2 * r⁻¹ := by rw [hr2]
        _ = y * r := by rw [sq]; group
    calc y * r * (y₀ * w * t) = ((y₀ * w * t) * (y * r) * (y₀ * w * t)⁻¹) * (y₀ * w * t) := by
          rw [e]
      _ = y₀ * w * t * (y * r) := by group

theorem comm_eq_of_u_eq (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) {y₀ y₀' y : G} (hy₀ : y₀ ∈ szT₁ L T)
    (hy₀' : y₀' ∈ szT₁ L T) (hu : u y₀ = u y₀') (hy : y ∈ szT₁ L T) :
    y⁻¹ * y₀ * y * y₀⁻¹ = y⁻¹ * y₀' * y * y₀'⁻¹ := by
  have ha := hc.inv_mul_mem_szA₁_of_u_eq h.ha (h.card_K hK hc) hy₀ hy₀' hu
  have hc1 := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy
  have e : y₀' = y₀ * (y₀⁻¹ * y₀') := by group
  rw [e]
  calc y⁻¹ * y₀ * y * y₀⁻¹ = y⁻¹ * y₀ * (y * (y₀⁻¹ * y₀')) * (y₀⁻¹ * y₀')⁻¹ * y₀⁻¹ := by group
    _ = y⁻¹ * y₀ * ((y₀⁻¹ * y₀') * y) * (y₀⁻¹ * y₀')⁻¹ * y₀⁻¹ := by rw [hc1]
    _ = _ := by group

theorem cent_eq_of_u_eq (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hμ : U₁ ≤ centralizer (V : Set G))
    {y₀ y₀' w w' : G} (hy₀ : y₀ ∈ szT₁ L T) (hy₀' : y₀' ∈ szT₁ L T) (hu : u y₀ = u y₀')
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    U₁ ⊓ centralizer ({y₀ * w * t} : Set G) = U₁ ⊓ centralizer ({y₀' * w' * t} : Set G) := by
  have key : ∀ {y₀ y₀' w w' : G}, y₀ ∈ szT₁ L T → y₀' ∈ szT₁ L T → u y₀ = u y₀' →
      w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) → w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) →
      U₁ ⊓ centralizer ({y₀ * w * t} : Set G) ≤ U₁ ⊓ centralizer ({y₀' * w' * t} : Set G) := by
    intro y₀ y₀' w w' hy₀ hy₀' hu hw hw' z hz
    have hzs := h.cent_le_sup hK hc (mul_mem (h.T₁_le_U₁ hy₀) (mem_inf.mp hw).1) hz
    obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hzs
    refine mem_inf.mpr ⟨(mem_inf.mp hz).1, ?_⟩
    rw [h.mem_cent_iff hμ hy₀' hw' hy hr, ← h.comm_eq_of_u_eq hK hc hy₀ hy₀' hu hy]
    exact (h.mem_cent_iff hμ hy₀ hw hy hr).mp (mem_inf.mp hz).2
  exact le_antisymm (key hy₀ hy₀' hu hw hw') (key hy₀' hy₀ hu.symm hw' hw)

theorem T₁_eq_cent (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hμ : U₁ ≤ centralizer (V : Set G)) {y₀ : G}
    (hy₀ : y₀ ∈ szT₁ L T) (hu0 : u y₀ = 0) :
    szT₁ L T = U₁ ⊓ centralizer ({y₀ * t} : Set G) := by
  have hy₀A := (hc.mem_szA₁_iff h.ha (h.card_K hK hc) hy₀).mpr hu0
  have hle : szT₁ L T ≤ U₁ ⊓ centralizer ({y₀ * t} : Set G) := fun y hy => by
    refine mem_inf.mpr ⟨h.T₁_le_U₁ hy, mem_centralizer_singleton_iff.mpr ?_⟩
    have e1 : y * y₀ = y₀ * y := mem_centralizer_iff.mp (mem_szA₁.mp hy₀A).2 y hy
    calc y * (y₀ * t) = y₀ * y * t := by rw [← mul_assoc, e1]
      _ = y₀ * t * y := by rw [mul_assoc, h.t_comm hy, ← mul_assoc]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h.card_T₁ hK hc, sq]
  exact h.card_cent_le hK hc hμ (h.T₁_le_U₁ hy₀)

theorem u_eq_of_cent_eq (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hμ : U₁ ≤ centralizer (V : Set G)) {y₀ y₀' : G}
    (hy₀ : y₀ ∈ szT₁ L T) (hy₀' : y₀' ∈ szT₁ L T)
    (heq : U₁ ⊓ centralizer ({y₀ * t} : Set G) = U₁ ⊓ centralizer ({y₀' * t} : Set G)) :
    u y₀ = u y₀' := by
  have hK' := h.card_K hK hc
  have hk := h.one_le_k hK hc
  have h1 : (1 : G) ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := one_mem _
  have hcomm : ∀ y ∈ szT₁ L T, y⁻¹ * y₀ * y * y₀⁻¹ = y⁻¹ * y₀' * y * y₀'⁻¹ := by
    intro y hy
    have hA : y⁻¹ * y₀ * y * y₀⁻¹ ∈ szA₁ (szT₁ L T) := by
      have := h.conj_T₁ y₀ (h.U₁_le (h.T₁_le_U₁ hy₀)) y hy
      have e := hc.comm_mem_szA₁ h.ha hK' (inv_mem hy) hy₀
      rw [inv_inv] at e
      exact e
    have hAk : (y⁻¹ * y₀ * y * y₀⁻¹) ^ 2 ^ k = 1 := by
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hj, pow_succ', pow_mul, hc.sq_eq_one_of_mem_szA₁ h.ha hK' hA, one_pow]
    obtain ⟨r, hr, hr2⟩ := SzC1.exists_sq_eq_of_pow_eq_one h.comm h.omega h.pow
      (by rw [h.card_szA₁ hK hc, h.card]) (h.le hA) hAk
    have hmem : y * r ∈ U₁ ⊓ centralizer ({y₀ * 1 * t} : Set G) :=
      mem_inf.mpr ⟨mul_mem (h.T₁_le_U₁ hy) (h.V_le_U₁ hr),
        (h.mem_cent_iff hμ hy₀ h1 hy hr).mpr hr2.symm⟩
    rw [mul_one, heq, ← mul_one y₀'] at hmem
    rw [hr2]
    exact (h.mem_cent_iff hμ hy₀' h1 hy hr).mp (mem_inf.mp hmem).2
  have hz : y₀'⁻¹ * y₀ ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨mul_mem (inv_mem hy₀') hy₀, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have e := hcomm y hy
    have e1 : y₀ * y * y₀⁻¹ = y₀' * y * y₀'⁻¹ := by
      have := congrArg (fun z => y * z) e
      simpa [mul_assoc] using this
    calc y * (y₀'⁻¹ * y₀) = y₀'⁻¹ * (y₀' * y * y₀'⁻¹) * y₀ := by group
      _ = y₀'⁻¹ * (y₀ * y * y₀⁻¹) * y₀ := by rw [e1]
      _ = y₀'⁻¹ * y₀ * y := by group
  have hu := hc.u_eq_zero_of_mem_szA₁ h.ha hK' hz
  rw [(hc.mul _ (inv_mem hy₀') _ hy₀).1, (hc.inv hy₀').1] at hu
  linear_combination hu - u y₀' * (CharTwo.two_eq_zero : (2 : K) = 0)


theorem map_conj_d_cent (h : SzC1Stage G L f a t T d V U U₁ k) (y₀ : G) :
    (U₁ ⊓ centralizer ({y₀ * t} : Set G)).map (MulAut.conj d⁻¹).toMonoidHom =
      U₁ ⊓ centralizer ({(d⁻¹ * y₀ * d) * t} : Set G) := by
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.mp h.d_norm.2
  ext z
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxU, hxC⟩ := mem_inf.mp hx
    rw [mem_centralizer_singleton_iff] at hxC
    refine mem_inf.mpr ⟨by simpa using (mem_normalizer_iff.mp (inv_mem h.d_mem_U₁) x).mp hxU,
      mem_centralizer_singleton_iff.mpr ?_⟩
    calc d⁻¹ * x * d * (d⁻¹ * y₀ * d * t) = d⁻¹ * (x * (y₀ * t)) * d := by
          rw [show d⁻¹ * x * d * (d⁻¹ * y₀ * d * t) = d⁻¹ * x * y₀ * (d * t) by group, hdt]
          group
      _ = d⁻¹ * ((y₀ * t) * x) * d := by rw [hxC]
      _ = d⁻¹ * y₀ * d * t * (d⁻¹ * x * d) := by
          rw [show d⁻¹ * y₀ * d * t * (d⁻¹ * x * d) = d⁻¹ * y₀ * (d * t * d⁻¹) * x * d by group,
            show d * t * d⁻¹ = t by rw [hdt, mul_inv_cancel_right]]
          group
  · intro hz
    obtain ⟨hzU, hzC⟩ := mem_inf.mp hz
    rw [mem_centralizer_singleton_iff] at hzC
    refine ⟨d * z * d⁻¹, mem_inf.mpr ⟨(mem_normalizer_iff.mp h.d_mem_U₁ z).mp hzU,
      mem_centralizer_singleton_iff.mpr ?_⟩, by group⟩
    calc d * z * d⁻¹ * (y₀ * t) = d * (z * (d⁻¹ * y₀ * d * t)) * d⁻¹ := by
          rw [show d * (z * (d⁻¹ * y₀ * d * t)) * d⁻¹ = d * z * d⁻¹ * y₀ * (d * t) * d⁻¹ by group,
            hdt]
          group
      _ = d * ((d⁻¹ * y₀ * d * t) * z) * d⁻¹ := by rw [hzC]
      _ = y₀ * t * (d * z * d⁻¹) := by
          rw [show d * ((d⁻¹ * y₀ * d * t) * z) * d⁻¹ = y₀ * (d * t) * z * d⁻¹ by group, hdt]
          group

theorem t_not_mem_centralizer_V (h : SzC1Stage G L f a t T d V U U₁ k) :
    t ∉ centralizer (V : Set G) := by
  intro ht
  obtain ⟨r, hr, hr2⟩ := h.exists_sq_ne_one
  apply hr2
  have e1 : t * r * t⁻¹ = r := by rw [← mem_centralizer_iff.mp ht r hr, mul_inv_cancel_right]
  rw [h.inv r hr] at e1
  rw [sq]
  nth_rewrite 1 [← e1]
  exact inv_mul_cancel r

theorem conj_mem_szA₁_of_normalizer (h : SzC1Stage G L f a t T d V U U₁ k)
    (hμ : U₁ ≤ centralizer (V : Set G)) {n : G} (hn : n ∈ normalizer (U : Set G)) {b : G}
    (hb : b ∈ szA₁ (szT₁ L T)) : n * b * n⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hbU : b ∈ U := h.U₁_le (h.V_le_U₁ (h.le hb))
  have hzU : n * b * n⁻¹ ∈ U := (mem_normalizer_iff.mp hn b).mp hbU
  have hcent : ∀ x ∈ U, x * (n * b * n⁻¹) = (n * b * n⁻¹) * x := by
    intro x hx
    have hx' : n⁻¹ * x * n ∈ U := by simpa using (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
    have e := h.conj_szA₁ _ hx' b hb
    have e1 : (n⁻¹ * x * n) * b = b * (n⁻¹ * x * n) := by
      calc (n⁻¹ * x * n) * b = ((n⁻¹ * x * n) * b * (n⁻¹ * x * n)⁻¹) * (n⁻¹ * x * n) := by group
        _ = b * (n⁻¹ * x * n) := by rw [e]
    calc x * (n * b * n⁻¹) = n * ((n⁻¹ * x * n) * b) * n⁻¹ := by group
      _ = n * (b * (n⁻¹ * x * n)) * n⁻¹ := by rw [e1]
      _ = n * b * n⁻¹ * x := by group
  have hzU₁ : n * b * n⁻¹ ∈ U₁ := by
    refine (h.mem_or_mul_t_mem hzU).resolve_right fun hzt => h.t_not_mem_centralizer_V ?_
    have e : t = (n * b * n⁻¹)⁻¹ * (n * b * n⁻¹ * t) := by group
    rw [e]
    refine mul_mem (inv_mem (mem_centralizer_iff.mpr fun r hr => ?_)) (hμ hzt)
    exact (hcent r (h.U₁_le (h.V_le_U₁ hr)))
  have hzT := h.mem_T₁_of_comm hzU₁ (hcent t h.t_mem_U).symm
  exact mem_szA₁.mpr ⟨hzT, mem_centralizer_iff.mpr fun y hy =>
    hcent y (h.U₁_le (h.T₁_le_U₁ hy))⟩

theorem exists_mul_of_mem_U₁ (_h : SzC1Stage G L f a t T d V U U₁ k)
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {x : G} (hx : x ∈ U₁) :
    ∃ y ∈ szT₁ L T, ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), x = y * w := by
  have hTN : szT₁ L T ≤ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
      rw [mem_centralizer_iff.mp (mem_inf.mp hw).2 _ (inv_mem hy), inv_mul_cancel_right]
      exact hw
  have hx' : x ∈ ((szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) : Set G) := by
    rw [← hlam]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hTN] at hx'
  obtain ⟨y, hy, w, hw, rfl⟩ := hx'
  exact ⟨y, hy, w, hw, rfl⟩

theorem mem_V_of_sq_mem_szA₁ (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hμ : U₁ ≤ centralizer (V : Set G)) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (hw2 : w ^ 2 ∈ szA₁ (szT₁ L T)) : w ∈ V := by
  have hK' := h.card_K hK hc
  have hk := h.one_le_k hK hc
  have hσ2 : (w * t * w⁻¹ * t⁻¹) ^ 2 = 1 := by
    rw [← h.sq_sq_eq hμ (mem_inf.mp hw).1, hc.sq_eq_one_of_mem_szA₁ h.ha hK' hw2]
  have hS : v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, pow_succ', pow_mul, hσ2, one_pow, hc.v_one]
  exact h.mem_V_of_mem_V₁_of_mem_sup hw (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 hS)

theorem conj_mem_sup_of_normalizer (h : SzC1Stage G L f a t T d V U U₁ k)
    (hK : Fintype.card K = 2 ^ f) (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {n : G}
    (hn : n ∈ normalizer (U : Set G)) {y : G} (hy : y ∈ szT₁ L T) : n * y * n⁻¹ ∈ szT₁ L T ⊔ V := by
  have hK' := h.card_K hK hc
  obtain ⟨y', hy', w, hw, hyw⟩ := h.exists_mul_of_mem_U₁ hlam
    (h.conj_mem_U₁_of_normalizer hμ hn (h.T₁_le_U₁ hy))
  have hz2 : (n * y * n⁻¹) ^ 2 ∈ szA₁ (szT₁ L T) := by
    rw [conj_pow]
    exact h.conj_mem_szA₁_of_normalizer hμ hn (hc.sq_mem_szA₁ h.ha hK' hy)
  have hwy : y' * w = w * y' := mem_centralizer_iff.mp (mem_inf.mp hw).2 y' hy'
  have e : w ^ 2 = (y' ^ 2)⁻¹ * (n * y * n⁻¹) ^ 2 := by
    rw [hyw, sq, sq, sq]
    calc w * w = (y' * y')⁻¹ * (y' * (y' * w) * w) := by group
      _ = (y' * y')⁻¹ * (y' * (w * y') * w) := by rw [hwy]
      _ = (y' * y')⁻¹ * (y' * w * (y' * w)) := by group
  have hw2 : w ^ 2 ∈ szA₁ (szT₁ L T) := by
    rw [e]
    exact mul_mem (inv_mem (hc.sq_mem_szA₁ h.ha hK' hy')) hz2
  rw [hyw]
  exact mul_mem (mem_sup_left hy') (mem_sup_right (h.mem_V_of_sq_mem_szA₁ hK hc hμ hw hw2))

theorem map_conj_T₁_eq
    (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {n : G}
    (hn : n ∈ normalizer (U : Set G)) :
    ∃ y₀ ∈ szT₁ L T, ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), n * t * n⁻¹ = y₀ * w * t ∧
      (szT₁ L T).map (MulAut.conj n).toMonoidHom =
        U₁ ⊓ centralizer ({y₀ * w * t} : Set G) := by
  have hxU : n * t * n⁻¹ ∈ U := (mem_normalizer_iff.mp hn t).mp h.t_mem_U
  have hxt := (h.mem_or_mul_t_mem hxU).resolve_left (h.conj_not_mem_U₁ n)
  obtain ⟨y₀, hy₀, w, hw, hyw⟩ := h.exists_mul_of_mem_U₁ hlam hxt
  have hx : n * t * n⁻¹ = y₀ * w * t := by
    rw [← hyw, mul_assoc (n * t * n⁻¹) t t, h.t_mul_self, mul_one]
  refine ⟨y₀, hy₀, w, hw, hx, ?_⟩
  have hle : (szT₁ L T).map (MulAut.conj n).toMonoidHom ≤
      U₁ ⊓ centralizer ({y₀ * w * t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.mpr ⟨h.conj_mem_U₁_of_normalizer hμ hn (h.T₁_le_U₁ hy),
      mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hx]
    calc n * y * n⁻¹ * (n * t * n⁻¹) = n * (y * t) * n⁻¹ := by group
      _ = n * (t * y) * n⁻¹ := by rw [h.t_comm hy]
      _ = n * t * n⁻¹ * (n * y * n⁻¹) := by group
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, h.card_T₁ hK hc, sq]
  exact h.card_cent_le hK hc hμ (mul_mem (h.T₁_le_U₁ hy₀) (mem_inf.mp hw).1)

end SzC1Stage

end CFSG.SeitzReduction.RankOne
