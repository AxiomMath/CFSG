module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem tau_ne_one (h : Ctx t L S x₁ x₂ lam rho tau) : tau ≠ 1 := by
  intro h1
  apply h.tau_not_mem
  rw [h1]
  exact Subgroup.mem_sup_left (twoCore t).one_mem

private theorem tau_mem_invCent (h : Ctx t L S x₁ x₂ lam rho tau) : tau ∈ invCent t :=
  h.le_invCent h.tau_mem

private theorem t_mem_S (h : Ctx t L S x₁ x₂ lam rho tau) : t ∈ S := by
  rw [h.S_eq]
  exact Subgroup.mem_sup_left h.hyp.mem_twoCore

private theorem zpowers_t_le_S (h : Ctx t L S x₁ x₂ lam rho tau) : zpowers t ≤ S :=
  Subgroup.zpowers_le.mpr (t_mem_S h)

private theorem zpowers_t_eq_one_or (h : Hyp G t L) {p : G} (hp : p ∈ zpowers t) :
    p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht : t * t = 1 := t_mul_self h
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private theorem zpowers_t_sq (h : Hyp G t L) {p : G} (hp : p ∈ zpowers t) : p * p = 1 := by
  rcases zpowers_t_eq_one_or h hp with rfl | rfl
  · rw [one_mul]
  · exact t_mul_self h

private theorem t_commute_S (h : Ctx t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ S) :
    t * g = g * t :=
  (mem_invCent_iff.mp (h.le_invCent hg)).symm

private theorem zpowers_t_commute_S (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ zpowers t) {g : G} (hg : g ∈ S) : p * g = g * p := by
  have hc : Commute t g := t_commute_S h hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  rw [← hk]
  exact hc.zpow_left k

private theorem t_mul_t_mul (h : Ctx t L S x₁ x₂ lam rho tau) (v : G) :
    t * (t * v) = v := by
  rw [← mul_assoc, t_mul_self h.hyp, one_mul]

theorem m12Rel_of_ctx (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    M12Rel x₁ x₂ lam tau :=
  { toWreathRel := h.wreath
    ord_tau := orderOf_eq_prime h44 (tau_ne_one h)
    comm_lam_tau := h.tau_lam.symm
    tau_x₁ := h.tau_x₁
    tau_x₂ := h.tau_x₂ }

theorem S_eq_prod_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) :
    S = zpowers t ⊔ m12Grp x₁ x₂ lam tau ∧ zpowers t ⊓ m12Grp x₁ x₂ lam tau = ⊥ := by
  have hSe : S = zpowers t ⊔ m12Grp x₁ x₂ lam tau := by
    rw [h.S_eq, h43]
  refine ⟨hSe, ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxzp, hxM⟩ := hx
  rcases zpowers_t_eq_one_or h.hyp hxzp with hx1 | hxt
  · rw [hx1]
  · exfalso
    have htM : t ∈ m12Grp x₁ x₂ lam tau := hxt ▸ hxM
    have hS_eq_M : S = m12Grp x₁ x₂ lam tau := by
      rw [hSe]
      exact le_antisymm (sup_le (Subgroup.zpowers_le.mpr htM) le_rfl) le_sup_right
    have hcardS : Nat.card S = 2 ^ 7 := by
      rw [h.card_S, h43, Nat.card_zpowers, h.hyp.ord_t]
      norm_num
    have hcardM : Nat.card (m12Grp x₁ x₂ lam tau) = 64 :=
      (m12Rel_of_ctx h h44).card_m12Grp
    rw [hS_eq_M, hcardM] at hcardS
    exact absurd hcardS (by norm_num)

theorem card_S_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t) :
    Nat.card S = 2 ^ 7 := by
  rw [h.card_S, h43, Nat.card_zpowers, h.hyp.ord_t]
  norm_num

theorem center_S_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t) :
    S ⊓ centralizer (S : Set G) = closure {t, (x₁ * x₂) ^ 2} := by
  refine le_antisymm ?_ h.center_ge
  calc S ⊓ centralizer (S : Set G) ≤ twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2) := h.center_le
    _ = zpowers t ⊔ zpowers ((x₁ * x₂) ^ 2) := by rw [h43]
    _ ≤ closure {t, (x₁ * x₂) ^ 2} := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le]
          exact Subgroup.subset_closure (by simp)
        · rw [Subgroup.zpowers_le]
          exact Subgroup.subset_closure (by simp)

theorem m12Grp_le_S (h : Ctx t L S x₁ x₂ lam rho tau) : m12Grp x₁ x₂ lam tau ≤ S := by
  rw [h.S_eq]
  exact le_sup_right

theorem mem_m12Grp_or_mul (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {s : G} (hs : s ∈ S) :
    s ∈ m12Grp x₁ x₂ lam tau ∨ t * s ∈ m12Grp x₁ x₂ lam tau := by
  have hSe := (S_eq_prod_of h h43 h44).1
  have hs' : s ∈ zpowers t ⊔ m12Grp x₁ x₂ lam tau := by
    rw [← hSe]
    exact hs
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ m12Grp x₁ x₂ lam tau, a * b = b * a := by
    intro a ha b hb
    exact zpowers_t_commute_S h ha (m12Grp_le_S h hb)
  obtain ⟨a, ha, m, hm, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hs'
  rcases zpowers_t_eq_one_or h.hyp ha with ha1 | hat
  · left
    rw [ha1]
    simpa using hm
  · right
    rw [hat, ← mul_assoc, t_mul_self h.hyp, one_mul]
    exact hm

theorem normalIn_inf_m12Grp (h : Ctx t L S x₁ x₂ lam rho tau) {V : Subgroup G}
    (hV : NormalIn V S) :
    NormalIn (V ⊓ m12Grp x₁ x₂ lam tau) (m12Grp x₁ x₂ lam tau) := by
  refine ⟨inf_le_right, ?_⟩
  intro g hg k hk
  rw [Subgroup.mem_inf] at hk ⊢
  exact ⟨hV.2 g (m12Grp_le_S h hg) k hk.1,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hk.2) (Subgroup.inv_mem _ hg)⟩

theorem centralizer_S_inf (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {Q : Subgroup G} (hQ : Q ≤ m12Grp x₁ x₂ lam tau) :
    S ⊓ centralizer (Q : Set G) =
      zpowers t ⊔ (m12Grp x₁ x₂ lam tau ⊓ centralizer (Q : Set G)) := by
  refine le_antisymm ?_ ?_
  · intro s hs
    rw [Subgroup.mem_inf] at hs
    obtain ⟨hsS, hsC⟩ := hs
    rcases mem_m12Grp_or_mul h h43 h44 hsS with hsM | htsM
    · exact Subgroup.mem_sup_right ⟨hsM, hsC⟩
    · have hmC : t * s ∈ centralizer (Q : Set G) := by
        rw [Subgroup.mem_centralizer_iff] at hsC ⊢
        intro q hq
        have hqS : q ∈ S := m12Grp_le_S h (hQ hq)
        have htq : t * q = q * t := t_commute_S h hqS
        calc q * (t * s) = (q * t) * s := by group
          _ = (t * q) * s := by rw [← htq]
          _ = t * (q * s) := by group
          _ = t * (s * q) := by rw [hsC q hq]
          _ = (t * s) * q := by group
      have hs_eq : s = t * (t * s) := (t_mul_t_mul h s).symm
      rw [hs_eq]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) ⟨htsM, hmC⟩
  · refine sup_le ?_ ?_
    · intro p hp
      refine Subgroup.mem_inf.mpr ⟨zpowers_t_le_S h hp, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (zpowers_t_commute_S h hp (m12Grp_le_S h (hQ hq))).symm
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨m12Grp_le_S h hx.1, hx.2⟩

theorem card_le_two_mul_inf (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {V : Subgroup G} (hV : V ≤ S) :
    Nat.card V ≤ 2 * Nat.card (V ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) := by
  by_cases hVM : ∀ v ∈ V, v ∈ m12Grp x₁ x₂ lam tau
  · have hC : V ⊓ m12Grp x₁ x₂ lam tau = V :=
      le_antisymm inf_le_left (fun v hv => ⟨hv, hVM v hv⟩)
    rw [hC]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  · push Not at hVM
    obtain ⟨v₀, hv₀V, hv₀M⟩ := hVM
    have htv₀ : t * v₀ ∈ m12Grp x₁ x₂ lam tau :=
      (mem_m12Grp_or_mul h h43 h44 (hV hv₀V)).resolve_left hv₀M
    have hcover : ∀ n ∈ V,
        n ∈ V ⊓ m12Grp x₁ x₂ lam tau ∨ v₀⁻¹ * n ∈ V ⊓ m12Grp x₁ x₂ lam tau := by
      intro n hn
      rcases mem_m12Grp_or_mul h h43 h44 (hV hn) with hnM | htnM
      · exact Or.inl ⟨hn, hnM⟩
      · refine Or.inr ⟨V.mul_mem (V.inv_mem hv₀V) hn, ?_⟩
        have hid : v₀⁻¹ * n = (t * v₀)⁻¹ * (t * n) := by group
        rw [hid]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htv₀) htnM
    have hrel : (V ⊓ m12Grp x₁ x₂ lam tau).relIndex V ≤ 2 :=
      relIndex_le_two_of_forall inf_le_left v₀ hv₀V hcover
    have hcard : Nat.card V =
        (V ⊓ m12Grp x₁ x₂ lam tau).relIndex V *
          Nat.card (V ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) := by
      have hrc := Subgroup.relIndex_mul_card
        (H := V ⊓ m12Grp x₁ x₂ lam tau) (K := V)
      rw [inf_eq_left.mpr inf_le_left] at hrc
      exact hrc.symm
    rw [hcard]
    exact Nat.mul_le_mul_right _ hrel

theorem eq_sup_inf_of_t_mem (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {V : Subgroup G} (hV : V ≤ S) (ht : t ∈ V) :
    V = zpowers t ⊔ (V ⊓ m12Grp x₁ x₂ lam tau) ∧
      Nat.card V = 2 * Nat.card (V ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) := by
  have hVeq : V = zpowers t ⊔ (V ⊓ m12Grp x₁ x₂ lam tau) := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rcases mem_m12Grp_or_mul h h43 h44 (hV hv) with hvM | htvM
      · exact Subgroup.mem_sup_right ⟨hv, hvM⟩
      · have hmV : t * v ∈ V := V.mul_mem ht hv
        have hv_eq : v = t * (t * v) := (t_mul_t_mul h v).symm
        rw [hv_eq]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) ⟨hmV, htvM⟩
    · refine sup_le ?_ inf_le_left
      exact Subgroup.zpowers_le.mpr ht
  refine ⟨hVeq, ?_⟩
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ V ⊓ m12Grp x₁ x₂ lam tau, a * b = b * a := by
    intro a ha b hb
    exact zpowers_t_commute_S h ha (hV hb.1)
  have hinf : zpowers t ⊓ (V ⊓ m12Grp x₁ x₂ lam tau) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxz, hxVM⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ zpowers t ⊓ m12Grp x₁ x₂ lam tau := ⟨hxz, hxVM.2⟩
    rw [(S_eq_prod_of h h43 h44).2] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hcard := card_sup_of_commute (P := zpowers t) (Q := V ⊓ m12Grp x₁ x₂ lam tau)
    hcomm hinf
  nth_rewrite 1 [hVeq]
  rw [hcard, Nat.card_zpowers, h.hyp.ord_t]

theorem normalIn_sup_zpowers (h : Ctx t L S x₁ x₂ lam rho tau) {V : Subgroup G}
    (hV : NormalIn V S) : NormalIn (V ⊔ zpowers t) S := by
  refine ⟨sup_le hV.1 (zpowers_t_le_S h), ?_⟩
  intro g hg x hx
  have hcomm : ∀ a ∈ V, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    exact (zpowers_t_commute_S h hb (hV.1 ha)).symm
  obtain ⟨v, hv, p, hp, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
  have hgp : g * p * g⁻¹ = p := by
    have hc : Commute p g := zpowers_t_commute_S h hp hg
    calc g * p * g⁻¹ = p * g * g⁻¹ := by rw [← hc.eq]
      _ = p := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hconj : g * (v * p) * g⁻¹ = (g * v * g⁻¹) * p := by
    calc g * (v * p) * g⁻¹ = (g * v * g⁻¹) * (g * p * g⁻¹) := by group
      _ = (g * v * g⁻¹) * p := by rw [hgp]
  rw [hconj]
  exact Subgroup.mul_mem_sup (hV.2 g hg v hv) hp

theorem isElemAbelian_sup_zpowers (h : Ctx t L S x₁ x₂ lam rho tau) {V : Subgroup G}
    (hVS : V ≤ S) (hV : CFSG.Open.IsElemAbelian 2 V) :
    CFSG.Open.IsElemAbelian 2 (V ⊔ zpowers t) := by
  have hcomm : ∀ a ∈ V, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    exact (zpowers_t_commute_S h hb (hVS ha)).symm
  refine ⟨?_, ?_⟩
  · exact isMulCommutative_sup_of_commute hcomm hV.1 inferInstance
  · intro x hx
    obtain ⟨v, hv, p, hp, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
    have hp2 : p ^ 2 = 1 := by
      rw [pow_two]
      exact zpowers_t_sq h.hyp hp
    have hv2 : v ^ 2 = 1 := hV.2 v hv
    have hvp : Commute v p := hcomm v hv p hp
    rw [hvp.mul_pow 2, hv2, hp2, mul_one]

theorem card_sup_zpowers_of_t_not_mem (h : Ctx t L S x₁ x₂ lam rho tau) {V : Subgroup G}
    (hVS : V ≤ S) (htV : t ∉ V) : Nat.card (V ⊔ zpowers t : Subgroup G) = 2 * Nat.card V := by
  have hcomm : ∀ a ∈ V, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    exact (zpowers_t_commute_S h hb (hVS ha)).symm
  have hinf : V ⊓ zpowers t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rcases zpowers_t_eq_one_or h.hyp hx.2 with hx1 | hxt
    · rw [hx1]
    · exact absurd (hxt ▸ hx.1) htV
  have hcard := card_sup_of_commute (P := V) (Q := zpowers t) hcomm hinf
  rw [hcard, Nat.card_zpowers, h.hyp.ord_t, Nat.mul_comm]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
