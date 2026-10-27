module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Class
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Iface

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.L4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local.P27.Psp4 CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G] {S P₁ P₂ : Subgroup G} {z t w : G} {a : ℕ}

theorem card_sup_zpowers_two [Finite G] {K : Subgroup G} {a : G} (hconj : ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hsq : a * a ∈ K) (ha : a ∉ K) : Nat.card ↥(K ⊔ zpowers a) = 2 * Nat.card ↥K := by
  have h2 : K.relIndex (K ⊔ zpowers a) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨a, mem_sup_right (mem_zpowers a), fun b hb => ?_⟩
    rcases (Psp4.mem_sup_zpowers_iff hconj hsq).1 hb with hbK | ⟨k, hk, rfl⟩
    · refine Or.inr ⟨hbK, fun hba => ha ?_⟩
      have := mul_mem (inv_mem hbK) hba
      simpa using this
    · refine Or.inl ⟨?_, fun hka => ha ?_⟩
      · have : k * a * a = k * (a * a) := by rw [mul_assoc]
        rw [this]; exact mul_mem hk hsq
      · have := mul_mem (inv_mem hk) hka
        simpa using this
  have h3 := Subgroup.relIndex_mul_card K (K ⊔ zpowers a)
  rw [h2, inf_eq_left.2 le_sup_left] at h3
  exact h3.symm

theorem mem_zpowers_sq_iff {y x : G} (hy : y * y = 1) : x ∈ zpowers y ↔ x = 1 ∨ x = y := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have h2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy
    have hk : y ^ k = y ^ (k % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [hk, h, zpow_zero]
    · right; rw [hk, h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem comm_AA {g : G} (hz : z * g = g * z) (ht : t * g = g * t) :
    ∀ x ∈ zpowers z ⊔ zpowers t, x * g = g * x := by
  have : zpowers z ⊔ zpowers t ≤ centralizer ({g} : Set G) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_singleton_iff]
    · exact hz
    · exact ht
  intro x hx
  exact mem_centralizer_singleton_iff.1 (this hx)

namespace DataL4

variable [Finite G] (h : DataL4 S P₁ P₂ z t w a)

include h

theorem mem_US_iff {g : G} : g ∈ US P₁ t ↔ ∃ q ∈ P₁, g = rr t q q := by
  have hd := h.toPsp4
  constructor
  · intro hg
    let K : Subgroup G :=
      { carrier := {g | ∃ q ∈ P₁, g = rr t q q}
        one_mem' := ⟨1, one_mem _, by simp [rr]⟩
        mul_mem' := by
          rintro _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
          exact ⟨q * q', mul_mem hq hq', hd.rr_mul hq hq'⟩
        inv_mem' := by
          rintro _ ⟨q, hq, rfl⟩
          exact ⟨q⁻¹, inv_mem hq, hd.rr_inv hq hq⟩ }
    have : US P₁ t ≤ K := (Subgroup.closure_le K).2 (by rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩)
    exact this hg
  · rintro ⟨q, hq, rfl⟩
    exact Subgroup.subset_closure ⟨q, hq, rfl⟩

theorem rr_mem_US {q : G} (hq : q ∈ P₁) : rr t q q ∈ US P₁ t := (h.mem_US_iff).2 ⟨q, hq, rfl⟩

theorem US_le_R : US P₁ t ≤ P₁ ⊔ P₂ := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := (h.mem_US_iff).1 hg
  exact h.toPsp4.rr_mem_R hq hq

theorem t_comm_US {g : G} (hg : g ∈ US P₁ t) : t * g = g * t := by
  obtain ⟨q, hq, rfl⟩ := (h.mem_US_iff).1 hg
  exact h.toPsp4.rr_mul_t hq hq

theorem w_conj_US {g : G} (hg : g ∈ US P₁ t) : w * g * w⁻¹ ∈ US P₁ t := by
  obtain ⟨q, hq, rfl⟩ := (h.mem_US_iff).1 hg
  rw [h.w_rr]
  exact h.rr_mem_US (h.w_norm q hq)

theorem z_not_mem_US : z ∉ US P₁ t := by
  intro hz
  obtain ⟨q, hq, hqz⟩ := (h.mem_US_iff).1 hz
  have hd := h.toPsp4
  have hz1 : z = rr t z 1 := by simp [rr]
  rw [hz1] at hqz
  rcases (hd.rr_eq_iff hq hq h.z_mem₁ (one_mem _)).1 hqz.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact h.z_ne_one (e1.trans e2.symm)
  · have hq1 : q = 1 := by
      have : z * q = z * 1 := by rw [mul_one]; exact e1.symm
      exact mul_left_cancel this
    rw [hq1, mul_one] at e2
    exact h.z_ne_one e2.symm

def usHom : ↥P₁ →* G where
  toFun q := rr t q.1 q.1
  map_one' := by simp [rr]
  map_mul' q₁ q₂ := (h.toPsp4.rr_mul q₁.2 q₂.2).symm

theorem usHom_range : (usHom h).range = US P₁ t := by
  ext g
  rw [MonoidHom.mem_range, h.mem_US_iff]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩

theorem usHom_ker : (usHom h).ker = (zpowers z).subgroupOf P₁ := by
  have hd := h.toPsp4
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_zpowers_sq_iff h.z_sq]
  have hq := q.2
  have e : (usHom h) q = 1 ↔ rr t q.1 q.1 = rr t 1 1 := by
    show rr t q.1 q.1 = 1 ↔ _
    rw [Data.rr_one]
  rw [e, hd.rr_eq_iff hq hq (one_mem _) (one_mem _)]
  constructor
  · rintro (⟨e1, -⟩ | ⟨e1, -⟩)
    · exact Or.inl e1.symm
    · refine Or.inr ?_
      calc (q : G) = z⁻¹ * (z * q) := by group
        _ = z := by rw [← e1, mul_one, h.z_inv]
  · rintro (e1 | e1)
    · exact Or.inl ⟨e1.symm, e1.symm⟩
    · refine Or.inr ⟨?_, ?_⟩ <;> rw [e1, h.z_sq]

theorem card_US : Nat.card ↥(US P₁ t) = 2 ^ (a - 1) := by
  have h1 : Nat.card ↥P₁ = Nat.card (↥P₁ ⧸ (usHom h).ker) * Nat.card ↥(usHom h).ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (↥P₁ ⧸ (usHom h).ker) = Nat.card ↥(usHom h).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (usHom h)).toEquiv
  have h3 : Nat.card ↥(usHom h).ker = 2 := by
    rw [usHom_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((zpowers_le).2 h.z_mem₁)).toEquiv,
      Nat.card_zpowers, h.z_ord]
  rw [h.card_P₁, h2, h3, usHom_range] at h1
  have : 2 ^ a = 2 ^ (a - 1) * 2 := by
    rw [← pow_succ]; congr 1; have := h.three_le; omega
  omega

theorem t_ne_one : t ≠ 1 := by
  intro ht
  exact h.t_not (ht ▸ one_mem _)

theorem orderOf_t : orderOf t = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.t_inv) h.t_ne_one

omit [Finite G] in
theorem z_comm_t : z * t = t * z := (h.z_cent t h.t_mem).symm

theorem z_ne_t : z ≠ t := fun e => h.t_not (e ▸ h.z_mem_R)

theorem zpowers_z_inf_t : zpowers z ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxz, hxt⟩ := Subgroup.mem_inf.1 hx
  rw [mem_zpowers_sq_iff h.z_sq] at hxz
  rw [mem_zpowers_sq_iff h.t_inv] at hxt
  rcases hxz with rfl | rfl
  · exact one_mem _
  · rcases hxt with h1 | h1
    · exact absurd h1 h.z_ne_one
    · exact absurd h1 h.z_ne_t

theorem card_AA : Nat.card ↥(zpowers z ⊔ zpowers t) = 4 := by
  have hcomm : ∀ g ∈ zpowers z, ∀ g' ∈ zpowers t, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg'
    exact (Commute.zpow_zpow (show Commute z t from h.z_comm_t) m n).eq
  rw [card_sup_of_commute hcomm h.zpowers_z_inf_t, Nat.card_zpowers, Nat.card_zpowers, h.z_ord, h.orderOf_t]

theorem card_BB : Nat.card ↥(US P₁ t ⊔ zpowers w) = 2 * 2 ^ (a - 1) := by
  rw [card_sup_zpowers_two (fun k hk => h.w_conj_US hk) (by rw [h.w_inv]; exact one_mem _)
    (fun hw => h.w_not (h.US_le_R hw)), h.card_US]

theorem AA_comm_BB : ∀ x ∈ zpowers z ⊔ zpowers t, ∀ y ∈ US P₁ t ⊔ zpowers w, x * y = y * x := by
  intro x hx y hy
  have hconj : ∀ k ∈ US P₁ t, w * k * w⁻¹ ∈ US P₁ t := fun k hk => h.w_conj_US hk
  have hsq : w * w ∈ US P₁ t := by rw [h.w_inv]; exact one_mem _
  have hcw : x * w = w * x :=
    comm_AA (h.z_cent w h.w_mem |>.symm) h.tw_comm x hx
  have hck : ∀ k ∈ US P₁ t, x * k = k * x := fun k hk =>
    comm_AA (h.z_comm (h.R_mem_S (h.US_le_R hk))) (h.t_comm_US hk) x hx
  rcases (Psp4.mem_sup_zpowers_iff hconj hsq).1 hy with hk | ⟨k, hk, rfl⟩
  · exact hck y hk
  · calc x * (k * w) = (x * k) * w := by rw [mul_assoc]
      _ = (k * x) * w := by rw [hck k hk]
      _ = k * (x * w) := by rw [mul_assoc]
      _ = k * (w * x) := by rw [hcw]
      _ = (k * w) * x := by rw [mul_assoc]

omit [Finite G] in
theorem mem_AA_iff {x : G} : x ∈ zpowers z ⊔ zpowers t ↔ x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  have hcomm : ∀ g ∈ zpowers z, ∀ g' ∈ zpowers t, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg'
    exact (Commute.zpow_zpow (show Commute z t from h.z_comm_t) m n).eq
  rw [mem_sup_iff_of_commute hcomm]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    rw [mem_zpowers_sq_iff h.z_sq] at hp
    rw [mem_zpowers_sq_iff h.t_inv] at hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact Or.inl (mul_one _)
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
    · exact ⟨x, mem_zpowers x, 1, one_mem _, (mul_one x).symm⟩
    · exact ⟨1, one_mem _, x, mem_zpowers x, (one_mul x).symm⟩
    · exact ⟨z, mem_zpowers z, t, mem_zpowers t, rfl⟩

theorem AA_inf_BB : (zpowers z ⊔ zpowers t) ⊓ (US P₁ t ⊔ zpowers w) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyA, hyB⟩ := Subgroup.mem_inf.1 hy
  have hconj : ∀ k ∈ US P₁ t, w * k * w⁻¹ ∈ US P₁ t := fun k hk => h.w_conj_US hk
  have hsq : w * w ∈ US P₁ t := by rw [h.w_inv]; exact one_mem _
  have hzR : z ∈ P₁ ⊔ P₂ := h.z_mem_R
  rw [h.mem_AA_iff] at hyA
  rcases (Psp4.mem_sup_zpowers_iff hconj hsq).1 hyB with hk | ⟨k, hk, rfl⟩ <;>
    have hkR : ∀ k' ∈ US P₁ t, k' ∈ P₁ ⊔ P₂ := fun k' hk' => h.US_le_R hk'
  · rcases hyA with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact absurd hk h.z_not_mem_US
    · exact absurd (hkR _ hk) h.t_not
    · exact absurd (by simpa using mul_mem (inv_mem hzR) (hkR _ hk)) h.t_not
  · have hkR' := hkR k hk
    rcases hyA with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · exfalso
      apply h.w_not
      have : w = k⁻¹ * z := by
        have e : k * w = z := h1
        calc w = k⁻¹ * (k * w) := by group
          _ = k⁻¹ * z := by rw [e]
      rw [this]; exact mul_mem (inv_mem hkR') hzR
    · exfalso
      apply h.tw_not
      have : t * w = k := by
        have e : k * w = t := h1
        calc t * w = (k * w) * w := by rw [e]
          _ = k := by rw [mul_assoc, h.w_inv, mul_one]
      rw [this]; exact hkR'
    · exfalso
      apply h.tw_not
      have e : k * w = z * t := h1
      have : t * w = z⁻¹ * k := by
        calc t * w = z⁻¹ * (z * t) * w := by group
          _ = z⁻¹ * (k * w) * w := by rw [← e]
          _ = z⁻¹ * k := by rw [mul_assoc, mul_assoc, h.w_inv, mul_one]
      rw [this]; exact mul_mem (inv_mem hzR) hkR'

theorem CSt_eq : S ⊓ centralizer ({t} : Set G) = (zpowers z ⊔ zpowers t) ⊔ (US P₁ t ⊔ zpowers w) := by
  have hd := h.toPsp4
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxc
    obtain ⟨ρ, hρ, τ, hτ, rfl⟩ := h.S_decomp hxS
    have hτt : t * τ = τ * t := (h.V_comm (c := t) rfl h.wt_comm hτ).symm
    have hρt : ρ * t = t * ρ := by
      have e : ρ * t * τ = t * ρ * τ := by
        calc ρ * t * τ = ρ * (t * τ) := by rw [mul_assoc]
          _ = ρ * (τ * t) := by rw [hτt]
          _ = ρ * τ * t := by rw [mul_assoc]
          _ = t * (ρ * τ) := hxt
          _ = t * ρ * τ := by rw [mul_assoc]
      exact mul_right_cancel e
    obtain ⟨p, hp, q, hq, rfl⟩ := hd.mem_R_iff.1 hρ
    have hσ : rr t q p = rr t p q := by
      rw [← hd.σ_rr hp hq]
      calc t * rr t p q * t⁻¹ = (t * rr t p q) * t⁻¹ := rfl
        _ = (rr t p q * t) * t⁻¹ := by rw [← hρt]
        _ = rr t p q := by group
    have hAB : ∀ g : G, g ∈ zpowers z → ∀ g' ∈ US P₁ t, ∀ τ' ∈ ({1, t, w, t * w} : Set G),
        g * g' * τ' ∈ (zpowers z ⊔ zpowers t) ⊔ (US P₁ t ⊔ zpowers w) := by
      intro g hg g' hg' τ' hτ'
      have hgA : g ∈ (zpowers z ⊔ zpowers t) ⊔ (US P₁ t ⊔ zpowers w) := mem_sup_left (mem_sup_left hg)
      have hg'B : g' ∈ (zpowers z ⊔ zpowers t) ⊔ (US P₁ t ⊔ zpowers w) :=
        mem_sup_right (mem_sup_left hg')
      have ht' : t ∈ (zpowers z ⊔ zpowers t) ⊔ (US P₁ t ⊔ zpowers w) :=
        mem_sup_left (mem_sup_right (mem_zpowers t))
      have hw' : w ∈ (zpowers z ⊔ zpowers t) ⊔ (US P₁ t ⊔ zpowers w) :=
        mem_sup_right (mem_sup_right (mem_zpowers w))
      refine mul_mem (mul_mem hgA hg'B) ?_
      rcases hτ' with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact ht'
      · exact hw'
      · exact mul_mem ht' hw'
    have hτ' : τ ∈ ({1, t, w, t * w} : Set G) := by
      rcases hτ with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    rcases (hd.rr_eq_iff hq hp hp hq).1 hσ with ⟨e1, -⟩ | ⟨e1, e2⟩
    ·
      have : rr t p q = 1 * rr t q q := by rw [e1, one_mul]
      rw [this]
      exact hAB 1 (one_mem _) _ (h.rr_mem_US hq) τ hτ'
    ·
      have : rr t p q = z * rr t q q := by rw [e1, z_mul_rr_left]
      rw [this]
      exact hAB z (mem_zpowers z) _ (h.rr_mem_US hq) τ hτ'
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [zpowers_le]
      exact ⟨h.z_mem, mem_centralizer_singleton_iff.2 h.z_comm_t⟩
    · rw [zpowers_le]
      exact ⟨h.t_mem, mem_centralizer_singleton_iff.2 rfl⟩
    · intro g hg
      exact ⟨h.R_mem_S (h.US_le_R hg), mem_centralizer_singleton_iff.2 (h.t_comm_US hg).symm⟩
    · rw [zpowers_le]
      exact ⟨h.w_mem, mem_centralizer_singleton_iff.2 h.tw_comm.symm⟩

theorem card_Ct : Nat.card ↥(S ⊓ centralizer ({t} : Set G)) = 2 ^ (a + 2) := by
  rw [h.CSt_eq, card_sup_of_commute h.AA_comm_BB h.AA_inf_BB, h.card_AA, h.card_BB]
  have : 2 ^ (a + 2) = 2 ^ (a - 1) * 8 := by
    rw [show a + 2 = (a - 1) + 3 by have := h.three_le; omega, pow_add]; norm_num
  omega

theorem BB_conj_US {y d : G} (hy : y ∈ US P₁ t ⊔ zpowers w) (hd : d ∈ US P₁ t) :
    y * d * y⁻¹ ∈ US P₁ t := by
  have hconj : ∀ k ∈ US P₁ t, w * k * w⁻¹ ∈ US P₁ t := fun k hk => h.w_conj_US hk
  have hsq : w * w ∈ US P₁ t := by rw [h.w_inv]; exact one_mem _
  rcases (Psp4.mem_sup_zpowers_iff hconj hsq).1 hy with hk | ⟨k, hk, rfl⟩
  · exact mul_mem (mul_mem hk hd) (inv_mem hk)
  · have e : k * w * d * (k * w)⁻¹ = k * (w * d * w⁻¹) * k⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hk (h.w_conj_US hd)) (inv_mem hk)

theorem US_normal {c d : G} (hc : c ∈ S ⊓ centralizer ({t} : Set G)) (hd : d ∈ US P₁ t) :
    c * d * c⁻¹ ∈ US P₁ t := by
  rw [h.CSt_eq] at hc
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_commute h.AA_comm_BB).1 hc
  have hg : y * d * y⁻¹ ∈ US P₁ t := h.BB_conj_US hy hd
  have hgB : y * d * y⁻¹ ∈ US P₁ t ⊔ zpowers w := mem_sup_left hg
  have hxg : x * (y * d * y⁻¹) = (y * d * y⁻¹) * x := h.AA_comm_BB x hx _ hgB
  have e : x * y * d * (x * y)⁻¹ = x * (y * d * y⁻¹) * x⁻¹ := by group
  rw [e, hxg]
  simpa using hg

theorem US_inter {y : G} (hy : y ∈ US P₁ t) (hyA : y ∈ zpowers z ⊔ zpowers t) : y = 1 := by
  have : y ∈ (zpowers z ⊔ zpowers t) ⊓ (US P₁ t ⊔ zpowers w) := ⟨hyA, mem_sup_left hy⟩
  rw [h.AA_inf_BB, mem_bot] at this
  exact this

theorem US_cls {d : G} (hd : d ∈ US P₁ t) (hd2 : d * d = 1) (hd1 : d ≠ 1) :
    d ∈ XcL (P₁ ⊔ P₂) z t w ∧ z * d ∈ XcL (P₁ ⊔ P₂) z t w ∧ t * d ∈ XcL (P₁ ⊔ P₂) z t w ∧
      t * z * d ∈ ZcL (P₁ ⊔ P₂) z t w := by
  have hdd := h.toPsp4
  have hdU := hd
  obtain ⟨q, hq, rfl⟩ := (h.mem_US_iff).1 hd
  have hqR : rr t q q ∈ P₁ ⊔ P₂ := hdd.rr_mem_R hq hq
  have hqq : q * q = z := by
    have e : rr t (q * q) (q * q) = rr t 1 1 := by rw [← hdd.rr_mul hq hq, hd2, Data.rr_one]
    rcases (hdd.rr_eq_iff (mul_mem hq hq) (mul_mem hq hq) (one_mem _) (one_mem _)).1 e with
      ⟨e1, -⟩ | ⟨e1, -⟩
    · exfalso
      apply hd1
      by_cases hq1 : q = 1
      · rw [hq1]; simp [rr]
      · have : q = z := h.unique_invol hq e1.symm hq1
        rw [this]
        calc rr t z z = z * (t * z * t⁻¹) := rfl
          _ = z * z := by rw [hdd.σ_z]
          _ = 1 := h.z_sq
    · calc q * q = z⁻¹ * (z * (q * q)) := by group
        _ = z := by rw [← e1, mul_one, h.z_inv]
  have hzd : z * rr t q q ∈ P₁ ⊔ P₂ := mul_mem h.z_mem_R hqR
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h.mem_XcL_R hqR).2 ⟨hd2, hd1, fun e => h.z_not_mem_US (e ▸ hdU)⟩
  · refine (h.mem_XcL_R hzd).2 ⟨?_, ?_, ?_⟩
    · have : z * rr t q q * (z * rr t q q) = (z * z) * (rr t q q * rr t q q) := by
        calc z * rr t q q * (z * rr t q q) = z * (rr t q q * z) * rr t q q := by simp only [mul_assoc]
          _ = z * (z * rr t q q) * rr t q q := by
            rw [← h.z_comm (h.R_mem_S hqR)]
          _ = (z * z) * (rr t q q * rr t q q) := by simp only [mul_assoc]
      rw [this, h.z_sq, hd2, mul_one]
    · intro e
      apply h.z_not_mem_US
      have : rr t q q = z⁻¹ := by
        calc rr t q q = z⁻¹ * (z * rr t q q) := by group
          _ = z⁻¹ := by rw [e, mul_one]
      rw [h.z_inv] at this
      exact this ▸ hdU
    · intro e
      apply hd1
      calc rr t q q = z⁻¹ * (z * rr t q q) := by group
        _ = 1 := by rw [e, inv_mul_cancel]
  · have e : t * rr t q q = rr t q q * t := hdd.rr_mul_t hq hq
    rw [e]
    exact (h.rrt_mem_XcL_iff hq hq).2 hqq
  · have e : t * z * rr t q q = rr t (z * q) q * t := by
      calc t * z * rr t q q = z * t * rr t q q := by rw [← h.z_comm_t]
        _ = z * (t * rr t q q) := by rw [mul_assoc]
        _ = z * (rr t q q * t) := by rw [hdd.rr_mul_t hq hq]
        _ = (z * rr t q q) * t := by rw [mul_assoc]
        _ = rr t (z * q) q * t := by rw [z_mul_rr_left]
    rw [e]
    refine (h.rrt_mem_ZcL_iff (mul_mem h.z_mem₁ hq) hq).2 ?_
    calc z * q * q = z * (q * q) := by rw [mul_assoc]
      _ = z * z := by rw [hqq]
      _ = 1 := h.z_sq

theorem US_eq_sup {a₀ b₀ : G} {M : ℕ} (ha : a₀ ∈ P₁) (hb : b₀ ∈ P₁)
    (hspan : ∀ x ∈ P₁, ∃ k : ℕ, x = a₀ ^ k ∨ x = a₀ ^ k * b₀)
    (hrel : Rel a₀ b₀ (t * a₀ * t⁻¹) (t * b₀ * t⁻¹) t M) :
    US P₁ t = zpowers (a₀ * (t * a₀ * t⁻¹)) ⊔ zpowers (b₀ * (t * b₀ * t⁻¹)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := (h.mem_US_iff).1 hg
    obtain ⟨k, hk | hk⟩ := hspan q hq
    · subst hk
      have e : rr t (a₀ ^ k) (a₀ ^ k) = (a₀ * (t * a₀ * t⁻¹)) ^ k := by
        unfold rr
        rw [Commute.mul_pow hrel.commute_a_a', conj_pow]
      rw [e]
      exact mem_sup_left (pow_mem (mem_zpowers _) k)
    · subst hk
      have e : rr t (a₀ ^ k * b₀) (a₀ ^ k * b₀) =
          (a₀ * (t * a₀ * t⁻¹)) ^ k * (b₀ * (t * b₀ * t⁻¹)) := by
        unfold rr
        have e1 : t * (a₀ ^ k * b₀) * t⁻¹ = (t * a₀ * t⁻¹) ^ k * (t * b₀ * t⁻¹) := by
          rw [conj_pow]; group
        have e2 : b₀ * (t * a₀ * t⁻¹) ^ k = (t * a₀ * t⁻¹) ^ k * b₀ :=
          ((show Commute b₀ (t * a₀ * t⁻¹) from hrel.c_ba).pow_right k).eq
        rw [e1, Commute.mul_pow hrel.commute_a_a']
        calc a₀ ^ k * b₀ * ((t * a₀ * t⁻¹) ^ k * (t * b₀ * t⁻¹))
            = a₀ ^ k * (b₀ * (t * a₀ * t⁻¹) ^ k) * (t * b₀ * t⁻¹) := by simp only [mul_assoc]
          _ = a₀ ^ k * ((t * a₀ * t⁻¹) ^ k * b₀) * (t * b₀ * t⁻¹) := by rw [e2]
          _ = a₀ ^ k * (t * a₀ * t⁻¹) ^ k * (b₀ * (t * b₀ * t⁻¹)) := by simp only [mul_assoc]
      rw [e]
      exact mul_mem (mem_sup_left (pow_mem (mem_zpowers _) k)) (mem_sup_right (mem_zpowers _))
  · refine sup_le ?_ ?_ <;> rw [zpowers_le]
    · exact h.rr_mem_US ha
    · exact h.rr_mem_US hb

theorem US_dih : IVK.IsDihedralTwoGroup ↥(US P₁ t) (a - 1) := by
  obtain ⟨a₀, b₀, M, ha, hb, hM, hN, hqg, hspan⟩ := h.toPsp4.exists_gens
  have hrel := (h.toPsp4.rel_of_gens ha hb hM hqg hspan).2
  rw [h.US_eq_sup ha hb hspan hrel]
  have hr : orderOf (a₀ * (t * a₀ * t⁻¹)) = 2 ^ (a - 2) := by rw [hrel.orderOf_dl2, hN]
  have hs : (b₀ * (t * b₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹)) = 1 := hrel.b0_sq
  have hsr : (b₀ * (t * b₀ * t⁻¹)) * (a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹))⁻¹ =
      (a₀ * (t * a₀ * t⁻¹))⁻¹ := by
    have e1 : (b₀ * (t * b₀ * t⁻¹)) * a₀ = a₀⁻¹ * (b₀ * (t * b₀ * t⁻¹)) := by
      simpa using hrel.b0_zpow_a 1
    have e2 : (b₀ * (t * b₀ * t⁻¹)) * (t * a₀ * t⁻¹) = (t * a₀ * t⁻¹)⁻¹ * (b₀ * (t * b₀ * t⁻¹)) := by
      simpa using hrel.b0_zpow_a' 1
    rw [hrel.b0_inv]
    calc (b₀ * (t * b₀ * t⁻¹)) * (a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹))
        = ((b₀ * (t * b₀ * t⁻¹)) * a₀) * (t * a₀ * t⁻¹) * (b₀ * (t * b₀ * t⁻¹)) := by
          simp only [mul_assoc]
      _ = a₀⁻¹ * ((b₀ * (t * b₀ * t⁻¹)) * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹)) := by
          rw [e1]; simp only [mul_assoc]
      _ = a₀⁻¹ * ((t * a₀ * t⁻¹)⁻¹ * (b₀ * (t * b₀ * t⁻¹))) * (b₀ * (t * b₀ * t⁻¹)) := by rw [e2]
      _ = a₀⁻¹ * (t * a₀ * t⁻¹)⁻¹ * ((b₀ * (t * b₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹))) := by
          simp only [mul_assoc]
      _ = (t * a₀ * t⁻¹)⁻¹ * a₀⁻¹ := by
          rw [hs, mul_one]
          exact hrel.commute_a_a'.inv_inv.eq
      _ = (a₀ * (t * a₀ * t⁻¹))⁻¹ := (mul_inv_rev _ _).symm
  have hns : (b₀ * (t * b₀ * t⁻¹)) ∉ zpowers (a₀ * (t * a₀ * t⁻¹)) := by
    intro hmem
    apply hrel.b0_not_comm_a
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    rw [← hk]
    exact ((Commute.mul_right (Commute.refl a₀) hrel.commute_a_a')).zpow_right k
  have := Psp4.isDihedralTwoGroup_sup (a - 2) (by have := h.three_le; omega) _ _ hr hs hsr hns
  have e : a - 2 + 1 = a - 1 := by have := h.three_le; omega
  rw [e] at this
  exact this

end DataL4

theorem l4_actual [Finite G] (h : DataL4 S P₁ P₂ z t w a) :
    L4Actual S z t a (ZcL (P₁ ⊔ P₂) z t w) (XcL (P₁ ⊔ P₂) z t w) (US P₁ t) where
  z_Z := Or.inl (Or.inl (Or.inl rfl))
  t_Z := Or.inl (Or.inl (Or.inr ⟨1, one_mem _, by simp⟩))
  tz_X := Or.inl (Or.inr ⟨1, one_mem _, by simp⟩)
  partition := h.partition
  card_Ct := h.card_Ct
  US_le := fun g hg =>
    ⟨h.R_mem_S (h.US_le_R hg), mem_centralizer_singleton_iff.2 (h.t_comm_US hg).symm⟩
  US_normal := fun c hc d hd => h.US_normal hc hd
  US_card := h.card_US
  US_inter := fun y hy hyA => h.US_inter hy hyA
  US_cls := fun d hd hd2 hd1 => h.US_cls hd hd2 hd1
  US_dih := h.US_dih

end CFSG.GH74.GLS.Stage2.Local.P27.L4




