module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Std
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Part
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dih1

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

section ActRel

theorem Rel.act_b0_dl2 {a b a' b' t : G} {M : ℕ} (h : Rel a b a' b' t M) :
    (b * b') * (a * a') * (b * b') = (a * a')⁻¹ := by
  have e1 : (b * b') * a = a⁻¹ * (b * b') := by simpa using h.b0_zpow_a 1
  have e2 : (b * b') * a' = a'⁻¹ * (b * b') := by simpa using h.b0_zpow_a' 1
  calc (b * b') * (a * a') * (b * b') = ((b * b') * a) * a' * (b * b') := by simp only [mul_assoc]
    _ = a⁻¹ * ((b * b') * a') * (b * b') := by rw [e1]; simp only [mul_assoc]
    _ = a⁻¹ * (a'⁻¹ * (b * b')) * (b * b') := by rw [e2]
    _ = a⁻¹ * a'⁻¹ * ((b * b') * (b * b')) := by simp only [mul_assoc]
    _ = (a * a')⁻¹ := by
      rw [h.b0_sq, mul_one, mul_inv_rev]
      exact h.commute_a_a'.inv_inv.eq

end ActRel

section ActNoFin

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

namespace Data

theorem act_t_ne_one (h : Data S P₁ P₂ z t a) : t ≠ 1 := by
  intro ht
  apply h.t_not
  rw [ht]
  exact one_mem _

theorem act_z_ne_t (h : Data S P₁ P₂ z t a) : z ≠ t := by
  intro e
  apply h.t_not
  rw [← e]
  exact mem_sup_left h.z_mem₁

theorem act_zpowers_inf (h : Data S P₁ P₂ z t a) : zpowers z ⊓ zpowers t = ⊥ :=
  zpowers_inf_zpowers_of_sq h.z_sq h.t_inv h.act_z_ne_t

theorem act_mem_US_iff (h : Data S P₁ P₂ z t a) {g : G} :
    g ∈ US P₁ t ↔ ∃ q ∈ P₁, g = rr t q q := by
  constructor
  · intro hg
    let K : Subgroup G :=
      { carrier := {g | ∃ q ∈ P₁, g = rr t q q}
        one_mem' := ⟨1, one_mem _, (rr_one t).symm⟩
        mul_mem' := by
          rintro _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
          exact ⟨q * q', mul_mem hq hq', h.rr_mul hq hq'⟩
        inv_mem' := by
          rintro _ ⟨q, hq, rfl⟩
          exact ⟨q⁻¹, inv_mem hq, h.rr_inv hq hq⟩ }
    have : US P₁ t ≤ K := (Subgroup.closure_le K).2 (by rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩)
    exact this hg
  · rintro ⟨q, hq, rfl⟩
    exact Subgroup.subset_closure ⟨q, hq, rfl⟩

theorem act_rr_mem_US (h : Data S P₁ P₂ z t a) {q : G} (hq : q ∈ P₁) : rr t q q ∈ US P₁ t :=
  h.act_mem_US_iff.2 ⟨q, hq, rfl⟩

theorem act_t_comm_US (h : Data S P₁ P₂ z t a) {g : G} (hg : g ∈ US P₁ t) : t * g = g * t := by
  obtain ⟨q, hq, rfl⟩ := h.act_mem_US_iff.1 hg
  exact h.rr_mul_t hq hq

theorem act_z_not_mem_US (h : Data S P₁ P₂ z t a) : z ∉ US P₁ t := by
  intro hz
  obtain ⟨q, hq, hqz⟩ := h.act_mem_US_iff.1 hz
  have hqz' : rr t q q = rr t z 1 := by rw [Data.rr_p_one]; exact hqz.symm
  rcases (h.rr_eq_iff hq hq h.z_mem₁ (one_mem _)).1 hqz' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact h.z_ne_one (e1.trans e2.symm)
  · exact h.z_ne_one (e1.trans e2.symm)

theorem act_involution_P₁ (h : Data S P₁ P₂ z t a) {q : G} (hq : q ∈ P₁) (hq2 : q * q = 1) :
    q = 1 ∨ q = z := by
  by_cases hq1 : q = 1
  · exact Or.inl hq1
  · right
    obtain ⟨a₀, b₀, M, hc⟩ := h.exists_canon
    exact (hc.qg.eq_aN_of_involution (P := P₁) (by have := hc.one_le; omega) hc.span hq hq2
      hq1).trans hc.hz.symm

theorem act_sq_eq_z (h : Data S P₁ P₂ z t a) {q : G} (hq : q ∈ P₁)
    (hd2 : rr t q q * rr t q q = 1) (hd1 : rr t q q ≠ 1) : q * q = z := by
  have hqq : q * q ∈ P₁ := mul_mem hq hq
  have e : rr t (q * q) (q * q) = rr t 1 1 := by rw [← h.rr_mul hq hq, hd2, rr_one]
  rcases (h.rr_eq_iff hqq hqq (one_mem _) (one_mem _)).1 e with ⟨e1, -⟩ | ⟨e1, -⟩
  · exfalso
    apply hd1
    rcases h.act_involution_P₁ hq e1.symm with hq1 | hqz
    · rw [hq1, rr_one]
    · rw [hqz]
      unfold rr
      rw [h.σ_z, h.z_sq]
  · calc q * q = z⁻¹ * (z * (q * q)) := by group
      _ = z := by rw [← e1, mul_one, h.z_inv]

end Data

namespace Canon

variable {a₀ b₀ : G} {M : ℕ}

theorem act_US_eq (hc : Canon S P₁ P₂ z t a a₀ b₀ M) :
    US P₁ t = zpowers (a₀ * (t * a₀ * t⁻¹)) ⊔ zpowers (b₀ * (t * b₀ * t⁻¹)) := by
  have hd := hc.data
  have hrel := hc.rel
  apply le_antisymm
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := hd.act_mem_US_iff.1 hg
    obtain ⟨k, rfl | rfl⟩ := hc.span q hq
    · have e : rr t (a₀ ^ k) (a₀ ^ k) = (a₀ * (t * a₀ * t⁻¹)) ^ k := by
        unfold rr
        rw [Commute.mul_pow hrel.commute_a_a', conj_pow]
      rw [e]
      exact mem_sup_left (pow_mem (mem_zpowers _) k)
    · have hba : b₀ * (t * a₀ * t⁻¹) ^ k = (t * a₀ * t⁻¹) ^ k * b₀ :=
        ((show Commute b₀ (t * a₀ * t⁻¹) from hrel.c_ba).pow_right k).eq
      have e1 : t * (a₀ ^ k * b₀) * t⁻¹ = (t * a₀ * t⁻¹) ^ k * (t * b₀ * t⁻¹) := by
        rw [conj_pow]
        exact Data.σ_mul _ _
      have e : rr t (a₀ ^ k * b₀) (a₀ ^ k * b₀) =
          (a₀ * (t * a₀ * t⁻¹)) ^ k * (b₀ * (t * b₀ * t⁻¹)) := by
        unfold rr
        rw [Commute.mul_pow hrel.commute_a_a', e1]
        calc a₀ ^ k * b₀ * ((t * a₀ * t⁻¹) ^ k * (t * b₀ * t⁻¹))
            = a₀ ^ k * (b₀ * (t * a₀ * t⁻¹) ^ k) * (t * b₀ * t⁻¹) := by simp only [mul_assoc]
          _ = a₀ ^ k * ((t * a₀ * t⁻¹) ^ k * b₀) * (t * b₀ * t⁻¹) := by rw [hba]
          _ = a₀ ^ k * (t * a₀ * t⁻¹) ^ k * (b₀ * (t * b₀ * t⁻¹)) := by simp only [mul_assoc]
      rw [e]
      exact mul_mem (mem_sup_left (pow_mem (mem_zpowers _) k)) (mem_sup_right (mem_zpowers _))
  · refine sup_le ?_ ?_ <;> rw [zpowers_le]
    · exact hd.act_rr_mem_US hc.ha
    · exact hd.act_rr_mem_US hc.hb

theorem act_s_conj (hc : Canon S P₁ P₂ z t a a₀ b₀ M) :
    (b₀ * (t * b₀ * t⁻¹)) * (a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹))⁻¹ =
      (a₀ * (t * a₀ * t⁻¹))⁻¹ := by
  rw [hc.rel.b0_inv]
  exact hc.rel.act_b0_dl2

theorem act_s_not_mem (hc : Canon S P₁ P₂ z t a a₀ b₀ M) :
    b₀ * (t * b₀ * t⁻¹) ∉ zpowers (a₀ * (t * a₀ * t⁻¹)) := by
  intro hs
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hs
  apply hc.rel.b0_not_comm_a
  rw [← hk]
  exact (Commute.mul_right (Commute.refl a₀) hc.rel.commute_a_a').zpow_right k

end Canon

namespace Data

theorem act_US_struct (h : Data S P₁ P₂ z t a) :
    ∃ δ s : G, orderOf δ = 2 ^ (a - 2) ∧ s * s = 1 ∧ s * δ * s⁻¹ = δ⁻¹ ∧ s ∉ zpowers δ ∧
      US P₁ t = zpowers δ ⊔ zpowers s := by
  obtain ⟨a₀, b₀, M, hc⟩ := h.exists_canon
  exact ⟨a₀ * (t * a₀ * t⁻¹), b₀ * (t * b₀ * t⁻¹), hc.rel.orderOf_dl2.trans hc.hN, hc.rel.b0_sq,
    hc.act_s_conj, hc.act_s_not_mem, hc.act_US_eq⟩

theorem US_dih (h : Data S P₁ P₂ z t a) : IVK.IsDihedralTwoGroup ↥(US P₁ t) (a - 1) := by
  obtain ⟨δ, s, hδ, hs, hsδ, hns, hUS⟩ := h.act_US_struct
  have h3 : 3 ≤ a := h.P₁_quat.1
  rw [hUS]
  have := isDihedralTwoGroup_sup (a - 2) (by omega) δ s hδ hs hsδ hns
  rwa [show a - 2 + 1 = a - 1 by omega] at this

theorem US_card (h : Data S P₁ P₂ z t a) : Nat.card ↥(US P₁ t) = 2 ^ (a - 1) := by
  obtain ⟨δ, s, hδ, hs, hsδ, hns, hUS⟩ := h.act_US_struct
  have h3 : 3 ≤ a := h.P₁_quat.1
  have : NeZero (2 ^ (a - 2)) := ⟨by positivity⟩
  rw [hUS, card_dihedral_sup (2 ^ (a - 2)) δ s hδ hs hsδ hns,
    show a - 1 = (a - 2) + 1 by omega, pow_succ]
  ring

end Data

end ActNoFin

section ActFin

variable [Finite G] {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

namespace Data

theorem act_US_le_R (h : Data S P₁ P₂ z t a) : US P₁ t ≤ P₁ ⊔ P₂ := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := h.act_mem_US_iff.1 hg
  exact h.rr_mem_R hq hq

theorem US_le (h : Data S P₁ P₂ z t a) : US P₁ t ≤ S ⊓ centralizer ({t} : Set G) := by
  intro g hg
  rw [mem_inf, mem_centralizer_singleton_iff]
  exact ⟨h.R_le_S (h.act_US_le_R hg), (h.act_t_comm_US hg).symm⟩

theorem act_AA_comm_US (h : Data S P₁ P₂ z t a) :
    ∀ x ∈ zpowers z ⊔ zpowers t, ∀ y ∈ US P₁ t, x * y = y * x := by
  intro x hx g hg
  have hz : z * g = g * z := h.z_cent' (h.R_le_S (h.act_US_le_R hg))
  have ht : t * g = g * t := h.act_t_comm_US hg
  have : zpowers z ⊔ zpowers t ≤ centralizer ({g} : Set G) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_singleton_iff]
    · exact hz
    · exact ht
  exact mem_centralizer_singleton_iff.1 (this hx)

theorem act_AA_inf_US (h : Data S P₁ P₂ z t a) : (zpowers z ⊔ zpowers t) ⊓ US P₁ t = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  rw [mem_bot]
  rcases (mem_sup_of_sq_comm h.z_sq h.t_inv h.part_z_comm_t).1 hg1 with e | e | e | e
  · exact e
  · exfalso
    rw [e] at hg2
    exact h.act_z_not_mem_US hg2
  · exfalso
    apply h.t_not
    rw [← e]
    exact h.act_US_le_R hg2
  · exfalso
    apply h.t_not
    have hzR : z ∈ P₁ ⊔ P₂ := mem_sup_left h.z_mem₁
    have et : t = z⁻¹ * g := by rw [e, inv_mul_cancel_left]
    rw [et]
    exact mul_mem (inv_mem hzR) (h.act_US_le_R hg2)

theorem act_cent_t_eq (h : Data S P₁ P₂ z t a) :
    S ⊓ centralizer ({t} : Set G) = (zpowers z ⊔ zpowers t) ⊔ US P₁ t := by
  have hmem : ∀ p ∈ P₁, ∀ q ∈ P₁, rr t p q = rr t q p →
      rr t p q ∈ (zpowers z ⊔ zpowers t) ⊔ US P₁ t := by
    intro p hp q hq e
    rcases (h.rr_eq_iff hp hq hq hp).1 e with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1]
      exact mem_sup_right (h.act_rr_mem_US hp)
    · rw [e1, ← h.z_mul_rr_right hp]
      exact mul_mem (mem_sup_left (mem_sup_left (mem_zpowers z)))
        (mem_sup_right (h.act_rr_mem_US hp))
  apply le_antisymm
  · intro g hg
    obtain ⟨hgS, hgc⟩ := mem_inf.1 hg
    rw [mem_centralizer_singleton_iff] at hgc
    obtain ⟨p, hp, q, hq, hg | hg⟩ := h.mem_S_iff.1 hgS
    · rw [hg] at hgc ⊢
      exact hmem p hp q hq (mul_right_cancel (hgc.trans (h.rr_mul_t hp hq)))
    · rw [hg] at hgc ⊢
      have e1 : rr t p q * t * t = rr t p q := by rw [mul_assoc, h.t_inv, mul_one]
      have e2 : t * (rr t p q * t) = rr t q p := by
        rw [← mul_assoc, h.rr_mul_t hp hq, mul_assoc, h.t_inv, mul_one]
      exact mul_mem (hmem p hp q hq (e1.symm.trans (hgc.trans e2)))
        (mem_sup_left (mem_sup_right (mem_zpowers t)))
  · have hz : z ∈ S ⊓ centralizer ({t} : Set G) :=
      mem_inf.2 ⟨h.z_mem, mem_centralizer_singleton_iff.2 h.part_z_comm_t⟩
    have ht : t ∈ S ⊓ centralizer ({t} : Set G) :=
      mem_inf.2 ⟨h.t_mem, mem_centralizer_singleton_iff.2 rfl⟩
    exact sup_le (sup_le (zpowers_le.2 hz) (zpowers_le.2 ht)) h.US_le

theorem US_normal (h : Data S P₁ P₂ z t a) :
    ∀ c ∈ S ⊓ centralizer ({t} : Set G), ∀ d ∈ US P₁ t, c * d * c⁻¹ ∈ US P₁ t := by
  intro c hc d hd
  rw [h.act_cent_t_eq, mem_sup_iff_of_commute h.act_AA_comm_US] at hc
  obtain ⟨f, hf, u, hu, rfl⟩ := hc
  have hy : u * d * u⁻¹ ∈ US P₁ t := mul_mem (mul_mem hu hd) (inv_mem hu)
  have e : f * u * d * (f * u)⁻¹ = f * (u * d * u⁻¹) * f⁻¹ := by group
  have hfy : f * (u * d * u⁻¹) = (u * d * u⁻¹) * f := h.act_AA_comm_US f hf _ hy
  rw [e, hfy, mul_inv_cancel_right]
  exact hy

theorem US_inter (h : Data S P₁ P₂ z t a) :
    ∀ y ∈ US P₁ t, y ∈ zpowers z ⊔ zpowers t → y = 1 := by
  intro y hy hy'
  have : y ∈ (zpowers z ⊔ zpowers t) ⊓ US P₁ t := ⟨hy', hy⟩
  rw [h.act_AA_inf_US] at this
  exact mem_bot.1 this

theorem actual_card (h : Data S P₁ P₂ z t a) :
    Nat.card ↥(S ⊓ centralizer ({t} : Set G)) = 2 ^ (a + 1) := by
  have hcomm : ∀ g ∈ zpowers z, ∀ g' ∈ zpowers t, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hg'
    exact ((show Commute z t from h.part_z_comm_t).zpow_zpow i j).eq
  have hA : Nat.card ↥(zpowers z ⊔ zpowers t) = 4 := by
    rw [card_sup_of_commute hcomm h.act_zpowers_inf, card_zpowers_of_sq h.z_sq h.z_ne_one,
      card_zpowers_of_sq h.t_inv h.act_t_ne_one]
  have h3 : 3 ≤ a := h.P₁_quat.1
  rw [h.act_cent_t_eq, card_sup_of_commute h.act_AA_comm_US h.act_AA_inf_US, hA, h.US_card,
    show a + 1 = (a - 1) + 2 by omega, pow_add]
  ring

theorem US_cls (h : Data S P₁ P₂ z t a) :
    ∀ d ∈ US P₁ t, d * d = 1 → d ≠ 1 →
      d ∈ Xc (P₁ ⊔ P₂) z t ∧ z * d ∈ Xc (P₁ ⊔ P₂) z t ∧ t * d ∈ Xc (P₁ ⊔ P₂) z t ∧
        t * z * d ∈ Zc (P₁ ⊔ P₂) z t := by
  intro d hd hd2 hd1
  obtain ⟨q, hq, rfl⟩ := h.act_mem_US_iff.1 hd
  have hdR : rr t q q ∈ P₁ ⊔ P₂ := h.rr_mem_R hq hq
  have hdz : rr t q q ≠ z := fun e => h.act_z_not_mem_US (by rw [← e]; exact hd)
  have hzR : z ∈ P₁ ⊔ P₂ := mem_sup_left h.z_mem₁
  have hzd : z * rr t q q = rr t q q * z := h.z_cent' (h.R_le_S hdR)
  have hqq : q * q = z := h.act_sq_eq_z hq hd2 hd1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h.mem_Xc_of_mem_R hdR).2 ⟨hd2, hd1, hdz⟩
  · refine (h.mem_Xc_of_mem_R (mul_mem hzR hdR)).2 ⟨?_, ?_, ?_⟩
    · calc z * rr t q q * (z * rr t q q) = z * (rr t q q * z) * rr t q q := by simp only [mul_assoc]
        _ = z * (z * rr t q q) * rr t q q := by rw [hzd]
        _ = (z * z) * (rr t q q * rr t q q) := by simp only [mul_assoc]
        _ = 1 := by rw [h.z_sq, hd2, one_mul]
    · intro e
      apply hdz
      calc rr t q q = z⁻¹ * (z * rr t q q) := by group
        _ = z := by rw [e, mul_one, h.z_inv]
    · intro e
      apply hd1
      exact mul_left_cancel (e.trans (mul_one z).symm)
  · rw [h.rr_mul_t hq hq]
    exact (h.rrt_mem_Xc_iff hq hq).2 hqq
  · have e : t * z * rr t q q = rr t (z * q) q * t := by
      calc t * z * rr t q q = z * t * rr t q q := by rw [← h.part_z_comm_t]
        _ = z * (t * rr t q q) := by rw [mul_assoc]
        _ = z * (rr t q q * t) := by rw [h.rr_mul_t hq hq]
        _ = (z * rr t q q) * t := by rw [mul_assoc]
        _ = rr t (z * q) q * t := by rw [part_mul_rr]
    rw [e]
    refine (h.rrt_mem_Zc_iff (mul_mem h.z_mem₁ hq) hq).2 ?_
    calc z * q * q = z * (q * q) := by rw [mul_assoc]
      _ = 1 := by rw [hqq, h.z_sq]

end Data

end ActFin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
