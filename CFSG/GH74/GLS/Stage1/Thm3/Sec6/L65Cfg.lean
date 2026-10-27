module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65P1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Prop66b
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

structure Cfg65 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t : G) : Prop where
  std : Std4 G z S K₁ K₂
  hQ : Qz S z = zpowers z
  a₁ : Cond6a S K₁
  d₁ : IsDoubleCoverOfAlt (HatT K₁) 7
  t_mem : t ∈ S
  t_conj : IsConj z t
  t_ne : t ≠ z
  t_swap : Interchanges t K₁ K₂
  t_fus : ∀ x ∈ Pz S z, orderOf x = 2 → x ≠ z → IsConj (t * z) x
  tz_ne : ¬ IsConj z (t * z)

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem orderOf_conj_eq'' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa using this

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t)

include h

theorem m4 (hII : II4_4_4_center) : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ :=
  m4_of_std hII h.std

theorem z_sq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two h.std.orderOf_z

theorem z_ne : z ≠ 1 := ne_one_of_orderOf_eq_two h.std.orderOf_z

theorem orderOf_t : orderOf t = 2 := by
  obtain ⟨g, hg⟩ := M.exists_conj_inv h.t_conj
  have h1 := orderOf_conj_eq'' g⁻¹ z
  rw [inv_inv, hg] at h1
  rw [h1]
  exact h.std.orderOf_z

theorem t_sq : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_t

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

theorem t_comm (hII : II4_4_4_center) : t * z = z * t :=
  M.centralizer_comm ((h.m4 hII).S_syl.1 h.t_mem)

theorem tz_sq (hII : II4_4_4_center) : (t * z) * (t * z) = 1 := by
  calc (t * z) * (t * z) = t * (z * t) * z := by group
    _ = t * (t * z) * z := by rw [← h.t_comm hII]
    _ = (t * t) * (z * z) := by group
    _ = 1 := by rw [h.t_sq, h.z_sq, one_mul]

theorem mem_K₂_iff {y : G} : y ∈ K₂ ↔ t * y * t⁻¹ ∈ K₁ := by
  have h1 : y ∈ conjugate K₁ t ↔ t * y * t⁻¹ ∈ K₁ := mem_conjugate_iff'
  rw [h.t_swap.1] at h1
  exact h1

theorem mem_K₁_iff {y : G} : y ∈ K₁ ↔ t * y * t⁻¹ ∈ K₂ := by
  have h1 : y ∈ conjugate K₂ t ↔ t * y * t⁻¹ ∈ K₂ := mem_conjugate_iff'
  rw [h.t_swap.2] at h1
  exact h1

theorem P_comm (hII : II4_4_4_center) :
    ∀ a ∈ Pof S K₁, ∀ b ∈ Pof S K₂, a * b = b * a :=
  fun _ ha _ hb => (h.m4 hII).comm_of_S ha.2 hb.2 ha.1 hb.1

theorem P_inf (hII : II4_4_4_center) : Pof S K₁ ⊓ Pof S K₂ = zpowers z := by
  have hM := h.m4 hII
  apply le_antisymm
  · rintro x ⟨⟨hxS, hxK₁⟩, ⟨-, hxK₂⟩⟩
    exact M4facts.inf_comps_le_zpowers hM hxS hxK₁ hxK₂
  · exact zpowers_le.2 ⟨⟨hM.z_mem_S, hM.z_mem_comp (Or.inl rfl)⟩, ⟨hM.z_mem_S, hM.z_mem_comp (Or.inr rfl)⟩⟩

theorem Pz_eq_sup (hII : II4_4_4_center) : Pz S z = Pof S K₁ ⊔ Pof S K₂ := by
  have hM := h.m4 hII
  have e1 : M.Pm S K₁ K₂ ⊓ K₁ = Pof S K₁ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have e2 : M.Pm S K₁ K₂ ⊓ K₂ = Pof S K₂ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_right : K₂ ≤ K₁ ⊔ K₂)]
  rw [Pz_eq h.std, hM.P_eq, e1, e2]

theorem norm_iff (hII : II4_4_4_center) {x : G} (hx : x ∈ S) :
    x ∈ normalizer (K₁ : Set G) ↔ x ∈ normalizer (K₂ : Set G) := by
  have hM := h.m4 hII
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx
  have hne : K₁ ≠ K₂ := h.std.ne
  rcases hM.perm x hxC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => M.cj_eq_iff_normalizer.1 h2, fun _ => M.cj_eq_iff_normalizer.1 h1⟩
  · constructor
    · intro hn
      exfalso
      have := M.cj_eq_iff_normalizer.2 hn
      rw [h1] at this
      exact hne this.symm
    · intro hn
      exfalso
      have := M.cj_eq_iff_normalizer.2 hn
      rw [h2] at this
      exact hne this

theorem Q_comm_P {K : Subgroup G} (hII : II4_4_4_center) (hK : K = K₁ ∨ K = K₂) :
    ∀ q ∈ Qof S K, ∀ p ∈ Pof S K, q * p = p * q := by
  have hM := h.m4 hII
  intro q hq p hp
  have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2 p hp.2
  have h2 : ⁅p, q⁆ ∈ S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp.1 hq.1) (inv_mem hp.1)) (inv_mem hq.1)
  have h3 : ⁅p, q⁆ ∈ S ⊓ pPrimeCoreOf 2 K := ⟨h2, h1⟩
  rw [M.inf_eq_bot_of_pgroup_odd hM.S_pgroup (hM.core K hK).odd, Subgroup.mem_bot,
    commutatorElement_def] at h3
  have h4 : p * q = q * p := by
    have h5 : p * q * p⁻¹ * q⁻¹ = 1 := h3
    calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
      _ = q * p := by rw [h5, one_mul]
  exact h4.symm

theorem Q_inf_Q (hII : II4_4_4_center) : Qof S K₁ ⊓ Qof S K₂ = zpowers z := by
  have hM := h.m4 hII
  apply le_antisymm
  · rintro c ⟨hc1, hc2⟩
    have hcS : c ∈ S := hc1.1
    have hcC : c ∈ centralizer ({z} : Set G) := hM.S_syl.1 hcS
    have h1 : ∀ x ∈ K₁, ⁅x, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun x hx =>
      hM.O_le_OK (Or.inl rfl) (hc1.2.2.2 x hx)
    have h2 : ∀ y ∈ K₂, ⁅y, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun y hy =>
      hM.O_le_OK (Or.inr rfl) (hc2.2.2.2 y hy)
    have hcs : c ∈ M.secCent (K₁ ⊔ K₂) (pPrimeCoreOf 2 (K₁ ⊔ K₂)) := hM.secCent_of_gen hcC h1 h2
    have hcQ : c ∈ Qz S z := by
      rw [Qz_eq h.std]
      exact ⟨hcS, hcs⟩
    rw [h.hQ] at hcQ
    exact hcQ
  · refine zpowers_le.2 ⟨⟨hM.z_mem_S, hM.z_mem_secCent_comp (Or.inl rfl)⟩,
      ⟨hM.z_mem_S, hM.z_mem_secCent_comp (Or.inr rfl)⟩⟩

theorem P₂_le_Q₁ (hII : II4_4_4_center) : Pof S K₂ ≤ Qof S K₁ :=
  fun _ hx => ⟨hx.1, (h.m4 hII).cs₁ hx.2⟩

theorem z_mem_P (hII : II4_4_4_center) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : z ∈ Pof S K :=
  ⟨(h.m4 hII).z_mem_S, (h.m4 hII).z_mem_comp hK⟩

theorem t_conj_P₁ {x : G} (hx : x ∈ Pof S K₁) : t * x * t⁻¹ ∈ Pof S K₂ :=
  ⟨S.mul_mem (S.mul_mem h.t_mem hx.1) (S.inv_mem h.t_mem), (h.mem_K₁_iff).1 hx.2⟩

theorem t_conj_P₂ {x : G} (hx : x ∈ Pof S K₂) : t * x * t⁻¹ ∈ Pof S K₁ :=
  ⟨S.mul_mem (S.mul_mem h.t_mem hx.1) (S.inv_mem h.t_mem), (h.mem_K₂_iff).1 hx.2⟩

theorem t_conj_Q₁ {x : G} (hx : x ∈ Qof S K₁) : t * x * t⁻¹ ∈ Qof S K₂ := by
  refine ⟨S.mul_mem (S.mul_mem h.t_mem hx.1) (S.inv_mem h.t_mem), ?_⟩
  have h1 : (t * x * t⁻¹) ∈ cSec (conjugate K₁ t) ↔ t * (t * x * t⁻¹) * t⁻¹ ∈ cSec K₁ :=
    mem_cSec_conjugate
  rw [h.t_swap.1] at h1
  apply h1.2
  have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [h.t_sq, h.t_inv, h.t_sq]; group
  rw [e]
  exact hx.2

theorem S1_t_inv (hII : II4_4_4_center) {s : G} (hs : s ∈ S1 S K₁) : t * s * t⁻¹ ∈ S1 S K₁ := by
  have hM := h.m4 hII
  have hsN₂ : s ∈ normalizer (K₂ : Set G) := (h.norm_iff hII hs.1).1 hs.2
  have key : ∀ g : G, g ∈ S → g ∈ normalizer (K₂ : Set G) → t * g * t⁻¹ ∈ normalizer (K₁ : Set G) := by
    intro g hg hgN
    have hgN' : ∀ x, x ∈ K₂ ↔ g * x * g⁻¹ ∈ K₂ := fun x => (Subgroup.mem_normalizer_iff.1 hgN) x
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have e : t * g * t⁻¹ * x * (t * g * t⁻¹)⁻¹ = t * (g * (t⁻¹ * x * t) * g⁻¹) * t⁻¹ := by group
    rw [e, ← h.mem_K₂_iff]
    have h1 : x ∈ K₁ ↔ t⁻¹ * x * t ∈ K₂ := by
      rw [h.mem_K₁_iff, h.t_inv]
    rw [h1, hgN' (t⁻¹ * x * t)]
  refine ⟨S.mul_mem (S.mul_mem h.t_mem hs.1) (S.inv_mem h.t_mem), key s hs.1 hsN₂⟩

theorem S1_le_P₂Q₂ (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) {s : G} (hs : s ∈ S1 S K₁) :
    ∃ p ∈ Pof S K₂, ∃ q ∈ Qof S K₂, s = p * q := by
  have hstd6 : Std6 G z S := Std4.toStd6' h.std
  have hcond : Cond6a (S1 S K₁) K₁ := fun s hs => h.a₁ s hs.1
  obtain ⟨-, h7, -⟩ := h4hij G z S hstd6 K₁ (h.std.comp_rigid (Or.inl rfl)) hcond
  have hS1 : S1 S K₁ = Pof S K₁ ⊔ Qof S K₁ := h7 h.d₁
  have hts : t * s * t⁻¹ ∈ Pof S K₁ ⊔ Qof S K₁ := by rw [← hS1]; exact h.S1_t_inv hII hs
  obtain ⟨p, hp, q, hq, hpq⟩ := M.mem_sup_of_commute (fun a ha b hb => (h.Q_comm_P hII (Or.inl rfl) b hb a ha).symm) hts
  refine ⟨t * p * t⁻¹, h.t_conj_P₁ hp, t * q * t⁻¹, h.t_conj_Q₁ hq, ?_⟩
  calc s = t⁻¹ * (t * s * t⁻¹) * t := by group
    _ = t⁻¹ * (p * q) * t := by rw [hpq]
    _ = (t * p * t⁻¹) * (t * q * t⁻¹) := by
      have e : (t * p * t⁻¹) * (t * q * t⁻¹) = t * (p * q) * t⁻¹ := by group
      rw [e, h.t_inv]

theorem Q₁_le_P₂ (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) : Qof S K₁ ≤ Pof S K₂ := by
  have hstd6 : Std6 G z S := Std4.toStd6' h.std
  have hcond : Cond6a (S1 S K₁) K₁ := fun s hs => h.a₁ s hs.1
  intro x hx
  have hxS1 : x ∈ S1 S K₁ := ⟨hx.1, hx.2.1⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := h.S1_le_P₂Q₂ hII h4hij hxS1
  have hpQ₁ : p ∈ Qof S K₁ := h.P₂_le_Q₁ hII hp
  have hq₁ : q ∈ Qof S K₁ := by
    have : p⁻¹ * (p * q) ∈ Qof S K₁ := mul_mem (inv_mem hpQ₁) hx
    simpa using this
  have hqz : q ∈ zpowers z := by
    rw [← h.Q_inf_Q hII]
    exact ⟨hq₁, hq⟩
  have hqP₂ : q ∈ Pof S K₂ := zpowers_le.2 (h.z_mem_P hII (Or.inr rfl)) hqz
  exact mul_mem hp hqP₂

theorem S1_eq_P (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) : S1 S K₁ = Pz S z := by
  have hstd6 : Std6 G z S := Std4.toStd6' h.std
  have hcond : Cond6a (S1 S K₁) K₁ := fun s hs => h.a₁ s hs.1
  obtain ⟨-, h7, -⟩ := h4hij G z S hstd6 K₁ (h.std.comp_rigid (Or.inl rfl)) hcond
  have hS1 : S1 S K₁ = Pof S K₁ ⊔ Qof S K₁ := h7 h.d₁
  apply le_antisymm
  · rw [hS1, h.Pz_eq_sup hII]
    exact sup_le le_sup_left ((h.Q₁_le_P₂ hII h4hij).trans le_sup_right)
  · rw [h.Pz_eq_sup hII]
    refine sup_le (fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩) (fun x hx => ⟨hx.1, ?_⟩)
    exact (h.m4 hII).n₂₁ hx.2

theorem S_cases (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) {s : G} (hs : s ∈ S) :
    s ∈ Pz S z ∨ s * t ∈ Pz S z := by
  have hM := h.m4 hII
  have hsC : s ∈ centralizer ({z} : Set G) := hM.S_syl.1 hs
  rcases hM.perm s hsC with ⟨h1, -⟩ | ⟨h1, h2⟩
  · left
    rw [← h.S1_eq_P hII h4hij]
    exact ⟨hs, M.cj_eq_iff_normalizer.1 h1⟩
  · right
    rw [← h.S1_eq_P hII h4hij]
    refine ⟨S.mul_mem hs h.t_mem, Subgroup.mem_normalizer_iff.2 (fun x => ?_)⟩
    have e : s * t * x * (s * t)⁻¹ = s * (t * x * t⁻¹) * s⁻¹ := by group
    rw [e]
    have hmem : ∀ y, y ∈ K₂ ↔ s * y * s⁻¹ ∈ K₁ := by
      intro y
      have := M.mem_cj (H := K₁) (g := s) (x := y)
      rw [h1] at this
      exact this
    rw [h.mem_K₁_iff, hmem]

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
