module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

namespace Cfg7

theorem m4 (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ := m4_of_std hII h.std.std

theorem z_sq (h : Cfg7 G z S K₁ K₂ t u q) : z * z = 1 :=
  mul_self_eq_one_of_orderOf_eq_two h.std.std.orderOf_z

theorem z_ne (h : Cfg7 G z S K₁ K₂ t u q) : z ≠ 1 := ne_one_of_orderOf_eq_two h.std.std.orderOf_z

theorem z_mem_S (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : z ∈ S :=
  (h.m4 hII).z_mem_S

theorem z_mem_P {K : Subgroup G} (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hK : K = K₁ ∨ K = K₂) : z ∈ Pof S K := ⟨(h.m4 hII).z_mem_S, (h.m4 hII).z_mem_comp hK⟩

theorem z_mem_Q {K : Subgroup G} (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hK : K = K₁ ∨ K = K₂) : z ∈ Qof S K := ⟨(h.m4 hII).z_mem_S, (h.m4 hII).z_mem_secCent_comp hK⟩

theorem S_pgroup (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : IsPGroup 2 ↥S :=
  (h.m4 hII).S_pgroup

theorem S_le_C (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    S ≤ centralizer ({z} : Set G) := (h.m4 hII).S_syl.1

omit [Finite G] in
theorem mem_cSec {K : Subgroup G} {x : G} :
    x ∈ cSec K ↔ x ∈ normalizer (K : Set G) ∧ x ∈ normalizer (pPrimeCoreOf 2 K : Set G) ∧
      ∀ k ∈ K, ⁅k, x⁆ ∈ pPrimeCoreOf 2 K := Iff.rfl

theorem P_comm (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ a ∈ Pof S K₁, ∀ b ∈ Pof S K₂, a * b = b * a :=
  fun _ ha _ hb => (h.m4 hII).comm_of_S ha.2 hb.2 ha.1 hb.1

theorem P_inf (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    Pof S K₁ ⊓ Pof S K₂ = zpowers z := by
  have hM := h.m4 hII
  apply le_antisymm
  · rintro x ⟨⟨hxS, hxK₁⟩, ⟨-, hxK₂⟩⟩
    have hx : x ∈ S ⊓ M.ZsM (pPrimeCoreOf 2) K₁ := ⟨hxS, hxK₁, hM.cs₁ hxK₂⟩
    rw [(hM.S_inf_Zs_comp (Or.inl rfl)).2] at hx
    exact hx
  · exact zpowers_le.2 ⟨h.z_mem_P hII (Or.inl rfl), h.z_mem_P hII (Or.inr rfl)⟩

theorem P_inf_Q {K : Subgroup G} (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hK : K = K₁ ∨ K = K₂) : Pof S K ⊓ Qof S K ≤ zpowers z := by
  have hM := h.m4 hII
  rintro x ⟨⟨hxS, hxK⟩, ⟨-, hxc⟩⟩
  have hx : x ∈ S ⊓ M.ZsM (pPrimeCoreOf 2) K := ⟨hxS, hxK, hxc⟩
  rw [(hM.S_inf_Zs_comp hK).2] at hx
  exact hx

theorem Pz_eq_sup (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    Pz S z = Pof S K₁ ⊔ Pof S K₂ := by
  have hM := h.m4 hII
  have e1 : M.Pm S K₁ K₂ ⊓ K₁ = Pof S K₁ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have e2 : M.Pm S K₁ K₂ ⊓ K₂ = Pof S K₂ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_right : K₂ ≤ K₁ ⊔ K₂)]
  rw [Pz_eq h.std.std, hM.P_eq, e1, e2]

theorem norm_iff (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {x : G} (hx : x ∈ S) :
    x ∈ normalizer (K₁ : Set G) ↔ x ∈ normalizer (K₂ : Set G) := by
  have hM := h.m4 hII
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx
  have hne : K₁ ≠ K₂ := h.std.std.ne
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

theorem Q_comm_P {K : Subgroup G} (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hK : K = K₁ ∨ K = K₂) : ∀ q ∈ Qof S K, ∀ p ∈ Pof S K, q * p = p * q := by
  have hM := h.m4 hII
  intro q hq p hp
  have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := (mem_cSec.1 hq.2).2.2 p hp.2
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

theorem Q_inf_Q (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    Qof S K₁ ⊓ Qof S K₂ = zpowers z := by
  have hM := h.m4 hII
  apply le_antisymm
  · rintro c ⟨hc1, hc2⟩
    have hcS : c ∈ S := hc1.1
    have hcC : c ∈ centralizer ({z} : Set G) := hM.S_syl.1 hcS
    have h1 : ∀ x ∈ K₁, ⁅x, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun x hx =>
      hM.O_le_OK (Or.inl rfl) ((mem_cSec.1 hc1.2).2.2 x hx)
    have h2 : ∀ y ∈ K₂, ⁅y, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun y hy =>
      hM.O_le_OK (Or.inr rfl) ((mem_cSec.1 hc2.2).2.2 y hy)
    have hcs : c ∈ M.secCent (K₁ ⊔ K₂) (pPrimeCoreOf 2 (K₁ ⊔ K₂)) := hM.secCent_of_gen hcC h1 h2
    have hcQ : c ∈ Qz S z := by
      rw [Qz_eq h.std.std]
      exact ⟨hcS, hcs⟩
    rw [h.std.hQ] at hcQ
    exact hcQ
  · exact zpowers_le.2 ⟨h.z_mem_Q hII (Or.inl rfl), h.z_mem_Q hII (Or.inr rfl)⟩

theorem P₁_le_Q₂ (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : Pof S K₁ ≤ Qof S K₂ :=
  fun _ hx => ⟨hx.1, (h.m4 hII).cs₂ hx.2⟩

theorem P₂_le_Q₁ (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : Pof S K₂ ≤ Qof S K₁ :=
  fun _ hx => ⟨hx.1, (h.m4 hII).cs₁ hx.2⟩

theorem Q₁_le_S1 (_h : Cfg7 G z S K₁ K₂ t u q) : Qof S K₁ ≤ S1 S K₁ :=
  fun _ hx => ⟨hx.1, (mem_cSec.1 hx.2).1⟩

theorem Q₂_le_S1 (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : Qof S K₂ ≤ S1 S K₁ :=
  fun _ hx => ⟨hx.1, (h.norm_iff hII hx.1).2 (mem_cSec.1 hx.2).1⟩

omit [Finite G] in
theorem S1_le_S : S1 S K₁ ≤ S := inf_le_left

theorem S1_norm₂ (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {x : G} (hx : x ∈ S1 S K₁) :
    x ∈ normalizer (K₂ : Set G) := (h.norm_iff hII hx.1).1 hx.2

theorem S1_normalizes_Q₁ (_h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ s ∈ S1 S K₁, ∀ q ∈ Qof S K₁, s * q * s⁻¹ ∈ Qof S K₁ := fun _ hs _ hq =>
  ⟨S.mul_mem (S.mul_mem hs.1 hq.1) (S.inv_mem hs.1), cSec_conj K₁ hs.2 hq.2⟩

theorem S1_normalizes_Q₂ (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ s ∈ S1 S K₁, ∀ q ∈ Qof S K₂, s * q * s⁻¹ ∈ Qof S K₂ := fun _ hs _ hq =>
  ⟨S.mul_mem (S.mul_mem hs.1 hq.1) (S.inv_mem hs.1), cSec_conj K₂ (h.S1_norm₂ hII hs) hq.2⟩

theorem S_normalizes_P (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ s ∈ S, ∀ p ∈ Pof S K₁ ⊔ Pof S K₂, s * p * s⁻¹ ∈ Pof S K₁ ⊔ Pof S K₂ := by
  intro s hs p hp
  have hM := h.m4 hII
  rw [← h.Pz_eq_sup hII] at hp ⊢
  have hrp : rigidProduct z = K₁ ⊔ K₂ := h.std.std.rigidProduct_eq
  have hpS : p ∈ S := hp.1
  have hpK : p ∈ K₁ ⊔ K₂ := by
    have := hp.2
    rwa [hrp] at this
  have h1 : s * p * s⁻¹ ∈ K₁ ⊔ K₂ := hM.C_norm_K (hM.S_syl.1 hs) hpK
  exact ⟨S.mul_mem (S.mul_mem hs hpS) (S.inv_mem hs), by rw [hrp]; exact h1⟩

theorem P₁_le_S1 (_h : Cfg7 G z S K₁ K₂ t u q) : Pof S K₁ ≤ S1 S K₁ :=
  fun _ hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩

theorem P₂_le_S1 (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : Pof S K₂ ≤ S1 S K₁ :=
  fun _ hx => ⟨hx.1, (h.m4 hII).n₂₁ hx.2⟩

theorem S1_normalizes_P₁ (_h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ s ∈ S1 S K₁, ∀ p ∈ Pof S K₁, s * p * s⁻¹ ∈ Pof S K₁ := fun _ hs p hp =>
  ⟨S.mul_mem (S.mul_mem hs.1 hp.1) (S.inv_mem hs.1), (Subgroup.mem_normalizer_iff.1 hs.2 p).1 hp.2⟩

theorem P_le_S1 (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    Pof S K₁ ⊔ Pof S K₂ ≤ S1 S K₁ := sup_le h.P₁_le_S1 (h.P₂_le_S1 hII)

end Cfg7

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
