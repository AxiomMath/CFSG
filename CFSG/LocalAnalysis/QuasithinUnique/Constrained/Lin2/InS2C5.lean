module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2C4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Block

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem mul_comm_of_cyclic {F : Subgroup G} (hF : IsCyclic ↥F) {a b : G} (ha : a ∈ F)
    (hb : b ∈ F) : a * b = b * a := by
  have := hF
  exact congrArg Subtype.val ((IsCyclic.commGroup (α := F)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

omit [Finite G] B in
theorem blockZ_conjR : blockZ (conjR L t) = conjR (blockZ L) t := by
  unfold blockZ
  rw [DoubleA3.blockU_conjR, conjR_inf, conjR_centralizer]

theorem Z₂_le_W₂ : blockZ (conjR L t) ≤ conjR W t := by
  rw [blockZ_conjR]
  exact conjR_mono B.Z_le_W t

theorem loc₂' : AppE.Loc (baum S) (conjR L t) (blockU (conjR L t))
    (conjSubgroup (baum S ⊓ Subgroup.centralizer (blockU L : Set G)) t) (conjR W t) q := by
  rw [DoubleA3.blockU_conjR]
  exact B.su.loc₂

theorem baum_le_normalizer_D : D ≤ Subgroup.normalizer (baum S : Set G) := by
  rw [B.baum_eq]; exact B.D_le_normalizer_R

theorem hall_comm {B' : Subgroup G} (hH : S2Hall S L D x₀ B') {D₁ D₂ : Subgroup G}
    (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂) :
    ∀ d ∈ D, ∀ d' ∈ conjR D x₀, d * d' = d' * d := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have hD₁D : D₁ ≤ D := hD ▸ le_sup_left
  have hD₂D : D₂ ≤ D := hD ▸ le_sup_right
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    rw [hD]
    exact commute_sup_of_comm (fun a ha b hb => mul_comm_of_cyclic hT₁.cyclic ha hb)
      (fun a ha b hb => mul_comm_of_cyclic hT₂.cyclic ha hb)
      (fun a ha b hb => B.comm_elem a (hD₁L ha) b (hD₂L hb))
  have hDyc : ∀ a ∈ conjR D x₀, ∀ b ∈ conjR D x₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := mem_conjR_iff'.1 ha
    obtain ⟨b', hb', rfl⟩ := mem_conjR_iff'.1 hb
    have := hDc a' ha' b' hb'
    calc x₀⁻¹ * a' * x₀ * (x₀⁻¹ * b' * x₀) = x₀⁻¹ * (a' * b') * x₀ := by group
      _ = x₀⁻¹ * (b' * a') * x₀ := by rw [this]
      _ = x₀⁻¹ * b' * x₀ * (x₀⁻¹ * a' * x₀) := by group
  have hBD : B' ≤ Subgroup.normalizer (D : Set G) := by
    rw [hH.eq_sup]
    exact sup_le Subgroup.le_normalizer hH.conj_le
  have hBDy : B' ≤ Subgroup.normalizer ((conjR D x₀ : Subgroup G) : Set G) := by
    have h1 := conjR_mono hBD x₀
    rwa [← conjR_normalizer, conjR_eq_of_mem_normalizer hH.y_norm] at h1
  obtain ⟨hBL, hBL₂⟩ := B.hall_le_normalizer_L hH
  have hD₁eq := B.D_inf_L_eq hD₁L hD₂L hD
  have hD₂eq := B.D_inf_L₂_eq hD₁L hD₂L hD
  have hBD₁ : B' ≤ Subgroup.normalizer (D₁ : Set G) := by
    intro b hb
    refine mem_normalizer_of_conj_mem fun d hd => ?_
    have h1 : b * d * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 (hBD hb) d).1 (hD₁D hd)
    have h2 : b * d * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hBL hb) d).1 (hD₁L hd)
    rw [← hD₁eq]; exact ⟨h1, h2⟩
  have hBD₂ : B' ≤ Subgroup.normalizer (D₂ : Set G) := by
    intro b hb
    refine mem_normalizer_of_conj_mem fun d hd => ?_
    have h1 : b * d * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 (hBD hb) d).1 (hD₂D hd)
    have h2 : b * d * b⁻¹ ∈ conjR L t :=
      (Subgroup.mem_normalizer_iff.1 (hBL₂ hb) d).1 (hD₂L hd)
    rw [← hD₂eq]; exact ⟨h1, h2⟩
  have hbR : ∀ b ∈ B', b ∈ Subgroup.normalizer (baum S : Set G) := by
    intro b hb
    rw [B.baum_eq]; exact hH.le_R hb
  have hBW : B' ≤ Subgroup.normalizer (W : Set G) := by
    intro b hb
    have := mem_normalizer_commutator (C1.mem_normalizer_blockU (hBL hb)) (hbR b hb)
    rwa [B.su.loc.rk.comm_UB] at this
  have hBW₂ : B' ≤ Subgroup.normalizer ((conjR W t : Subgroup G) : Set G) := by
    intro b hb
    have h1 : b ∈ Subgroup.normalizer ((blockU (conjR L t) : Subgroup G) : Set G) :=
      C1.mem_normalizer_blockU (hBL₂ hb)
    rw [DoubleA3.blockU_conjR] at h1
    have h2 := mem_normalizer_commutator h1 (hbR b hb)
    have h3 : b ∈ Subgroup.normalizer
        ((⁅conjSubgroup (blockU L) t, baum S⁆ : Subgroup G) : Set G) := h2
    rw [B.su.loc₂.rk.comm_UB] at h3
    exact h3
  intro d hd d' hd'
  have hd'B : d' ∈ B' := hH.eq_sup ▸ Subgroup.mem_sup_right hd'
  have hcomm : ∀ d ∈ D, d' * (d * d' * d⁻¹ * d'⁻¹) = (d * d' * d⁻¹ * d'⁻¹) * d' := by
    intro d hd
    have hc : d * d' * d⁻¹ * d'⁻¹ ∈ conjR D x₀ := by
      have h1 : d * d' * d⁻¹ ∈ conjR D x₀ :=
        (Subgroup.mem_normalizer_iff.1 (hBDy (hH.D_le hd)) d').1 hd'
      exact (conjR D x₀).mul_mem h1 ((conjR D x₀).inv_mem hd')
    exact hDyc d' hd' _ hc
  have h₁ := commute_of_block B.hn B.hL B.hlin B.su.loc B.Z_le_W hT₁ (B.baum_le_normalizer_D.trans' hD₁D)
    (hD₁D.trans hH.D_le) hBD₁ hBW hd'B (fun d hd => hcomm d (hD₁D hd))
  have h₂ := commute_of_block B.hn B.hL₂ B.hlin₂ B.loc₂' B.Z₂_le_W₂ hT₂
    (B.baum_le_normalizer_D.trans' hD₂D) (hD₂D.trans hH.D_le) hBD₂ hBW₂ hd'B
    (fun d hd => hcomm d (hD₂D hd))
  have hN : D₂ ≤ Subgroup.normalizer (D₁ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => B.comm_elem a (hD₁L ha) b (hD₂L hb)
  rw [hD] at hd
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hd
  calc d₁ * d₂ * d' = d₁ * (d₂ * d') := by group
    _ = d₁ * (d' * d₂) := by rw [h₂ d₂ hd₂]
    _ = (d₁ * d') * d₂ := by group
    _ = (d' * d₁) * d₂ := by rw [h₁ d₁ hd₁]
    _ = d' * (d₁ * d₂) := by group

theorem hall_abelian {B' : Subgroup G} (hH : S2Hall S L D x₀ B') {D₁ D₂ : Subgroup G}
    (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂) :
    ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    rw [hD]
    exact commute_sup_of_comm (fun a ha b hb => mul_comm_of_cyclic hT₁.cyclic ha hb)
      (fun a ha b hb => mul_comm_of_cyclic hT₂.cyclic ha hb)
      (fun a ha b hb => B.comm_elem a (hD₁L ha) b (hD₂L hb))
  have hDyc : ∀ a ∈ conjR D x₀, ∀ b ∈ conjR D x₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := mem_conjR_iff'.1 ha
    obtain ⟨b', hb', rfl⟩ := mem_conjR_iff'.1 hb
    have := hDc a' ha' b' hb'
    calc x₀⁻¹ * a' * x₀ * (x₀⁻¹ * b' * x₀) = x₀⁻¹ * (a' * b') * x₀ := by group
      _ = x₀⁻¹ * (b' * a') * x₀ := by rw [this]
      _ = x₀⁻¹ * b' * x₀ * (x₀⁻¹ * a' * x₀) := by group
  intro a ha b hb
  rw [hH.eq_sup] at ha hb
  exact commute_sup_of_comm hDc hDyc (B.hall_comm hH hT₁ hT₂ hD) a ha b hb

end S2Base

end CFSG.QuasithinUnique.Lin2
