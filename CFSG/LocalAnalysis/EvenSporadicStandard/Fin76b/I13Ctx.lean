module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma620C
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611J
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13EDef

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

structure I13Ctx {G : Type} [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B S : Subgroup G) (α : G) : Prop where
  h : Hyp69 L z t T₀ E Q x β B S
  hα : AlphaSpec S z t α
  hF : EFacts611 E t
  hWr : ∃ hz : z ∈ centralizer ({β} : Set G),
    WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩)
  hBD : BetaData65 E β

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

@[expose] noncomputable def Qs : Subgroup G :=
  c.h.Fsub c.hα ⊓ centralizer ({α} : Set G)

@[expose] noncomputable def W1 : Subgroup G := c.h.Wsub c.hα (zpowers α)

@[expose] noncomputable def W2 : Subgroup G := c.h.Wsub c.hα (zpowers (α * t))

@[expose] def Zs (_c : I13Ctx L z t T₀ E Q x β B S α) : Subgroup G := zpowers α ⊔ zpowers t

@[expose] noncomputable def Nc : Subgroup G := normalizer (c.Qs : Set G)

@[expose] noncomputable def N1 : Subgroup G := c.Nc ⊓ centralizer ({α} : Set G)

theorem mem_Qs {q : G} : q ∈ c.Qs ↔ q ∈ c.h.Fsub c.hα ∧ q * α = α * q := by
  simp only [Qs, mem_inf, mem_centralizer_singleton_iff]

theorem mem_Nc {g : G} : g ∈ c.Nc ↔ ∀ q : G, q ∈ c.Qs ↔ g * q * g⁻¹ ∈ c.Qs := by
  simp only [Nc, mem_normalizer_iff]

theorem mem_N1 {g : G} : g ∈ c.N1 ↔ g ∈ c.Nc ∧ g * α * g⁻¹ = α := by
  rw [N1, mem_inf, mem_cent_singleton_iff_conj]

theorem mem_Zs {u : G} : u ∈ c.Zs ↔ u = 1 ∨ u = t ∨ u = α ∨ u = α * t :=
  c.h.mem_Zg c.hα

theorem alpha_mem_Zs : α ∈ c.Zs := c.h.alpha_mem_Zg c.hα

theorem t_mem_Zs : t ∈ c.Zs := c.h.t_mem_Zg c.hα

theorem alpha_t_mem_Zs : α * t ∈ c.Zs := mul_mem c.alpha_mem_Zs c.t_mem_Zs

theorem Zs_le_Qs : c.Zs ≤ c.Qs := fun _ ha => c.h.Zg_le_Qs c.hα ha

theorem Zs_comm_Qs {a q : G} (ha : a ∈ c.Zs) (hq : q ∈ c.Qs) : a * q = q * a :=
  (c.h.Zg_cent_Q c.hα ha).2 q hq

theorem E_le_Qs : E ≤ c.Qs := c.h.E_le_Qs c.hα

theorem W1_le_Qs : c.W1 ≤ c.Qs := fun _ hw => hw.1

theorem W2_le_Qs : c.W2 ≤ c.Qs := fun _ hw => hw.1

theorem Zs_le_W1 : c.Zs ≤ c.W1 := fun _ ha => c.h.Zg_mem_Wsub c.hα _ ha

theorem Zs_le_W2 : c.Zs ≤ c.W2 := fun _ ha => c.h.Zg_mem_Wsub c.hα _ ha

theorem card_Qs : Nat.card c.Qs = 1024 := c.h.card_QF c.hα

theorem cl : Lemma611Cl E B z t α (c.h.Fsub c.hα) c.W1 c.W2 :=
  c.h.lemma611Cl_of_pairing c.hα c.hF (c.h.pairing_eps_one c.hα c.hF c.hWr c.hBD)

theorem theta_mem {w : G} (hw : w ∈ c.W1) : w * (z * w * z⁻¹) ∈ E := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := c.cl
  exact h1 w hw

theorem theta_surj {e : G} (he : e ∈ E) : ∃ w ∈ c.W1, e = w * (z * w * z⁻¹) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h2⟩ := c.cl
  exact h2 e he

theorem W1_comm_W2 {w₁ w₂ : G} (h₁ : w₁ ∈ c.W1) (h₂ : w₂ ∈ c.W2) : w₁ * w₂ = w₂ * w₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := c.cl
  exact h w₁ h₁ w₂ h₂

theorem Qs_eq {q : G} (hq : q ∈ c.Qs) : ∃ w₁ ∈ c.W1, ∃ w₂ ∈ c.W2, q = w₁ * w₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := c.cl
  exact h q hq

theorem z_conj_W1 {w : G} (hw : w ∈ c.W1) : z * w * z⁻¹ ∈ c.W2 := c.h.conj_z_W1 c.hα hw

theorem z_conj_W2 {w : G} (hw : w ∈ c.W2) : z * w * z⁻¹ ∈ c.W1 := c.h.conj_z_W2 c.hα hw

theorem z_conj_Qs {q : G} (hq : q ∈ c.Qs) : z * q * z⁻¹ ∈ c.Qs := c.h.z_norm_Qs c.hα hq

include c in
theorem z_conj_conj (w : G) : z * (z * w * z⁻¹) * z⁻¹ = w := by
  calc z * (z * w * z⁻¹) * z⁻¹ = (z * z) * w * (z * z)⁻¹ := by group
    _ = w := by rw [c.h.z_sq]; group

theorem z_mem_Nc : z ∈ c.Nc := by
  rw [mem_Nc]
  intro q
  refine ⟨fun hq => c.z_conj_Qs hq, fun hq => ?_⟩
  have := c.z_conj_Qs hq
  rwa [c.z_conj_conj] at this

theorem Qs_le_Nc : c.Qs ≤ c.Nc := by
  intro g hg
  rw [mem_Nc]
  intro q
  exact ⟨fun hq => mul_mem (mul_mem hg hq) (inv_mem hg), fun hq => by
    have := mul_mem (mul_mem (inv_mem hg) hq) hg
    simpa [mul_assoc] using this⟩

theorem M_le_Nc {m : G} (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) : m ∈ c.Nc := by
  rw [mem_Nc]
  intro q
  refine ⟨fun hq => c.h.QF_normal c.hα hm hq, fun hq => ?_⟩
  have := c.h.QF_normal c.hα (inv_mem hm) hq
  rwa [show m⁻¹ * (m * q * m⁻¹) * m⁻¹⁻¹ = q by group] at this

theorem B_le_Nc : B ≤ c.Nc := fun _ hb => c.M_le_Nc (c.h.W_mem_M (c.h.B_le_W hb))

theorem Nc_t {g : G} (hg : g ∈ c.Nc) : g * t * g⁻¹ = t :=
  (c.h.normalizer_Q_perm_W c.hα c.hF c.hWr c.hBD (c.mem_Nc.1 hg)).1

theorem Nc_perm {g : G} (hg : g ∈ c.Nc) :
    (g * α * g⁻¹ = α ∧ (∀ w ∈ c.W1, g * w * g⁻¹ ∈ c.W1) ∧ ∀ w ∈ c.W2, g * w * g⁻¹ ∈ c.W2) ∨
    (g * α * g⁻¹ = α * t ∧ (∀ w ∈ c.W1, g * w * g⁻¹ ∈ c.W2) ∧ ∀ w ∈ c.W2, g * w * g⁻¹ ∈ c.W1) :=
  (c.h.normalizer_Q_perm_W c.hα c.hF c.hWr c.hBD (c.mem_Nc.1 hg)).2

theorem N1_W1 {n w : G} (hn : n ∈ c.N1) (hw : w ∈ c.W1) : n * w * n⁻¹ ∈ c.W1 := by
  obtain ⟨hn1, hn2⟩ := c.mem_N1.1 hn
  rcases c.Nc_perm hn1 with ⟨-, h1, -⟩ | ⟨h1, -⟩
  · exact h1 w hw
  · exact absurd (hn2.symm.trans h1) (fun h => c.h.t_ne (by simpa using h))

theorem Qs_le_N1 : c.Qs ≤ c.N1 := fun q hq =>
  c.mem_N1.2 ⟨c.Qs_le_Nc hq, by
    have := ((c.mem_Qs.1 hq).2)
    rw [this]; group⟩

theorem B_le_N1 : B ≤ c.N1 := fun b hb =>
  c.mem_N1.2 ⟨c.B_le_Nc hb, by rw [c.h.BS b hb α c.hα.mem]; group⟩

theorem Zs_le_N1 : c.Zs ≤ c.N1 := fun _ ha => c.Qs_le_N1 (c.Zs_le_Qs ha)

theorem N1_le_Nc : c.N1 ≤ c.Nc := inf_le_left

theorem z_conj_N1 {n : G} (hn : n ∈ c.N1) : z * n * z⁻¹ ∈ c.N1 := by
  obtain ⟨hn1, hn2⟩ := c.mem_N1.1 hn
  refine c.mem_N1.2 ⟨mul_mem (mul_mem c.z_mem_Nc hn1) (inv_mem c.z_mem_Nc), ?_⟩
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
  have hzα : z⁻¹ * α * z = α * t := by
    have := c.h.z_conj_alpha c.hα
    rw [hzi] at this ⊢
    exact this
  have hzαt : z * (α * t) * z⁻¹ = α := by
    calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      _ = α * t * t := by rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t]
      _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
  have hnt := c.Nc_t hn1
  calc z * n * z⁻¹ * α * (z * n * z⁻¹)⁻¹ = z * (n * (z⁻¹ * α * z) * n⁻¹) * z⁻¹ := by group
    _ = z * (n * (α * t) * n⁻¹) * z⁻¹ := by rw [hzα]
    _ = z * ((n * α * n⁻¹) * (n * t * n⁻¹)) * z⁻¹ := by group
    _ = z * (α * t) * z⁻¹ := by rw [hn2, hnt]
    _ = α := hzαt

theorem Nc_xor {g : G} (hg : g ∈ c.Nc) :
    Xor (g * z ∈ c.N1) (g ∈ c.N1) := by
  have hx := c.h.xor_mem_cent_alpha c.hα c.hF c.hWr c.hBD (c.mem_Nc.1 hg)
  have hgz : g * z ∈ c.Nc := mul_mem hg c.z_mem_Nc
  simp only [N1, mem_inf]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨⟨hgz, h1⟩, fun h => h2 h.2⟩
  · exact Or.inr ⟨⟨hg, h1⟩, fun h => h2 h.2⟩

theorem N1_relIndex : c.N1.relIndex c.Nc = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨z, c.z_mem_Nc⟩, fun b => ?_⟩
  have := c.Nc_xor b.2
  simpa [mem_subgroupOf] using this

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
