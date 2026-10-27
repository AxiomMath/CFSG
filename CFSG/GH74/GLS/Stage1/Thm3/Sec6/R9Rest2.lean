module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Count
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9CaseB

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q : Subgroup G} {FA : G → Prop}

structure Setup9 (G : Type) [Group G] [Finite G] (z : G) (S P Q : Subgroup G) (FA : G → Prop)
    (U : Subgroup G) (x u₁ u₂ : G) : Prop where
  cfg : Cfg1 G z S P Q Q FA
  quatP : ∃ n, IVK.IsQuaternionTwoGroup ↥P n
  quatQ : ∃ n, IVK.IsQuaternionTwoGroup ↥Q n
  card_eq : Nat.card ↥P = Nat.card ↥Q
  idx : (P ⊔ Q).relIndex S = 2
  U_le : U ≤ P ⊔ Q
  U_four : Four U
  U_norm : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U
  u₁_mem : u₁ ∈ P
  u₂_mem : u₂ ∈ Q
  u₁_sq : u₁ * u₁ = z
  u₂_sq : u₂ * u₂ = z
  u_mem : u₁ * u₂ ∈ U
  V₁_cyc : IsCyclic ↥(P ⊓ centralizer ({u₁} : Set G))
  V₁_idx : (P ⊓ centralizer ({u₁} : Set G)).relIndex P = 2
  V₂_cyc : IsCyclic ↥(Q ⊓ centralizer ({u₂} : Set G))
  V₂_idx : (Q ⊓ centralizer ({u₂} : Set G)).relIndex Q = 2
  x_W : ∀ w : G, w ∈ S ⊓ centralizer (U : Set G) ↔ x * w * x⁻¹ ∈ S ⊓ centralizer (U : Set G)
  x_U : ∀ v ∈ U, x * v * x⁻¹ ∈ U
  x_z : x * z * x⁻¹ ≠ z

namespace Setup9

variable {U : Subgroup G} {x u₁ u₂ : G} (c : Setup9 G z S P Q FA U x u₁ u₂)
include c

theorem hz2 : z * z = 1 := c.cfg.z_sq

theorem hz1 : z ≠ 1 := c.cfg.z_ne

theorem U_le_S : U ≤ S := c.U_le.trans (sup_le c.cfg.P_le c.cfg.Q_le)

theorem z_mem_U : z ∈ U := c.cfg.z_mem_four c.U_four c.U_le_S c.U_norm

theorem Q_inv : ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z :=
  quat_invol_sub c.quatQ.choose_spec c.cfg.z_Q c.hz2 c.hz1

theorem u₁_ne : u₁ ≠ 1 ∧ u₁ ≠ z := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h := c.u₁_sq; rw [e, one_mul] at h; exact c.hz1 h.symm
  · have h := c.u₁_sq; rw [e, c.hz2] at h; exact c.hz1 h.symm

theorem u₂_ne : u₂ ≠ 1 ∧ u₂ ≠ z := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h := c.u₂_sq; rw [e, one_mul] at h; exact c.hz1 h.symm
  · have h := c.u₂_sq; rw [e, c.hz2] at h; exact c.hz1 h.symm

theorem u₁_inv : u₁⁻¹ = u₁ * z := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, c.u₁_sq, c.hz2]

theorem u₂_inv : u₂⁻¹ = u₂ * z := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, c.u₂_sq, c.hz2]

theorem z_comm {s : G} (hs : s ∈ S) : s * z = z * s := (c.cfg.z_cent s hs).symm

theorem u_ne : u₁ * u₂ ≠ 1 ∧ u₁ * u₂ ≠ z := by
  have hP : u₁⁻¹ ∈ P := inv_mem c.u₁_mem
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h1 : u₂ = u₁⁻¹ := by
      calc u₂ = u₁⁻¹ * (u₁ * u₂) := by group
        _ = u₁⁻¹ := by rw [e, mul_one]
    have : u₂ ∈ P := h1 ▸ hP
    rcases c.cfg.PQ_inf u₂ this c.u₂_mem with h2 | h2
    · exact c.u₂_ne.1 h2
    · exact c.u₂_ne.2 h2
  · have h1 : u₂ = u₁⁻¹ * z := by
      calc u₂ = u₁⁻¹ * (u₁ * u₂) := by group
        _ = u₁⁻¹ * z := by rw [e]
    have : u₂ ∈ P := h1 ▸ mul_mem hP c.cfg.z_P
    rcases c.cfg.PQ_inf u₂ this c.u₂_mem with h2 | h2
    · exact c.u₂_ne.1 h2
    · exact c.u₂_ne.2 h2

theorem mem_U {v : G} (hv : v ∈ U) : v = 1 ∨ v = z ∨ v = u₁ * u₂ ∨ v = z * (u₁ * u₂) :=
  Four.mem_cases c.U_four c.z_mem_U c.u_mem c.hz1 c.u_ne.1 c.u_ne.2 hv

theorem z'_cases : x * z * x⁻¹ = u₁ * u₂ ∨ x * z * x⁻¹ = z * (u₁ * u₂) := by
  have hmem := c.x_U z c.z_mem_U
  have h2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
    calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [c.hz2]; group
  have h1 : x * z * x⁻¹ ≠ 1 := by
    intro e
    apply c.hz1
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [e]; group
  rcases c.mem_U hmem with e | e | e | e
  · exact absurd e h1
  · exact absurd e c.x_z
  · exact Or.inl e
  · exact Or.inr e

theorem z'_not_P : x * z * x⁻¹ ∉ P := by
  intro hP
  have hu : u₁ * u₂ ∈ P := by
    rcases c.z'_cases with e | e
    · rw [← e]; exact hP
    · have : z⁻¹ * (z * (u₁ * u₂)) ∈ P := mul_mem (inv_mem c.cfg.z_P) (e ▸ hP)
      simpa using this
  have : u₂ ∈ P := by
    have : u₁⁻¹ * (u₁ * u₂) ∈ P := mul_mem (inv_mem c.u₁_mem) hu
    simpa using this
  rcases c.cfg.PQ_inf u₂ this c.u₂_mem with h2 | h2
  · exact c.u₂_ne.1 h2
  · exact c.u₂_ne.2 h2

theorem z'_not_Q : x * z * x⁻¹ ∉ Q := by
  intro hQ
  have hu : u₁ * u₂ ∈ Q := by
    rcases c.z'_cases with e | e
    · rw [← e]; exact hQ
    · have : z⁻¹ * (z * (u₁ * u₂)) ∈ Q := mul_mem (inv_mem c.cfg.z_Q) (e ▸ hQ)
      simpa using this
  have : u₁ ∈ Q := by
    have : (u₁ * u₂) * u₂⁻¹ ∈ Q := mul_mem hu (inv_mem c.u₂_mem)
    simpa using this
  rcases c.cfg.PQ_inf u₁ c.u₁_mem this with h2 | h2
  · exact c.u₁_ne.1 h2
  · exact c.u₁_ne.2 h2

theorem norm_u {s : G} (hs : s ∈ S) :
    (s * u₁ * s⁻¹ = u₁ ∨ s * u₁ * s⁻¹ = u₁ * z) ∧ (s * u₂ * s⁻¹ = u₂ ∨ s * u₂ * s⁻¹ = u₂ * z) :=
  c.cfg.conj_comp c.U_le c.U_four c.U_norm c.u_mem c.u_ne.1 c.u_ne.2 c.u₁_mem c.u₂_mem rfl hs

theorem comm_U_of {v : G} (hz : v * z = z * v) (hu : v * (u₁ * u₂) = (u₁ * u₂) * v) :
    ∀ w ∈ U, v * w = w * v := by
  intro w hw
  rcases c.mem_U hw with e | e | e | e
  · rw [e]; simp
  · rw [e]; exact hz
  · rw [e]; exact hu
  · rw [e]
    calc v * (z * (u₁ * u₂)) = (v * z) * (u₁ * u₂) := by group
      _ = (z * v) * (u₁ * u₂) := by rw [hz]
      _ = z * (v * (u₁ * u₂)) := by group
      _ = z * ((u₁ * u₂) * v) := by rw [hu]
      _ = (z * (u₁ * u₂)) * v := by group

theorem V₁_comm_U {v : G} (hv : v ∈ P ⊓ centralizer ({u₁} : Set G)) : ∀ w ∈ U, v * w = w * v := by
  obtain ⟨hvP, hvC⟩ := hv
  have hvu₁ : v * u₁ = u₁ * v := Subgroup.mem_centralizer_singleton_iff.1 hvC
  have hvu₂ : v * u₂ = u₂ * v := c.cfg.PQ_comm v hvP u₂ c.u₂_mem
  refine c.comm_U_of (c.z_comm (c.cfg.P_le hvP)) ?_
  calc v * (u₁ * u₂) = (v * u₁) * u₂ := by group
    _ = (u₁ * v) * u₂ := by rw [hvu₁]
    _ = u₁ * (v * u₂) := by group
    _ = u₁ * (u₂ * v) := by rw [hvu₂]
    _ = (u₁ * u₂) * v := by group

theorem V₂_comm_U {v : G} (hv : v ∈ Q ⊓ centralizer ({u₂} : Set G)) : ∀ w ∈ U, v * w = w * v := by
  obtain ⟨hvQ, hvC⟩ := hv
  have hvu₂ : v * u₂ = u₂ * v := Subgroup.mem_centralizer_singleton_iff.1 hvC
  have hvu₁ : u₁ * v = v * u₁ := c.cfg.PQ_comm u₁ c.u₁_mem v hvQ
  refine c.comm_U_of (c.z_comm (c.cfg.Q_le hvQ)) ?_
  calc v * (u₁ * u₂) = (v * u₁) * u₂ := by group
    _ = (u₁ * v) * u₂ := by rw [hvu₁]
    _ = u₁ * (v * u₂) := by group
    _ = u₁ * (u₂ * v) := by rw [hvu₂]
    _ = (u₁ * u₂) * v := by group

theorem V₁_le_W : P ⊓ centralizer ({u₁} : Set G) ≤ S ⊓ centralizer (U : Set G) := by
  intro v hv
  refine ⟨c.cfg.P_le hv.1, Subgroup.mem_centralizer_iff.2 (fun w hw => ?_)⟩
  exact (c.V₁_comm_U hv w hw).symm

theorem V₂_le_W : Q ⊓ centralizer ({u₂} : Set G) ≤ S ⊓ centralizer (U : Set G) := by
  intro v hv
  refine ⟨c.cfg.Q_le hv.1, Subgroup.mem_centralizer_iff.2 (fun w hw => ?_)⟩
  exact (c.V₂_comm_U hv w hw).symm

theorem V₁_norm : ∀ s ∈ S, ∀ v ∈ P ⊓ centralizer ({u₁} : Set G),
    s * v * s⁻¹ ∈ P ⊓ centralizer ({u₁} : Set G) := by
  intro s hs v hv
  obtain ⟨hvP, hvC⟩ := hv
  have hvu₁ : v * u₁ = u₁ * v := Subgroup.mem_centralizer_singleton_iff.1 hvC
  refine ⟨c.cfg.P_norm s hs v hvP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have ha' : s⁻¹ * u₁ * s = u₁ ∨ s⁻¹ * u₁ * s = u₁ * z := by
    have := (c.norm_u (S.inv_mem hs)).1
    simpa using this
  have hvz : v * z = z * v := c.z_comm (c.cfg.P_le hvP)
  have hva : v * (s⁻¹ * u₁ * s) = (s⁻¹ * u₁ * s) * v := by
    rcases ha' with e | e
    · rw [e]; exact hvu₁
    · rw [e]
      calc v * (u₁ * z) = (v * u₁) * z := by group
        _ = (u₁ * v) * z := by rw [hvu₁]
        _ = u₁ * (v * z) := by group
        _ = u₁ * (z * v) := by rw [hvz]
        _ = (u₁ * z) * v := by group
  calc s * v * s⁻¹ * u₁ = s * (v * (s⁻¹ * u₁ * s)) * s⁻¹ := by group
    _ = s * ((s⁻¹ * u₁ * s) * v) * s⁻¹ := by rw [hva]
    _ = u₁ * (s * v * s⁻¹) := by group

theorem z_mem_V₁ : z ∈ P ⊓ centralizer ({u₁} : Set G) := by
  have hu₁V : u₁ ∈ P ⊓ centralizer ({u₁} : Set G) :=
    ⟨c.u₁_mem, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  rw [← c.u₁_sq]; exact mul_mem hu₁V hu₁V

theorem xinv_W {w : G} (hw : w ∈ S ⊓ centralizer (U : Set G)) :
    x⁻¹ * w * x ∈ S ⊓ centralizer (U : Set G) := by
  refine (c.x_W _).2 ?_
  have e : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
  rw [e]; exact hw

section Gen

variable {a₀ : G}

theorem g_mem_W (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G)) :
    x * a₀ * x⁻¹ ∈ S ⊓ centralizer (U : Set G) :=
  (c.x_W a₀).1 (c.V₁_le_W ha₀)

theorem z'_mem_zpowers_g (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) :
    x * z * x⁻¹ ∈ zpowers (x * a₀ * x⁻¹) := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen z c.z_mem_V₁)
  refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
  rw [← hi]; exact conj_zpow

theorem W_norm_g (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) {w : G}
    (hw : w ∈ S ⊓ centralizer (U : Set G)) (k : ℤ) :
    ∃ k' : ℤ, w * (x * a₀ * x⁻¹) ^ k * w⁻¹ = (x * a₀ * x⁻¹) ^ k' := by
  have h1 := c.V₁_norm (x⁻¹ * w * x) (c.xinv_W hw).1 (a₀ ^ k)
    ⟨Subgroup.zpow_mem _ ha₀.1 k, Subgroup.mem_centralizer_singleton_iff.2
      ((Commute.zpow_left (show Commute a₀ u₁ from Subgroup.mem_centralizer_singleton_iff.1 ha₀.2) k).eq)⟩
  obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.1 (hgen _ h1)
  refine ⟨k', ?_⟩
  calc w * (x * a₀ * x⁻¹) ^ k * w⁻¹ = x * ((x⁻¹ * w * x) * a₀ ^ k * (x⁻¹ * w * x)⁻¹) * x⁻¹ := by
        rw [conj_zpow]; group
    _ = x * a₀ ^ k' * x⁻¹ := by rw [hk']
    _ = (x * a₀ * x⁻¹) ^ k' := conj_zpow.symm

theorem g_mem_S (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G)) : x * a₀ * x⁻¹ ∈ S :=
  (c.g_mem_W ha₀).1

theorem zpowers_g_pgroup (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G)) :
    IsPGroup 2 ↥(zpowers (x * a₀ * x⁻¹)) :=
  c.cfg.S_pgroup.to_le (zpowers_le.2 (c.g_mem_S ha₀))

theorem z'_sq : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
  calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
    _ = 1 := by rw [c.hz2]; group

theorem z'_ne_one : x * z * x⁻¹ ≠ 1 := by
  intro e
  apply c.hz1
  calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
    _ = 1 := by rw [e]; group

theorem gpow_P (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) (k : ℤ)
    (hk : (x * a₀ * x⁻¹) ^ k ∈ P) : (x * a₀ * x⁻¹) ^ k = 1 := by
  by_contra hne
  have h := invol_mem_zpowers (V := zpowers (x * a₀ * x⁻¹)) inferInstance (c.zpowers_g_pgroup ha₀)
    (Subgroup.zpow_mem _ (mem_zpowers _) k) hne (c.z'_mem_zpowers_g hgen) c.z'_sq c.z'_ne_one
  exact c.z'_not_P ((zpowers_le.2 hk) h)

theorem gpow_Q (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) (k : ℤ)
    (hk : (x * a₀ * x⁻¹) ^ k ∈ Q) : (x * a₀ * x⁻¹) ^ k = 1 := by
  by_contra hne
  have h := invol_mem_zpowers (V := zpowers (x * a₀ * x⁻¹)) inferInstance (c.zpowers_g_pgroup ha₀)
    (Subgroup.zpow_mem _ (mem_zpowers _) k) hne (c.z'_mem_zpowers_g hgen) c.z'_sq c.z'_ne_one
  exact c.z'_not_Q ((zpowers_le.2 hk) h)

theorem V₁_comm_gpow (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) {v : G}
    (hv : v ∈ P ⊓ centralizer ({u₁} : Set G)) (k : ℤ) :
    v * (x * a₀ * x⁻¹) ^ k = (x * a₀ * x⁻¹) ^ k * v := by
  obtain ⟨k', hk'⟩ := c.W_norm_g ha₀ hgen (c.V₁_le_W hv) k
  have hgkS : (x * a₀ * x⁻¹) ^ k ∈ S := S.zpow_mem (c.g_mem_S ha₀) k
  have h1 : (x * a₀ * x⁻¹) ^ (k' - k) ∈ P := by
    have : (x * a₀ * x⁻¹) ^ (k' - k) = v * ((x * a₀ * x⁻¹) ^ k * v⁻¹ * ((x * a₀ * x⁻¹) ^ k)⁻¹) := by
      rw [zpow_sub, ← hk']; group
    rw [this]
    exact mul_mem hv.1 (c.cfg.P_norm _ hgkS _ (inv_mem hv.1))
  have h2 := c.gpow_P ha₀ hgen _ h1
  rw [zpow_sub, mul_inv_eq_one] at h2
  rw [h2] at hk'
  calc v * (x * a₀ * x⁻¹) ^ k = (v * (x * a₀ * x⁻¹) ^ k * v⁻¹) * v := by group
    _ = (x * a₀ * x⁻¹) ^ k * v := by rw [hk']

theorem V₂_comm_gpow (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) {v : G}
    (hv : v ∈ Q ⊓ centralizer ({u₂} : Set G)) (k : ℤ) :
    v * (x * a₀ * x⁻¹) ^ k = (x * a₀ * x⁻¹) ^ k * v := by
  obtain ⟨k', hk'⟩ := c.W_norm_g ha₀ hgen (c.V₂_le_W hv) k
  have hgkS : (x * a₀ * x⁻¹) ^ k ∈ S := S.zpow_mem (c.g_mem_S ha₀) k
  have h1 : (x * a₀ * x⁻¹) ^ (k' - k) ∈ Q := by
    have : (x * a₀ * x⁻¹) ^ (k' - k) = v * ((x * a₀ * x⁻¹) ^ k * v⁻¹ * ((x * a₀ * x⁻¹) ^ k)⁻¹) := by
      rw [zpow_sub, ← hk']; group
    rw [this]
    exact mul_mem hv.1 (c.cfg.Q_norm _ hgkS _ (inv_mem hv.1))
  have h2 := c.gpow_Q ha₀ hgen _ h1
  rw [zpow_sub, mul_inv_eq_one] at h2
  rw [h2] at hk'
  calc v * (x * a₀ * x⁻¹) ^ k = (v * (x * a₀ * x⁻¹) ^ k * v⁻¹) * v := by group
    _ = (x * a₀ * x⁻¹) ^ k * v := by rw [hk']

omit [Finite G] c in
theorem V₁_eq_zpowers (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) :
    P ⊓ centralizer ({u₁} : Set G) = zpowers a₀ :=
  le_antisymm (fun v hv => hgen v hv) (zpowers_le.2 ha₀)

omit [Finite G] c in
theorem orderOf_g (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) :
    orderOf (x * a₀ * x⁻¹) = Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := by
  have h1 : orderOf (x * a₀ * x⁻¹) = orderOf a₀ := by
    have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective a₀
    simpa using this
  rw [h1, ← Nat.card_zpowers, ← V₁_eq_zpowers ha₀ hgen]

theorem g_not_R (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) :
    x * a₀ * x⁻¹ ∉ P ⊔ Q := by
  intro hmem
  have hQnc : ∃ b ∈ Q, ∃ b' ∈ Q, b * b' ≠ b' * b := by
    obtain ⟨a, b, hab⟩ := quat_noncomm_group c.quatQ.choose_spec
    exact ⟨a, a.2, b, b.2, fun e => hab (Subtype.ext e)⟩
  have hb := cyc_bound (A := P) (B := Q) (C := zpowers (x * a₀ * x⁻¹)) (z := z) c.hz2 c.hz1
    c.cfg.z_P c.cfg.z_Q (fun a ha b hb => c.cfg.PQ_comm a ha b hb)
    (fun y hy hy' => c.cfg.PQ_inf y hy hy')
    (fun c' hc' a ha => c.cfg.P_norm c' (zpowers_le.2 (c.g_mem_S ha₀) hc') a ha) inferInstance
    (zpowers_le.2 hmem)
    (fun c' hc' hcP => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc'
      rw [← hk] at hcP ⊢
      exact c.gpow_P ha₀ hgen k hcP) hQnc
  rw [Nat.card_zpowers, orderOf_g ha₀ hgen] at hb
  have hP : Nat.card ↥P = 2 * Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := by
    have := Subgroup.relIndex_mul_card (P ⊓ centralizer ({u₁} : Set G)) P
    rw [c.V₁_idx, inf_of_le_left inf_le_left] at this
    exact this.symm
  have hpos : 0 < Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := Nat.card_pos
  have := c.card_eq
  omega

end Gen

theorem exists_notin_V₁ : ∃ p₀ ∈ P, p₀ ∉ P ⊓ centralizer ({u₁} : Set G) := by
  by_contra hcon
  push Not at hcon
  have h1 : (P ⊓ centralizer ({u₁} : Set G)).relIndex P = 1 :=
    Subgroup.relIndex_eq_one.2 (fun p hp => hcon p hp)
  have := c.V₁_idx
  omega

theorem exists_notin_V₂ : ∃ q₀ ∈ Q, q₀ ∉ Q ⊓ centralizer ({u₂} : Set G) := by
  by_contra hcon
  push Not at hcon
  have h1 : (Q ⊓ centralizer ({u₂} : Set G)).relIndex Q = 1 :=
    Subgroup.relIndex_eq_one.2 (fun p hp => hcon p hp)
  have := c.V₂_idx
  omega

theorem quatOut₁ : ∀ b ∈ P, b ∉ P ⊓ centralizer ({u₁} : Set G) → b * b = z ∧
    ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), b * v * b⁻¹ = v⁻¹ :=
  quat_outside_cyclic c.quatP.choose_spec c.cfg.z_P c.hz2 c.hz1 inf_le_left c.V₁_cyc c.V₁_idx

theorem quatOut₂ : ∀ b ∈ Q, b ∉ Q ⊓ centralizer ({u₂} : Set G) → b * b = z ∧
    ∀ v ∈ Q ⊓ centralizer ({u₂} : Set G), b * v * b⁻¹ = v⁻¹ :=
  quat_outside_cyclic c.quatQ.choose_spec c.cfg.z_Q c.hz2 c.hz1 inf_le_left c.V₂_cyc c.V₂_idx

theorem u₁_mem_V₁ : u₁ ∈ P ⊓ centralizer ({u₁} : Set G) :=
  ⟨c.u₁_mem, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem u₂_mem_V₂ : u₂ ∈ Q ⊓ centralizer ({u₂} : Set G) :=
  ⟨c.u₂_mem, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

end Setup9

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
