module

public import CFSG.GH74.GLS.LU.Local.FiveL88c
public import CFSG.GH74.GLS.LU.Local.FiveL85c
public import CFSG.GH74.GLS.LU.Local.FiveL88a
public import CFSG.GH74.GLS.LU.Local.FiveL88b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L88d

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg.X4_inf_X6 (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    X4 v t X₁ ⊓ X6 v t w₁ X₁ = ⊥ := by
  apply eq_bot_iff.mpr
  calc X4 v t X₁ ⊓ X6 v t w₁ X₁ ≤ (XB t X₁ ⊔ Y) ⊓ cjL w₁ Y :=
        inf_le_inf (c.X4_le_Y.trans le_sup_right) c.X6_le_Y'
    _ = ⊥ := c.W_inf_Y'

theorem Cfg8.mem_E (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) {e : G} (he : e ∈ EE v t w₁ X₁) :
    ∃ a ∈ XB t X₁, ∃ b ∈ X4 v t X₁, ∃ d ∈ X6 v t w₁ X₁, a * b * d = e := by
  have hE := c.E_comm c.b86
  obtain ⟨x, hx, d, hd, rfl⟩ := (mem_sup_of_commute (A := XB t X₁ ⊔ X4 v t X₁) (B := X6 v t w₁ X₁)
    (fun a ha b hb => hE a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb))).mp he
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute (A := XB t X₁) (B := X4 v t X₁)
    (fun a ha b hb => (c.X2_central b (c.X4_le_R2 hb) a ha).symm)).mp hx
  exact ⟨a, ha, b, hb, d, hd, rfl⟩

theorem Cfg8.E_inf_Cz (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    EE v t w₁ X₁ ⊓ centralizer ({z} : Set G) = XB t X₁ := by
  apply le_antisymm
  · rintro e ⟨he, hez⟩
    obtain ⟨a, ha, b, hb, d, hd, rfl⟩ := c.mem_E he
    have hez' : (a * b * d) * z = z * (a * b * d) := Subgroup.mem_centralizer_singleton_iff.mp hez
    have hza : z * a * z⁻¹ = a := by
      have := c.hc.cz₂ (c.X2_le_K2 ha)
      calc z * a * z⁻¹ = (a * z) * z⁻¹ := by rw [this]
        _ = a := by group
    have hzb : z * b * z⁻¹ = b⁻¹ := c.z_inv_Y b (c.X4_le_Y hb)
    have hzd : z * d * z⁻¹ = d⁻¹ := c.z_inv_Yw d (c.X6_le_Y' hd)
    have h1 : a * b * d = a * b⁻¹ * d⁻¹ := by
      calc a * b * d = (a * b * d) * z * z⁻¹ := by group
        _ = z * (a * b * d) * z⁻¹ := by rw [hez']
        _ = (z * a * z⁻¹) * (z * b * z⁻¹) * (z * d * z⁻¹) := by group
        _ = a * b⁻¹ * d⁻¹ := by rw [hza, hzb, hzd]
    have h2 : b * d = b⁻¹ * d⁻¹ := by
      apply mul_left_cancel (a := a)
      simpa only [mul_assoc] using h1
    have h3 : (b * b) * (d * d) = 1 := by
      calc (b * b) * (d * d) = b * (b * d) * d := by group
        _ = b * (b⁻¹ * d⁻¹) * d := by rw [h2]
        _ = 1 := by group
    have h4 : b * b = 1 := by
      have h6 : b * b ∈ X6 v t w₁ X₁ := by
        have e : b * b = (d * d)⁻¹ := eq_inv_of_mul_eq_one_left h3
        rw [e]
        exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hd hd)
      have hmem : b * b ∈ X4 v t X₁ ⊓ X6 v t w₁ X₁ :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hb hb, h6⟩
      rw [c.X4_inf_X6] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h5 : d * d = 1 := by rw [h4, one_mul] at h3; exact h3
    have hb1 : b = 1 := by
      have hb5 : b ^ 5 = 1 := pow_five_of_card c.card_X4 hb
      calc b = b ^ 5 * ((b * b)⁻¹) ^ 2 := by group
        _ = 1 := by rw [hb5, h4]; simp
    have hd1 : d = 1 := by
      have hd5 : d ^ 5 = 1 := pow_five_of_card c.card_X6 hd
      calc d = d ^ 5 * ((d * d)⁻¹) ^ 2 := by group
        _ = 1 := by rw [hd5, h5]; simp
    rw [hb1, hd1, mul_one, mul_one]
    exact ha
  · intro x hx
    exact ⟨c.X2_le_E hx, Subgroup.mem_centralizer_singleton_iff.mpr (c.hc.cz₂ (c.X2_le_K2 hx))⟩

theorem Cfg8.QQ_five (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    IsPGroup 5 ↥(QQ (EE v t w₁ X₁)) :=
  isPGroup_five_of_noInv c.H_two (QQ_odd _)
    (fun _ hh => cjL_eq_of_mem_normalizer (normalizer_le_normalizer_QQ _ (c.H_N hh)))
    c.b82.no_inv_sub

theorem Cfg8.CQ_z (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    QQ (EE v t w₁ X₁) ⊓ centralizer ({z} : Set G) ≤ XB t X₁ := by
  have hCz : ∀ k ∈ K₁, k ∈ centralizer ({z} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c.hc.cz₁ hk)
  have hmemX : ∀ y : G, y ∈ XB t X₁ ↔ y ∈ EE v t w₁ X₁ ∧ y ∈ centralizer ({z} : Set G) := fun y => by
    rw [← Subgroup.mem_inf, c.E_inf_Cz]
  refine c.five_le_X2 (A := QQ (EE v t w₁ X₁) ⊓ centralizer ({z} : Set G))
    (c.QQ_five.to_le inf_le_left) ?_ inf_le_right ?_
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := (Subgroup.mem_normalizer_iff.mp (QQ_le _ ha.1)) y
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ha.2)) y
    constructor
    · intro hy
      exact (hmemX _).mpr ⟨h1.mp ((hmemX y).mp hy).1, h2.mp ((hmemX y).mp hy).2⟩
    · intro hy
      exact (hmemX y).mpr ⟨h1.mpr ((hmemX _).mp hy).1, h2.mpr ((hmemX _).mp hy).2⟩
  · intro k hk b hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_QQ _ (c.K1_N hk)) b).mp hb.1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hCz k hk) hb.2) (Subgroup.inv_mem _ (hCz k hk))

theorem Cfg8.CQ_conj (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) {g y : G}
    (hg : g ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) (hgy : g * z * g⁻¹ = y) :
    QQ (EE v t w₁ X₁) ⊓ centralizer ({y} : Set G) ≤ cjL g (XB t X₁) := by
  rintro a ⟨haQ, hay⟩
  rw [mem_cjL]
  apply c.CQ_z
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_QQ _ (inv_mem hg)) a).mp haQ
    simpa using this
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hay
    rw [← hgy] at h1
    calc g⁻¹ * a * g * z = g⁻¹ * (a * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * a) * g := by rw [h1]
      _ = z * (g⁻¹ * a * g) := by group

theorem Cfg8.CQ_u (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    QQ (EE v t w₁ X₁) ⊓ centralizer ({u} : Set G) ≤ X6 v t w₁ X₁ := by
  rw [X6_eq]
  exact c.CQ_conj c.P_N c.g_z

theorem Cfg8.CQ_zu (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    QQ (EE v t w₁ X₁) ⊓ centralizer ({z * u} : Set G) ≤ X4 v t X₁ :=
  c.CQ_conj c.v_N c.b84.v_z

theorem Cfg8.QQ_eq (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    QQ (EE v t w₁ X₁) = EE v t w₁ X₁ := by
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hu1 : u ≠ 1 := by
    intro h
    have := c.hs.u_ord
    rw [h, orderOf_one] at this
    omega
  have hzN : z ∈ normalizer ((QQ (EE v t w₁ X₁) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_QQ _ (c.NG_X2_le_N c.z_mem_M)
  have huN : u ∈ normalizer ((QQ (EE v t w₁ X₁) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_QQ _ (c.H_N c.b66.u_mem)
  have hBW := CFSG.Walter.J1.card_mul_card_sq_eq_mul hz2 hu2 c.z_ne_one hu1 (Ne.symm c.hs.u_ne)
    c.hs.zu_comm (QQ (EE v t w₁ X₁)) hzN huN (QQ_odd _)
  have h1 : Nat.card ↥(QQ (EE v t w₁ X₁) ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 5 :=
    (Subgroup.card_le_of_le c.CQ_z).trans c.card_X2.le
  have h2 : Nat.card ↥(QQ (EE v t w₁ X₁) ⊓ centralizer ({u} : Set G) : Subgroup G) ≤ 5 :=
    (Subgroup.card_le_of_le c.CQ_u).trans c.card_X6.le
  have h3 : Nat.card ↥(QQ (EE v t w₁ X₁) ⊓ centralizer ({z * u} : Set G) : Subgroup G) ≤ 5 :=
    (Subgroup.card_le_of_le c.CQ_zu).trans c.card_X4.le
  have hle : Nat.card ↥(QQ (EE v t w₁ X₁)) ≤ 125 := by
    have hpos : 0 < Nat.card ↥(QQ (EE v t w₁ X₁) ⊓ centralizer ({z} : Set G) ⊓
        centralizer ({u} : Set G) : Subgroup G) ^ 2 := by
      have := Nat.card_pos (α := ↥(QQ (EE v t w₁ X₁) ⊓ centralizer ({z} : Set G) ⊓
        centralizer ({u} : Set G) : Subgroup G))
      positivity
    have h4 : Nat.card ↥(QQ (EE v t w₁ X₁)) ≤ Nat.card ↥(QQ (EE v t w₁ X₁)) *
        Nat.card ↥(QQ (EE v t w₁ X₁) ⊓ centralizer ({z} : Set G) ⊓
          centralizer ({u} : Set G) : Subgroup G) ^ 2 :=
      Nat.le_mul_of_pos_right _ hpos
    have h5 := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega
  have hE : Nat.card ↥(EE v t w₁ X₁) = 125 := by rw [c.E_card c.b86]; norm_num
  have hodd : Odd (Nat.card ↥(EE v t w₁ X₁)) := by rw [hE]; decide
  exact (Subgroup.eq_of_le_of_card_ge (le_QQ hodd) (by rw [hE]; exact hle)).symm

end L88d

end CFSG.GH74.GLS.LU.Local.Five
