module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Proof
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Coord
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
import all CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6
public import CFSG.Fischer.Uniq.CompTau

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod

structure XFrame {X : Type} [Group X] [Finite X] (x e₂ e₃ t ρ : X) (s : ℤ) : Prop
    extends VITriple x e₂ e₃ where
  t_x : t * x * t⁻¹ = e₂
  t_e₂ : t * e₂ * t⁻¹ = e₃
  t_e₃ : t * e₃ * t⁻¹ = x
  ρ_x : ρ * x * ρ⁻¹ = x
  ρ_e₂ : ρ * e₂ * ρ⁻¹ = e₃ ^ s
  ρ_e₃ : ρ * e₃ * ρ⁻¹ = e₂ ^ (-s)
  s_cases : s = 1 ∨ s = -1

theorem vec_g1 (a b c : ZMod 3) : ((a, b, c) + (a, -b, -c) : Vec) = (a + a, 0, 0) := by
  revert a b c; decide

theorem vec_g2 (a b c : ZMod 3) : ((a, b, c) + (-a, b, -c) : Vec) = (0, b + b, 0) := by
  revert a b c; decide

theorem vec_g3 (a b c : ZMod 3) : ((a, b, c) + (-a, -b, c) : Vec) = (0, 0, c + c) := by
  revert a b c; decide

theorem vec_double_ne {a b c : ZMod 3} (h : ((a, b, c) : Vec) ≠ 0) :
    a + a ≠ 0 ∨ b + b ≠ 0 ∨ c + c ≠ 0 := by
  revert h; revert a b c; decide

def rot (v : Vec) : Vec := (v.2.2, v.1, v.2.1)

theorem exists_diag_comb (v : Vec) (hv : v ≠ 0) :
    ∃ α β γ : ZMod 3, mv α v + mv β (rot v) + mv γ (rot (rot v)) = (1, 1, 1) := by
  revert v; decide

namespace Tri

variable {X : Type} [Group X] [Finite X] {x e₂ e₃ : X}

theorem gp_eq_one_iff {g : X} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {a : ZMod 3} :
    gp g a = 1 ↔ a = 0 := by
  constructor
  · intro ha
    have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    have hdvd : orderOf g ∣ a.val := orderOf_dvd_of_pow_eq_one ha
    rw [hord] at hdvd
    have hlt : a.val < 3 := ZMod.val_lt a
    have h0 : a.val = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      omega
    exact (ZMod.val_eq_zero a).mp h0
  · rintro rfl
    exact gp_zero g

theorem mem_of_gp_mem {W : Subgroup X} {g : X} (hg3 : g ^ 3 = 1) {k : ZMod 3} (hk : k ≠ 0)
    (hgk : gp g k ∈ W) : g ∈ W := by
  have hkk' : ∀ k : ZMod 3, k ≠ 0 → k * k = 1 := by decide
  have hkk := hkk' k hk
  have := pow_mem hgk k.val
  have e : gp (gp g k) k = g := by rw [gp_gp hg3, hkk, gp_one hg3]
  rw [← e]
  exact this

variable (h : VITriple x e₂ e₃)

include h

theorem qel_add (a b : Vec) : qel x e₂ e₃ (a + b) = qel x e₂ e₃ a * qel x e₂ e₃ b := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  obtain ⟨b₁, b₂, b₃⟩ := b
  have c₁ : ∀ i j : ZMod 3, Commute (gp x i) (gp e₂ j) := fun i j =>
    Commute.pow_pow (show Commute x e₂ from h.comm_x₂) _ _
  have c₂ : ∀ i j : ZMod 3, Commute (gp x i) (gp e₃ j) := fun i j =>
    Commute.pow_pow (show Commute x e₃ from h.comm_x₃) _ _
  have c₃ : ∀ i j : ZMod 3, Commute (gp e₂ i) (gp e₃ j) := fun i j =>
    Commute.pow_pow (show Commute e₂ e₃ from h.comm_23) _ _
  simp only [qel, Prod.mk_add_mk, gp_add h.x_pow, gp_add h.e₂_pow, gp_add h.e₃_pow]
  exact (mul3 (c₁ _ _).symm (c₂ _ _).symm (c₃ _ _).symm).symm

theorem qel_zero : qel x e₂ e₃ 0 = 1 := by
  simp [qel, gp_zero]

theorem x_mem : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)

theorem e₂_mem : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))

theorem e₃_mem : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))

theorem Q_le_of_mem {W : Subgroup X} (hx : x ∈ W) (h₂ : e₂ ∈ W) (h₃ : e₃ ∈ W) :
    Qf x e₂ e₃ ≤ W :=
  sup_le (zpowers_le.mpr hx) (sup_le (zpowers_le.mpr h₂) (zpowers_le.mpr h₃))

theorem qel_mem (v : Vec) : qel x e₂ e₃ v ∈ Qf x e₂ e₃ :=
  mul_mem (mul_mem (mem_sup_left (pow_mem (mem_zpowers x) _))
    (mem_sup_right (mem_sup_left (pow_mem (mem_zpowers e₂) _))))
    (mem_sup_right (mem_sup_right (pow_mem (mem_zpowers e₃) _)))

theorem exists_qel {q : X} (hq : q ∈ Qf x e₂ e₃) : ∃ v : Vec, qel x e₂ e₃ v = q := by
  obtain ⟨a, ha, c, hc, rfl⟩ := u3l42_decomp h.x_T hq
  obtain ⟨b, hb, d, hd, rfl⟩ := u3l42_decomp h.T_comm_gen hc
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hd
  refine ⟨((i : ZMod 3), (j : ZMod 3), (k : ZMod 3)), ?_⟩
  simp only [qel]
  rw [← zpow_eq_gp h.x_pow, ← zpow_eq_gp h.e₂_pow, ← zpow_eq_gp h.e₃_pow, mul_assoc]

theorem qel_eq_one {v : Vec} (hv : qel x e₂ e₃ v = 1) : v = 0 := by
  obtain ⟨a, b, c⟩ := v
  simp only [qel] at hv
  have hA : gp x a ∈ zpowers x := pow_mem (mem_zpowers x) _
  have hB : gp e₂ b ∈ zpowers e₂ := pow_mem (mem_zpowers e₂) _
  have hC : gp e₃ c ∈ zpowers e₃ := pow_mem (mem_zpowers e₃) _
  have hBC : gp e₂ b * gp e₃ c ∈ zpowers e₂ ⊔ zpowers e₃ :=
    mul_mem (mem_sup_left hB) (mem_sup_right hC)
  have hxa : gp x a = (gp e₂ b * gp e₃ c)⁻¹ := by
    rw [mul_assoc] at hv
    exact eq_inv_of_mul_eq_one_left hv
  have h1 : gp x a = 1 := by
    have hmem : gp x a ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x :=
      Subgroup.mem_inf.mpr ⟨by rw [hxa]; exact inv_mem hBC, hA⟩
    rw [h.ind_x] at hmem
    exact mem_bot.mp hmem
  rw [h1, one_mul] at hv
  have hb : gp e₂ b = (gp e₃ c)⁻¹ := eq_inv_of_mul_eq_one_left hv
  have h2 : gp e₂ b = 1 := by
    have hmem : gp e₂ b ∈ zpowers e₂ ⊓ zpowers e₃ :=
      Subgroup.mem_inf.mpr ⟨hB, by rw [hb]; exact inv_mem hC⟩
    rw [h.ind_23] at hmem
    exact mem_bot.mp hmem
  rw [h2, one_mul] at hv
  rw [(gp_eq_one_iff h.x_pow h.x_ne).mp h1, (gp_eq_one_iff h.e₂_pow h.e₂_ne).mp h2,
    (gp_eq_one_iff h.e₃_pow h.e₃_ne).mp hv]
  rfl

theorem qel_inj {v w : Vec} (hvw : qel x e₂ e₃ v = qel x e₂ e₃ w) : v = w := by
  have h1 : qel x e₂ e₃ (v - w) * qel x e₂ e₃ w = qel x e₂ e₃ w := by
    rw [← qel_add h, sub_add_cancel, hvw]
  have h2 : qel x e₂ e₃ (v - w) = 1 := by
    have := congrArg (fun z => z * (qel x e₂ e₃ w)⁻¹) h1
    simpa using this
  exact sub_eq_zero.mp (qel_eq_one h h2)

theorem qel_mv_nat (v : Vec) (n : ℕ) : qel x e₂ e₃ (mv (n : ZMod 3) v) = qel x e₂ e₃ v ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, mv_zero, qel_zero h, pow_zero]
  | succ n ih => rw [Nat.cast_succ, mv_add, mv_one, qel_add h, ih, pow_succ]

theorem qel_mv_mem {W : Subgroup X} (v : Vec) (hv : qel x e₂ e₃ v ∈ W) (i : ZMod 3) :
    qel x e₂ e₃ (mv i v) ∈ W := by
  have : i = ((i.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val i).symm
  rw [this, qel_mv_nat h]
  exact pow_mem hv _

theorem qel_x : qel x e₂ e₃ (1, 0, 0) = x := by
  simp only [qel, gp_one h.x_pow, gp_zero, mul_one]

theorem qel_e₂ : qel x e₂ e₃ (0, 1, 0) = e₂ := by
  simp only [qel, gp_one h.e₂_pow, gp_zero, mul_one, one_mul]

theorem qel_e₃ : qel x e₂ e₃ (0, 0, 1) = e₃ := by
  simp only [qel, gp_one h.e₃_pow, gp_zero, one_mul]

theorem qel_diag : qel x e₂ e₃ (1, 1, 1) = x * e₂ * e₃ := by
  simp only [qel, gp_one h.x_pow, gp_one h.e₂_pow, gp_one h.e₃_pow]

theorem qel_neg (v : Vec) : qel x e₂ e₃ (-v) = (qel x e₂ e₃ v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have hv : ∀ w : Vec, -w + w = 0 := by decide
  rw [← qel_add h, hv, qel_zero h]

theorem conj_rot {t : X} (htx : t * x * t⁻¹ = e₂) (hte₂ : t * e₂ * t⁻¹ = e₃)
    (hte₃ : t * e₃ * t⁻¹ = x) (a b c : ZMod 3) :
    t * qel x e₂ e₃ (a, b, c) * t⁻¹ = qel x e₂ e₃ (c, a, b) := by
  simp only [qel]
  rw [conj_mul3, conj_gp, conj_gp, conj_gp, htx, hte₂, hte₃]
  have hc : Commute (gp x c) (gp e₂ a * gp e₃ b) :=
    (Commute.pow_pow (show Commute x e₂ from h.comm_x₂) _ _).mul_right
      (Commute.pow_pow (show Commute x e₃ from h.comm_x₃) _ _)
  rw [mul_assoc (gp x c)]
  exact hc.eq.symm

end Tri

namespace XFrame

variable {X : Type} [Group X] [Finite X] {x e₂ e₃ t ρ : X} {s : ℤ}
  (h : XFrame x e₂ e₃ t ρ s)

include h

theorem frame3 : Frame3 x e₂ e₃ t ρ s :=
  { x3 := h.x_pow, e₂3 := h.e₂_pow, e₃3 := h.e₃_pow, c₂ := h.comm_x₂, c₃ := h.comm_x₃,
    c₂₃ := h.comm_23, tx := h.t_x, te₂ := h.t_e₂, te₃ := h.t_e₃, ρx := h.ρ_x,
    ρe₂ := h.ρ_e₂, ρe₃ := h.ρ_e₃, s_cases := h.s_cases }

theorem x_mem : x ∈ Qf x e₂ e₃ := Tri.x_mem h.toVITriple

theorem e₂_mem : e₂ ∈ Qf x e₂ e₃ := Tri.e₂_mem h.toVITriple

theorem e₃_mem : e₃ ∈ Qf x e₂ e₃ := Tri.e₃_mem h.toVITriple

theorem Q_le_of_mem {W : Subgroup X} (hx : x ∈ W) (h₂ : e₂ ∈ W) (h₃ : e₃ ∈ W) :
    Qf x e₂ e₃ ≤ W :=
  Tri.Q_le_of_mem h.toVITriple hx h₂ h₃

theorem qel_mem (v : Vec) : qel x e₂ e₃ v ∈ Qf x e₂ e₃ := Tri.qel_mem h.toVITriple v

theorem exists_qel {q : X} (hq : q ∈ Qf x e₂ e₃) : ∃ v : Vec, qel x e₂ e₃ v = q :=
  Tri.exists_qel h.toVITriple hq

theorem qel_inj {v w : Vec} (hvw : qel x e₂ e₃ v = qel x e₂ e₃ w) : v = w :=
  Tri.qel_inj h.toVITriple hvw

theorem qel_mv_mem {W : Subgroup X} (v : Vec) (hv : qel x e₂ e₃ v ∈ W) (i : ZMod 3) :
    qel x e₂ e₃ (mv i v) ∈ W :=
  Tri.qel_mv_mem h.toVITriple v hv i

theorem qel_x : qel x e₂ e₃ (1, 0, 0) = x := Tri.qel_x h.toVITriple

theorem qel_e₂ : qel x e₂ e₃ (0, 1, 0) = e₂ := Tri.qel_e₂ h.toVITriple

theorem qel_e₃ : qel x e₂ e₃ (0, 0, 1) = e₃ := Tri.qel_e₃ h.toVITriple

theorem qel_diag : qel x e₂ e₃ (1, 1, 1) = x * e₂ * e₃ := Tri.qel_diag h.toVITriple


theorem all_mem_of_one {W : Subgroup X} (ht : ∀ w ∈ W, t * w * t⁻¹ ∈ W)
    (hone : x ∈ W ∨ e₂ ∈ W ∨ e₃ ∈ W) : x ∈ W ∧ e₂ ∈ W ∧ e₃ ∈ W := by
  have h1 : x ∈ W → e₂ ∈ W := fun hx => h.t_x ▸ ht x hx
  have h2 : e₂ ∈ W → e₃ ∈ W := fun he => h.t_e₂ ▸ ht e₂ he
  have h3 : e₃ ∈ W → x ∈ W := fun he => h.t_e₃ ▸ ht e₃ he
  rcases hone with hx | he | he
  · exact ⟨hx, h1 hx, h2 (h1 hx)⟩
  · exact ⟨h3 (h2 he), he, h2 he⟩
  · exact ⟨h3 he, h1 (h3 he), he⟩

theorem eq_bot_or_eq_of_invariant {W : Subgroup X} (hWQ : W ≤ Qf x e₂ e₃)
    (ht : ∀ w ∈ W, t * w * t⁻¹ ∈ W) (hρ : ∀ w ∈ W, ρ * w * ρ⁻¹ ∈ W) :
    W = ⊥ ∨ W = Qf x e₂ e₃ := by
  rcases W.bot_or_exists_ne_one with hbot | ⟨w, hwW, hw1⟩
  · exact Or.inl hbot
  right
  obtain ⟨⟨a, b, c⟩, hv⟩ := h.exists_qel (hWQ hwW)
  have hF := h.frame3
  have hcj : ∀ g : X, (∀ w ∈ W, g * w * g⁻¹ ∈ W) → ∀ g' : X, (∀ w ∈ W, g' * w * g'⁻¹ ∈ W) →
      ∀ w ∈ W, (g * g') * w * (g * g')⁻¹ ∈ W := by
    intro g hg g' hg' w hw
    have e : (g * g') * w * (g * g')⁻¹ = g * (g' * w * g'⁻¹) * g⁻¹ := by group
    rw [e]
    exact hg _ (hg' w hw)
  have htinv : ∀ w ∈ W, t⁻¹ * w * t⁻¹⁻¹ ∈ W := by
    have hfin : ∀ w ∈ W, (t * t) * w * (t * t)⁻¹ ∈ W := hcj t ht t ht
    intro w hw
    have e : t⁻¹ * w * t⁻¹⁻¹ = (t * t) * (t⁻¹ * (t⁻¹ * (t⁻¹ * w * t) * t) * t) * (t * t)⁻¹ := by
      group
    have e3 : t⁻¹ * (t⁻¹ * (t⁻¹ * w * t) * t) * t = (t * t * t)⁻¹ * w * (t * t * t) := by group
    have ht3 : ∀ q ∈ Qf x e₂ e₃, (t * t * t) * q * (t * t * t)⁻¹ = q := by
      intro q hq
      obtain ⟨⟨a', b', c'⟩, rfl⟩ := h.exists_qel hq
      have e1 : (t * t * t) * qel x e₂ e₃ (a', b', c') * (t * t * t)⁻¹ =
          t * (t * (t * qel x e₂ e₃ (a', b', c') * t⁻¹) * t⁻¹) * t⁻¹ := by group
      rw [e1, hF.conj_t, hF.conj_t, hF.conj_t]
    have hw' : (t * t * t)⁻¹ * w * (t * t * t) = w := by
      have := ht3 w (hWQ hw)
      calc (t * t * t)⁻¹ * w * (t * t * t)
          = (t * t * t)⁻¹ * ((t * t * t) * w * (t * t * t)⁻¹) * (t * t * t) := by rw [this]
        _ = w := by group
    rw [e, e3, hw']
    exact hfin w hw
  have hg1 : ∀ w ∈ W, (ρ * ρ) * w * (ρ * ρ)⁻¹ ∈ W := hcj ρ hρ ρ hρ
  have hg2 : ∀ w ∈ W, (t * (ρ * ρ) * t⁻¹) * w * (t * (ρ * ρ) * t⁻¹)⁻¹ ∈ W :=
    hcj (t * (ρ * ρ)) (hcj t ht (ρ * ρ) hg1) t⁻¹ htinv
  have hg3 : ∀ w ∈ W, (t * (t * (ρ * ρ) * t⁻¹) * t⁻¹) * w *
      (t * (t * (ρ * ρ) * t⁻¹) * t⁻¹)⁻¹ ∈ W :=
    hcj (t * (t * (ρ * ρ) * t⁻¹)) (hcj t ht _ hg2) t⁻¹ htinv
  rw [← hv] at hwW
  have hv0 : ((a, b, c) : Vec) ≠ 0 := by
    intro h0
    apply hw1
    rw [← hv, h0, hF.qel_zero]
  have k1 : qel x e₂ e₃ (a + a, 0, 0) ∈ W := by
    have := W.mul_mem hwW (hg1 _ hwW)
    rw [hF.conj_g1, ← hF.qel_add] at this
    rwa [vec_g1] at this
  have k2 : qel x e₂ e₃ (0, b + b, 0) ∈ W := by
    have := W.mul_mem hwW (hg2 _ hwW)
    rw [hF.conj_g2, ← hF.qel_add] at this
    rwa [vec_g2] at this
  have k3 : qel x e₂ e₃ (0, 0, c + c) ∈ W := by
    have := W.mul_mem hwW (hg3 _ hwW)
    rw [hF.conj_g3, ← hF.qel_add] at this
    rwa [vec_g3] at this
  have hone : x ∈ W ∨ e₂ ∈ W ∨ e₃ ∈ W := by
    have hcase : a + a ≠ 0 ∨ b + b ≠ 0 ∨ c + c ≠ 0 := vec_double_ne hv0
    rcases hcase with ha | hb | hc
    · left
      refine Tri.mem_of_gp_mem h.x_pow ha ?_
      simpa [qel, gp_zero] using k1
    · right; left
      refine Tri.mem_of_gp_mem h.e₂_pow hb ?_
      simpa [qel, gp_zero] using k2
    · right; right
      refine Tri.mem_of_gp_mem h.e₃_pow hc ?_
      simpa [qel, gp_zero] using k3
  obtain ⟨hx, h₂, h₃⟩ := h.all_mem_of_one ht hone
  exact le_antisymm hWQ (h.Q_le_of_mem hx h₂ h₃)

theorem t_mem_normalizer : t ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X) := by
  apply GL83P3A6Core.mem_normalizer_of_map_le
  rw [Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le ?_ (sup_le ?_ ?_)
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h.t_x]
    exact le_sup_of_le_right le_sup_left
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h.t_e₂]
    exact le_sup_of_le_right le_sup_right
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h.t_e₃]
    exact le_sup_left

theorem ρ_mem_normalizer : ρ ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X) := by
  apply GL83P3A6Core.mem_normalizer_of_map_le
  rw [Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le ?_ (sup_le ?_ ?_)
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h.ρ_x]
    exact le_sup_left
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h.ρ_e₂]
    exact le_sup_of_le_right (le_sup_of_le_right (zpowers_le.mpr (zpow_mem_zpowers e₃ s)))
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h.ρ_e₃]
    exact le_sup_of_le_right (le_sup_of_le_left (zpowers_le.mpr (zpow_mem_zpowers e₂ (-s))))

theorem conj_mem_of_mem_normalizer {g q : X}
    (hg : g ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X)) (hq : q ∈ Qf x e₂ e₃) :
    g * q * g⁻¹ ∈ Qf x e₂ e₃ :=
  (mem_normalizer_iff.mp hg q).mp hq

theorem diag_mem_of_t_invariant {W : Subgroup X} (hWQ : W ≤ Qf x e₂ e₃) (hW : W ≠ ⊥)
    (ht : ∀ w ∈ W, t * w * t⁻¹ ∈ W) : x * e₂ * e₃ ∈ W := by
  obtain ⟨w, hwW, hw1⟩ := (W.bot_or_exists_ne_one).resolve_left hW
  obtain ⟨⟨a, b, c⟩, rfl⟩ := h.exists_qel (hWQ hwW)
  have hF := h.frame3
  have hv0 : ((a, b, c) : Vec) ≠ 0 := by
    intro h0
    apply hw1
    rw [h0, hF.qel_zero]
  have h1 : qel x e₂ e₃ (c, a, b) ∈ W := by
    have := ht _ hwW
    rwa [hF.conj_t] at this
  have h2 : qel x e₂ e₃ (b, c, a) ∈ W := by
    have := ht _ h1
    rwa [hF.conj_t] at this
  obtain ⟨α, β, γ, hαβγ⟩ := exists_diag_comb (a, b, c) hv0
  have hsum := W.mul_mem (W.mul_mem (h.qel_mv_mem _ hwW α) (h.qel_mv_mem _ h1 β))
    (h.qel_mv_mem _ h2 γ)
  rw [← hF.qel_add, ← hF.qel_add] at hsum
  have e : mv α (a, b, c) + mv β (c, a, b) + mv γ (b, c, a) = (1, 1, 1) := hαβγ
  rw [e, h.qel_diag] at hsum
  exact hsum

theorem inf_ne_bot {P S : Subgroup X} (hcent : ∀ g ∈ P, g * x = x * g → g ∈ Qf x e₂ e₃)
    (hPQ : P ≤ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X)) (hSP : S ≤ P) (hS : S ≠ ⊥)
    (hQS : Qf x e₂ e₃ ≤ normalizer (S : Set X)) : S ⊓ Qf x e₂ e₃ ≠ ⊥ := by
  intro hbot
  apply hS
  rw [eq_bot_iff]
  intro g hg
  have hc : g * x * g⁻¹ * x⁻¹ ∈ S ⊓ Qf x e₂ e₃ := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
      rw [e]
      exact S.mul_mem hg ((mem_normalizer_iff.mp (hQS h.x_mem) g⁻¹).mp (S.inv_mem hg))
    · exact (Qf x e₂ e₃).mul_mem ((mem_normalizer_iff.mp (hPQ (hSP hg)) x).mp h.x_mem)
        ((Qf x e₂ e₃).inv_mem h.x_mem)
  rw [hbot, mem_bot] at hc
  have hgx : g * x = x * g := by
    have := congrArg (fun z => z * x * g) hc
    simp only [one_mul] at this
    calc g * x = g * x * g⁻¹ * x⁻¹ * x * g := by group
      _ = x * g := this
  have hgQ : g ∈ S ⊓ Qf x e₂ e₃ := Subgroup.mem_inf.mpr ⟨hg, hcent g (hSP hg) hgx⟩
  rw [hbot] at hgQ
  exact hgQ

theorem e₃_eq : (t * t) * x * (t * t)⁻¹ = e₃ := by
  rw [show (t * t) * x * (t * t)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ by group, h.t_x, h.t_e₂]

theorem map_conj_zpowers (g : X) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem lines_ne : zpowers x ≠ zpowers e₂ ∧ zpowers x ≠ zpowers e₃ ∧ zpowers e₂ ≠ zpowers e₃ := by
  refine ⟨fun he => ?_, fun he => ?_, fun he => h.e₃_nmem (he ▸ mem_zpowers e₃)⟩
  · have h1 : e₂ ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x :=
      Subgroup.mem_inf.mpr ⟨mem_sup_left (mem_zpowers e₂), he ▸ mem_zpowers e₂⟩
    rw [h.ind_x, mem_bot] at h1
    exact h.e₂_ne h1
  · have h1 : e₃ ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x :=
      Subgroup.mem_inf.mpr ⟨mem_sup_right (mem_zpowers e₃), he ▸ mem_zpowers e₃⟩
    rw [h.ind_x, mem_bot] at h1
    exact h.e₃_ne h1

theorem conjLinesIn_eq_three
    (hlines : ∀ g : X, g * x * g⁻¹ ∈ Qf x e₂ e₃ →
      g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers e₂ ∨ g * x * g⁻¹ ∈ zpowers e₃) :
    conjLinesIn (Qf x e₂ e₃) x = 3 := by
  obtain ⟨h12, h13, h23⟩ := h.lines_ne
  have hset : {c : Subgroup X | ∃ g : X, c = (zpowers x).map (MulAut.conj g).toMonoidHom ∧
      c ≤ Qf x e₂ e₃} = {zpowers x, zpowers e₂, zpowers e₃} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl, hle⟩
      rw [h.map_conj_zpowers g] at hle ⊢
      have hgQ : g * x * g⁻¹ ∈ Qf x e₂ e₃ := zpowers_le.mp hle
      have hg1 : g * x * g⁻¹ ≠ 1 := by
        intro h1
        apply h.x_ne
        have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this, h1]; group
      rcases hlines g hgQ with hl | hl | hl
      · exact Or.inl (zpowers_eq_of_mem h.x_pow h.x_ne hl hg1)
      · exact Or.inr (Or.inl (zpowers_eq_of_mem h.e₂_pow h.e₂_ne hl hg1))
      · exact Or.inr (Or.inr (zpowers_eq_of_mem h.e₃_pow h.e₃_ne hl hg1))
    · rintro (rfl | rfl | rfl)
      · refine ⟨1, ?_, zpowers_le.mpr h.x_mem⟩
        rw [h.map_conj_zpowers 1]
        simp
      · refine ⟨t, ?_, zpowers_le.mpr h.e₂_mem⟩
        rw [h.map_conj_zpowers t, h.t_x]
      · refine ⟨t * t, ?_, zpowers_le.mpr h.e₃_mem⟩
        rw [h.map_conj_zpowers (t * t), h.e₃_eq]
  unfold conjLinesIn
  rw [hset]
  exact Set.ncard_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩

theorem thompsonSubgroup_eq {P : Subgroup X}
    (e : P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) (hQP : Qf x e₂ e₃ ≤ P) :
    thompsonSubgroup P = Qf x e₂ e₃ := by
  have hJA := thompsonSubgroup_le_map_ker e
  set A₁ : Subgroup X := (RegularWreathProduct.rightHom : Multiplicative (ZMod 3) ≀ᵣ
      Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker.map
        (P.subtype.comp e.symm.toMonoidHom) with hA₁
  have hinj : Function.Injective (P.subtype.comp e.symm.toMonoidHom) :=
    P.subtype_injective.comp e.symm.injective
  have hA₁card : Nat.card A₁ = 27 :=
    (Subgroup.card_map_of_injective hinj).trans wreath_card_ker
  have hQc : IsMulCommutative (Qf x e₂ e₃) := h.Q_el.1
  have hQ27 : Nat.card (Qf x e₂ e₃) = 27 := h.Q_card
  obtain ⟨A₀, ⟨hA₀P, hA₀c⟩, hmax⟩ := Set.exists_max_image
    {A : Subgroup X | A ≤ P ∧ IsMulCommutative A} (fun A : Subgroup X => Nat.card A)
    (Set.toFinite _) ⟨⊥, bot_le, ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩⟩
  have hmax' : ∀ B : Subgroup X, B ≤ P → IsMulCommutative B → Nat.card B ≤ Nat.card A₀ :=
    fun B hB hBc => hmax B ⟨hB, hBc⟩
  have hA₀J : A₀ ≤ thompsonSubgroup P := CFSG.le_ambientMaxCardThompson ⟨hA₀P, hA₀c, hmax'⟩
  have hA₀le : Nat.card A₀ ≤ 27 := by
    rw [← hA₁card]
    exact Subgroup.card_le_of_le (hA₀J.trans hJA)
  have hQJ : Qf x e₂ e₃ ≤ thompsonSubgroup P :=
    CFSG.le_ambientMaxCardThompson ⟨hQP, hQc, fun B hB hBc => (hmax' B hB hBc).trans
      (hA₀le.trans hQ27.ge)⟩
  refine (Subgroup.eq_of_le_of_card_ge hQJ ?_).symm
  rw [hQ27, ← hA₁card]
  exact Subgroup.card_le_of_le hJA

end XFrame

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
