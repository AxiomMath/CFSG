module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDC0

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Data

variable (d : Data G)

@[expose] def normJ (y : G) : G := y * (d.j₀ * y * d.j₀⁻¹) * (d.j₀ * (d.j₀ * y * d.j₀⁻¹) * d.j₀⁻¹)

abbrev Z₂S : Subgroup G := d.X₈ ⊔ zpowers d.z

end Data

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem x₃_cent_V₁ [Finite G] : d.x₃ ∈ centralizer (d.V₁ : Set G) :=
  h.K₁_le_cent_V₁ h.x₃_mem_K₁

theorem D_le_cent_x₃ [Finite G] : d.D ≤ centralizer ({d.x₃} : Set G) := by
  have hx₃L : d.x₃ ∈ d.L := h.Sig_le_L h.x₃_mem_Sig
  have hx₃A : d.x₃ ∈ centralizer (d.A₄ : Set G) := h.Sig_le_cent_A₄ h.x₃_mem_Sig
  have hx₃t : d.x₃ * d.t = d.t * d.x₃ := h.comm_of_mem_L hx₃L
  have hΛx : ∀ l ∈ d.Λ, l * d.x₃ = d.x₃ * l := fun l hl => h.Λ_comm_Sig l hl _ h.x₃_mem_Sig
  let R : Subgroup G :=
    { carrier := {b | ∃ c ∈ d.D ⊓ centralizer ({d.x₃} : Set G), c⁻¹ * d.t * c * d.t = b}
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, mul_mem hp hq, h.crossed_U₄_mul (h.D_le_U₄ hp.1) (h.D_le_U₄ hq.1)⟩
      inv_mem' := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p⁻¹, inv_mem hp, h.crossed_U₄_inv (h.D_le_U₄ hp.1)⟩ }
  have horb : (fun l => l * d.z * l⁻¹) '' (d.Λ : Set G) ⊆ R := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
    have hlX := h.Λ_le_X₄ hl
    have hlt : l * d.t = d.t * l := h.comm_of_mem_L (h.Λ_le_L hl)
    refine ⟨l * v * l⁻¹, mem_inf.mpr ⟨(mem_normalizer_iff.mp (h.X₄_le_normalizer_D hlX) v).mp
      (h.V₁_le_D hv), ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have hxv : d.x₃ * v = v * d.x₃ := (mem_centralizer_iff.mp h.x₃_cent_V₁ v hv).symm
      calc l * v * l⁻¹ * d.x₃ = l * (v * (l⁻¹ * d.x₃)) := by group
        _ = l * (v * (d.x₃ * l⁻¹)) := by
            rw [show l⁻¹ * d.x₃ = d.x₃ * l⁻¹ by
              calc l⁻¹ * d.x₃ = l⁻¹ * (d.x₃ * l) * l⁻¹ := by group
                _ = l⁻¹ * (l * d.x₃) * l⁻¹ := by rw [hΛx l hl]
                _ = d.x₃ * l⁻¹ := by group]
        _ = l * ((v * d.x₃) * l⁻¹) := by group
        _ = l * ((d.x₃ * v) * l⁻¹) := by rw [hxv]
        _ = (l * d.x₃) * v * l⁻¹ := by group
        _ = d.x₃ * (l * v * l⁻¹) := by rw [hΛx l hl]; group
    · rw [crossed_conj hlt, hvt, mul_assoc d.z d.t d.t, h.t_sq, mul_one]
  have hA₄R : d.A₄ ≤ R := h.A₄_le_orbit_z.trans ((closure_le R).mpr horb)
  intro x hx
  obtain ⟨c, hc, hcx⟩ := hA₄R (h.crossed_X₄ (D_le_X₄ hx))
  obtain ⟨hcD, hcx₃⟩ := mem_inf.mp hc
  have hxc : x * c⁻¹ ∈ d.withT d.A₄ := by
    rw [← h.D_inf_H]
    refine mem_inf.mpr ⟨mul_mem hx (inv_mem hcD), ?_⟩
    change x * c⁻¹ ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have e1 : x⁻¹ * d.t * x = c⁻¹ * d.t * c := mul_right_cancel hcx.symm
    calc x * c⁻¹ * d.t = x * (c⁻¹ * d.t * c) * c⁻¹ := by group
      _ = x * (x⁻¹ * d.t * x) * c⁻¹ := by rw [e1]
      _ = d.t * (x * c⁻¹) := by group
  have hwx : x * c⁻¹ ∈ centralizer ({d.x₃} : Set G) := by
    have hle : d.withT d.A₄ ≤ centralizer ({d.x₃} : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp hx₃A a ha)
      · rw [zpowers_le, mem_centralizer_singleton_iff]
        exact hx₃t.symm
    exact hle hxc
  have e : x = (x * c⁻¹) * c := by group
  rw [e]
  exact mul_mem hwx hcx₃

theorem D_le_cent_A₂ [Finite G] : d.D ≤ centralizer (d.A₂ : Set G) := by
  intro x hx
  have h1 : x ∈ centralizer ((zpowers d.x₃ ⊔ d.A₃ : Subgroup G) : Set G) := by
    refine mem_centralizer_sup ?_ (h.D_le_cent_A₃ hx)
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have hxx : d.x₃ * x = x * d.x₃ := (mem_centralizer_singleton_iff.mp (h.D_le_cent_x₃ hx)).symm
    exact Commute.zpow_left (show Commute d.x₃ x from hxx) k
  exact centralizer_le h.A₂_le_x₃ h1

theorem D_le_C₂ [Finite G] : d.D ≤ d.C₂ := by
  intro x hx
  refine h.C₂_max (mem_inf.mpr ⟨?_, h.D_le_cent_A₂ hx⟩)
  have hxA := h.D_le_cent_A₂ hx
  have hle : d.withT d.A₂ ≤ (d.withT d.A₂).comap (MulAut.conj x⁻¹).toMonoidHom := by
    refine sup_le (fun a ha => ?_) ?_
    · change x⁻¹ * a * x⁻¹⁻¹ ∈ d.withT d.A₂
      rw [inv_inv, mul_assoc, mem_centralizer_iff.mp hxA a ha, ← mul_assoc, inv_mul_cancel,
        one_mul]
      exact le_withT _ ha
    · rw [zpowers_le]
      change x⁻¹ * d.t * x⁻¹⁻¹ ∈ d.withT d.A₂
      rw [inv_inv]
      have hc := h.crossed_X₄ (D_le_X₄ hx)
      have e : x⁻¹ * d.t * x = (x⁻¹ * d.t * x * d.t) * d.t := by
        rw [mul_assoc _ d.t d.t, h.t_sq, mul_one]
      rw [e]
      exact mul_mem (le_withT _ (h.A₄_le_A₂ hc)) (t_mem_withT _)
  have hx' : x⁻¹ ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun y hy => hle hy
  simpa using inv_mem hx'

theorem D₄_le_C₂ [Finite G] : d.D₄ ≤ d.C₂ := h.D₄_le_D.trans h.D_le_C₂

theorem V₁_le_C₂ [Finite G] : d.V₁ ≤ d.C₂ := h.V₁_le_D.trans h.D_le_C₂

theorem j₀_mem_X₄ [Finite G] : d.j₀ ∈ d.X₄ :=
  h.NLA₃_le_X₄ (mem_inf.mpr ⟨h.j₀_mem_L, h.j₀_norm_A₃⟩)

theorem J_le_X₄ [Finite G] : d.J ≤ d.X₄ := by rw [h.J_eq, zpowers_le]; exact h.j₀_mem_X₄

theorem X₁_eq : d.X₁ = closure {d.u₁, d.u₂} := by
  refine le_antisymm h.X₁_le_closure ((closure_le _).mpr ?_)
  rintro x (rfl | rfl)
  · exact h.u₁_mem
  · exact h.u₂_mem

theorem j₀_mem_normalizer_X₁ [Finite G] : d.j₀ ∈ normalizer (d.X₁ : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : d.X₁ ≤ d.X₁.comap (MulAut.conj d.j₀).toMonoidHom := by
    rw [h.X₁_eq, closure_le]
    rintro x (rfl | rfl)
    · change d.j₀ * d.u₁ * d.j₀⁻¹ ∈ closure {d.u₁, d.u₂}
      rw [h.j₀_u₁]; exact subset_closure (by simp)
    · change d.j₀ * d.u₂ * d.j₀⁻¹ ∈ closure {d.u₁, d.u₂}
      rw [h.j₀_u₂]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  exact fun y hy => hle hy

theorem j₀_mem_normalizer_V₁ [Finite G] : d.j₀ ∈ normalizer (d.V₁ : Set G) :=
  mem_normalizer_of_conj_mem fun v hv => mem_inf.mpr
    ⟨(mem_normalizer_iff.mp (h.X₄_le_normalizer_D₄ h.j₀_mem_X₄) v).mp (mem_inf.mp hv).1,
      conj_mem_centralizer h.j₀_mem_normalizer_X₁ (mem_inf.mp hv).2⟩

theorem J_le_normalizer_D₄ [Finite G] : d.J ≤ normalizer (d.D₄ : Set G) :=
  h.J_le_X₄.trans h.X₄_le_normalizer_D₄

theorem comm_D₄_J_le [Finite G] : ⁅d.D₄, d.J⁆ ≤ d.D₄ := by
  rw [commutator_le]
  intro y hy g hg
  rw [commutatorElement_def, show y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) by group]
  exact mul_mem hy ((mem_normalizer_iff.mp (h.J_le_normalizer_D₄ hg) _).mp (inv_mem hy))

theorem j₀_mem_J : d.j₀ ∈ d.J := by rw [h.J_eq]; exact mem_zpowers _

theorem conj_j₀_D₄ [Finite G] {y : G} (hy : y ∈ d.D₄) : d.j₀ * y * d.j₀⁻¹ ∈ d.D₄ :=
  (mem_normalizer_iff.mp (h.J_le_normalizer_D₄ h.j₀_mem_J) y).mp hy

theorem normJ_conj [Finite G] {y : G} (hy : y ∈ d.D₄) :
    d.normJ (d.j₀ * y * d.j₀⁻¹) = d.normJ y := by
  have h1 := h.conj_j₀_D₄ hy
  have h2 := h.conj_j₀_D₄ h1
  have h3 : d.j₀ * (d.j₀ * (d.j₀ * y * d.j₀⁻¹) * d.j₀⁻¹) * d.j₀⁻¹ = y := by
    rw [show d.j₀ * (d.j₀ * (d.j₀ * y * d.j₀⁻¹) * d.j₀⁻¹) * d.j₀⁻¹ =
      (d.j₀ * d.j₀ * d.j₀) * y * (d.j₀ * d.j₀ * d.j₀)⁻¹ by group, ← pow_three', h.j₀_pow]
    group
  simp only [Data.normJ]
  rw [h3, h.D₄_comm (mul_mem h1 h2) hy, ← mul_assoc]

theorem normJ_mul [Finite G] {x y : G} (hx : x ∈ d.D₄) (hy : y ∈ d.D₄) :
    d.normJ (x * y) = d.normJ x * d.normJ y := by
  have hx1 := h.conj_j₀_D₄ hx
  have hy1 := h.conj_j₀_D₄ hy
  have hx2 := h.conj_j₀_D₄ hx1
  have hy2 := h.conj_j₀_D₄ hy1
  have hc : ∀ {a b : G}, a ∈ d.D₄ → b ∈ d.D₄ → a * b = b * a := fun ha hb => h.D₄_comm ha hb
  simp only [Data.normJ]
  rw [show d.j₀ * (x * y) * d.j₀⁻¹ = (d.j₀ * x * d.j₀⁻¹) * (d.j₀ * y * d.j₀⁻¹) by group,
    show d.j₀ * ((d.j₀ * x * d.j₀⁻¹) * (d.j₀ * y * d.j₀⁻¹)) * d.j₀⁻¹ =
      (d.j₀ * (d.j₀ * x * d.j₀⁻¹) * d.j₀⁻¹) * (d.j₀ * (d.j₀ * y * d.j₀⁻¹) * d.j₀⁻¹) by group]
  set a₁ := d.j₀ * x * d.j₀⁻¹
  set b₁ := d.j₀ * y * d.j₀⁻¹
  set a₂ := d.j₀ * a₁ * d.j₀⁻¹
  set b₂ := d.j₀ * b₁ * d.j₀⁻¹
  calc x * y * (a₁ * b₁) * (a₂ * b₂) = x * (y * a₁) * b₁ * (a₂ * b₂) := by group
    _ = x * (a₁ * y) * b₁ * (a₂ * b₂) := by rw [hc hy hx1]
    _ = (x * a₁) * (y * b₁) * (a₂ * b₂) := by group
    _ = (x * a₁) * ((y * b₁) * a₂) * b₂ := by group
    _ = (x * a₁) * (a₂ * (y * b₁)) * b₂ := by rw [hc (mul_mem hy hy1) hx2]
    _ = x * a₁ * a₂ * (y * b₁ * b₂) := by group

omit h in
theorem normJ_one : d.normJ 1 = 1 := by simp [Data.normJ]

theorem normJ_inv [Finite G] {y : G} (hy : y ∈ d.D₄) : d.normJ y⁻¹ = (d.normJ y)⁻¹ := by
  have := h.normJ_mul hy (inv_mem hy)
  rw [mul_inv_cancel, normJ_one] at this
  exact (eq_inv_of_mul_eq_one_right this.symm)

theorem exists_pow_of_mem_J [Finite G] {g : G} (hg : g ∈ d.J) : ∃ k : ℕ, g = d.j₀ ^ k := by
  classical
  rw [h.J_eq, (isOfFinOrder_of_finite d.j₀).mem_zpowers_iff_mem_range_orderOf] at hg
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hg
  exact ⟨k, rfl⟩

theorem conj_pow_j₀_D₄ [Finite G] (k : ℕ) {y : G} (hy : y ∈ d.D₄) :
    d.j₀ ^ k * y * (d.j₀ ^ k)⁻¹ ∈ d.D₄ := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ', show d.j₀ * d.j₀ ^ k * y * (d.j₀ * d.j₀ ^ k)⁻¹ =
      d.j₀ * (d.j₀ ^ k * y * (d.j₀ ^ k)⁻¹) * d.j₀⁻¹ by group]
    exact h.conj_j₀_D₄ ih

theorem normJ_conj_J [Finite G] {g y : G} (hg : g ∈ d.J) (hy : y ∈ d.D₄) :
    d.normJ (g * y * g⁻¹) = d.normJ y := by
  obtain ⟨k, rfl⟩ := h.exists_pow_of_mem_J hg
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', show d.j₀ * d.j₀ ^ k * y * (d.j₀ * d.j₀ ^ k)⁻¹ =
      d.j₀ * (d.j₀ ^ k * y * (d.j₀ ^ k)⁻¹) * d.j₀⁻¹ by group,
      h.normJ_conj (h.conj_pow_j₀_D₄ k hy), ih (pow_mem h.j₀_mem_J k)]

theorem normJ_comm [Finite G] {y : G} (hy : y ∈ ⁅d.D₄, d.J⁆) : d.normJ y = 1 := by
  let K : Subgroup G :=
    { carrier := {x | x ∈ d.D₄ ∧ d.normJ x = 1}
      one_mem' := ⟨one_mem _, normJ_one⟩
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        exact ⟨mul_mem ha hb, by rw [h.normJ_mul ha hb, ha1, hb1, one_mul]⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        exact ⟨inv_mem ha, by rw [h.normJ_inv ha, ha1, inv_one]⟩ }
  have hle : ⁅d.D₄, d.J⁆ ≤ K := by
    rw [commutator_le]
    intro x hx g hg
    have hgx : g * x⁻¹ * g⁻¹ ∈ d.D₄ :=
      (mem_normalizer_iff.mp (h.J_le_normalizer_D₄ hg) _).mp (inv_mem hx)
    refine ⟨h.comm_D₄_J_le (commutator_mem_commutator hx hg), ?_⟩
    rw [commutatorElement_def, show x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) by group,
      h.normJ_mul hx hgx, h.normJ_conj_J hg (inv_mem hx), h.normJ_inv hx, mul_inv_cancel]
  exact (hle hy).2

theorem comm_D₄_J_inf_cent [Finite G] {y : G} (hy : y ∈ ⁅d.D₄, d.J⁆)
    (hyj : d.j₀ * y = y * d.j₀) : y = 1 := by
  have hn := h.normJ_comm hy
  have hjy : d.j₀ * y * d.j₀⁻¹ = y := by rw [hyj]; group
  simp only [Data.normJ, hjy] at hn
  have h3 : y ^ 3 = 1 := by rw [pow_three', hn.symm, mul_assoc]
  have hD : y ∈ d.D₄ := h.comm_D₄_J_le hy
  have h2 : y ^ 2 ^ 8 = 1 := by
    have := pow_card_eq_one' (G := d.D₄) (x := ⟨y, hD⟩)
    rw [h.card_D₄] at this
    simpa using congrArg Subtype.val this
  have hord3 := orderOf_dvd_of_pow_eq_one h3
  have hord2 := orderOf_dvd_of_pow_eq_one h2
  have : orderOf y ∣ Nat.gcd 3 (2 ^ 8) := Nat.dvd_gcd hord3 hord2
  rw [show Nat.gcd 3 (2 ^ 8) = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

theorem J_le_L : d.J ≤ d.L := by rw [h.J_eq, zpowers_le]; exact h.j₀_mem_L

theorem X₈_le_A₄ [Finite G] : d.X₈ ≤ d.A₄ := by
  rw [← h.comm_A₄_J, commutator_le]
  intro a ha g hg
  rw [commutatorElement_def, show a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) by group]
  exact mul_mem ha ((mem_normalizer_iff.mp (h.X₄_le_normalizer_A₄ (h.J_le_X₄ hg)) _).mp
    (inv_mem ha))

theorem X₈_le_comm [Finite G] : d.X₈ ≤ ⁅d.D₄, d.J⁆ := by
  rw [← h.comm_A₄_J]; exact commutator_mono h.A₄_le_D₄ le_rfl

theorem comm_inf_A₄ [Finite G] : ⁅d.D₄, d.J⁆ ⊓ d.A₄ = d.X₈ := by
  refine le_antisymm (fun y hy => ?_) (le_inf h.X₈_le_comm h.X₈_le_A₄)
  obtain ⟨hyc, hyA⟩ := mem_inf.mp hy
  obtain ⟨c, hc, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => h.A₄_comm (mem_inf.mp ha).1 (h.X₈_le_A₄ hb)) (h.A₄_le_cent_J_sup hyA)
  have hcJ : d.j₀ * c = c * d.j₀ := (mem_centralizer_iff.mp (mem_inf.mp hc).2 _ h.j₀_mem_J)
  have hc' : c ∈ ⁅d.D₄, d.J⁆ := by
    have := mul_mem hyc (inv_mem (h.X₈_le_comm hb))
    simpa using this
  rw [h.comm_D₄_J_inf_cent hc' hcJ, one_mul]
  exact hb

theorem crossed_comm_J [Finite G] {x g : G} (hx : x ∈ d.D₄) (hg : g ∈ d.J) :
    ⁅x, g⁆⁻¹ * d.t * ⁅x, g⁆ * d.t = ⁅x⁻¹ * d.t * x * d.t, g⁆ := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  have hgt : g * d.t = d.t * g := h.comm_of_mem_L (h.J_le_L hg)
  have hgx : g * x⁻¹ * g⁻¹ ∈ d.D₄ :=
    (mem_normalizer_iff.mp (h.J_le_normalizer_D₄ hg) _).mp (inv_mem hx)
  have e1 : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
  rw [e1, h.crossed_U₄_mul (hU hx) (hU hgx), crossed_conj hgt, h.crossed_U₄_inv (hU hx),
    commutatorElement_def]
  group

theorem crossed_comm_D₄_J [Finite G] {y : G} (hy : y ∈ ⁅d.D₄, d.J⁆) :
    y⁻¹ * d.t * y * d.t ∈ d.X₈ := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  let R : Subgroup G :=
    { carrier := {y | y ∈ d.D₄ ∧ y⁻¹ * d.t * y * d.t ∈ d.X₈}
      one_mem' := ⟨one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by rw [h.crossed_U₄_mul (hU ha) (hU hb)]; exact mul_mem ha' hb'⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨inv_mem ha, by rw [h.crossed_U₄_inv (hU ha)]; exact inv_mem ha'⟩ }
  have hle : ⁅d.D₄, d.J⁆ ≤ R := by
    rw [commutator_le]
    intro x hx g hg
    refine ⟨h.comm_D₄_J_le (commutator_mem_commutator hx hg), ?_⟩
    rw [h.crossed_comm_J hx hg, ← h.comm_A₄_J]
    exact commutator_mem_commutator (h.crossed_X₄ (D_le_X₄ (h.D₄_le_D hx))) hg
  exact (hle hy).2

theorem exists_comm_D₄_J_conj [Finite G] {b : G} (hb : b ∈ d.X₈) :
    ∃ y ∈ ⁅d.D₄, d.J⁆, y⁻¹ * d.t * y * d.t = b := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  let R : Subgroup G :=
    { carrier := {b | ∃ y ∈ ⁅d.D₄, d.J⁆, y⁻¹ * d.t * y * d.t = b}
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, mul_mem hp hq, h.crossed_U₄_mul (hU (h.comm_D₄_J_le hp))
          (hU (h.comm_D₄_J_le hq))⟩
      inv_mem' := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p⁻¹, inv_mem hp, h.crossed_U₄_inv (hU (h.comm_D₄_J_le hp))⟩ }
  have hle : d.X₈ ≤ R := by
    rw [← h.comm_A₄_J, commutator_le]
    intro a ha g hg
    obtain ⟨x, hx, hxt⟩ := h.exists_D₄_conj ha
    have hxa : x⁻¹ * d.t * x * d.t = a := by rw [hxt, mul_assoc, h.t_sq, mul_one]
    exact ⟨⁅x, g⁆, commutator_mem_commutator hx hg, by rw [h.crossed_comm_J hx hg, hxa]⟩
  exact hle hb

theorem z_not_mem_X₈ : d.z ∉ d.X₈ := fun hz => h.z_ne_one (by
  have : d.z ∈ d.X₈ ⊓ zpowers d.z := mem_inf.mpr ⟨hz, mem_zpowers _⟩
  rwa [h.X₈_inf_z, mem_bot] at this)

theorem Z₂S_le_A₄ [Finite G] : d.Z₂S ≤ d.A₄ := sup_le h.X₈_le_A₄ (zpowers_le.mpr h.z_mem_A₄)

theorem Z₂S_le_A₁ : d.Z₂S ≤ d.A₁ := sup_le h.X₈_le_A₁ (zpowers_le.mpr h.z_mem_A₁)

theorem card_Z₂S [Finite G] : Nat.card d.Z₂S = 8 := by
  have := card_sup_zpowers (B := d.X₈) h.z_sq
    (fun b hb => h.A₄_comm (h.X₈_le_A₄ hb) h.z_mem_A₄) h.z_not_mem_X₈
  rw [this, h.card_X₈]

theorem V₂_le_D₄ [Finite G] : d.V₂ ≤ d.D₄ := sup_le h.comm_D₄_J_le V₁_le_D₄

theorem Z₂S_le_V₂ [Finite G] : d.Z₂S ≤ d.V₂ :=
  sup_le (h.X₈_le_comm.trans le_sup_left) (zpowers_le.mpr (mem_sup_right h.z_mem_V₁))

theorem crossed_V₂ [Finite G] {y : G} (hy : y ∈ d.V₂) : y⁻¹ * d.t * y * d.t ∈ d.Z₂S := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha v hv => h.D₄_comm (h.comm_D₄_J_le ha) (V₁_le_D₄ hv)) hy
  rw [h.crossed_U₄_mul (hU (h.comm_D₄_J_le ha)) (hU (V₁_le_D₄ hv))]
  exact mul_mem (mem_sup_left (h.crossed_comm_D₄_J ha)) (mem_sup_right (h.crossed_V₁ hv))

theorem exists_V₂_conj [Finite G] {b : G} (hb : b ∈ d.Z₂S) :
    ∃ y ∈ d.V₂, y⁻¹ * d.t * y * d.t = b := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  let R : Subgroup G :=
    { carrier := {b | ∃ y ∈ d.V₂, y⁻¹ * d.t * y * d.t = b}
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, mul_mem hp hq, h.crossed_U₄_mul (hU (h.V₂_le_D₄ hp)) (hU (h.V₂_le_D₄ hq))⟩
      inv_mem' := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p⁻¹, inv_mem hp, h.crossed_U₄_inv (hU (h.V₂_le_D₄ hp))⟩ }
  have hle : d.Z₂S ≤ R := by
    refine sup_le (fun b hb => ?_) (zpowers_le.mpr ?_)
    · obtain ⟨y, hy, hyb⟩ := h.exists_comm_D₄_J_conj hb
      exact ⟨y, mem_sup_left hy, hyb⟩
    · obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
      exact ⟨v, mem_sup_right hv, by rw [hvt, mul_assoc, h.t_sq, mul_one]⟩
  exact hle hb

theorem V₂_inf_H [Finite G] : d.V₂ ⊓ d.H = d.Z₂S := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  refine le_antisymm (fun y hy => ?_) (le_inf h.Z₂S_le_V₂ (h.Z₂S_le_A₄.trans
    (h.A₄_le_L.trans h.L_le_H)))
  obtain ⟨hyV, hyH⟩ := mem_inf.mp hy
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha v hv => h.D₄_comm (h.comm_D₄_J_le ha) (V₁_le_D₄ hv)) hyV
  have hcr : (a * v)⁻¹ * d.t * (a * v) * d.t = 1 :=
    (crossed_eq_one_iff h.t_sq).mpr (mem_centralizer_singleton_iff.mp hyH)
  rw [h.crossed_U₄_mul (hU (h.comm_D₄_J_le ha)) (hU (V₁_le_D₄ hv))] at hcr
  have h1 := h.crossed_comm_D₄_J ha
  have h2 := h.crossed_V₁ hv
  have h3 : a⁻¹ * d.t * a * d.t ∈ d.X₈ ⊓ zpowers d.z := by
    refine mem_inf.mpr ⟨h1, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hcr]
    exact inv_mem h2
  rw [h.X₈_inf_z, mem_bot] at h3
  rw [h3, one_mul] at hcr
  have haH : a ∈ d.X₈ := by
    rw [← h.comm_inf_A₄]
    refine mem_inf.mpr ⟨ha, ?_⟩
    rw [← h.D₄_inf_H]
    exact mem_inf.mpr ⟨h.comm_D₄_J_le ha,
      mem_centralizer_singleton_iff.mpr ((crossed_eq_one_iff h.t_sq).mp h3)⟩
  have hvH : v ∈ zpowers d.z := h.V₁_inf_H_le (mem_inf.mpr ⟨hv,
    mem_centralizer_singleton_iff.mpr ((crossed_eq_one_iff h.t_sq).mp hcr)⟩)
  exact mul_mem (mem_sup_left haH) (mem_sup_right hvH)

theorem card_V₂ [Finite G] : Nat.card d.V₂ = 2 ^ 6 := by
  have hcent : d.V₂ ≤ centralizer (d.Z₂S : Set G) := fun y hy =>
    mem_centralizer_iff.mpr fun b hb => h.A₄_comm_D (h.Z₂S_le_A₄ hb) (h.D₄_le_D (h.V₂_le_D₄ hy))
  rw [card_eq_of_crossed_onto h.t_sq hcent (fun y hy => h.crossed_V₂ hy)
    (fun b hb => h.exists_V₂_conj hb)]
  change Nat.card (d.V₂ ⊓ d.H : Subgroup G) * _ = _
  rw [h.V₂_inf_H, h.card_Z₂S]
  norm_num

theorem X₁_cases {x : G} (hx : x ∈ d.X₁) : x = 1 ∨ x = d.u₁ ∨ x = d.u₂ ∨ x = d.u₁ * d.u₂ := by
  have h1 := h.u₁_sq
  have h2 := h.u₂_sq
  have hc := h.u₁_comm_u₂
  let T : Subgroup G :=
    { carrier := {g | g = 1 ∨ g = d.u₁ ∨ g = d.u₂ ∨ g = d.u₁ * d.u₂}
      one_mem' := Or.inl rfl
      mul_mem' := by
        have e1 : d.u₁ * d.u₂ * d.u₁ = d.u₂ := by rw [hc, mul_assoc, h1, mul_one]
        have e2 : d.u₁ * (d.u₁ * d.u₂) = d.u₂ := by rw [← mul_assoc, h1, one_mul]
        have e3 : d.u₂ * d.u₁ = d.u₁ * d.u₂ := hc.symm
        have e4 : d.u₂ * (d.u₁ * d.u₂) = d.u₁ := by rw [← mul_assoc, ← hc, mul_assoc, h2, mul_one]
        have e5 : d.u₁ * d.u₂ * d.u₂ = d.u₁ := by rw [mul_assoc, h2, mul_one]
        have e6 : d.u₁ * d.u₂ * (d.u₁ * d.u₂) = 1 := by rw [← mul_assoc, e1, h2]
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp only [Set.mem_ofPred_eq, one_mul, mul_one, h1, h2, e1, e2, e3, e4, e5, e6,
            true_or, or_true]
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl)
        · simp
        · right; left; exact inv_eq_of_mul_eq_one_right h1
        · right; right; left; exact inv_eq_of_mul_eq_one_right h2
        · right; right; right
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h2, hc] }
  have hle : closure {d.u₁, d.u₂} ≤ T := by
    rw [closure_le]
    rintro g (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  exact hle (h.X₁_le_closure hx)

theorem X₁_sq {x : G} (hx : x ∈ d.X₁) : x * x = 1 := by
  rcases h.X₁_cases hx with rfl | rfl | rfl | rfl
  · simp
  · exact h.u₁_sq
  · exact h.u₂_sq
  · rw [show d.u₁ * d.u₂ * (d.u₁ * d.u₂) = d.u₁ * (d.u₂ * d.u₁) * d.u₂ by group,
      ← h.u₁_comm_u₂, show d.u₁ * (d.u₁ * d.u₂) * d.u₂ = (d.u₁ * d.u₁) * (d.u₂ * d.u₂) by group,
      h.u₁_sq, h.u₂_sq, one_mul]

theorem comm_X₁_D₄ [Finite G] {x y : G} (hx : x ∈ d.X₁) (hy : y ∈ d.D₄)
    (hcy : y⁻¹ * d.t * y * d.t ∈ d.Z₂S) : x * y * x⁻¹ * y⁻¹ ∈ d.Z₂S ⊔ d.V₁ := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  have hxN : x ∈ normalizer (d.D₄ : Set G) := h.Λ_le_normalizer_D₄ (h.X₁_le_Λ hx)
  have hxt : x * d.t = d.t * x := h.comm_of_mem_L (h.Λ_le_L (h.X₁_le_Λ hx))
  have hxy : x * y * x⁻¹ ∈ d.D₄ := (mem_normalizer_iff.mp hxN y).mp hy
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcD : c ∈ d.D₄ := mul_mem hxy (inv_mem hy)
  have hcr : c⁻¹ * d.t * c * d.t ∈ zpowers d.z := by
    rw [hc, h.crossed_U₄_mul (hU hxy) (inv_mem (hU hy)), crossed_conj hxt, h.crossed_U₄_inv (hU hy)]
    have := h.comm_X₁_Z₂ x hx _ hcy
    simpa [mul_assoc] using this
  by_cases hx1 : x = 1
  · rw [hc, hx1]; simp
  obtain ⟨v, hv, hvc⟩ : ∃ v ∈ d.V₁, v⁻¹ * d.t * v * d.t = c⁻¹ * d.t * c * d.t := by
    rcases h.mem_zpowers_z_iff.mp hcr with h1 | h1
    · exact ⟨1, one_mem _, by rw [h1, inv_one, one_mul, mul_one, h.t_sq]⟩
    · obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
      exact ⟨v, hv, by rw [h1, hvt, mul_assoc, h.t_sq, mul_one]⟩
  set a := c * v⁻¹ with ha
  have haA : a ∈ d.A₄ := by
    rw [← h.D₄_inf_H]
    refine mem_inf.mpr ⟨mul_mem hcD (inv_mem (V₁_le_D₄ hv)), ?_⟩
    change a ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff, ← crossed_eq_one_iff h.t_sq, ha,
      h.crossed_U₄_mul (hU hcD) (inv_mem (hU (V₁_le_D₄ hv))), h.crossed_U₄_inv (hU (V₁_le_D₄ hv)),
      ← hvc, mul_inv_cancel]
  have hvX : x * v = v * x := mem_centralizer_iff.mp (V₁_le_cent_X₁ hv) x hx
  have hx2 : x * x = 1 := h.X₁_sq hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hav : a * v = v * a := h.D₄_comm (h.A₄_le_D₄ haA) (V₁_le_D₄ hv)
  have hca : c = a * v := by rw [ha]; group
  have hvv : v * v ∈ zpowers d.z := by
    refine h.V₁_inf_H_le (mem_inf.mpr ⟨mul_mem hv hv, mem_centralizer_singleton_iff.mpr ?_⟩)
    rw [← crossed_eq_one_iff h.t_sq, h.crossed_U₄_mul (hU (V₁_le_D₄ hv)) (hU (V₁_le_D₄ hv))]
    rcases h.mem_zpowers_z_iff.mp (h.crossed_V₁ hv) with h1 | h1 <;> rw [h1]
    · rw [one_mul]
    · exact h.z_sq
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    rw [hc, hxi]
    calc x * (x * y * x * y⁻¹) * x = (x * x) * y * x * y⁻¹ * x := by group
      _ = (x * y * x * y⁻¹)⁻¹ := by
          rw [hx2, one_mul, show (x * y * x * y⁻¹)⁻¹ = y * x⁻¹ * y⁻¹ * x⁻¹ by group, hxi]
  have hxa : x * a * x⁻¹ * a⁻¹ = (v * v)⁻¹ := by
    have e1 : x * a * x⁻¹ = c⁻¹ * v⁻¹ := by
      rw [ha, show x * (c * v⁻¹) * x⁻¹ = (x * c * x⁻¹) * (x * v⁻¹ * x⁻¹) by group, hxc,
        show x * v⁻¹ * x⁻¹ = v⁻¹ by
          calc x * v⁻¹ * x⁻¹ = (x * v * x⁻¹)⁻¹ := by group
            _ = v⁻¹ := by rw [hvX, mul_inv_cancel_right]]
    rw [e1, hca, ha]
    have ha2 : a * a = 1 := h.A₄_sq haA
    calc (a * v)⁻¹ * v⁻¹ * (c * v⁻¹)⁻¹ = (a * v)⁻¹ * v⁻¹ * (a * v * v⁻¹)⁻¹ := by rw [hca]
      _ = v⁻¹ * a⁻¹ * v⁻¹ * a⁻¹ := by group
      _ = (v * v)⁻¹ := by
          have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
          rw [hai, show v⁻¹ * a * v⁻¹ * a = v⁻¹ * (a * v⁻¹) * a by group,
            show a * v⁻¹ = v⁻¹ * a by
              calc a * v⁻¹ = v⁻¹ * (v * a) * v⁻¹ := by group
                _ = v⁻¹ * (a * v) * v⁻¹ := by rw [hav]
                _ = v⁻¹ * a := by group,
            show v⁻¹ * (v⁻¹ * a) * a = v⁻¹ * v⁻¹ * (a * a) by group, ha2]
          group
  have haZ : a ∈ d.Z₂S := h.A₄_comm_X₁ x hx hx1 a haA (by rw [hxa]; exact inv_mem hvv)
  rw [hca]
  exact mul_mem (mem_sup_left haZ) (mem_sup_right hv)

theorem X₁_le_normalizer_Z₂V₁ [Finite G] {x : G} (hx : x ∈ d.X₁) :
    x ∈ normalizer ((d.Z₂S ⊔ d.V₁ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : d.Z₂S ⊔ d.V₁ ≤ (d.Z₂S ⊔ d.V₁).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun b hb => ?_) (fun v hv => ?_)
    · change x * b * x⁻¹ ∈ d.Z₂S ⊔ d.V₁
      have e : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
      rw [e]
      exact mul_mem (mem_sup_left (mem_sup_right (h.comm_X₁_Z₂ x hx b hb))) (mem_sup_left hb)
    · change x * v * x⁻¹ ∈ d.Z₂S ⊔ d.V₁
      rw [mem_centralizer_iff.mp (V₁_le_cent_X₁ hv) x hx, mul_inv_cancel_right]
      exact mem_sup_right hv
  exact fun g hg => hle hg

theorem A₃_le_cent_Z₂V₁ [Finite G] : d.A₃ ≤ centralizer ((d.Z₂S ⊔ d.V₁ : Subgroup G) : Set G) := by
  intro a ha
  refine mem_centralizer_sup ?_ ?_
  · rw [mem_centralizer_iff]
    intro b hb
    exact (mem_centralizer_iff.mp (h.A₃_le_cent_A₄ ha) b (h.Z₂S_le_A₄ hb))
  · rw [mem_centralizer_iff]
    intro v hv
    exact (mem_centralizer_iff.mp (h.V₁_le_cent_A₃ hv) a ha).symm

theorem mem_normalizer_C₀_of [Finite G] {y : G} (hy : y ∈ d.D₄)
    (hcy : y⁻¹ * d.t * y * d.t ∈ d.Z₂S) : y ∈ normalizer (d.C₀ : Set G) := by
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  rw [h.C₀_eq]
  let T : Subgroup G :=
    { carrier := {g | g ∈ normalizer ((d.Z₂S ⊔ d.V₁ : Subgroup G) : Set G) ∧
        y * g * y⁻¹ * g⁻¹ ∈ d.Z₂S ⊔ d.V₁}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
            (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha' ((mem_normalizer_iff.mp ha _).mp hb')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := (mem_normalizer_iff.mp (inv_mem ha) _).mp (inv_mem ha')
        simpa using this }
  have hX₁T : d.X₁ ≤ T := fun x hx =>
    ⟨h.X₁_le_normalizer_Z₂V₁ hx, by
      have := inv_mem (h.comm_X₁_D₄ hx hy hcy)
      rwa [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group] at this⟩
  have hA₃T : d.A₃ ≤ T := fun a ha =>
    ⟨centralizer_le_normalizer _ (h.A₃_le_cent_Z₂V₁ ha), by
      rw [← mem_centralizer_iff.mp (h.D_le_cent_A₃ (h.D₄_le_D hy)) a ha]
      simp⟩
  have hA₁T : d.A₁ ≤ T := h.A₁_le.trans (sup_le hX₁T hA₃T)
  have hZV : d.Z₂S ⊔ d.V₁ ≤ d.C₀' := sup_le (h.Z₂S_le_A₁.trans le_sup_left)
    (le_sup_left.trans le_sup_right)
  apply mem_normalizer_of_conj_mem
  have hle : d.C₀' ≤ d.C₀'.comap (MulAut.conj y).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (sup_le (fun v hv => ?_) ?_)
    · change y * a * y⁻¹ ∈ d.C₀'
      have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact mul_mem (hZV (hA₁T ha).2) (mem_sup_left ha)
    · change y * v * y⁻¹ ∈ d.C₀'
      rw [h.D₄_comm hy (V₁_le_D₄ hv), mul_inv_cancel_right]
      exact mem_sup_right (mem_sup_left hv)
    · rw [zpowers_le]
      change y * d.t * y⁻¹ ∈ d.C₀'
      have hc' : y⁻¹⁻¹ * d.t * y⁻¹ * d.t ∈ d.Z₂S := by
        rw [h.crossed_U₄_inv (hU hy)]; exact inv_mem hcy
      rw [inv_inv] at hc'
      have e : y * d.t * y⁻¹ = (y * d.t * y⁻¹ * d.t) * d.t := by
        rw [mul_assoc _ d.t d.t, h.t_sq, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left (h.Z₂S_le_A₁ hc')) (mem_sup_right (mem_sup_right
        (mem_zpowers _)))
  exact fun g hg => hle hg

theorem V₂_le_normalizer_C₀ [Finite G] : d.V₂ ≤ normalizer (d.C₀ : Set G) := fun _ hy =>
  h.mem_normalizer_C₀_of (h.V₂_le_D₄ hy) (h.crossed_V₂ hy)

theorem V₂_le_normalizer_V₁ [Finite G] : d.V₂ ≤ normalizer (d.V₁ : Set G) := fun _ hy =>
  centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hv =>
    h.D₄_comm (V₁_le_D₄ hv) (h.V₂_le_D₄ hy))

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
