module

public import CFSG.LargeExtraspecial.S10EightA
public import CFSG.LargeExtraspecial.S10Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem exists_ρ_of_mem_Yb {u : S.O} (hu : u ∈ Yb) : ∃ k : S.M, S.ρ k = u :=
  MonoidHom.mem_range.mp (Rbar_le_Mbar (D.dec.le_Rbar_right hu))

theorem mem_Lbar_mul {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) {k : S.M} (hk : S.ρ k ∈ Yb) :
    τ ∈ S.Lbar ((k : G) * g) := by
  have h := conj_mem_Lbar_mul S k hτ.1
  have hc : S.ρ k * τ * (S.ρ k)⁻¹ = τ := by
    rw [← D.dec.comm τ hτ.2 _ hk]
    group
  rwa [hc] at h

theorem t_mem_Ebar (hCE : CentralExtInput.{u}) : t ∈ S.Lbar g ⊓ Xb :=
  ⟨X.ht, D.dec.Nbar_le hCE X (self_mem_Nbar X.H X.ht)⟩

theorem Yb_le_Rbar {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) : Yb ≤ Rbar S g τ := by
  obtain ⟨y, hyY, hyL, hyN⟩ := D.exists_y
  have hconj : ∀ v : Yb, ((v * ⟨y, hyY⟩ * v⁻¹ : Yb) : S.O) ∈ Rbar S g τ := by
    intro v
    obtain ⟨k, hk⟩ := D.exists_ρ_of_mem_Yb v.2
    have hkY : S.ρ k ∈ Yb := by rw [hk]; exact v.2
    have h1 := Lbar_mul_le_Rbar (D.mem_Lbar_mul hτ hkY) (conj_mem_Lbar_mul S k hyL)
    rw [hk] at h1
    simpa using h1
  obtain ⟨e⟩ := D.dec.iso
  have hs1 : e ⟨y, hyY⟩ * e ⟨y, hyY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hyY⟩ : Yb) * ⟨y, hyY⟩ = 1 := Subtype.ext (S4.mul_self_of_mem_Lbar S X.haQ hyL)
    rw [this, map_one]
  have hs2 : e ⟨y, hyY⟩ ≠ 1 := by
    intro h
    have : (⟨y, hyY⟩ : Yb) = 1 := e.injective (by rw [h, map_one])
    exact hyN (by rw [show y = 1 from congrArg Subtype.val this]; exact one_mem _)
  have key : ∀ a : Equiv.Perm (Fin 3),
      ((e.symm (a * e ⟨y, hyY⟩ * a⁻¹) : Yb) : S.O) ∈ Rbar S g τ := by
    intro a
    have : e.symm (a * e ⟨y, hyY⟩ * a⁻¹) = e.symm a * ⟨y, hyY⟩ * (e.symm a)⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [this]
    exact hconj _
  intro u hu
  have hu' : u = ((e.symm (e ⟨u, hu⟩) : Yb) : S.O) := by rw [MulEquiv.symm_apply_apply]
  rcases perm_three_gen _ (e ⟨u, hu⟩) hs1 hs2 with ⟨a, ha⟩ | ⟨a, b, hab⟩
  · rw [hu', ha]
    exact key a
  · rw [hu', hab, map_mul, Subgroup.coe_mul]
    exact mul_mem (key a) (key b)

theorem sup_le_Rbar {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) :
    (S.Lbar g ⊓ Xb) ⊔ Yb ≤ Rbar S g τ :=
  sup_le (inf_le_left.trans (Lbar_le_Rbar hτ.1)) (D.Yb_le_Rbar hτ)

theorem conj_mem_sup {u : S.O} (hu : u ∈ Yb) {w : S.O} (hw : w ∈ (S.Lbar g ⊓ Xb) ⊔ Yb) :
    u * w * u⁻¹ ∈ (S.Lbar g ⊓ Xb) ⊔ Yb := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute (A := S.Lbar g ⊓ Xb) (B := Yb)
    (fun a ha b hb => D.dec.comm a ha.2 b hb) hw
  have hau : a * u = u * a := D.dec.comm a ha.2 u hu
  have e : u * (a * b) * u⁻¹ = a * (u * b * u⁻¹) := by
    calc u * (a * b) * u⁻¹ = (u * a) * b * u⁻¹ := by group
      _ = (a * u) * b * u⁻¹ := by rw [hau]
      _ = a * (u * b * u⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right (mul_mem (mul_mem hu hb) (inv_mem hu)))

theorem Lbar_le_sup (hCE : CentralExtInput.{u}) : S.Lbar g ≤ (S.Lbar g ⊓ Xb) ⊔ Yb := by
  obtain ⟨F, -, hFX, y, hyY, hyL, hπy⟩ := D.exists_frame hCE
  intro l hl
  have hlR := Lbar_le_Rbar X.ht hl
  have hyR := Lbar_le_Rbar X.ht hyL
  rcases stab_mem_Γ₁_or _ (F.π_mem_stabA hl) with h | h
  · refine Subgroup.mem_sup_left ⟨hl, ?_⟩
    rw [hFX]
    exact (F.mem_pre).mpr ⟨hlR, mem_Γ₁.mpr h⟩
  · have hly : l * y ∈ S.Lbar g ⊓ Xb := by
      refine ⟨mul_mem hl hyL, ?_⟩
      rw [hFX]
      refine (F.mem_pre).mpr ⟨mul_mem hlR hyR, ?_⟩
      have e : F.π ⟨l * y, mul_mem hlR hyR⟩ = F.π ⟨l, hlR⟩ * τ₂ := by
        rw [← hπy, ← map_mul]
        rfl
      rw [mem_Γ₁, e]
      exact h
    have e : l = l * y * y := by rw [mul_assoc, S4.mul_self_of_mem_Lbar S X.haQ hyL, mul_one]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hly) (Subgroup.mem_sup_right hyY)

theorem Lbar_mul_le_sup (hCE : CentralExtInput.{u}) {k : S.M} (hk : S.ρ k ∈ Yb) :
    S.Lbar ((k : G) * g) ≤ (S.Lbar g ⊓ Xb) ⊔ Yb := by
  rw [Lbar_mul S k g]
  rintro _ ⟨l, hl, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact D.conj_mem_sup hk (D.Lbar_le_sup hCE hl)

theorem two_mul_card_Ebar (hCE : CentralExtInput.{u}) :
    2 * Nat.card (S.Lbar g ⊓ Xb : Subgroup S.O) = Nat.card (S.Lbar g) := by
  have h1 := Subgroup.relIndex_mul_card (S.Lbar g ⊓ Xb) (S.Lbar g)
  rw [(timmesfeld_10_3_hyperplane hCE X D.dec).1,
    inf_of_le_left (inf_le_left : S.Lbar g ⊓ Xb ≤ S.Lbar g)] at h1
  exact h1

theorem exists_d (hCE : CentralExtInput.{u}) :
    ∃ k : S.M, S.ρ k ∈ ⁅Yb, Yb⁆ ∧ S.ρ k ≠ 1 ∧
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) ∧
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
        S.cl (((k * k : S.M) : G) * g * S.z * (((k * k : S.M) : G) * g)⁻¹) := by
  obtain ⟨F, hFY, -, -⟩ := D.exists_frame hCE
  obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.dec.commutator_ne_bot
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hdY := ((D.dec.mem_commutator_iff).mp hdY').1
  have hd3 := ((D.dec.mem_commutator_iff).mp hdY').2
  obtain ⟨k, rfl⟩ := D.exists_ρ_of_mem_Yb hdY
  have hkR := D.dec.le_Rbar_right hdY
  have hπ1 : (F.π ⟨S.ρ k, hkR⟩).1 = 1 := mem_Γ₂.mp (hFY ▸ ⟨⟨S.ρ k, hdY⟩, rfl⟩)
  have hπ3 : F.π ⟨S.ρ k, hkR⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨S.ρ k, hkR⟩ : Rbar S g t) ^ 3 = 1 := Subtype.ext hd3
    rw [this, map_one]
  have hπne : F.π ⟨S.ρ k, hkR⟩ ≠ 1 := fun h => hd1 (by
    have := D.dec.piY_injective hCE F (a₁ := ⟨S.ρ k, hdY⟩) (a₂ := 1)
      (by rw [DirDec.piY_apply, map_one]; exact h)
    exact congrArg Subtype.val this)
  have hth := D.mem_Lbar_mul (D.t_mem_Ebar hCE) hdY
  have hφb : F.φ (bV hth) = act (F.π ⟨S.ρ k, hkR⟩) E00 := by
    rw [bV_eq_resV X hkR hth, F.φ_resV_aV]
  have hkkY : S.ρ (k * k) ∈ Yb := by rw [map_mul]; exact mul_mem hdY hdY
  have hkkR := D.dec.le_Rbar_right hkkY
  have hth2 := D.mem_Lbar_mul (D.t_mem_Ebar hCE) hkkY
  have hφb2 : F.φ (bV hth2) = act (F.π ⟨S.ρ k, hkR⟩ * F.π ⟨S.ρ k, hkR⟩) E00 := by
    rw [bV_eq_resV X hkkR hth2, F.φ_resV_aV, ← map_mul]
    congr 2
    exact Subtype.ext (map_mul S.ρ k k)
  refine ⟨k, hdY', hd1, fun h => ?_, ?_, ?_⟩
  · have h1 : bV hth = aV X.ht := Subtype.ext (by rw [coe_bV]; exact h)
    have h2 := congrArg F.φ h1
    rw [hφb, F.base] at h2
    exact act_Γ₂_ne _ hπ1 hπ3 hπne h2
  · have h1 := (beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ (bV hth)).mp (by
      rw [F.beta_eq, F.base, hφb]
      exact pf_act_Γ₂ _ hπ1)
    rwa [coe_bV] at h1
  · have h1 : aV X.ht + bV hth = bV hth2 := F.φ.injective (by
      rw [map_add, F.base, hφb, hφb2]
      exact act_Γ₂_add _ hπ1 hπ3 hπne)
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_add, coe_bV, coe_bV] at h2
    exact h2

end Dec108

end CFSG.LargeExtraspecial.S10
